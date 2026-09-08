/-
Reference terminal-event probabilities for `Program`.

The finite sample points are terminal branch occurrences paired with basis
indices inside the declared quantum register.  An event may inspect the basis
index, semantic branch history, final classical register, and immutable input,
but it cannot inspect amplitudes.  The history includes reset outcomes and
serves as a diagnostic semantic record.  Public outputs use the selected fields.
-/
import VQ.Program.Semantics
import VQ.Semantics.Marginal

namespace VQ
namespace Tests
namespace ProgramObservation

open Algebra Semantics Op

structure TerminalView where
  basisIndex : Nat
  history : List Bool
  classical : Nat
  input : Nat
  deriving DecidableEq

def view (b : Branch d) (i : Nat) : TerminalView :=
  { basisIndex := i, history := b.outcomes, classical := b.creg, input := b.input }

def branchEventProb (w : Nat) (event : TerminalView → Bool) (b : Branch d) : Dy d :=
  dsum (2 ^ w) fun i => if event (view b i) then absSq (b.state i) else Dy.zero d

def eventProb (w : Nat) (event : TerminalView → Bool) : List (Branch d) → Dy d
  | [] => Dy.zero d
  | b :: bs => branchEventProb w event b + eventProb w event bs

def terminalEventProb (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) (event : TerminalView → Bool) : Dy (deg level) :=
  eventProb p.width event (runProgram level p input u)

theorem branchEventProb_false (w : Nat) (b : Branch d) :
    branchEventProb w (fun _ => false) b = Dy.zero d := by
  rw [branchEventProb]
  exact dsum_eq_zero (fun _ _ => rfl)

theorem branchEventProb_true (w : Nat) (b : Branch d) :
    branchEventProb w (fun _ => true) b = branchProb w b := by
  rw [branchEventProb, branchProb, normSq]
  exact dsum_congr (fun _ _ => rfl)

theorem eventProb_false (w : Nat) (bs : List (Branch d)) :
    eventProb w (fun _ => false) bs = Dy.zero d := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [eventProb, branchEventProb_false, ih, Dy.add_zero]

theorem eventProb_true (w : Nat) (bs : List (Branch d)) :
    eventProb w (fun _ => true) bs = totalProb w bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [eventProb, totalProb_cons, branchEventProb_true, ih]

theorem terminalEventProb_false (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) :
    terminalEventProb level p input u (fun _ => false) = Dy.zero (deg level) :=
  eventProb_false p.width _

theorem terminalEventProb_true (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) :
    terminalEventProb level p input u (fun _ => true) =
      totalProb p.width (runProgram level p input u) :=
  eventProb_true p.width _

theorem terminalEventProb_basis_total (level : Nat) (p : Program)
    (hp : p.wellFormed level = true) (input inp : Nat) (hinp : inp < 2 ^ p.width) :
    terminalEventProb level p input (basis inp) (fun _ => true) = Dy.one (deg level) := by
  rw [terminalEventProb_true]
  exact totalProb_basis level p hp input hinp

/-- Lift a basis-index predicate to a terminal event that ignores branch metadata. -/
def quantumEvent (accept : Nat → Bool) : TerminalView → Bool :=
  fun v => accept v.basisIndex

/-- The weight of a basis-index event in one pure state. -/
def stateEventProb (w : Nat) (accept : Nat → Bool) (u : Vec d) : Dy d :=
  dsum (2 ^ w) fun i => if accept i then absSq (u i) else Dy.zero d

private theorem branchEventProb_quantum_smul
    (w : Nat) (accept : Nat → Bool) (b : Branch d)
    (a : Dy d) (u : Vec d) (hstate : b.state = a • u) :
    branchEventProb w (quantumEvent accept) b =
      absSq a * stateEventProb w accept u := by
  rw [branchEventProb, stateEventProb, hstate, dsum_mul_left]
  refine dsum_congr (fun i _ => ?_)
  dsimp +instances only [quantumEvent, view]
  simp only [Vec.smul_apply]
  by_cases h : accept i = true
  · rw [if_pos h, if_pos h, absSq_mul]
  · rw [if_neg h, if_neg h, Dy.mul_zero]

private theorem eventProb_quantum_factor
    (w : Nat) (accept : Nat → Bool) (u : Vec d)
    (amp : List Bool → Dy d)
    (hnorm : normSq (2 ^ w) u = Dy.one d) :
    ∀ bs : List (Branch d),
      (∀ b ∈ bs, b.state = amp b.outcomes • u) →
        eventProb w (quantumEvent accept) bs =
          totalProb w bs * stateEventProb w accept u := by
  intro bs
  induction bs with
  | nil =>
      intro _
      rw [eventProb, totalProb_nil, Dy.zero_mul]
  | cons b bs ih =>
      intro hstate
      have hbstate : b.state = amp b.outcomes • u :=
        hstate b (List.mem_cons_self ..)
      have htail : ∀ x ∈ bs, x.state = amp x.outcomes • u :=
        fun x hx => hstate x (List.mem_cons_of_mem b hx)
      have hbranchEvent := branchEventProb_quantum_smul
        w accept b (amp b.outcomes) u hbstate
      have hbranchProb : branchProb w b = absSq (amp b.outcomes) := by
        rw [branchProb, hbstate, normSq_smul, hnorm, Dy.mul_one]
      rw [eventProb, totalProb_cons, hbranchEvent, hbranchProb,
        ih htail, Dy.right_distrib]

/-- If every branch differs from one normalised state only by a scalar, summing a
quantum-only event over the normalised branch list recovers that state's event
weight. -/
theorem eventProb_quantum_of_proportional
    {w d : Nat} {bs : List (Branch d)} {u : Vec d}
    {amp : List Bool → Dy d}
    (hstate : ∀ b ∈ bs, b.state = amp b.outcomes • u)
    (hnorm : normSq (2 ^ w) u = Dy.one d)
    (htotal : totalProb w bs = Dy.one d)
    (accept : Nat → Bool) :
    eventProb w (quantumEvent accept) bs = stateEventProb w accept u := by
  calc
    eventProb w (quantumEvent accept) bs =
        totalProb w bs * stateEventProb w accept u :=
      eventProb_quantum_factor w accept u amp hnorm bs hstate
    _ = stateEventProb w accept u := by rw [htotal, Dy.one_mul]

/-- The Program form of `eventProb_quantum_of_proportional`.  Well-formedness and
an in-range basis input supply total probability one. -/
theorem terminalEventProb_quantum_of_proportional
    {level : Nat} {p : Program} {input inp : Nat}
    {u : Vec (deg level)} {amp : List Bool → Dy (deg level)}
    (hp : p.wellFormed level = true)
    (hinp : inp < 2 ^ p.width)
    (hstate : ∀ b ∈ runProgram level p input (basis inp),
      b.state = amp b.outcomes • u)
    (hnorm : normSq (2 ^ p.width) u = Dy.one (deg level))
    (accept : Nat → Bool) :
    terminalEventProb level p input (basis inp) (quantumEvent accept) =
      stateEventProb p.width accept u := by
  rw [terminalEventProb]
  exact eventProb_quantum_of_proportional hstate hnorm
    (totalProb_basis level p hp input hinp) accept

theorem nonneg_branchEventProb (w : Nat) (event : TerminalView → Bool) (b : Branch 4) :
    Nonneg (branchEventProb w event b) := by
  rw [branchEventProb]
  induction 2 ^ w with
  | zero => exact nonneg_zero
  | succ n ih =>
      rw [dsum_succ]
      refine nonneg_add ih ?_
      by_cases h : event (view b n) = true
      · rw [if_pos h]
        exact nonneg_absSq _
      · rw [if_neg h]
        exact nonneg_zero

theorem nonneg_eventProb (w : Nat) (event : TerminalView → Bool)
    (bs : List (Branch 4)) : Nonneg (eventProb w event bs) := by
  induction bs with
  | nil => exact nonneg_zero
  | cons b bs ih =>
      rw [eventProb]
      exact nonneg_add (nonneg_branchEventProb w event b) ih

theorem nonneg_terminalEventProb (p : Program) (input : Nat) (u : Vec 4)
    (event : TerminalView → Bool) : Nonneg (terminalEventProb 3 p input u event) :=
  nonneg_eventProb p.width event _

theorem isReal_branchEventProb (w : Nat) (event : TerminalView → Bool) (b : Branch d) :
    IsReal (branchEventProb w event b) := by
  show Dy.conj (branchEventProb w event b) = branchEventProb w event b
  rw [branchEventProb]
  induction 2 ^ w with
  | zero => exact Dy.conj_zero
  | succ n ih =>
      rw [dsum_succ, Dy.conj_add, ih]
      congr 1
      by_cases h : event (view b n) = true
      · rw [if_pos h]
        exact conj_absSq _
      · rw [if_neg h]
        exact Dy.conj_zero

theorem isReal_eventProb (w : Nat) (event : TerminalView → Bool)
    (bs : List (Branch d)) : IsReal (eventProb w event bs) := by
  induction bs with
  | nil => exact Dy.conj_zero
  | cons b bs ih =>
      rw [eventProb]
      exact isReal_add (isReal_branchEventProb w event b) ih

theorem isReal_terminalEventProb (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) (event : TerminalView → Bool) :
    IsReal (terminalEventProb level p input u event) :=
  isReal_eventProb p.width event _

def complement (event : TerminalView → Bool) : TerminalView → Bool :=
  fun v => !event v

theorem branchEventProb_complement (w : Nat) (event : TerminalView → Bool)
    (b : Branch d) :
    branchEventProb w event b + branchEventProb w (complement event) b = branchProb w b := by
  rw [branchEventProb, branchEventProb, branchProb, normSq, ← dsum_add]
  refine dsum_congr (fun i _ => ?_)
  cases h : event (view b i) <;> simp [complement, h, Dy.zero_add, Dy.add_zero]

theorem eventProb_complement (w : Nat) (event : TerminalView → Bool)
    (bs : List (Branch d)) :
    eventProb w event bs + eventProb w (complement event) bs = totalProb w bs := by
  induction bs with
  | nil => exact Dy.add_zero _
  | cons b bs ih =>
      rw [eventProb, eventProb, totalProb_cons]
      have hb := branchEventProb_complement w event b
      grind

theorem terminalEventProb_complement (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) (event : TerminalView → Bool) :
    terminalEventProb level p input u event +
        terminalEventProb level p input u (complement event) =
      totalProb p.width (runProgram level p input u) :=
  eventProb_complement p.width event _

def union (left right : TerminalView → Bool) : TerminalView → Bool :=
  fun v => left v || right v

def disjoint (left right : TerminalView → Bool) : Prop :=
  ∀ v, left v = true → right v = false

theorem branchEventProb_disjoint_union (w : Nat) (left right : TerminalView → Bool)
    (hdisjoint : disjoint left right) (b : Branch d) :
    branchEventProb w (union left right) b =
      branchEventProb w left b + branchEventProb w right b := by
  rw [branchEventProb, branchEventProb, branchEventProb, ← dsum_add]
  refine dsum_congr (fun i _ => ?_)
  by_cases hl : left (view b i) = true
  · have hr := hdisjoint (view b i) hl
    simp [union, hl, hr, Dy.add_zero]
  · have hl' : left (view b i) = false := Bool.eq_false_iff.mpr hl
    cases hr : right (view b i) <;> simp [union, hl', hr, Dy.zero_add]

theorem eventProb_disjoint_union (w : Nat) (left right : TerminalView → Bool)
    (hdisjoint : disjoint left right) (bs : List (Branch d)) :
    eventProb w (union left right) bs = eventProb w left bs + eventProb w right bs := by
  induction bs with
  | nil => exact (Dy.add_zero _).symm
  | cons b bs ih =>
      rw [eventProb, eventProb, eventProb, branchEventProb_disjoint_union w left right hdisjoint, ih]
      grind

theorem terminalEventProb_disjoint_union (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) (left right : TerminalView → Bool)
    (hdisjoint : disjoint left right) :
    terminalEventProb level p input u (union left right) =
      terminalEventProb level p input u left + terminalEventProb level p input u right :=
  eventProb_disjoint_union p.width left right hdisjoint _

theorem eventProb_perm (w : Nat) (event : TerminalView → Bool)
    {left right : List (Branch d)} (hperm : left.Perm right) :
    eventProb w event left = eventProb w event right := by
  induction hperm with
  | nil => rfl
  | cons b hperm ih => rw [eventProb, eventProb, ih]
  | swap a b bs =>
    simp only [eventProb]
    rw [← Dy.add_assoc, Dy.add_comm (branchEventProb w event b), Dy.add_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def SameTerminalMetadata (left right : Branch d) : Prop :=
  left.outcomes = right.outcomes ∧ left.creg = right.creg ∧ left.input = right.input

theorem view_eq_of_sameTerminalMetadata {left right : Branch d}
    (h : SameTerminalMetadata left right) (i : Nat) :
    view left i = view right i := by
  rcases h with ⟨houtcomes, hcreg, hinput⟩
  simp [view, houtcomes, hcreg, hinput]

def PointwiseProbSplit (w : Nat) (whole left right : Branch d) : Prop :=
  SameTerminalMetadata whole left ∧ SameTerminalMetadata whole right ∧
    ∀ i, i < 2 ^ w →
      absSq (whole.state i) = absSq (left.state i) + absSq (right.state i)

theorem branchEventProb_split (w : Nat) (event : TerminalView → Bool)
    (whole left right : Branch d) (hsplit : PointwiseProbSplit w whole left right) :
    branchEventProb w event whole =
      branchEventProb w event left + branchEventProb w event right := by
  rw [branchEventProb, branchEventProb, branchEventProb, ← dsum_add]
  refine dsum_congr (fun i hi => ?_)
  have hleft := view_eq_of_sameTerminalMetadata hsplit.1 i
  have hright := view_eq_of_sameTerminalMetadata hsplit.2.1 i
  by_cases hevent : event (view whole i) = true
  · rw [if_pos hevent, if_pos (by simpa [← hleft] using hevent),
      if_pos (by simpa [← hright] using hevent), hsplit.2.2 i hi]
  · have heventFalse : event (view whole i) = false := Bool.eq_false_iff.mpr hevent
    rw [if_neg hevent, if_neg (by simpa [← hleft] using heventFalse),
      if_neg (by simpa [← hright] using heventFalse), Dy.zero_add]

theorem eventProb_split_cons (w : Nat) (event : TerminalView → Bool)
    (whole left right : Branch d) (bs : List (Branch d))
    (hsplit : PointwiseProbSplit w whole left right) :
    eventProb w event (whole :: bs) = eventProb w event (left :: right :: bs) := by
  rw [eventProb, eventProb, eventProb, branchEventProb_split w event whole left right hsplit,
    Dy.add_assoc]

theorem terminalEventProb_le_total (p : Program) (input : Nat) (u : Vec 4)
    (event : TerminalView → Bool) :
    Le (terminalEventProb 3 p input u event)
      (totalProb p.width (runProgram 3 p input u)) := by
  rw [Le, ← terminalEventProb_complement 3 p input u event, Dy.sub_eq_add_neg,
    Dy.add_comm (terminalEventProb 3 p input u event), Dy.add_assoc,
    Dy.add_neg_cancel, Dy.add_zero]
  exact nonneg_terminalEventProb p input u (complement event)

theorem terminalEventProb_le_one (p : Program) (hp : p.wellFormed 3 = true)
    (input inp : Nat) (hinp : inp < 2 ^ p.width) (event : TerminalView → Bool) :
    Le (terminalEventProb 3 p input (basis inp) event) (Dy.one 4) := by
  rw [← totalProb_basis 3 p hp input hinp]
  exact terminalEventProb_le_total p input (basis inp) event

private def measureResetCost : Op → Nat
  | .measure _ _ | .reset _ => 1
  | _ => 0

theorem outcomes_length_runOp_runOps (level w : Nat) :
    (∀ o : Op, ∀ b b' : Branch (deg level), b' ∈ runOp level w o b →
      b'.outcomes.length ≤
        b.outcomes.length + (Program.tallyOp measureResetCost o).hi) ∧
    (∀ os : List Op, ∀ b b' : Branch (deg level), b' ∈ runOps level w os b →
      b'.outcomes.length ≤
        b.outcomes.length + (Program.tallyOps measureResetCost os).hi) := by
  refine opInduction (fun g b b' hm => ?_) (fun q c b b' hm => ?_)
    (fun q b b' hm => ?_) (fun c value b b' hm => ?_)
    (fun c b b' hm => ?_) (fun c t e ht he b b' hm => ?_)
    (fun b b' hm => ?_) (fun o os ho hos b b' hm => ?_)
  · rw [runOp_gate, List.mem_singleton] at hm
    subst b'
    simp [Program.tallyOp, measureResetCost]
  · rw [runOp_measure] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;>
      simp [Program.tallyOp, measureResetCost, Range.point]
  · rw [runOp_reset] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;>
      simp [Program.tallyOp, measureResetCost, Range.point]
  · rw [runOp_store, List.mem_singleton] at hm
    subst b'
    simp [Program.tallyOp, measureResetCost]
  · rw [runOp_invert, List.mem_singleton] at hm
    subst b'
    simp [Program.tallyOp, measureResetCost]
  · rw [runOp_branch] at hm
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc] at hm
      have h := ht b b' hm
      simp [Program.tallyOp, Range.choice] at ⊢
      omega
    · rw [if_neg hc] at hm
      have h := he b b' hm
      simp [Program.tallyOp, Range.choice] at ⊢
      omega
  · rw [runOps_nil, List.mem_singleton] at hm
    subst b'
    simp [Program.tallyOps, Range.point]
  · rw [runOps_cons, List.mem_flatMap] at hm
    obtain ⟨x, hx, hb'⟩ := hm
    have hfirst := ho b x hx
    have hrest := hos x b' hb'
    simp [Program.tallyOps, Range.add] at ⊢
    omega

theorem outcomes_length_runProgram_le_measureResetCount
    (level : Nat) (p : Program) (input : Nat) (u : Vec (deg level))
    {b : Branch (deg level)} (hb : b ∈ runProgram level p input u) :
    b.outcomes.length ≤ p.measureResetCount.hi := by
  have h := (outcomes_length_runOp_runOps level p.width).2 p.ops
    { outcomes := [], creg := 0, state := u, input := input } b hb
  change b.outcomes.length ≤
    (Program.tallyOps
      (fun o => match o with | .measure _ _ | .reset _ => 1 | _ => 0)
      p.ops).hi
  unfold measureResetCost at h
  simpa using h

structure TerminalSelector (p : Program) where
  quantum : List (Fin p.width)
  history : List Nat
  classical : List (Fin p.cbits)

structure TerminalObservation where
  quantum : List Bool
  history : List (Option Bool)
  classical : List Bool
  deriving DecidableEq

def TerminalSelector.Valid {p : Program} (selector : TerminalSelector p) : Prop :=
  selector.quantum.Nodup ∧ selector.history.Nodup ∧ selector.classical.Nodup ∧
    (selector.quantum ≠ [] ∨ selector.history ≠ [] ∨ selector.classical ≠ []) ∧
    ∀ k ∈ selector.history, k < p.measureResetCount.hi

instance {p : Program} (selector : TerminalSelector p) : Decidable selector.Valid := by
  unfold TerminalSelector.Valid
  infer_instance

def TerminalObservation.ValidFor {p : Program} (selector : TerminalSelector p)
    (observation : TerminalObservation) : Prop :=
  observation.quantum.length = selector.quantum.length ∧
    observation.history.length = selector.history.length ∧
    observation.classical.length = selector.classical.length

instance {p : Program} (selector : TerminalSelector p) (observation : TerminalObservation) :
    Decidable (observation.ValidFor selector) := by
  unfold TerminalObservation.ValidFor
  infer_instance

def observe {p : Program} (selector : TerminalSelector p)
    (v : TerminalView) : TerminalObservation :=
  { quantum := selector.quantum.map fun q => v.basisIndex.testBit q.val
    history := selector.history.map fun k => v.history.reverse[k]?
    classical := selector.classical.map fun c => v.classical.testBit c.val }

def pointProb (level : Nat) (p : Program) (input : Nat) (u : Vec (deg level))
    (selector : TerminalSelector p) (observation : TerminalObservation) : Dy (deg level) :=
  terminalEventProb level p input u fun v => observe selector v == observation

def acceptsAny (accepted : List TerminalObservation) : TerminalObservation → Bool :=
  fun observation => accepted.contains observation

def acceptedProb (level : Nat) (p : Program) (input : Nat) (u : Vec (deg level))
    (selector : TerminalSelector p) (accepted : List TerminalObservation) : Dy (deg level) :=
  terminalEventProb level p input u fun v => acceptsAny accepted (observe selector v)

theorem acceptsAny_eraseDups (accepted : List TerminalObservation) :
    acceptsAny accepted.eraseDups = acceptsAny accepted := by
  funext observation
  apply Bool.eq_iff_iff.mpr
  simp [acceptsAny]

theorem acceptedProb_eraseDups (level : Nat) (p : Program) (input : Nat)
    (u : Vec (deg level)) (selector : TerminalSelector p)
    (accepted : List TerminalObservation) :
    acceptedProb level p input u selector accepted.eraseDups =
      acceptedProb level p input u selector accepted := by
  unfold acceptedProb
  rw [acceptsAny_eraseDups]

def ValidRun (p : Program) (input : Nat) (u : Vec 4) : Prop :=
  p.wellFormed 3 = true ∧ input < 2 ^ p.inputBits ∧ WFVec (2 ^ p.width) u ∧
    normSq (2 ^ p.width) u = Dy.one 4

theorem validRun_basis (p : Program) (hp : p.wellFormed 3 = true)
    (input inp : Nat) (hinput : input < 2 ^ p.inputBits) (hinp : inp < 2 ^ p.width) :
    ValidRun p input (basis inp) :=
  ⟨hp, hinput, wfVec_basis hinp, normSq_basis hinp⟩

def AcceptedValid {p : Program} (selector : TerminalSelector p)
    (accepted : List TerminalObservation) : Prop :=
  accepted ≠ [] ∧ ∀ observation ∈ accepted, observation.ValidFor selector

instance {p : Program} (selector : TerminalSelector p)
    (accepted : List TerminalObservation) : Decidable (AcceptedValid selector accepted) := by
  unfold AcceptedValid
  infer_instance

def acceptedSlack (p : Program) (input : Nat) (u : Vec 4)
    (selector : TerminalSelector p) (accepted : List TerminalObservation)
    (num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) * acceptedProb 3 p input u selector accepted -
    Dy.ofInt 4 (Int.ofNat num)

def AcceptedCertain (p : Program) (input : Nat) (u : Vec 4)
    (selector : TerminalSelector p) (accepted : List TerminalObservation) : Prop :=
  ValidRun p input u ∧ selector.Valid ∧ AcceptedValid selector accepted ∧
    acceptedProb 3 p input u selector accepted = Dy.one 4

def AcceptedAtLeast (p : Program) (input : Nat) (u : Vec 4)
    (selector : TerminalSelector p) (accepted : List TerminalObservation)
    (num den : Nat) : Prop :=
  ValidRun p input u ∧ selector.Valid ∧ AcceptedValid selector accepted ∧ 0 < den ∧
    IsReal (acceptedSlack p input u selector accepted num den) ∧
    Nonneg (acceptedSlack p input u selector accepted num den)

def AcceptedAtMost (p : Program) (input : Nat) (u : Vec 4)
    (selector : TerminalSelector p) (accepted : List TerminalObservation)
    (num den : Nat) : Prop :=
  ValidRun p input u ∧ selector.Valid ∧ AcceptedValid selector accepted ∧ 0 < den ∧
    IsReal (acceptedSlack p input u selector accepted num den) ∧
    Nonneg (-acceptedSlack p input u selector accepted num den)

theorem isReal_acceptedSlack (p : Program) (input : Nat) (u : Vec 4)
    (selector : TerminalSelector p) (accepted : List TerminalObservation)
    (num den : Nat) : IsReal (acceptedSlack p input u selector accepted num den) := by
  unfold acceptedSlack
  refine isReal_sub (isReal_mul (isReal_ofInt _) ?_) (isReal_ofInt _)
  unfold acceptedProb
  exact isReal_terminalEventProb 3 p input u _

def intersection (left right : TerminalView → Bool) : TerminalView → Bool :=
  fun v => left v && right v

def conditionalSlack (p : Program) (input : Nat) (u : Vec 4)
    (result condition : TerminalView → Bool) (num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) *
      terminalEventProb 3 p input u (intersection result condition) -
    Dy.ofInt 4 (Int.ofNat num) * terminalEventProb 3 p input u condition

def ConditionalAtLeast (p : Program) (input : Nat) (u : Vec 4)
    (result condition : TerminalView → Bool) (num den : Nat) : Prop :=
  ValidRun p input u ∧ 0 < den ∧
    IsReal (terminalEventProb 3 p input u condition) ∧
    Nonneg (terminalEventProb 3 p input u condition) ∧
    terminalEventProb 3 p input u condition ≠ Dy.zero 4 ∧
    IsReal (conditionalSlack p input u result condition num den) ∧
    Nonneg (conditionalSlack p input u result condition num den)

theorem isReal_conditionalSlack (p : Program) (input : Nat) (u : Vec 4)
    (result condition : TerminalView → Bool) (num den : Nat) :
    IsReal (conditionalSlack p input u result condition num den) := by
  unfold conditionalSlack
  exact isReal_sub
    (isReal_mul (isReal_ofInt _) (isReal_terminalEventProb 3 p input u _))
    (isReal_mul (isReal_ofInt _) (isReal_terminalEventProb 3 p input u _))

def basisIs (out : Nat) : TerminalView → Bool :=
  fun v => v.basisIndex == out

def basisMaskIs (mask pattern : Nat) : TerminalView → Bool :=
  fun v => v.basisIndex &&& mask == pattern

theorem branchEventProb_basisIs {w out : Nat} (hout : out < 2 ^ w) (b : Branch d) :
    branchEventProb w (basisIs out) b = absSq (b.state out) := by
  rw [branchEventProb]
  calc
    dsum (2 ^ w) (fun i => if basisIs out (view b i) then absSq (b.state i) else Dy.zero d)
        = if basisIs out (view b out) then absSq (b.state out) else Dy.zero d :=
      dsum_eq_single hout (fun i _ hne => by simp [basisIs, view, hne])
    _ = absSq (b.state out) := by simp [basisIs, view]

theorem terminalEventProb_ofCircuit {level inp out : Nat} (c : Circuit)
    (hout : out < 2 ^ c.width) :
    terminalEventProb level (Program.ofCircuit c) 0 (basis inp) (basisIs out) =
      probAt level c inp out := by
  rw [terminalEventProb, runProgram_ofCircuit, eventProb, eventProb, Dy.add_zero,
    show (Program.ofCircuit c).width = c.width from rfl, branchEventProb_basisIs hout, probAt]

theorem terminalEventProb_ofCircuit_mask (level inp mask pattern : Nat)
    (c : Circuit) :
    terminalEventProb level (Program.ofCircuit c) 0 (basis inp)
        (basisMaskIs mask pattern) =
      probMarginal level c inp mask pattern := by
  rw [terminalEventProb, runProgram_ofCircuit, eventProb, eventProb, Dy.add_zero,
    show (Program.ofCircuit c).width = c.width from rfl,
    branchEventProb, probMarginal]
  exact dsum_congr (fun i _ => by
    simp [basisMaskIs, view, probAt])

def correlatedTerminal : Program :=
  { width := 2, cbits := 1,
    ops := [.gate (.h 0), .measure 0 0,
      .branch (.localBit 0) [.gate (.x 1)] [], .store 0 false] }

def correlationSelector : TerminalSelector correlatedTerminal :=
  { quantum := [⟨1, by decide⟩], history := [0], classical := [] }

def falseCorrelation : TerminalObservation :=
  { quantum := [false], history := [some false], classical := [] }

def trueCorrelation : TerminalObservation :=
  { quantum := [true], history := [some true], classical := [] }

def emptySelector : TerminalSelector correlatedTerminal :=
  { quantum := [], history := [], classical := [] }

def duplicateQuantumSelector : TerminalSelector correlatedTerminal :=
  { quantum := [⟨1, by decide⟩, ⟨1, by decide⟩], history := [], classical := [] }

def outOfRangeHistorySelector : TerminalSelector correlatedTerminal :=
  { quantum := [], history := [1], classical := [] }

def malformedCorrelation : TerminalObservation :=
  { quantum := [], history := [some false], classical := [] }

def quantumOne : TerminalView → Bool := fun v => v.basisIndex.testBit 1

def historyOne : TerminalView → Bool := fun v => v.history.reverse[0]? == some true

def quantumMatchesHistory : TerminalView → Bool :=
  fun v => v.history.reverse[0]? == some (v.basisIndex.testBit 1)

def localZero : TerminalView → Bool := fun v => !v.classical.testBit 0

def quantumMatchesLocal : TerminalView → Bool :=
  fun v => v.basisIndex.testBit 1 == v.classical.testBit 0

def splitWhole : Branch 4 :=
  { outcomes := [], creg := 0, state := basis 0, input := 0 }

def splitPart : Branch 4 :=
  { outcomes := [], creg := 0,
    state := Dy.invSqrt2 4 • (basis 0 : Vec 4), input := 0 }

def interferingWhole : Branch 4 :=
  { outcomes := [], creg := 0,
    state := (basis 0 : Vec 4) + basis 0, input := 0 }

def interferingPart : Branch 4 :=
  { outcomes := [], creg := 0, state := basis 0, input := 0 }

theorem splitPointwise : PointwiseProbSplit 0 splitWhole splitPart splitPart := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  decide

example : eventProb 0 (fun _ => true) [splitWhole] =
    eventProb 0 (fun _ => true) [splitPart, splitPart] :=
  eventProb_split_cons 0 (fun _ => true) splitWhole splitPart splitPart [] splitPointwise

example : eventProb 0 (fun _ => true) [splitPart, splitPart] = Dy.one 4 := by decide

example : interferingWhole.state = interferingPart.state + interferingPart.state := rfl

example : branchEventProb 0 (fun _ => true) interferingWhole ≠
    branchEventProb 0 (fun _ => true) interferingPart +
      branchEventProb 0 (fun _ => true) interferingPart := by decide

example : correlatedTerminal.wellFormed 3 = true := by decide

example : correlationSelector.Valid := by decide
example : falseCorrelation.ValidFor correlationSelector := by decide
example : trueCorrelation.ValidFor correlationSelector := by decide
example : ¬ emptySelector.Valid := by decide
example : ¬ duplicateQuantumSelector.Valid := by decide
example : ¬ outOfRangeHistorySelector.Valid := by decide
example : ¬ malformedCorrelation.ValidFor correlationSelector := by decide

example : pointProb 3 correlatedTerminal 0 (basis 0) correlationSelector falseCorrelation =
    Dy.half (Dy.one 4) := by decide

example : pointProb 3 correlatedTerminal 0 (basis 0) correlationSelector trueCorrelation =
    Dy.half (Dy.one 4) := by decide

example : acceptedProb 3 correlatedTerminal 0 (basis 0) correlationSelector
      [falseCorrelation, trueCorrelation] = Dy.one 4 := by decide

example : acceptedProb 3 correlatedTerminal 0 (basis 0) correlationSelector
      [falseCorrelation, falseCorrelation, trueCorrelation] =
    acceptedProb 3 correlatedTerminal 0 (basis 0) correlationSelector
      [falseCorrelation, trueCorrelation] := by decide

theorem correlatedValidRun : ValidRun correlatedTerminal 0 (basis 0) :=
  validRun_basis correlatedTerminal (by decide) 0 0 (by decide) (by decide)

example : AcceptedCertain correlatedTerminal 0 (basis 0) correlationSelector
    [falseCorrelation, trueCorrelation] := by
  exact ⟨correlatedValidRun, by decide, by decide, by decide⟩

example : AcceptedAtLeast correlatedTerminal 0 (basis 0) correlationSelector
    [falseCorrelation, trueCorrelation] 1 1 := by
  exact ⟨correlatedValidRun, by decide, by decide, by decide,
    isReal_acceptedSlack _ _ _ _ _ _ _, by decide⟩

example : AcceptedAtMost correlatedTerminal 0 (basis 0) correlationSelector
    [falseCorrelation, trueCorrelation] 1 1 := by
  exact ⟨correlatedValidRun, by decide, by decide, by decide,
    isReal_acceptedSlack _ _ _ _ _ _ _, by decide⟩

example : ¬ AcceptedAtLeast correlatedTerminal 0 (basis 0) correlationSelector
    [falseCorrelation, trueCorrelation] 1 0 := by
  intro h
  have hden : 0 < 0 := h.2.2.2.1
  omega

example : ¬ AcceptedAtMost correlatedTerminal 0 (basis 0) correlationSelector
    [falseCorrelation, trueCorrelation] 1 0 := by
  intro h
  have hden : 0 < 0 := h.2.2.2.1
  omega

example : ¬ ValidRun correlatedTerminal 0 (basis 4) := by
  intro h
  have hz := h.2.2.1 4 (by decide)
  rw [basis_self] at hz
  exact absurd hz (by decide)

example : ¬ ValidRun correlatedTerminal 0 (Vec.zero 4) := by
  intro h
  have hz := h.2.2.2
  rw [normSq_zero] at hz
  exact absurd hz (by decide)

example : terminalEventProb 3 correlatedTerminal 0 (basis 0) quantumOne =
    Dy.half (Dy.one 4) := by decide

example : terminalEventProb 3 correlatedTerminal 0 (basis 0) historyOne =
    Dy.half (Dy.one 4) := by decide

example : terminalEventProb 3 correlatedTerminal 0 (basis 0) quantumMatchesHistory =
    Dy.one 4 := by decide

example : terminalEventProb 3 correlatedTerminal 0 (basis 0) localZero =
    Dy.one 4 := by decide

example : terminalEventProb 3 correlatedTerminal 0 (basis 0) quantumMatchesLocal =
    Dy.half (Dy.one 4) := by decide

example : terminalEventProb 3 correlatedTerminal 0 (basis 0)
      (fun v => quantumOne v && historyOne v) =
    terminalEventProb 3 correlatedTerminal 0 (basis 0) historyOne := by decide

example : ConditionalAtLeast correlatedTerminal 0 (basis 0)
    quantumOne historyOne 1 1 := by
  exact ⟨correlatedValidRun, by decide,
    isReal_terminalEventProb 3 correlatedTerminal 0 (basis 0) historyOne,
    nonneg_terminalEventProb correlatedTerminal 0 (basis 0) historyOne,
    by decide, isReal_conditionalSlack _ _ _ _ _ _ _, by decide⟩

def inputDependentTerminal : Program :=
  { width := 2, inputBits := 1, cbits := 1,
    ops := [.branch (.input 0) [.gate (.x 0)] [], .measure 0 0,
      .branch (.localBit 0) [.gate (.x 1)] []] }

def inputDependentSelector : TerminalSelector inputDependentTerminal :=
  { quantum := [⟨1, by decide⟩], history := [0], classical := [] }

theorem inputDependentZeroValidRun :
    ValidRun inputDependentTerminal 0 (basis 0) :=
  validRun_basis inputDependentTerminal (by decide) 0 0 (by decide) (by decide)

theorem inputDependentOneValidRun :
    ValidRun inputDependentTerminal 1 (basis 0) :=
  validRun_basis inputDependentTerminal (by decide) 1 0 (by decide) (by decide)

example : ¬ ValidRun inputDependentTerminal 2 (basis 0) := by
  intro h
  have hinput := h.2.1
  change 2 < 2 ^ 1 at hinput
  omega

theorem inputDependent_zero_certain :
    AcceptedCertain inputDependentTerminal 0 (basis 0)
      inputDependentSelector [falseCorrelation] := by
  exact ⟨inputDependentZeroValidRun, by decide, by decide, by decide⟩

theorem inputDependent_one_certain :
    AcceptedCertain inputDependentTerminal 1 (basis 0)
      inputDependentSelector [trueCorrelation] := by
  exact ⟨inputDependentOneValidRun, by decide, by decide, by decide⟩

#guard inputDependentTerminal.gateCount == { lo := 0, hi := 2 }
#guard inputDependentTerminal.measureCount == Range.point 1
#guard inputDependentTerminal.resetCount == Range.point 0
#guard inputDependentTerminal.classicalOpCount == Range.point 3
#guard inputDependentTerminal.usedWires == 2
#guard inputDependentTerminal.usedInputBits == 1
#guard inputDependentTerminal.usedCbits == 1

example : pointProb 3 inputDependentTerminal 1 (basis 0)
    inputDependentSelector falseCorrelation = Dy.zero 4 := by decide

example : pointProb 3 inputDependentTerminal 0 (basis 0)
    inputDependentSelector trueCorrelation = Dy.zero 4 := by decide

def hadamard : Circuit := { width := 1, gates := [.h 0] }

example : terminalEventProb 3 (Program.ofCircuit hadamard) 0 (basis 0) (basisIs 1) =
    probAt 3 hadamard 0 1 := terminalEventProb_ofCircuit hadamard (by decide)

example : terminalEventProb 3 (Program.ofCircuit hadamard) 0 (basis 0)
      (basisMaskIs 1 1) = probMarginal 3 hadamard 0 1 1 :=
  terminalEventProb_ofCircuit_mask 3 0 1 1 hadamard

/-- info: 'VQ.Tests.ProgramObservation.nonneg_terminalEventProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nonneg_terminalEventProb

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_basis_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_basis_total

/-- info: 'VQ.Tests.ProgramObservation.eventProb_quantum_of_proportional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms eventProb_quantum_of_proportional

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_quantum_of_proportional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_quantum_of_proportional

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_ofCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_ofCircuit

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_ofCircuit_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_ofCircuit_mask

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_disjoint_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_disjoint_union

/-- info: 'VQ.Tests.ProgramObservation.eventProb_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eventProb_perm

/-- info: 'VQ.Tests.ProgramObservation.eventProb_split_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eventProb_split_cons

/-- info: 'VQ.Tests.ProgramObservation.terminalEventProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms terminalEventProb_le_one

/-- info: 'VQ.Tests.ProgramObservation.acceptedProb_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms acceptedProb_eraseDups

/-- info: 'VQ.Tests.ProgramObservation.isReal_conditionalSlack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isReal_conditionalSlack

/-- info: 'VQ.Tests.ProgramObservation.outcomes_length_runProgram_le_measureResetCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outcomes_length_runProgram_le_measureResetCount

end ProgramObservation
end Tests
end VQ
