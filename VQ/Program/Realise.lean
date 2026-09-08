/-
Program realization of register specifications.

`VQ/Reversible/ArithmeticSpec.lean` and `VQ/Curve/ReversibleSpec.lean` state what
a circuit computes as an equation between basis indices, and every predicate
there takes an `RCircuit` containing `x`, `cx`, and `ccx`.  Measurement and
classical control require `Program`, whose denotation is a branch list.  The
`Realises` predicate states register correctness for those programs.

`RegSpec` stores a width, a basis-input domain, and an output relation.
Equivalence theorems identify `MetBy` with the predicates in the reversible
specification modules.  `Realises` applies the same specification data to a
program and states its branch weights and outputs.

## Branch weights indexed by measurement records

Branchwise basis-state correctness and normalized branch probabilities do not
preserve coherence.  A program can measure a data wire, correct each basis-state
branch under classical control, and correlate the measurement record with the
data.  Applied to a superposition, that program destroys off-diagonal coherence
despite satisfying the two branchwise conditions.

`Realises` quantifies over inputs after fixing the branch weight `amp` and output
permutation `out`.  Each branch state has the form `amp s • basis (out i)`, so
the weight is independent of the input `i`.  By linearity of `runOps`,
`realises_pair` proves that every branch maps a two-term superposition to the
corresponding superposition of output basis states, scaled by the same weight.

Gidney's construction satisfies this definition.  `runOps_andUncompute` leaves two branches whose
states differ by an `x` on the ancilla, each at weight `1/√2` whatever the data
register holds, and `branchProb_andUncompute` is that weight.  The `x` is why a
realising program ends with a classically controlled correction on the ancilla:
the specification demands a clear workspace on every branch, and the outcome-one
branch leaves the measured wire set.
-/
import VQ.Program.Semantics
import VQ.Reversible.ArithmeticSpec
import VQ.Curve.ReversibleSpec
import VQ.Reversible.Denote

namespace VQ
namespace Semantics

open Algebra
open VQ.Reversible

/--
A specification of a reversible action on a register, as data.

`Pre` is the set of basis inputs the specification constrains and `Post` relates
an input index to the output index.  `Post` is a relation rather than a function
because `AddsPoint` is one: outside the domain where the affine formula is
defined, its only clause is that the workspace field returns to zero, which many
output indices satisfy.  Where a specification is functional, `realises_pair`
recovers the map from `Realises` itself.
-/
structure RegSpec where
  /-- The register width the specification speaks about. -/
  width : Nat
  /-- The basis inputs constrained. -/
  Pre : Nat → Prop
  /-- What the output index must satisfy, given the input index. -/
  Post : Nat → Nat → Prop

/-- Restrict a specification to basis inputs satisfying an additional
predicate.  The width and output relation remain unchanged. -/
def RegSpec.restrictPre (S : RegSpec) (P : Nat → Prop) : RegSpec where
  width := S.width
  Pre i := S.Pre i ∧ P i
  Post := S.Post

/-- A reversible circuit meets a specification when its action satisfies the
specification's relation on every admissible input. -/
def RegSpec.MetBy (S : RegSpec) (r : RCircuit) : Prop :=
  ∀ i, i < 2 ^ S.width → S.Pre i → S.Post i (act r i)

/-! ## Specification records

Each equivalence below relates `MetBy` to a predicate in
`VQ/Reversible/ArithmeticSpec.lean` or `VQ/Curve/ReversibleSpec.lean`.  The record
therefore gives a second description of the same proposition.  No specification
proposition changes. -/

/-- `AddsWrap` as a record. -/
def addsWrapSpec (ws n : Nat) : RegSpec where
  width := (adderLayout n ws).width
  Pre i := (adderLayout n ws).read i 2 = 0
  Post i j := j = (adderLayout n ws).write i 1
    (((adderLayout n ws).read i 0 + (adderLayout n ws).read i 1) % 2 ^ n)

theorem addsWrap_iff {ws n : Nat} {r : RCircuit} :
    AddsWrap ws n r ↔ (addsWrapSpec ws n).MetBy r := by
  constructor
  · intro h i hi h₂
    exact h _ _ i hi rfl rfl h₂
  · intro h a b i hi h₀ h₁ h₂
    subst h₀
    subst h₁
    exact h i hi h₂

/-- `AddsMod` as a record. -/
def addsModSpec (m ws n : Nat) : RegSpec where
  width := (adderLayout n ws).width
  Pre i := (adderLayout n ws).read i 2 = 0 ∧ m ≤ 2 ^ n ∧
    (adderLayout n ws).read i 0 < m ∧ (adderLayout n ws).read i 1 < m
  Post i j := j = (adderLayout n ws).write i 1
    (((adderLayout n ws).read i 0 + (adderLayout n ws).read i 1) % m)

theorem addsMod_iff {m ws n : Nat} {r : RCircuit} :
    AddsMod m ws n r ↔ (addsModSpec m ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ _ i hi rfl rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a b i hi h₀ h₁ h₂ hm ha hb
    subst h₀
    subst h₁
    exact h i hi ⟨h₂, hm, ha, hb⟩

/-- `SubsMod` as a record. -/
def subsModSpec (m ws n : Nat) : RegSpec where
  width := (adderLayout n ws).width
  Pre i := (adderLayout n ws).read i 2 = 0 ∧ m ≤ 2 ^ n ∧
    (adderLayout n ws).read i 0 < m ∧ (adderLayout n ws).read i 1 < m
  Post i j := j = (adderLayout n ws).write i 1
    (((adderLayout n ws).read i 1 + (m - (adderLayout n ws).read i 0)) % m)

theorem subsMod_iff {m ws n : Nat} {r : RCircuit} :
    SubsMod m ws n r ↔ (subsModSpec m ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ _ i hi rfl rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a b i hi h₀ h₁ h₂ hm ha hb
    subst h₀
    subst h₁
    exact h i hi ⟨h₂, hm, ha, hb⟩

/-- `MulsMod` as a record. -/
def mulsModSpec (m ws n : Nat) : RegSpec where
  width := (mulLayout n ws).width
  Pre i := (mulLayout n ws).read i 2 = 0 ∧ (mulLayout n ws).read i 3 = 0 ∧ m ≤ 2 ^ n ∧
    (mulLayout n ws).read i 0 < m ∧ (mulLayout n ws).read i 1 < m
  Post i j := j = (mulLayout n ws).write i 2
    ((mulLayout n ws).read i 0 * (mulLayout n ws).read i 1 % m)

theorem mulsMod_iff {m ws n : Nat} {r : RCircuit} :
    MulsMod m ws n r ↔ (mulsModSpec m ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ _ i hi rfl rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2
  · intro h a b i hi h₀ h₁ h₂ h₃ hm ha hb
    subst h₀
    subst h₁
    exact h i hi ⟨h₂, h₃, hm, ha, hb⟩

/-- `AddsConstMod` as a record. -/
def addsConstModSpec (m ws n c : Nat) : RegSpec where
  width := (constLayout n ws).width
  Pre i := (constLayout n ws).read i 1 = 0 ∧ m ≤ 2 ^ n ∧
    (constLayout n ws).read i 0 < m ∧ c < m
  Post i j := j = (constLayout n ws).write i 0 (((constLayout n ws).read i 0 + c) % m)

theorem addsConstMod_iff {m ws n c : Nat} {r : RCircuit} :
    AddsConstMod m ws n c r ↔ (addsConstModSpec m ws n c).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ i hi rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a i hi h₀ h₁ hm ha hc
    subst h₀
    exact h i hi ⟨h₁, hm, ha, hc⟩

/-- `InvertsFieldScaled` as a record. -/
def invertsFieldScaledSpec (c ws n : Nat) : RegSpec where
  width := (unaryLayout n ws).width
  Pre i := (unaryLayout n ws).read i 1 = 0 ∧ (unaryLayout n ws).read i 2 = 0 ∧
    Curve.p ≤ 2 ^ n ∧ (unaryLayout n ws).read i 0 < Curve.p
  Post i j := j = (unaryLayout n ws).write i 1
    (Curve.inv ((unaryLayout n ws).read i 0) * c % Curve.p)

theorem invertsFieldScaled_iff {c ws n : Nat} {r : RCircuit} :
    InvertsFieldScaled c ws n r ↔ (invertsFieldScaledSpec c ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ i hi rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a i hi h₀ h₁ h₂ hp ha
    subst h₀
    exact h i hi ⟨h₁, h₂, hp, ha⟩

/-- `SquaresMod` as a record. -/
def squaresModSpec (m ws n : Nat) : RegSpec where
  width := (unaryLayout n ws).width
  Pre i := (unaryLayout n ws).read i 1 = 0 ∧ (unaryLayout n ws).read i 2 = 0 ∧
    m ≤ 2 ^ n ∧ (unaryLayout n ws).read i 0 < m
  Post i j := j = (unaryLayout n ws).write i 1
    ((unaryLayout n ws).read i 0 * (unaryLayout n ws).read i 0 % m)

theorem squaresMod_iff {m ws n : Nat} {r : RCircuit} :
    SquaresMod m ws n r ↔ (squaresModSpec m ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ i hi rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a i hi h₀ h₁ h₂ hm ha
    subst h₀
    exact h i hi ⟨h₁, h₂, hm, ha⟩

/-- `NegatesMod` as a record. -/
def negatesModSpec (m ws n : Nat) : RegSpec where
  width := (constLayout n ws).width
  Pre i := (constLayout n ws).read i 1 = 0 ∧ m ≤ 2 ^ n ∧ (constLayout n ws).read i 0 < m
  Post i j := j = (constLayout n ws).write i 0 ((m - (constLayout n ws).read i 0) % m)

theorem negatesMod_iff {m ws n : Nat} {r : RCircuit} :
    NegatesMod m ws n r ↔ (negatesModSpec m ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ i hi rfl hpre.1 hpre.2.1 hpre.2.2
  · intro h a i hi h₀ h₁ hm ha
    subst h₀
    exact h i hi ⟨h₁, hm, ha⟩

/-- `AddsPoint` as a record.  Its `Post` relation permits several outputs when
the affine formula is undefined.  On those inputs, it constrains only the
workspace field to return to zero. -/
def addsPointSpec (ax ay ws : Nat) : RegSpec where
  width := (curveLayout ws).width
  Pre i := (curveLayout ws).read i 2 = 0
  Post i j :=
    (Curve.Addable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay = true →
      Curve.Recoverable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay = true →
        j = (curveLayout ws).write ((curveLayout ws).write i 0
          (Curve.addPoint ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay).1) 1
          (Curve.addPoint ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay).2) ∧
    (Curve.Representable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) = true →
      (curveLayout ws).read i 0 ≠ ax →
      Curve.Recoverable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay = true →
        (curveLayout ws).read j 2 = 0)

theorem addsPoint_iff {ax ay ws : Nat} {r : RCircuit} :
    AddsPoint ax ay ws r ↔ (addsPointSpec ax ay ws).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ _ i hi rfl rfl hpre
  · intro h x y i hi h₀ h₁ h₂
    subst h₀
    subst h₁
    exact h i hi h₂

/-- `AddsPointTotal` as a record: the same two clauses with no `Recoverable`
guard.  Nothing meets it, and it exists so a construction that handles the
exceptional branch is distinguishable from one that does not. -/
def addsPointTotalSpec (ax ay ws : Nat) : RegSpec where
  width := (curveLayout ws).width
  Pre i := (curveLayout ws).read i 2 = 0
  Post i j :=
    (Curve.Addable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay = true →
        j = (curveLayout ws).write ((curveLayout ws).write i 0
          (Curve.addPoint ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay).1) 1
          (Curve.addPoint ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) ax ay).2) ∧
    (Curve.Representable ((curveLayout ws).read i 0) ((curveLayout ws).read i 1) = true →
        (curveLayout ws).read j 2 = 0)

theorem addsPointTotal_iff {ax ay ws : Nat} {r : RCircuit} :
    AddsPointTotal ax ay ws r ↔ (addsPointTotalSpec ax ay ws).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ _ i hi rfl rfl hpre
  · intro h x y i hi h₀ h₁ h₂
    subst h₀
    subst h₁
    exact h i hi h₂

/-- `InvertsField` as a record. -/
def invertsFieldSpec (ws n : Nat) : RegSpec where
  width := (unaryLayout n ws).width
  Pre i := (unaryLayout n ws).read i 1 = 0 ∧ (unaryLayout n ws).read i 2 = 0 ∧
    Curve.p ≤ 2 ^ n ∧ (unaryLayout n ws).read i 0 < Curve.p
  Post i j := j = (unaryLayout n ws).write i 1 (Curve.inv ((unaryLayout n ws).read i 0))

theorem invertsField_iff {ws n : Nat} {r : RCircuit} :
    InvertsField ws n r ↔ (invertsFieldSpec ws n).MetBy r := by
  constructor
  · intro h i hi hpre
    exact h _ i hi rfl hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2
  · intro h a i hi h₀ h₁ h₂ hp ha
    subst h₀
    exact h i hi ⟨h₁, h₂, hp, ha⟩

/-! ## Program realization -/

/--
The program meets the specification.

`out` is the basis-index permutation performed by the program, and `amp` is
the weight carried by each measurement record.  Both functions are independent
of the selected input.  Input-dependent record weights would reveal information
about the data.

The last clause states normalisation.  Well-formedness supplies it through
`totalProb_basis`.  Retaining the clause excludes a program whose branches all
carry amplitude zero.
-/
def RealisesAt (level input : Nat) (S : RegSpec) (p : Program) : Prop :=
  p.width = S.width ∧
  p.wellFormed level = true ∧
  input < 2 ^ p.inputBits ∧
  ∃ (out : Nat → Nat) (amp : List Bool → Dy (deg level)),
    ∀ i, i < 2 ^ S.width → S.Pre i →
      S.Post i (out i) ∧ out i < 2 ^ S.width ∧
      (∀ b ∈ runProgram level p input (basis i),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level))) ∧
      totalProb p.width (runProgram level p input (basis i)) = Dy.one (deg level)

def Realises (level : Nat) (S : RegSpec) (p : Program) : Prop := RealisesAt level 0 S p

/-- A realization carries from one register specification to another when the
second specification selects fewer inputs and accepts every output established
by the first. -/
theorem realisesAt_mono {level input : Nat} {S T : RegSpec} {p : Program}
    (h : RealisesAt level input S p)
    (hwidth : T.width = S.width)
    (hpre : ∀ i, T.Pre i → S.Pre i)
    (hpost : ∀ i j, T.Pre i → S.Post i j → T.Post i j) :
    RealisesAt level input T p := by
  rcases h with ⟨hpwidth, hwf, hinput, out, amp, hall⟩
  refine ⟨hpwidth.trans hwidth.symm, hwf, hinput, out, amp, ?_⟩
  intro i hi hT
  have hiS : i < 2 ^ S.width := by simpa [hwidth] using hi
  rcases hall i hiS (hpre i hT) with ⟨hout, houtRange, hbranches, htotal⟩
  refine ⟨hpost i (out i) hT hout, ?_, hbranches, htotal⟩
  simpa [hwidth] using houtRange

/-- Restricting the admissible basis inputs preserves a realization and its
common output and measurement-record amplitude witnesses. -/
theorem realisesAt_restrictPre {level input : Nat} {S : RegSpec} {p : Program}
    (h : RealisesAt level input S p) (P : Nat → Prop) :
    RealisesAt level input (S.restrictPre P) p :=
  realisesAt_mono h rfl (fun _ hpre => hpre.1) (fun _ _ _ hpost => hpost)

/-- A circuit read as a program is well formed when every gate is.  This belongs
beside `Program.ofCircuit` and is here because this is the only file that needs
it: a submission whose target is a program still owes the well-formedness
obligation, and a lifted reversible circuit should not have to reprove it. -/
theorem opsWellFormed_map_gate {level w iw cw : Nat} :
    ∀ gs : List Gate, gs.all (Gate.wellFormedAt level w) = true →
      Program.opsWellFormed level w iw cw (gs.map Op.gate) = true
  | [], _ => rfl
  | g :: gs, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    show (Program.opWellFormed level w iw cw (Op.gate g)
      && Program.opsWellFormed level w iw cw (gs.map Op.gate)) = true
    rw [Bool.and_eq_true]
    exact ⟨h.1, opsWellFormed_map_gate gs h.2⟩

theorem wellFormed_ofCircuit {level : Nat} {c : Circuit}
    (h : c.gates.all (Gate.wellFormedAt level c.width) = true) :
    Program.wellFormed level (Program.ofCircuit c) = true :=
  opsWellFormed_map_gate c.gates h

/-- Compilation preserves well-formedness for reversible circuits.
`Program.ofCircuit` stores the compiled gate list as program operations.  The
theorem applies at semantic levels at least three. -/
theorem wellFormed_ofCircuit_compile {level : Nat} (hl : 3 ≤ level) {r : RCircuit}
    (h : r.wellFormed = true) :
    Program.wellFormed level (Program.ofCircuit (compile r)) = true := by
  refine wellFormed_ofCircuit (List.all_eq_true.mpr fun p hp => ?_)
  rw [width_compile]
  obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap (gates_compile r ▸ hp)
  exact wellFormedAt_compileGate
    (RCircuit.wellFormedAt_mem (RCircuit.wellFormedAt_of_wellFormed hl h) hg) hpg

/-- Compilation lifts a reversible circuit satisfying `RegSpec.MetBy` to a
program realization.  Every component built against
`VQ/Reversible/ArithmeticSpec.lean` or
`VQ/Curve/ReversibleSpec.lean` carries over to the program vocabulary through
this theorem.  The resulting program has one branch with weight one and uses
`act` as its basis-index permutation. -/
theorem realises_ofCircuit {level : Nat} (hl : 3 ≤ level) {S : RegSpec} {r : RCircuit}
    (hw : r.width = S.width) (hwf : r.wellFormed = true) (h : S.MetBy r) :
    Realises level S (Program.ofCircuit (compile r)) := by
  refine ⟨hw, wellFormed_ofCircuit_compile hl hwf, Nat.two_pow_pos _, act r,
    fun _ => Dy.one (deg level), fun i hi hpre => ?_⟩
  have hir : i < 2 ^ r.width := by rw [hw]; exact hi
  have hact : act r i < 2 ^ S.width := by rw [← hw]; exact act_lt hwf hir
  have hrun : runProgram level (Program.ofCircuit (compile r)) 0 (basis i)
      = [Branch.mk [] 0 (basis (act r i) : Vec (deg level)) 0] := by
    rw [runProgram_ofCircuit, run_compile_basis hl hwf]
  refine ⟨h i hi hpre, hact, ?_, ?_⟩
  · intro b hb
    rw [hrun] at hb
    rw [List.mem_singleton.mp hb]
    exact (Vec.one_smul _).symm
  · rw [hrun]
    show branchProb (Program.ofCircuit (compile r)).width _ + _ = _
    rw [totalProb_nil, Dy.add_zero]
    show normSq (2 ^ (compile r).width) (basis (act r i) : Vec (deg level)) = _
    exact normSq_basis (by rw [width_compile]; exact act_lt hwf hir)

/-- Scalar multiplication distributes over the sum of two states. -/
theorem smul_add_vec {d : Nat} (a : Dy d) (u v : Vec d) : a • (u + v) = a • u + a • v :=
  Vec.ext fun i => Dy.left_distrib a (u i) (v i)

/-- Two same-shaped branch lists whose states depend on their measurement
records combine record by record.  This list identity supplies the arithmetic
used by `realises_pair`. -/
theorem zipWith_addBranch_of_states {d : Nat} {L L' : List (Branch d)}
    (hs : shape L = shape L') {f g : List Bool → Vec d}
    (hL : ∀ b ∈ L, b.state = f b.outcomes) (hL' : ∀ b ∈ L', b.state = g b.outcomes)
    (a c : Dy d) :
    List.zipWith addBranch (L.map (smulBranch a)) (L'.map (smulBranch c))
      = L.map (fun b => { b with state := a • f b.outcomes + c • g b.outcomes }) := by
  induction L generalizing L' with
  | nil => cases L' <;> rfl
  | cons x xs ih =>
    cases L' with
    | nil => exact absurd hs (List.cons_ne_nil _ _)
    | cons y ys =>
      simp only [shape, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
      obtain ⟨⟨hrec, _, _⟩, hrest⟩ := hs
      rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, List.map_cons,
        ih hrest (fun b hb => hL b (List.mem_cons_of_mem _ hb))
          (fun b hb => hL' b (List.mem_cons_of_mem _ hb))]
      have hx := hL x (List.mem_cons_self ..)
      have hy := hL' y (List.mem_cons_self ..)
      have hhead : addBranch (smulBranch a x) (smulBranch c y)
          = ({ outcomes := x.outcomes, creg := x.creg,
               state := a • f x.outcomes + c • g x.outcomes,
               input := x.input } : Branch d) := by
        show (⟨x.outcomes, x.creg, a • x.state + c • y.state, x.input⟩ : Branch d) = _
        rw [hx, hy, ← hrec]
      rw [hhead]

/-- If each basis input yields branch states with an input-independent amplitude
for each measurement record, the same branch carries the corresponding
superposition for two basis inputs.  A program that measures data and separates
the two inputs into different records cannot satisfy the premise. -/
theorem realises_pair {level : Nat} {S : RegSpec} {p : Program}
    {out : Nat → Nat} {amp : List Bool → Dy (deg level)}
    (input : Nat)
    (hcl : ∀ i, i < 2 ^ S.width → S.Pre i →
      ∀ b ∈ runProgram level p input (basis i),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level)))
    {i i' : Nat} (hi : i < 2 ^ S.width) (hi' : i' < 2 ^ S.width)
    (hp : S.Pre i) (hp' : S.Pre i') (a c : Dy (deg level)) :
    runProgram level p input (a • basis i + c • basis i')
      = (runProgram level p input (basis i)).map (fun b =>
          { b with state := amp b.outcomes •
              (a • (basis (out i) : Vec (deg level)) + c • basis (out i')) }) := by
  have hsplit : runProgram level p input (a • basis i + c • basis i')
      = List.zipWith addBranch
          ((runProgram level p input (basis i)).map (smulBranch a))
          ((runProgram level p input (basis i')).map (smulBranch c)) := by
    show runOps level p.width p.ops
      (Branch.mk [] 0 (a • basis i + c • basis i') input) = _
    rw [(runOps_add level p.width).2 p.ops [] 0 input (a • basis i) (c • basis i')]
    congr 1
    · exact (runOps_smul level p.width).2 p.ops a (Branch.mk [] 0 (basis i) input)
    · exact (runOps_smul level p.width).2 p.ops c (Branch.mk [] 0 (basis i') input)
  have hshape : shape (runProgram level p input (basis i))
      = shape (runProgram level p input (basis i')) := by
    show shape (runOps level p.width p.ops (Branch.mk [] 0 (basis i) input))
        = shape (runOps level p.width p.ops (Branch.mk [] 0 (basis i') input))
    rw [(shape_runOps level p.width).2, (shape_runOps level p.width).2]
  rw [hsplit, zipWith_addBranch_of_states (f := fun o => amp o • (basis (out i) : Vec (deg level)))
      (g := fun o => amp o • (basis (out i') : Vec (deg level)))
      hshape (hcl i hi hp) (hcl i' hi' hp') a c]
  refine congrArg (fun f => List.map f (runProgram level p input (basis i))) (funext fun b => ?_)
  have hswap : ∀ (s : Dy (deg level)) (v : Vec (deg level)),
      s • (amp b.outcomes • v) = amp b.outcomes • (s • v) := fun s v => by
    rw [Vec.smul_smul, Vec.smul_smul, Dy.mul_comm]
  rw [hswap a, hswap c, ← smul_add_vec]

/-! ## Measured segment

Gidney's uncompute leaves the ancilla set on the outcome-one branch, so on its
own it sends one input to two different basis states and implements no
permutation.  `ImplementsU` rejects it for that reason, which is the definition
behaving as intended.  Correcting the ancilla under classical control makes the
two branches agree, and that corrected list is the segment a construction uses.
-/

/-- Gidney's uncompute with the ancilla returned to zero on both branches. -/
def andUncomputeClean (a b c m : Nat) : List Op :=
  andUncompute a b c m ++ [Op.branch (.localBit m) [Op.gate (Gate.x c)] []]

/-- Writing the same wire twice keeps the second value. -/
theorem writeBit_writeBit (n c : Nat) (x y : Bool) :
    writeBit (writeBit n c x) c y = writeBit n c y := by
  refine Nat.eq_of_testBit_eq (fun r => ?_)
  by_cases hr : r = c
  · subst hr; rw [testBit_writeBit, testBit_writeBit]
  · rw [testBit_writeBit_of_ne hr, testBit_writeBit_of_ne hr, testBit_writeBit_of_ne hr]

/-- On a basis state whose ancilla already holds the AND, the data Gidney's
uncompute leaves is the same basis state with the ancilla cleared. -/
theorem ancillaZero_andData_basis {level a b c i : Nat} (hac : a ≠ c) (hbc : b ≠ c)
    (hand : i.testBit c = (i.testBit a && i.testBit b)) :
    ancillaZero c (andData a b c (basis i : Vec (deg level)))
      = basis (writeBit i c false) := by
  refine Vec.ext (fun j => ?_)
  show (if j.testBit c then Dy.zero (deg level)
    else (basis i : Vec (deg level)) (writeBit j c (j.testBit a && j.testBit b))) = _
  by_cases hjc : j.testBit c = true
  · rw [if_pos hjc]
    have hne : j ≠ writeBit i c false := by
      intro h
      rw [h, testBit_writeBit] at hjc
      exact Bool.noConfusion hjc
    exact (basis_of_ne hne).symm
  · rw [Bool.not_eq_true] at hjc
    rw [if_neg (by rw [hjc]; exact Bool.noConfusion)]
    by_cases hj : j = writeBit i c false
    · subst hj
      rw [testBit_writeBit_of_ne hac, testBit_writeBit_of_ne hbc, ← hand,
        writeBit_writeBit, writeBit_self rfl, basis_self, basis_self]
    · have hne : writeBit j c (j.testBit a && j.testBit b) ≠ i := by
        intro h
        refine hj (Nat.eq_of_testBit_eq (fun r => ?_))
        by_cases hr : r = c
        · subst hr; rw [hjc, testBit_writeBit]
        · rw [testBit_writeBit_of_ne hr, ← h, testBit_writeBit_of_ne hr]
      rw [basis_of_ne hne, basis_of_ne hj]


/-- Scaling a branch list does not move its classical part. -/
theorem shape_map_smulBranch {d : Nat} (c : Dy d) (L : List (Branch d)) :
    shape (L.map (smulBranch c)) = shape L := by
  unfold shape
  rw [List.map_map]
  rfl

/-- Two branch lists of the same shape, each of whose states is a function of its
measurement record, add record by record. -/
theorem zipWith_addBranch_mem {d : Nat} :
    ∀ {X Y : List (Branch d)}, shape X = shape Y → ∀ {g h : List Bool → Vec d},
      (∀ x ∈ X, x.state = g x.outcomes) → (∀ y ∈ Y, y.state = h y.outcomes) →
        ∀ b ∈ List.zipWith addBranch X Y, b.state = g b.outcomes + h b.outcomes
  | [], Y, _, _, _, _, _, b, hb => by
    rw [List.zipWith_nil_left] at hb
    exact absurd hb (List.not_mem_nil)
  | x :: xs, [], hs, _, _, _, _, _, _ => by
    exact absurd hs (List.cons_ne_nil _ _)
  | x :: xs, y :: ys, hs, g, h, hX, hY, b, hb => by
    simp only [shape, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨hrec, _⟩, hrest⟩ := hs
    rw [List.zipWith_cons_cons, List.mem_cons] at hb
    rcases hb with h' | h'
    · subst h'
      show x.state + y.state = _
      rw [hX x (List.mem_cons_self ..), hY y (List.mem_cons_self ..), ← hrec]
      rfl
    · exact zipWith_addBranch_mem hrest
        (fun z hz => hX z (List.mem_cons_of_mem _ hz))
        (fun z hz => hY z (List.mem_cons_of_mem _ hz)) b h'

/-- A finite superposition of basis states: `Σ a i • |f i⟩` over a list. -/
def superpose {d : Nat} (f : Nat → Nat) (a : Nat → Dy d) : List Nat → Vec d
  | [] => Vec.zero d
  | i :: rest => a i • basis (f i) + superpose f a rest

/-- Every branch holds the same superposition of the images when the incoming
measurement record and classical register are fixed. -/
theorem runOps_superpose_at {level w input : Nat} {ops : List Op} {out : Nat → Nat}
    {amp : List Bool → Dy (deg level)} {dom : Nat → Prop}
    (rec : List Bool) (cr : Nat)
    (hcl : ∀ i, i < 2 ^ w → dom i →
      ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level))) :
    ∀ (L : List Nat) (a : Nat → Dy (deg level)),
      (∀ i ∈ L, i < 2 ^ w ∧ dom i) →
        ∀ b ∈ runOps level w ops (Branch.mk rec cr (superpose id a L) input),
          b.state = amp b.outcomes • superpose out a L
  | [], a, _, b, hb => by
    rw [show superpose (d := deg level) id a [] = Vec.zero (deg level) from rfl] at hb
    rw [runOps_zero_state level w ops rec cr input hb,
      show superpose (d := deg level) out a [] = Vec.zero (deg level) from rfl, Vec.smul_zero]
  | i :: L, a, hmem, b, hb => by
    have hi := hmem i (List.mem_cons_self ..)
    have hsplit : runOps level w ops (Branch.mk rec cr (superpose id a (i :: L)) input)
        = List.zipWith addBranch
            ((runOps level w ops (Branch.mk rec cr (basis i) input)).map (smulBranch (a i)))
            (runOps level w ops (Branch.mk rec cr (superpose id a L) input)) := by
      show runOps level w ops
        (Branch.mk rec cr (a i • basis (id i) + superpose id a L) input) = _
      rw [(runOps_add level w).2 ops rec cr input (a i • basis (id i)) (superpose id a L)]
      congr 1
      exact (runOps_smul level w).2 ops (a i) (Branch.mk rec cr (basis (id i)) input)
    have hshape : shape ((runOps level w ops (Branch.mk rec cr (basis i) input)).map
        (smulBranch (a i))) =
        shape (runOps level w ops (Branch.mk rec cr (superpose id a L) input)) := by
      rw [shape_map_smulBranch, (shape_runOps level w).2, (shape_runOps level w).2]
    rw [hsplit] at hb
    have hX : ∀ x ∈ (runOps level w ops (Branch.mk rec cr (basis i) input)).map
        (smulBranch (a i)),
        x.state = a i • (amp x.outcomes • (basis (out i) : Vec (deg level))) := by
      intro x hx
      obtain ⟨x₀, hx₀, hxe⟩ := List.mem_map.mp hx
      rw [← hxe]
      show a i • x₀.state = _
      rw [hcl i hi.1 hi.2 x₀ hx₀]
      rfl
    have hY := runOps_superpose_at rec cr hcl L a
      (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
    have := zipWith_addBranch_mem (g := fun s => a i • (amp s • (basis (out i) : Vec (deg level))))
      (h := fun s => amp s • superpose out a L) hshape hX hY b hb
    rw [this]
    refine Vec.ext (fun k => ?_)
    show a i * (amp b.outcomes * (basis (out i) : Vec (deg level)) k)
        + amp b.outcomes * superpose out a L k
      = amp b.outcomes * (a i * (basis (out (id i)) : Vec (deg level)) k
        + superpose out a L k)
    rw [Dy.left_distrib, ← Dy.mul_assoc, ← Dy.mul_assoc,
      Dy.mul_comm (a i) (amp b.outcomes)]
    rfl

/--
Every branch holds the same superposition of the images, scaled by a weight the
input does not reach.

`realises_pair` is this at two terms.  This is the statement the definition of
`Realises` exists for: any state supported on the inputs the specification covers
comes out permuted and scaled, and the scale carries no information about which
input it was.  A program whose branch weight depended on the input would fail it,
and `Tests/Realise.lean` exhibits such a program.
-/
theorem runOps_superpose {level w input : Nat} {ops : List Op} {out : Nat → Nat}
    {amp : List Bool → Dy (deg level)} {dom : Nat → Prop}
    (hcl : ∀ i, i < 2 ^ w → dom i → ∀ rec cr,
      ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level)))
    (rec : List Bool) (cr : Nat) :
    ∀ (L : List Nat) (a : Nat → Dy (deg level)),
      (∀ i ∈ L, i < 2 ^ w ∧ dom i) →
        ∀ b ∈ runOps level w ops (Branch.mk rec cr (superpose id a L) input),
          b.state = amp b.outcomes • superpose out a L :=
  runOps_superpose_at rec cr (fun i hi hdom ↦ hcl i hi hdom rec cr)

/-! ## Uniform segment semantics

Concatenating operation lists indexes branch weights by branch-list position.
`Realises` indexes weights by measurement record.  Composition therefore needs
a relation between those representations.

A record-indexed conversion would prove that branch records form a
suffix-antichain and then recover each weight by lookup.  Records from different
arms of an earlier measurement must have no common extension.  Proving this
requires `Nodup` results for `flatMap` that are unavailable in the current core
imports.

The implemented definition indexes weight by the number of measurements made
by the segment: `c ^ (record length minus incoming record length)`.
`opsShape_extends` proves that each output record extends its input record, so
composition reduces to arithmetic on lengths.  The conversion to `Realises`
uses `amp s := c ^ s.length`.

`UniformWeightRealises` represents equal per-measurement scalar weights.  Gidney
uncomputation gives each branch weight `1/√2`, and a unitary segment gives its
single branch weight `1`.  The repository has no uniformity theorem for
measurement-based unlookup.  Unequal branch weights require the record-indexed
conversion described above.
-/

/-- Every branch record a segment produces extends the record it started from. -/
theorem opsShape_extends :
    (∀ o : Op, ∀ (rec : List Bool) (n input : Nat), ∀ p ∈ opShape o rec n input,
        ∃ new : List Bool, p.1 = new ++ rec) ∧
    (∀ os : List Op, ∀ (rec : List Bool) (n input : Nat), ∀ p ∈ opsShape os rec n input,
        ∃ new : List Bool, p.1 = new ++ rec) := by
  refine opInduction (fun g rec n input p hp => ?_) (fun q c rec n input p hp => ?_)
    (fun q rec n input p hp => ?_) (fun c value rec n input p hp => ?_)
    (fun c rec n input p hp => ?_) (fun c t e ht he rec n input p hp => ?_)
    (fun rec n input p hp => ?_) (fun o os ho hos rec n input p hp => ?_)
  · rw [opShape] at hp
    rw [List.mem_singleton.mp hp]
    exact ⟨[], rfl⟩
  · rw [opShape] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h
    · exact ⟨[false], by subst h; rfl⟩
    · exact ⟨[true], by subst h; rfl⟩
  · rw [opShape] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h
    · exact ⟨[false], by subst h; rfl⟩
    · exact ⟨[true], by subst h; rfl⟩
  · rw [opShape] at hp
    rw [List.mem_singleton.mp hp]
    exact ⟨[], rfl⟩
  · rw [opShape] at hp
    rw [List.mem_singleton.mp hp]
    exact ⟨[], rfl⟩
  · rw [opShape] at hp
    by_cases hc : c.read input n
    · rw [if_pos hc] at hp; exact ht rec n input p hp
    · rw [if_neg hc] at hp; exact he rec n input p hp
  · rw [opsShape] at hp
    rw [List.mem_singleton.mp hp]
    exact ⟨[], rfl⟩
  · rw [opsShape, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨n₁, h₁⟩ := ho rec n input q hq
    obtain ⟨n₂, h₂⟩ := hos q.1 q.2.1 q.2.2 p hpq
    exact ⟨n₂ ++ n₁, by rw [h₂, h₁, List.append_assoc]⟩

/-- The same fact about a run rather than about the shape. -/
theorem runOps_extends (level w : Nat) (ops : List Op) (rec : List Bool) (cr : Nat)
    (input : Nat) (u : Vec (deg level)) {b : Branch (deg level)}
    (hb : b ∈ runOps level w ops (Branch.mk rec cr u input)) :
    ∃ new : List Bool, b.outcomes = new ++ rec := by
  have hmem : (b.outcomes, b.creg, b.input) ∈
      shape (runOps level w ops (Branch.mk rec cr u input)) :=
    List.mem_map_of_mem hb
  rw [(shape_runOps level w).2 ops rec cr input u] at hmem
  exact opsShape_extends.2 ops rec cr input _ hmem

/-- A run never shortens the record it started from. -/
theorem runOps_record_le (level w : Nat) (ops : List Op) (rec : List Bool) (cr : Nat)
    (input : Nat) (u : Vec (deg level)) {b : Branch (deg level)}
    (hb : b ∈ runOps level w ops (Branch.mk rec cr u input)) :
    rec.length ≤ b.outcomes.length := by
  obtain ⟨new, hnew⟩ := runOps_extends level w ops rec cr input u hb
  rw [hnew, List.length_append]
  omega

/-- Every branch holds one basis state, weighted by `c` to the number of
measurements that branch made. -/
def ImplementsU (level w input : Nat) (dom : Nat → Prop) (out : Nat → Nat)
    (c : Dy (deg level)) (ops : List Op) : Prop :=
  ∀ i, i < 2 ^ w → dom i → ∀ rec cr,
    ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
      b.state = c ^ (b.outcomes.length - rec.length) • (basis (out i) : Vec (deg level))

/-- A segment implementing something on a domain implements it on any smaller
one.  `implementsU_gates` proves its instance on every input, and a caller
usually has a narrower domain to chain. -/
theorem ImplementsU.mono {level w input : Nat} {dom dom' : Nat → Prop} {out : Nat → Nat}
    {c : Dy (deg level)} {ops : List Op}
    (h : ImplementsU level w input dom out c ops) (hsub : ∀ i, dom' i → dom i) :
    ImplementsU level w input dom' out c ops :=
  fun i hi hd rec cr b hb => h i hi (hsub i hd) rec cr b hb

/-- Segments compose: the permutations compose and the measurement counts add.

The domain hypotheses require the first segment's image to satisfy the second
segment's input condition and remain inside the register. -/
theorem ImplementsU.append {level w input : Nat} {dom₁ dom₂ : Nat → Prop}
    {out₁ out₂ : Nat → Nat} {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsU level w input dom₁ out₁ c a)
    (h₂ : ImplementsU level w input dom₂ out₂ c b)
    (hrange : ∀ i, i < 2 ^ w → dom₁ i → out₁ i < 2 ^ w)
    (hdom : ∀ i, i < 2 ^ w → dom₁ i → dom₂ (out₁ i)) :
    ImplementsU level w input dom₁ (fun i => out₂ (out₁ i)) c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxs := h₁ i hi hd rec cr x hx
  have hxi : x.input = input := input_runOps level w a hx
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (Branch.mk x.outcomes x.creg (basis (out₁ i)) input) := by
    cases x with
    | mk o cg st inp => simp only [smulBranch] at hxi ⊢; subst inp; rw [← hxs]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  have hys := h₂ (out₁ i) (hrange i hi hd) (hdom i hi hd) x.outcomes x.creg y hy
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ y.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hy
  have hout : br.outcomes = y.outcomes := by rw [← hyb]; rfl
  have hst : br.state = (c ^ (x.outcomes.length - rec.length)) • y.state := by
    rw [← hyb]; rfl
  rw [hst, hys, Vec.smul_smul, ← Dy.pow_add, hout]
  congr 2
  omega

/-- A uniform segment meets the committed claim, with the weight of a record
read off its length.  This is the bridge the file's design note describes. -/
theorem realisesAt_of_implementsU {level input : Nat} {S : RegSpec} {p : Program}
    {out : Nat → Nat} {c : Dy (deg level)}
    (hw : p.width = S.width)
    (hwf : p.wellFormed level = true)
    (hinput : input < 2 ^ p.inputBits)
    (himp : ImplementsU level p.width input S.Pre out c p.ops)
    (hpost : ∀ i, i < 2 ^ S.width → S.Pre i → S.Post i (out i) ∧ out i < 2 ^ S.width)
    (hnorm : ∀ i, i < 2 ^ S.width → S.Pre i →
      totalProb p.width (runProgram level p input (basis i)) = Dy.one (deg level)) :
    RealisesAt level input S p := by
  refine ⟨hw, hwf, hinput, out, fun s => c ^ s.length, fun i hi hpre => ?_⟩
  have hiw : i < 2 ^ p.width := by rw [hw]; exact hi
  refine ⟨(hpost i hi hpre).1, (hpost i hi hpre).2, ?_, hnorm i hi hpre⟩
  intro b hb
  have := himp i hiw hpre [] 0 b hb
  simpa using this

theorem realises_of_implementsU {level : Nat} {S : RegSpec} {p : Program}
    {out : Nat → Nat} {c : Dy (deg level)}
    (hw : p.width = S.width)
    (hwf : p.wellFormed level = true)
    (himp : ImplementsU level p.width 0 S.Pre out c p.ops)
    (hpost : ∀ i, i < 2 ^ S.width → S.Pre i → S.Post i (out i) ∧ out i < 2 ^ S.width)
    (hnorm : ∀ i, i < 2 ^ S.width → S.Pre i →
      totalProb p.width (runProgram level p 0 (basis i)) = Dy.one (deg level)) :
    Realises level S p :=
  realisesAt_of_implementsU hw hwf (Nat.two_pow_pos _) himp hpost hnorm

/-- A gate list is a uniform segment at any weight: one branch, no measurement,
so the exponent is zero. -/
theorem implementsU_gates {level w input : Nat} (hl : 3 ≤ level) {r : Reversible.RCircuit}
    (hw : r.width = w) (hwf : r.wellFormed = true) (c : Dy (deg level)) :
    ImplementsU level w input (fun _ => True) (Reversible.act r) c
      ((Reversible.compile r).gates.map Op.gate) := by
  intro i _ _ rec cr b hb
  rw [runOps_gates, List.mem_singleton] at hb
  subst hb
  show runGates level w (Reversible.compile r).gates (basis i)
    = c ^ (rec.length - rec.length) • (basis (Reversible.act r i) : Vec (deg level))
  have hrun : runGates level w (Reversible.compile r).gates (basis i)
      = (basis (Reversible.act r i) : Vec (deg level)) := by
    subst hw
    exact Reversible.run_compile_basis hl hwf i
  rw [hrun, Nat.sub_self]
  show _ = Dy.one (deg level) • _
  rw [Vec.one_smul]

/-- Flipping a wire twice is the identity. -/
theorem flipVec_flipVec {d : Nat} (q : Nat) (u : Vec d) : flipVec q (flipVec q u) = u := by
  refine Vec.ext (fun i => ?_)
  show u ((i ^^^ (1 <<< q)) ^^^ (1 <<< q)) = u i
  rw [Nat.one_shiftLeft, xor_two_pow_cancel]

/-- A basis state whose ancilla holds the AND of the two inputs. -/
theorem andAncilla_basis {d a b c i : Nat}
    (hand : i.testBit c = (i.testBit a && i.testBit b)) :
    AndAncilla a b c (basis i : Vec d) := by
  intro j hj
  refine basis_of_ne (fun h => hj ?_)
  subst h
  exact hand

/--
Gidney's uncompute, corrected, is a uniform segment at weight `1/√2`.

Both branches leave the register in the input with the ancilla cleared, and each
carries the input-independent weight `1/√2`.  The measurement record therefore
reveals no data.  The correction aligns the branch outputs.  Omitting it leaves
the outcome-one ancilla set and prevents the segment from implementing a
permutation.
-/
theorem implementsU_andUncomputeClean {level w input a b c m : Nat} (hl : 3 ≤ level)
    (haw : a < w) (hbw : b < w) (hcw : c < w) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ImplementsU level w input
      (fun i => i.testBit c = (i.testBit a && i.testBit b))
      (fun i => writeBit i c false)
      (Dy.invSqrt2 (deg level)) (andUncomputeClean a b c m) := by
  intro i _ hand rec cr br hbr
  rw [andUncomputeClean, runOps_append,
    runOps_andUncompute hl haw hbw hcw hab hac hbc (andAncilla_basis hand) rec cr input] at hbr
  have hpow : Dy.invSqrt2 (deg level) ^ 1 = Dy.invSqrt2 (deg level) := by
    rw [Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]
  have hsm : ∀ v : Vec (deg level), ancillaZero c (Dy.invSqrt2 (deg level) • v)
      = Dy.invSqrt2 (deg level) • ancillaZero c v := by
    intro v
    refine Vec.ext (fun j => ?_)
    show (if j.testBit c then Dy.zero (deg level) else Dy.invSqrt2 (deg level) * v j)
        = Dy.invSqrt2 (deg level) * (if j.testBit c then Dy.zero (deg level) else v j)
    by_cases hjc : j.testBit c
    · rw [if_pos hjc, if_pos hjc, Dy.mul_zero]
    · rw [if_neg hjc, if_neg hjc]
  have hclean : ancillaZero c (Dy.invSqrt2 (deg level) •
      andData a b c (basis i : Vec (deg level)))
      = Dy.invSqrt2 (deg level) • (basis (writeBit i c false) : Vec (deg level)) := by
    rw [hsm, ancillaZero_andData_basis hac hbc hand]
  have hgx : (Gate.x c).wellFormedAt level w = true := by
    simp only [Gate.wellFormedAt, decide_eq_true_eq]; omega
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    runOps_singleton, runOp_branch] at hbr
  rcases hbr with h | h
  · rw [if_neg (by simp [CRef.read, testBit_writeBit])] at h
    rw [runOps_nil, List.mem_singleton] at h
    have hout : br.outcomes = false :: rec := by rw [h]
    have hst : br.state
        = ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c (basis i : Vec (deg level))) := by
      rw [h]
    rw [hst, hclean, hout, List.length_cons, Nat.add_sub_cancel_left, hpow]
  · rw [if_pos (by simp [CRef.read, testBit_writeBit])] at h
    rw [runOp_gate, List.mem_singleton] at h
    have hout : br.outcomes = true :: rec := by rw [h]
    have hst : br.state = gateVec level w (Gate.x c)
        (flipVec c (ancillaZero c
          (Dy.invSqrt2 (deg level) • andData a b c (basis i : Vec (deg level))))) := by
      rw [h]
    rw [hst, gateVec_of_wf hgx]
    show flipVec c (flipVec c _) = _
    rw [flipVec_flipVec, hclean, hout, List.length_cons, Nat.add_sub_cancel_left, hpow]

end Semantics
end VQ
