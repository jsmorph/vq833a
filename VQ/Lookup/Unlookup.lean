/-
Measured unlookup, realization, and generic resource bounds for three-bit lookup.
-/
import VQ.Lookup.Resources
import VQ.Program.Depth

namespace VQ
namespace Lookup3

open Algebra Reversible Semantics

def gateOps (gs : List RGate) : List Op :=
  (gs.flatMap compileGate).map Op.gate

def phaseRowOps (m row : Nat) : List Op :=
  gateOps (compute m row) ++ [.gate (.z (flagWire m))] ++
    gateOps (compute m row).reverse

def phaseRows (table : List Nat) (m bit : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | row, count + 1 =>
      (if (value table m row).testBit bit then phaseRowOps m row else []) ++
        phaseRows table m bit (row + 1) count

def phaseForBit (table : List Nat) (m bit : Nat) : List Op :=
  phaseRows table m bit 0 (2 ^ addressWidth)

def unlookupBit (table : List Nat) (m bit : Nat) : List Op :=
  [.gate (.h (outputOffset + bit)), .measure (outputOffset + bit) 0,
    .branch (.localBit 0)
      (phaseForBit table m bit ++ [.gate (.x (outputOffset + bit))]) []]

def unlookupAux (table : List Nat) (m : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      unlookupBit table m bit ++ unlookupAux table m (bit + 1) count

def unlookupOps (table : List Nat) (m : Nat) : List Op :=
  unlookupAux table m 0 m

def unlookupProgram (table : List Nat) (m : Nat) : Program :=
  { width := width m, cbits := if m = 0 then 0 else 1, ops := unlookupOps table m }

def roundTripProgram (table : List Nat) (m : Nat) : Program :=
  { width := width m, cbits := if m = 0 then 0 else 1,
    ops := gateOps (lookupGates table m) ++ unlookupOps table m }

theorem gateOps_run {level w : Nat} (gs : List RGate) (b : Branch (deg level)) :
    runOps level w (gateOps gs) b =
      [{ b with state := runGates level w (gs.flatMap compileGate) b.state }] := by
  exact runOps_gates level w (gs.flatMap compileGate) b

theorem phaseRow_run {level : Nat} (hl : 3 ≤ level) {m row i : Nat}
    (hrow : row < 2 ^ addressWidth) (hclear : workspaceClear m i)
    (rec : List Bool) (cr input : Nat) :
    runOps level (width m) (phaseRowOps m row)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if address i = row then -(basis i : Vec (deg level)) else basis i) input] := by
  let r : RCircuit := { width := width m, gates := compute m row }
  have hr : r.wellFormed = true := compute_wellFormed m row
  have hrev : r.reverse.wellFormed = true := RCircuit.wellFormed_reverse hr
  have hflag := compute_flag (row := row) hclear
  rw [phaseRowOps, runOps_append, runOps_append, gateOps_run,
    List.flatMap_singleton, runOps_singleton, runOp_gate, List.flatMap_singleton,
    gateOps_run]
  change [Branch.mk rec cr (run level (compile r.reverse)
    (gateVec level (width m) (.z (flagWire m))
      (run level (compile r) (basis i)))) input] = _
  rw [Reversible.run_compile_basis hl hr,
    apply_z (level := level) (w := width m) (q := flagWire m)
      (by simp [flagWire, width]) (by omega) (act r i)]
  change (act r i).testBit (flagWire m) = _ at hflag
  rw [hflag]
  by_cases heq : address i = row
  · rw [if_pos (show decide (address i = row % 2 ^ addressWidth) = true by
        simp [Nat.mod_eq_of_lt hrow, heq]), if_pos heq]
    have hnegOut : -(basis i : Vec (deg level)) =
        (-Dy.one (deg level)) • basis i := by
      apply Vec.ext
      intro j
      exact neg_eq_neg_one_mul _
    rw [Semantics.run_smul, Reversible.run_compile_basis hl hrev,
      act_reverse hr, ← hnegOut]
  · rw [if_neg (show ¬decide (address i = row % 2 ^ addressWidth) = true by
        simp [Nat.mod_eq_of_lt hrow, heq]), if_neg heq,
      Reversible.run_compile_basis hl hrev, act_reverse hr]

theorem runOps_neg (level w : Nat) (ops : List Op) (rec : List Bool)
    (cr input : Nat) (u : Vec (deg level)) :
    runOps level w ops (Branch.mk rec cr (-u) input) =
      (runOps level w ops (Branch.mk rec cr u input)).map
        (fun b => { b with state := -b.state }) := by
  have hneg (v : Vec (deg level)) : -v = (-Dy.one (deg level)) • v := by
    apply Vec.ext
    intro j
    exact neg_eq_neg_one_mul _
  rw [hneg u]
  change runOps level w ops
      (smulBranch (-Dy.one (deg level)) (Branch.mk rec cr u input)) = _
  rw [(runOps_smul level w).2]
  apply List.map_congr_left
  intro b hb
  cases b
  simp [smulBranch, hneg]

theorem phaseRows_run {level : Nat} (hl : 3 ≤ level) {table : List Nat} {m bit : Nat} :
    ∀ start count i, start + count ≤ 2 ^ addressWidth → workspaceClear m i →
      ∀ rec cr input,
      runOps level (width m) (phaseRows table m bit start count)
        (Branch.mk rec cr (basis i) input) =
          [Branch.mk rec cr
            (if start ≤ address i ∧ address i < start + count ∧
                (value table m (address i)).testBit bit
              then -(basis i : Vec (deg level)) else basis i) input] := by
  intro start count
  induction count generalizing start with
  | zero =>
    intro i _ _ rec cr input
    rw [phaseRows, runOps_nil, if_neg]
    omega
  | succ count ih =>
    intro i hbound hclear rec cr input
    rw [phaseRows, runOps_append]
    by_cases hbit : (value table m start).testBit bit = true
    · rw [if_pos hbit, phaseRow_run hl (show start < 2 ^ addressWidth by omega) hclear,
        List.flatMap_singleton]
      by_cases heq : address i = start
      · rw [if_pos heq]
        have htail := ih (start + 1) i (by omega) hclear rec cr input
        rw [if_neg (by rw [heq]; omega)] at htail
        rw [runOps_neg, htail]
        simp only [List.map_cons, List.map_nil]
        rw [if_pos]
        exact ⟨by omega, by omega, by simpa [heq] using hbit⟩
      · rw [if_neg heq, ih (start + 1) i (by omega) hclear]
        by_cases hrange : start + 1 ≤ address i ∧ address i < start + 1 + count ∧
            (value table m (address i)).testBit bit
        · rw [if_pos hrange, if_pos]
          exact ⟨by omega, by omega, hrange.2.2⟩
        · rw [if_neg hrange, if_neg]
          intro h
          apply hrange
          exact ⟨by omega, by omega, h.2.2⟩
    · rw [if_neg hbit, runOps_nil, List.flatMap_singleton,
        ih (start + 1) i (by omega) hclear]
      by_cases hrange : start + 1 ≤ address i ∧ address i < start + 1 + count ∧
          (value table m (address i)).testBit bit
      · rw [if_pos hrange, if_pos]
        exact ⟨by omega, by omega, hrange.2.2⟩
      · rw [if_neg hrange, if_neg]
        intro h
        by_cases heq : address i = start
        · subst heq
          exact hbit h.2.2
        · apply hrange
          exact ⟨by omega, by omega, h.2.2⟩

theorem phaseForBit_run {level : Nat} (hl : 3 ≤ level) {table : List Nat} {m bit i : Nat}
    (hclear : workspaceClear m i) (rec : List Bool) (cr input : Nat) :
    runOps level (width m) (phaseForBit table m bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if (value table m (address i)).testBit bit
            then -(basis i : Vec (deg level)) else basis i) input] := by
  rw [phaseForBit, phaseRows_run hl 0 (2 ^ addressWidth) i (by omega) hclear]
  by_cases hb : (value table m (address i)).testBit bit <;>
    simp [hb, address_lt]

theorem projVec_basis_same {d q j : Nat} {b : Bool} (h : j.testBit q = b) :
    projVec q b (basis j : Vec d) = basis j := by
  apply Vec.ext
  intro i
  by_cases hij : i = j
  · subst i
    simp [projVec, h]
  · simp [projVec, basis_of_ne hij]

theorem projVec_basis_other {d q j : Nat} {b : Bool} (h : j.testBit q ≠ b) :
    projVec q b (basis j : Vec d) = Vec.zero d := by
  apply Vec.ext
  intro i
  by_cases hij : i = j
  · subst i
    simp [projVec, h]
  · simp [projVec, basis_of_ne hij, Vec.zero]

theorem projVec_sub (q : Nat) (b : Bool) (u v : Vec d) :
    projVec q b (u - v) = projVec q b u - projVec q b v := by
  apply Vec.ext
  intro i
  by_cases h : i.testBit q = b <;> simp [projVec, h, Vec.sub_apply, Semantics.sub_zero]

theorem vec_add_zero (u : Vec d) : u + Vec.zero d = u := by
  exact Vec.ext (fun i => Dy.add_zero _)

theorem vec_zero_add (u : Vec d) : Vec.zero d + u = u := by
  exact Vec.ext (fun i => Dy.zero_add _)

theorem vec_sub_zero (u : Vec d) : u - Vec.zero d = u := by
  exact Vec.ext (fun i => Semantics.sub_zero _)

theorem vec_zero_sub (u : Vec d) : Vec.zero d - u = -u := by
  apply Vec.ext
  intro i
  rw [Vec.sub_apply, Vec.zero_apply, Vec.neg_apply, Dy.sub_eq_add_neg, Dy.zero_add]

theorem vec_smul_neg (a : Dy d) (u : Vec d) : a • (-u) = -(a • u) := by
  apply Vec.ext
  intro i
  rw [Vec.smul_apply, Vec.neg_apply, Vec.neg_apply, Vec.smul_apply, Dy.mul_neg]

theorem vec_neg_smul_neg (a : Dy d) (u : Vec d) : -(a • (-u)) = a • u := by
  apply Vec.ext
  intro i
  rw [Vec.neg_apply, Vec.smul_apply, Vec.neg_apply, Dy.mul_neg, Dy.neg_neg,
    Vec.smul_apply]

theorem xMeasure_basis {level w q c i : Nat} (hl : 3 ≤ level) (hq : q < w)
    (rec : List Bool) (cr input : Nat) :
    runOps level w [.gate (.h q), .measure q c]
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk (false :: rec) (writeBit cr c false)
            (Dy.invSqrt2 (deg level) • basis (writeBit i q false)) input,
          Branch.mk (true :: rec) (writeBit cr c true)
            (if i.testBit q then
              -(Dy.invSqrt2 (deg level) • basis (writeBit i q true))
            else Dy.invSqrt2 (deg level) • basis (writeBit i q true)) input] := by
  rw [runOps_cons, runOp_gate, Semantics.apply_h hq hl, List.flatMap_singleton,
    runOps_singleton, runOp_measure]
  by_cases hb : i.testBit q = true
  · rw [if_pos hb]
    have hflip : (i ^^^ (1 <<< q)).testBit q = false := by
      rw [Semantics.testBit_xor_self, hb]
      rfl
    have hclear : writeBit i q false = i ^^^ (1 <<< q) := by
      apply Nat.eq_of_testBit_eq
      intro r
      by_cases hr : r = q
      · subst r
        rw [testBit_writeBit, hflip]
      · rw [testBit_writeBit_of_ne hr, Semantics.testBit_xor_of_ne hr]
    have hset : writeBit i q true = i := writeBit_self hb
    rw [projVec_smul, projVec_smul, projVec_sub, projVec_sub,
      projVec_basis_same hflip, projVec_basis_other (by simp [hb]),
      projVec_basis_other (by simp [hflip]), projVec_basis_same hb,
      hclear, hset, vec_sub_zero, vec_zero_sub, vec_smul_neg]
    simp [hb]
  · have hb' : i.testBit q = false := Bool.eq_false_iff.mpr hb
    rw [if_neg hb]
    have hflip : (i ^^^ (1 <<< q)).testBit q = true := by
      rw [Semantics.testBit_xor_self, hb']
      rfl
    have hclear : writeBit i q false = i := writeBit_self hb'
    have hset : writeBit i q true = i ^^^ (1 <<< q) := by
      apply Nat.eq_of_testBit_eq
      intro r
      by_cases hr : r = q
      · subst r
        rw [testBit_writeBit, hflip]
      · rw [testBit_writeBit_of_ne hr, Semantics.testBit_xor_of_ne hr]
    rw [projVec_smul, projVec_smul, projVec_add, projVec_add,
      projVec_basis_same hb', projVec_basis_other (by simp [hflip]),
      projVec_basis_other (by simp [hb']), projVec_basis_same hflip,
      hclear, hset, vec_add_zero, vec_zero_add]
    simp [hb]

theorem address_writeBit_output {m i bit : Nat} (_hbit : bit < m) (b : Bool) :
    address (writeBit i (outputOffset + bit) b) = address i := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [address, testBit_readField, address, testBit_readField]
  by_cases hq : q < addressWidth
  · simp only [hq, decide_true, Bool.true_and, Nat.zero_add]
    have hne : q ≠ outputOffset + bit := by
      simp [outputOffset, addressWidth] at hq ⊢
      omega
    rw [testBit_writeBit_of_ne hne]
  · simp [hq]

theorem workspaceClear_writeBit_output {m i bit : Nat} (hbit : bit < m)
    (hclear : workspaceClear m i) (b : Bool) :
    workspaceClear m (writeBit i (outputOffset + bit) b) := by
  constructor
  · rw [testBit_writeBit_of_ne (by simp [workWire, outputOffset]; omega)]
    exact hclear.1
  · rw [testBit_writeBit_of_ne (by simp [flagWire, outputOffset]; omega)]
    exact hclear.2

theorem phaseForBit_x_run {level : Nat} (hl : 3 ≤ level) {table : List Nat}
    {m bit i : Nat} (hbit : bit < m) (hclear : workspaceClear m i)
    (hset : i.testBit (outputOffset + bit) = true)
    (rec : List Bool) (cr input : Nat) :
    runOps level (width m) (phaseForBit table m bit ++ [.gate (.x (outputOffset + bit))])
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if (value table m (address i)).testBit bit
            then -(basis (writeBit i (outputOffset + bit) false) : Vec (deg level))
            else basis (writeBit i (outputOffset + bit) false)) input] := by
  rw [runOps_append, phaseForBit_run hl hclear, List.flatMap_singleton,
    runOps_singleton, runOp_gate]
  have hq : outputOffset + bit < width m := by
    simp [width, outputOffset]
    omega
  have hout : i ^^^ (1 <<< (outputOffset + bit)) =
      writeBit i (outputOffset + bit) false := by
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases heq : q = outputOffset + bit
    · subst q
      rw [Semantics.testBit_xor_self, hset, testBit_writeBit]
      rfl
    · rw [Semantics.testBit_xor_of_ne heq, testBit_writeBit_of_ne heq]
  split
  · have hneg : -(basis i : Vec (deg level)) =
        (-Dy.one (deg level)) • basis i := by
      apply Vec.ext
      intro q
      exact neg_eq_neg_one_mul _
    have hnegOut : -(basis (writeBit i (outputOffset + bit) false) : Vec (deg level)) =
        (-Dy.one (deg level)) • basis (writeBit i (outputOffset + bit) false) := by
      apply Vec.ext
      intro q
      exact neg_eq_neg_one_mul _
    rw [hneg, gateVec_smul, Semantics.apply_x hq, hout, ← hnegOut]
  · rw [Semantics.apply_x hq, hout]

theorem unlookupBit_run {level : Nat} (hl : 3 ≤ level) {table : List Nat}
    {m bit i : Nat} (hbit : bit < m) (hclear : workspaceClear m i)
    (hdata : i.testBit (outputOffset + bit) =
      (value table m (address i)).testBit bit)
    (rec : List Bool) (cr input : Nat) :
    runOps level (width m) (unlookupBit table m bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk (false :: rec) (writeBit cr 0 false)
            (Dy.invSqrt2 (deg level) •
              basis (writeBit i (outputOffset + bit) false)) input,
          Branch.mk (true :: rec) (writeBit cr 0 true)
            (Dy.invSqrt2 (deg level) •
              basis (writeBit i (outputOffset + bit) false)) input] := by
  let q := outputOffset + bit
  have hq : q < width m := by
    simp [q, width, outputOffset]
    omega
  have haddrSet : address (writeBit i q true) = address i :=
    address_writeBit_output hbit true
  have hworkSet : workspaceClear m (writeBit i q true) :=
    workspaceClear_writeBit_output hbit hclear true
  have hset : (writeBit i q true).testBit q = true := testBit_writeBit _ _ _
  have hclearTwice : writeBit (writeBit i q true) q false = writeBit i q false :=
    writeBit_writeBit i q true false
  change runOps level (width m)
    ([.gate (.h q), .measure q 0] ++
      [.branch (.localBit 0)
        (phaseForBit table m bit ++ [.gate (.x q)]) []])
      (Branch.mk rec cr (basis i) input) = _
  rw [runOps_append, xMeasure_basis hl hq, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    if_neg (by simp), runOps_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit, if_pos rfl]
  have hphase := phaseForBit_x_run hl (table := table) hbit hworkSet hset
    (true :: rec) (writeBit cr 0 true) input
  rw [haddrSet] at hphase
  have hscaled :
      runOps level (width m) (phaseForBit table m bit ++ [.gate (.x q)])
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (Dy.invSqrt2 (deg level) • basis (writeBit i q true)) input) =
        (runOps level (width m) (phaseForBit table m bit ++ [.gate (.x q)])
          (Branch.mk (true :: rec) (writeBit cr 0 true)
            (basis (writeBit i q true)) input)).map
          (smulBranch (Dy.invSqrt2 (deg level))) := by
    change runOps level (width m) (phaseForBit table m bit ++ [.gate (.x q)])
      (smulBranch (Dy.invSqrt2 (deg level))
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (basis (writeBit i q true)) input)) = _
    exact (runOps_smul level (width m)).2 _ _ _
  by_cases ht : (value table m (address i)).testBit bit = true
  · have hiq : i.testBit q = true := by simpa [ht] using hdata
    rw [if_pos hiq, runOps_neg, hscaled]
    rw [hphase, if_pos ht, hclearTwice]
    simp [q, smulBranch, vec_neg_smul_neg]
  · have hiq : i.testBit q = false := by
      rw [hdata]
      exact Bool.eq_false_iff.mpr ht
    rw [if_neg (by simpa using hiq), hscaled]
    rw [hphase, if_neg ht, hclearTwice]
    simp [q, smulBranch]

def bitReady (table : List Nat) (m bit i : Nat) : Prop :=
  workspaceClear m i ∧
    i.testBit (outputOffset + bit) = (value table m (address i)).testBit bit

def clearOutputBit (bit i : Nat) : Nat :=
  writeBit i (outputOffset + bit) false

theorem unlookupBit_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) {m bit : Nat} (hbit : bit < m) :
    ImplementsU level (width m) input (bitReady table m bit) (clearOutputBit bit)
      (Dy.invSqrt2 (deg level)) (unlookupBit table m bit) := by
  intro i _ hready rec cr b hb
  rw [unlookupBit_run hl hbit hready.1 hready.2 rec cr input] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;>
    simp [clearOutputBit, Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]

def rangeReady (table : List Nat) (m start count i : Nat) : Prop :=
  workspaceClear m i ∧ ∀ bit, start ≤ bit → bit < start + count →
    i.testBit (outputOffset + bit) = (value table m (address i)).testBit bit

def clearBits : Nat → Nat → Nat → Nat
  | _, 0, i => i
  | start, count + 1, i => clearBits (start + 1) count (clearOutputBit start i)

theorem writeBit_lt {i q w : Nat} {b : Bool} (hq : q < w) (hi : i < 2 ^ w) :
    writeBit i q b < 2 ^ w := by
  apply lt_two_pow_of_testBit
  intro r hr
  rw [testBit_writeBit_of_ne (show r ≠ q by omega)]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hr))

theorem rangeReady_bit {table : List Nat} {m start count i : Nat}
    (hcount : 0 < count) (h : rangeReady table m start count i) :
    bitReady table m start i :=
  ⟨h.1, h.2 start (Nat.le_refl _) (by omega)⟩

theorem rangeReady_tail {table : List Nat} {m start count i : Nat}
    (hstart : start < m) (h : rangeReady table m start (count + 1) i) :
    rangeReady table m (start + 1) count (clearOutputBit start i) := by
  constructor
  · exact workspaceClear_writeBit_output hstart h.1 false
  · intro bit hlo hhi
    rw [clearOutputBit,
      testBit_writeBit_of_ne (show outputOffset + bit ≠ outputOffset + start by omega),
      address_writeBit_output hstart]
    exact h.2 bit (by omega) (by omega)

theorem unlookupAux_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) {m : Nat} : ∀ start count, start + count ≤ m →
    ImplementsU level (width m) input (rangeReady table m start count)
      (clearBits start count) (Dy.invSqrt2 (deg level))
      (unlookupAux table m start count) := by
  intro start count
  induction count generalizing start with
  | zero =>
    intro _ i _ _ rec cr b hb
    rw [unlookupAux, runOps_nil, List.mem_singleton] at hb
    subst b
    simp only [clearBits, Nat.sub_self, Dy.pow_zero_eq]
    rw [Vec.one_smul]
  | succ count ih =>
    intro hbound
    have hstart : start < m := by omega
    have hfirst := (unlookupBit_implements (input := input) hl table hstart).mono
      (dom' := rangeReady table m start (count + 1))
      (fun _ h => rangeReady_bit (by omega) h)
    have htail := ih (start + 1) (by omega)
    have h := hfirst.append htail
      (fun i hi _ => writeBit_lt (by simp [width, outputOffset]; omega) hi)
      (fun _ _ hready => rangeReady_tail hstart hready)
    simpa [unlookupAux, clearBits, clearOutputBit, Function.comp_def] using h

theorem unlookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) :
    ImplementsU level (width m) input (rangeReady table m 0 m)
      (clearBits 0 m) (Dy.invSqrt2 (deg level)) (unlookupOps table m) := by
  exact unlookupAux_implements hl table 0 m (by omega)

theorem testBit_clearBits (start count i q : Nat) :
    (clearBits start count i).testBit q =
      if outputOffset + start ≤ q ∧ q < outputOffset + start + count
        then false else i.testBit q := by
  induction count generalizing start i with
  | zero =>
    rw [clearBits, if_neg]
    omega
  | succ count ih =>
    rw [clearBits, ih]
    by_cases htail : outputOffset + (start + 1) ≤ q ∧
        q < outputOffset + (start + 1) + count
    · rw [if_pos htail, if_pos (by omega)]
    · rw [if_neg htail]
      by_cases heq : q = outputOffset + start
      · subst q
        rw [if_pos (by omega), clearOutputBit, testBit_writeBit]
      · rw [clearOutputBit, testBit_writeBit_of_ne heq]
        by_cases hall : outputOffset + start ≤ q ∧
            q < outputOffset + start + (count + 1)
        · rw [if_pos hall]
          exfalso
          apply htail
          constructor <;> omega
        · rw [if_neg hall]

theorem clearBits_zero (m i : Nat) :
    clearBits 0 m i = writeField i outputOffset m 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_clearBits]
  by_cases hin : outputOffset ≤ q ∧ q < outputOffset + m
  · rw [if_pos (by simpa using hin), testBit_writeField_inside hin.1 hin.2,
      Nat.zero_testBit]
  · rw [if_neg (by simpa using hin), testBit_writeField_outside]
    by_cases hlo : q < outputOffset
    · exact Or.inl hlo
    · exact Or.inr (by omega)

theorem rangeReady_of_output {table : List Nat} {m i : Nat}
    (hclear : workspaceClear m i) (hout : output m i = value table m (address i)) :
    rangeReady table m 0 m i := by
  constructor
  · exact hclear
  · intro bit _ hbit
    have h := congrArg (fun x : Nat => x.testBit bit) hout
    have hbit' : bit < m := by omega
    have hdec : decide (bit < m) = true := by simp [hbit']
    rw [output, testBit_readField, hdec, Bool.true_and] at h
    exact h

theorem lookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) (weight : Dy (deg level)) :
    ImplementsU level (width m) input (workspaceClear m) (xorOutput table m) weight
      (gateOps (lookupGates table m)) := by
  have h := implementsU_gates (level := level) (w := width m) (input := input)
    (r := lookupCircuit table m) hl rfl (lookup_wellFormed table m) weight
  intro i hi hclear rec cr b hb
  have hbasis := h i hi trivial rec cr b hb
  rw [lookup_act hclear] at hbasis
  exact hbasis

theorem xorOutput_lt {table : List Nat} {m i : Nat} (hi : i < 2 ^ width m) :
    xorOutput table m i < 2 ^ width m := by
  exact writeField_lt (by simp [width, outputOffset]) hi

theorem xorOutput_ready {table : List Nat} {m i : Nat}
    (hclear : workspaceClear m i) (hout : output m i = 0) :
    rangeReady table m 0 m (xorOutput table m i) := by
  apply rangeReady_of_output
  · exact workspaceClear_write_output hclear
  · unfold output xorOutput
    rw [readField_writeField_self
        (Nat.xor_lt_two_pow (output_lt m i) (value_lt table m (address i))),
      hout, Nat.zero_xor, address_write_output]

theorem roundTrip_out {table : List Nat} {m i : Nat} (hout : output m i = 0) :
    clearBits 0 m (xorOutput table m i) = i := by
  rw [clearBits_zero, xorOutput, writeField_writeField]
  rw [← hout]
  exact writeField_read i outputOffset m

theorem roundTrip_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) :
    ImplementsU level (width m) input
      (fun i => workspaceClear m i ∧ output m i = 0) id
      (Dy.invSqrt2 (deg level)) (roundTripProgram table m).ops := by
  have hlookup := (lookup_implements (input := input) hl table m
    (Dy.invSqrt2 (deg level))).mono
    (dom' := fun i => workspaceClear m i ∧ output m i = 0) (fun _ h => h.1)
  have hunlookup := unlookup_implements (input := input) hl table m
  have h := hlookup.append hunlookup
    (fun i hi _ => xorOutput_lt hi)
    (fun _ _ hpre => xorOutput_ready hpre.1 hpre.2)
  intro i hi hpre rec cr b hb
  change b ∈ runOps level (width m)
    (gateOps (lookupGates table m) ++ unlookupOps table m)
    (Branch.mk rec cr (basis i) input) at hb
  have hstate := h i hi hpre rec cr b hb
  rw [hstate]
  change Dy.invSqrt2 (deg level) ^ (b.outcomes.length - rec.length) •
      basis (clearBits 0 m (xorOutput table m i)) =
    Dy.invSqrt2 (deg level) ^ (b.outcomes.length - rec.length) • basis i
  rw [roundTrip_out hpre.2]

theorem opsWellFormed_gateMap (level w iw cw : Nat) (gs : List Gate) :
    Program.opsWellFormed level w iw cw (gs.map Op.gate) =
      gs.all (Gate.wellFormedAt level w) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Program.opsWellFormed, Program.opWellFormed, ih]

theorem gateOps_wellFormed {level w iw cw : Nat} (hl : 3 ≤ level)
    {gs : List RGate} (hwf : gs.all (RGate.wellFormed w) = true) :
    Program.opsWellFormed level w iw cw (gateOps gs) = true := by
  rw [gateOps, opsWellFormed_gateMap]
  change (compile ({ width := w, gates := gs } : RCircuit)).wellFormedAt level = true
  exact wellFormedAt_compile (RCircuit.wellFormedAt_of_wellFormed hl hwf)

theorem phaseRowOps_wellFormed {level : Nat} (hl : 3 ≤ level) (m row : Nat) :
    Program.opsWellFormed level (width m) 0 1 (phaseRowOps m row) = true := by
  have hcompute := gateOps_wellFormed (iw := 0) (cw := 1) hl
    (compute_wellFormed m row)
  have hreverse := gateOps_wellFormed (iw := 0) (cw := 1) hl
    (show (compute m row).reverse.all (RGate.wellFormed (width m)) = true by
      simpa using compute_wellFormed m row)
  rw [phaseRowOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
    hcompute, hreverse]
  simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt,
    flagWire, width]
  omega

theorem phaseRows_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.opsWellFormed level (width m) 0 1
      (phaseRows table m bit start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.opsWellFormed_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRowOps_wellFormed hl, ih]
      rfl
    · rw [if_neg hb, ih]
      rfl

theorem phaseForBit_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m bit : Nat) :
    Program.opsWellFormed level (width m) 0 1
      (phaseForBit table m bit) = true :=
  phaseRows_wellFormed hl table m bit 0 (2 ^ addressWidth)

theorem unlookupBit_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) {m bit : Nat} (hbit : bit < m) :
    Program.opsWellFormed level (width m) 0 1
      (unlookupBit table m bit) = true := by
  have hp := phaseForBit_wellFormed hl table m bit
  have hq : outputOffset + bit < width m := by
    simp [outputOffset, width]
    omega
  simp only [unlookupBit, Program.opsWellFormed, Program.opWellFormed,
    Program.opsWellFormed_append]
  rw [hp]
  simp [CRef.wellFormed, Gate.wellFormedAt, hq, hl]

theorem unlookupAux_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) {m : Nat} : ∀ start count, start + count ≤ m →
    Program.opsWellFormed level (width m) 0 1
      (unlookupAux table m start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => intro _; rfl
  | succ count ih =>
    intro hbound
    rw [unlookupAux, Program.opsWellFormed_append,
      unlookupBit_wellFormed hl table (show start < m by omega),
      ih (start + 1) (by omega)]
    rfl

theorem unlookupProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) :
    (unlookupProgram table m).wellFormed level = true := by
  unfold unlookupProgram Program.wellFormed unlookupOps
  by_cases hm : m = 0
  · subst m
    rfl
  · simpa [hm] using unlookupAux_wellFormed hl table 0 m (by omega)

theorem roundTripProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) :
    (roundTripProgram table m).wellFormed level = true := by
  unfold roundTripProgram Program.wellFormed unlookupOps
  change Program.opsWellFormed level (width m) 0 (if m = 0 then 0 else 1)
    (gateOps (lookupGates table m) ++ unlookupAux table m 0 m) = true
  rw [Program.opsWellFormed_append]
  have hlookup : Program.opsWellFormed level (width m) 0
      (if m = 0 then 0 else 1) (gateOps (lookupGates table m)) = true :=
    gateOps_wellFormed (iw := 0) (cw := if m = 0 then 0 else 1) hl
      (lookup_wellFormed table m)
  rw [hlookup]
  simp only [Bool.true_and]
  by_cases hm : m = 0
  · subst m
    rfl
  · rw [if_neg hm]
    exact unlookupAux_wellFormed hl table 0 m (by omega)

def lookupSpec (_table : List Nat) (m : Nat) : RegSpec where
  width := width m
  Pre i := workspaceClear m i ∧ output m i = 0
  Post i j := j = i

theorem roundTrip_realises {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) :
    RealisesAt level 0 (lookupSpec table m) (roundTripProgram table m) := by
  have hwf := roundTripProgram_wellFormed hl table m
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := id) (c := Dy.invSqrt2 (deg level))
    (roundTrip_implements (input := 0) hl table m) ?_ ?_
  · intro i hi _
    exact ⟨rfl, hi⟩
  · intro i hi _
    exact totalProb_basis level (roundTripProgram table m) hwf 0 hi

theorem gateOps_append (a b : List RGate) :
    gateOps (a ++ b) = gateOps a ++ gateOps b := by
  simp [gateOps, List.flatMap_append]

theorem weighOps_gateMap_countP (p : Gate → Bool) (gs : List Gate) :
    Program.weighOps (fun g => if p g then 1 else 0) (gs.map Op.gate) =
      Range.point (gs.countP p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Program.weighOps, Program.weighOp,
      List.countP_cons, ih]
    cases p g <;> simp [Range.add, Range.point] <;> omega

theorem weighOps_gateMap_one (gs : List Gate) :
    Program.weighOps (fun _ => 1) (gs.map Op.gate) =
      Range.point gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Program.weighOps, Program.weighOp, ih, Range.add, Range.point]
    omega

theorem toffoli_gateOps (gs : List RGate) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0) (gateOps gs) =
      Range.point (gs.countP RGate.isCcx) := by
  rw [gateOps, weighOps_gateMap_countP]
  change Range.point
    (Circuit.toffoliCount (compile ({ width := 0, gates := gs } : RCircuit))) = _
  rw [toffoliCount_compile]

theorem gates_gateOps (gs : List RGate) :
    Program.weighOps (fun _ => 1) (gateOps gs) =
      Range.point (gs.length + 2 * gs.countP RGate.isCcx) := by
  rw [gateOps, weighOps_gateMap_one]
  change Range.point
    (Circuit.gateCount (compile ({ width := 0, gates := gs } : RCircuit))) = _
  rw [gateCount_compile]

theorem lookup_toffoli_exact (table : List Nat) (m : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (gateOps (lookupGates table m)) = Range.point 32 := by
  rw [toffoli_gateOps, lookupGates_ccx]

theorem lookup_gates_hi_le (table : List Nat) (m : Nat) :
    (Program.weighOps (fun _ => 1) (gateOps (lookupGates table m))).hi ≤
      144 + 8 * m := by
  rw [gates_gateOps, lookupGates_ccx]
  simp only [Range.point]
  have h := lookupGates_length_le table m
  omega

def measurementCost : Op → Nat
  | .measure _ _ => 1
  | _ => 0

def resetCost : Op → Nat
  | .reset _ => 1
  | _ => 0

theorem measure_gateMap (gs : List Gate) :
    Program.tallyOps measurementCost (gs.map Op.gate) = Range.point 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Program.tallyOps, Program.tallyOp, measurementCost, ih,
      Range.add, Range.point]

theorem reset_gateMap (gs : List Gate) :
    Program.tallyOps resetCost (gs.map Op.gate) = Range.point 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Program.tallyOps, Program.tallyOp, resetCost, ih,
      Range.add, Range.point]

theorem classical_gateMap (gs : List Gate) :
    Program.classicalOpCountOps (gs.map Op.gate) = Range.point 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Program.classicalOpCountOps, Program.classicalOpCountOp, ih,
      Range.add, Range.point]

theorem depth_gateMap_all (gs : List Gate) :
    Program.depthCostOps (fun _ => true) true (gs.map Op.gate) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Program.depthCostOps, Program.depthCostOp, ih,
      List.length_cons]
    simp [Nat.add_comm]

theorem depth_gateMap_none (gs : List Gate) :
    Program.depthCostOps (fun _ => false) true (gs.map Op.gate) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [Program.depthCostOps, Program.depthCostOp, ih]

theorem depth_gateMap_toffoli (gs : List Gate) :
    Program.depthCostOps Gate.isCcz false (gs.map Op.gate) =
      gs.countP Gate.isCcz := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, Program.depthCostOps, Program.depthCostOp,
      List.countP_cons, ih]
    cases h : g.isCcz <;> simp <;> omega

theorem measure_gateOps (gs : List RGate) :
    Program.tallyOps measurementCost (gateOps gs) = Range.point 0 := by
  exact measure_gateMap _

theorem reset_gateOps (gs : List RGate) :
    Program.tallyOps resetCost (gateOps gs) = Range.point 0 := by
  exact reset_gateMap _

theorem classical_gateOps (gs : List RGate) :
    Program.classicalOpCountOps (gateOps gs) = Range.point 0 := by
  exact classical_gateMap _

theorem depth_gateOps_all (gs : List RGate) :
    Program.depthCostOps (fun _ => true) true (gateOps gs) =
      gs.length + 2 * gs.countP RGate.isCcx := by
  rw [gateOps, depth_gateMap_all]
  change Circuit.gateCount (compile ({ width := 0, gates := gs } : RCircuit)) = _
  rw [gateCount_compile]

theorem depth_gateOps_none (gs : List RGate) :
    Program.depthCostOps (fun _ => false) true (gateOps gs) = 0 := by
  exact depth_gateMap_none _

theorem depth_gateOps_toffoli (gs : List RGate) :
    Program.depthCostOps Gate.isCcz false (gateOps gs) =
      gs.countP RGate.isCcx := by
  rw [gateOps, depth_gateMap_toffoli]
  change Circuit.toffoliCount (compile ({ width := 0, gates := gs } : RCircuit)) = _
  rw [toffoliCount_compile]

theorem toffoli_single_z (q : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0) [.gate (.z q)] =
      Range.point 0 := by
  rfl

theorem depth_single_z_all (q : Nat) :
    Program.depthCostOps (fun _ => true) true [.gate (.z q)] = 1 := by
  rfl

theorem depth_single_z_toffoli (q : Nat) :
    Program.depthCostOps Gate.isCcz false [.gate (.z q)] = 0 := by
  rfl

theorem phaseRow_toffoli_exact (m row : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0) (phaseRowOps m row) =
      Range.point 4 := by
  rw [phaseRowOps, Program.weighOps_append, Program.weighOps_append,
    toffoli_gateOps, toffoli_single_z, toffoli_gateOps]
  simp [compute_ccx, Range.add, Range.point]

theorem phaseRow_gates_hi_le (m row : Nat) :
    (Program.weighOps (fun _ => 1) (phaseRowOps m row)).hi ≤ 19 := by
  rw [phaseRowOps, Program.weighOps_append, Program.weighOps_append,
    gates_gateOps, gates_gateOps]
  simp only [List.countP_reverse, List.length_reverse, compute_ccx,
    Program.weighOps, Program.weighOp, Range.add, Range.point]
  have h := compute_length_le m row
  omega

theorem phaseRow_measure_exact (m row : Nat) :
    Program.tallyOps measurementCost (phaseRowOps m row) = Range.point 0 := by
  rw [phaseRowOps, Program.tallyOps_append, Program.tallyOps_append,
    measure_gateOps, measure_gateOps]
  rfl

theorem phaseRow_reset_exact (m row : Nat) :
    Program.tallyOps resetCost (phaseRowOps m row) = Range.point 0 := by
  rw [phaseRowOps, Program.tallyOps_append, Program.tallyOps_append,
    reset_gateOps, reset_gateOps]
  rfl

theorem phaseRow_classical_exact (m row : Nat) :
    Program.classicalOpCountOps (phaseRowOps m row) = Range.point 0 := by
  rw [phaseRowOps, Program.classicalOpCountOps_append,
    Program.classicalOpCountOps_append, classical_gateOps, classical_gateOps]
  rfl

theorem phaseRow_depth_all_le (m row : Nat) :
    Program.depthCostOps (fun _ => true) true (phaseRowOps m row) ≤ 19 := by
  rw [phaseRowOps, Program.depthCostOps_append, Program.depthCostOps_append,
    depth_gateOps_all, depth_single_z_all, depth_gateOps_all]
  simp only [List.length_reverse, List.countP_reverse, compute_ccx]
  have h := compute_length_le m row
  omega

theorem phaseRow_depth_none (m row : Nat) :
    Program.depthCostOps (fun _ => false) true (phaseRowOps m row) = 0 := by
  rw [phaseRowOps, Program.depthCostOps_append, Program.depthCostOps_append,
    depth_gateOps_none, depth_gateOps_none]
  rfl

theorem phaseRow_depth_toffoli (m row : Nat) :
    Program.depthCostOps Gate.isCcz false (phaseRowOps m row) = 4 := by
  rw [phaseRowOps, Program.depthCostOps_append, Program.depthCostOps_append,
    depth_gateOps_toffoli, depth_single_z_toffoli, depth_gateOps_toffoli]
  simp [compute_ccx]

theorem phaseRows_toffoli_hi_le (table : List Nat) (m bit : Nat) : ∀ start count,
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (phaseRows table m bit start count)).hi ≤ 4 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [phaseRows, Program.weighOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_toffoli_exact]
      have ht := ih (start + 1)
      simp only [Range.add, Range.point]
      omega
    · rw [if_neg hb]
      have ht := ih (start + 1)
      simp only [Program.weighOps, Range.add, Range.point]
      omega

theorem phaseRows_gates_hi_le (table : List Nat) (m bit : Nat) : ∀ start count,
    (Program.weighOps (fun _ => 1)
      (phaseRows table m bit start count)).hi ≤ 19 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [phaseRows, Program.weighOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb]
      have hr := phaseRow_gates_hi_le m start
      have ht := ih (start + 1)
      simp only [Range.add]
      omega
    · rw [if_neg hb]
      have ht := ih (start + 1)
      simp only [Program.weighOps, Range.add, Range.point]
      omega

theorem phaseRows_measure_exact (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.tallyOps measurementCost (phaseRows table m bit start count) =
      Range.point 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.tallyOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_measure_exact, ih]
      rfl
    · rw [if_neg hb, ih]
      rfl

theorem phaseRows_reset_exact (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.tallyOps resetCost (phaseRows table m bit start count) =
      Range.point 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.tallyOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_reset_exact, ih]
      rfl
    · rw [if_neg hb, ih]
      rfl

theorem phaseRows_classical_exact (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.classicalOpCountOps (phaseRows table m bit start count) =
      Range.point 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.classicalOpCountOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_classical_exact, ih]
      rfl
    · rw [if_neg hb, ih]
      rfl

theorem phaseRows_depth_all_le (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.depthCostOps (fun _ => true) true (phaseRows table m bit start count) ≤
      19 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [phaseRows, Program.depthCostOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb]
      have hr := phaseRow_depth_all_le m start
      have ht := ih (start + 1)
      omega
    · rw [if_neg hb]
      have ht := ih (start + 1)
      simp only [Program.depthCostOps, Nat.zero_add]
      omega

theorem phaseRows_depth_none (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.depthCostOps (fun _ => false) true (phaseRows table m bit start count) = 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.depthCostOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_depth_none, ih]
    · rw [if_neg hb, ih]
      rfl

theorem phaseRows_depth_toffoli_le (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.depthCostOps Gate.isCcz false (phaseRows table m bit start count) ≤
      4 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [phaseRows, Program.depthCostOps_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRow_depth_toffoli]
      have ht := ih (start + 1)
      omega
    · rw [if_neg hb]
      have ht := ih (start + 1)
      simp only [Program.depthCostOps, Nat.zero_add]
      omega

theorem phaseForBit_toffoli_hi_le (table : List Nat) (m bit : Nat) :
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (phaseForBit table m bit)).hi ≤ 32 := by
  exact phaseRows_toffoli_hi_le table m bit 0 8

theorem phaseForBit_gates_hi_le (table : List Nat) (m bit : Nat) :
    (Program.weighOps (fun _ => 1) (phaseForBit table m bit)).hi ≤ 152 := by
  exact phaseRows_gates_hi_le table m bit 0 8

theorem phaseForBit_measure_exact (table : List Nat) (m bit : Nat) :
    Program.tallyOps measurementCost (phaseForBit table m bit) = Range.point 0 :=
  phaseRows_measure_exact table m bit 0 8

theorem phaseForBit_reset_exact (table : List Nat) (m bit : Nat) :
    Program.tallyOps resetCost (phaseForBit table m bit) = Range.point 0 :=
  phaseRows_reset_exact table m bit 0 8

theorem phaseForBit_classical_exact (table : List Nat) (m bit : Nat) :
    Program.classicalOpCountOps (phaseForBit table m bit) = Range.point 0 :=
  phaseRows_classical_exact table m bit 0 8

theorem phaseForBit_depth_all_le (table : List Nat) (m bit : Nat) :
    Program.depthCostOps (fun _ => true) true (phaseForBit table m bit) ≤ 152 :=
  phaseRows_depth_all_le table m bit 0 8

theorem phaseForBit_depth_none (table : List Nat) (m bit : Nat) :
    Program.depthCostOps (fun _ => false) true (phaseForBit table m bit) = 0 :=
  phaseRows_depth_none table m bit 0 8

theorem phaseForBit_depth_toffoli_le (table : List Nat) (m bit : Nat) :
    Program.depthCostOps Gate.isCcz false (phaseForBit table m bit) ≤ 32 :=
  phaseRows_depth_toffoli_le table m bit 0 8

theorem unlookupBit_toffoli_hi_le (table : List Nat) (m bit : Nat) :
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (unlookupBit table m bit)).hi ≤ 32 := by
  simp only [unlookupBit, Program.weighOps, Program.weighOp,
    Program.weighOps_append, Range.add, Range.choice, Range.point]
  rw [show (Gate.h (outputOffset + bit)).isCcz = false by rfl,
    show (Gate.x (outputOffset + bit)).isCcz = false by rfl]
  simp only [Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero, Nat.max_zero]
  have h := phaseForBit_toffoli_hi_le table m bit
  omega

theorem unlookupBit_gates_hi_le (table : List Nat) (m bit : Nat) :
    (Program.weighOps (fun _ => 1) (unlookupBit table m bit)).hi ≤ 154 := by
  simp only [unlookupBit, Program.weighOps, Program.weighOp,
    Program.weighOps_append, Range.add, Range.choice, Range.point]
  have h := phaseForBit_gates_hi_le table m bit
  omega

theorem unlookupBit_measure_exact (table : List Nat) (m bit : Nat) :
    Program.tallyOps measurementCost (unlookupBit table m bit) = Range.point 1 := by
  simp only [unlookupBit, Program.tallyOps, Program.tallyOp,
    Program.tallyOps_append, phaseForBit_measure_exact, measurementCost,
    Range.add, Range.choice, Range.point]
  rfl

theorem unlookupBit_reset_exact (table : List Nat) (m bit : Nat) :
    Program.tallyOps resetCost (unlookupBit table m bit) = Range.point 0 := by
  simp only [unlookupBit, Program.tallyOps, Program.tallyOp,
    Program.tallyOps_append, phaseForBit_reset_exact, resetCost,
    Range.add, Range.choice, Range.point]
  rfl

theorem unlookupBit_classical_exact (table : List Nat) (m bit : Nat) :
    Program.classicalOpCountOps (unlookupBit table m bit) = Range.point 2 := by
  simp only [unlookupBit, Program.classicalOpCountOps,
    Program.classicalOpCountOp, Program.classicalOpCountOps_append,
    phaseForBit_classical_exact, Range.add, Range.choice, Range.point]
  rfl

theorem unlookupBit_depth_all_le (table : List Nat) (m bit : Nat) :
    Program.depthCostOps (fun _ => true) true (unlookupBit table m bit) ≤ 155 := by
  simp only [unlookupBit, Program.depthCostOps, Program.depthCostOp,
    Program.depthCostOps_append]
  simp only [if_true, Nat.add_zero, Nat.max_zero]
  have h := phaseForBit_depth_all_le table m bit
  omega

theorem unlookupBit_depth_none (table : List Nat) (m bit : Nat) :
    Program.depthCostOps (fun _ => false) true (unlookupBit table m bit) = 1 := by
  simp only [unlookupBit, Program.depthCostOps, Program.depthCostOp,
    Program.depthCostOps_append, phaseForBit_depth_none]
  rfl

theorem unlookupBit_depth_toffoli_le (table : List Nat) (m bit : Nat) :
    Program.depthCostOps Gate.isCcz false (unlookupBit table m bit) ≤ 32 := by
  simp only [unlookupBit, Program.depthCostOps, Program.depthCostOp,
    Program.depthCostOps_append]
  simp only [Gate.isCcz, Bool.false_eq_true, if_false, Nat.zero_add,
    Nat.add_zero, Nat.max_zero]
  have h := phaseForBit_depth_toffoli_le table m bit
  omega

theorem unlookupAux_toffoli_hi_le (table : List Nat) (m : Nat) : ∀ start count,
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (unlookupAux table m start count)).hi ≤ 32 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [unlookupAux, Program.weighOps_append]
    have hb := unlookupBit_toffoli_hi_le table m start
    have ht := ih (start + 1)
    simp only [Range.add]
    omega

theorem unlookupAux_gates_hi_le (table : List Nat) (m : Nat) : ∀ start count,
    (Program.weighOps (fun _ => 1) (unlookupAux table m start count)).hi ≤
      154 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [unlookupAux, Program.weighOps_append]
    have hb := unlookupBit_gates_hi_le table m start
    have ht := ih (start + 1)
    simp only [Range.add]
    omega

theorem unlookupAux_measure_exact (table : List Nat) (m : Nat) : ∀ start count,
    Program.tallyOps measurementCost (unlookupAux table m start count) =
      Range.point count := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [unlookupAux, Program.tallyOps_append, unlookupBit_measure_exact, ih]
    simp [Range.add, Range.point, Nat.add_comm]

theorem unlookupAux_reset_exact (table : List Nat) (m : Nat) : ∀ start count,
    Program.tallyOps resetCost (unlookupAux table m start count) = Range.point 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [unlookupAux, Program.tallyOps_append, unlookupBit_reset_exact, ih]
    rfl

theorem unlookupAux_classical_exact (table : List Nat) (m : Nat) : ∀ start count,
    Program.classicalOpCountOps (unlookupAux table m start count) =
      Range.point (2 * count) := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [unlookupAux, Program.classicalOpCountOps_append,
      unlookupBit_classical_exact, ih]
    simp [Range.add, Range.point]
    omega

theorem unlookupAux_depth_all_le (table : List Nat) (m : Nat) : ∀ start count,
    Program.depthCostOps (fun _ => true) true (unlookupAux table m start count) ≤
      155 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [unlookupAux, Program.depthCostOps_append]
    have hb := unlookupBit_depth_all_le table m start
    have ht := ih (start + 1)
    omega

theorem unlookupAux_depth_none (table : List Nat) (m : Nat) : ∀ start count,
    Program.depthCostOps (fun _ => false) true (unlookupAux table m start count) =
      count := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [unlookupAux, Program.depthCostOps_append, unlookupBit_depth_none, ih]
    omega

theorem unlookupAux_depth_toffoli_le (table : List Nat) (m : Nat) : ∀ start count,
    Program.depthCostOps Gate.isCcz false (unlookupAux table m start count) ≤
      32 * count := by
  intro start count
  induction count generalizing start with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    rw [unlookupAux, Program.depthCostOps_append]
    have hb := unlookupBit_depth_toffoli_le table m start
    have ht := ih (start + 1)
    omega

theorem unlookup_toffoli_hi_le (table : List Nat) (m : Nat) :
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (unlookupOps table m)).hi ≤ 32 * m :=
  unlookupAux_toffoli_hi_le table m 0 m

theorem unlookup_gates_hi_le (table : List Nat) (m : Nat) :
    (Program.weighOps (fun _ => 1) (unlookupOps table m)).hi ≤ 154 * m :=
  unlookupAux_gates_hi_le table m 0 m

theorem unlookup_measure_exact (table : List Nat) (m : Nat) :
    Program.tallyOps measurementCost (unlookupOps table m) = Range.point m :=
  unlookupAux_measure_exact table m 0 m

theorem unlookup_reset_exact (table : List Nat) (m : Nat) :
    Program.tallyOps resetCost (unlookupOps table m) = Range.point 0 :=
  unlookupAux_reset_exact table m 0 m

theorem unlookup_classical_exact (table : List Nat) (m : Nat) :
    Program.classicalOpCountOps (unlookupOps table m) = Range.point (2 * m) :=
  unlookupAux_classical_exact table m 0 m

theorem unlookup_depth_all_le (table : List Nat) (m : Nat) :
    Program.depthCostOps (fun _ => true) true (unlookupOps table m) ≤ 155 * m :=
  unlookupAux_depth_all_le table m 0 m

theorem unlookup_depth_none (table : List Nat) (m : Nat) :
    Program.depthCostOps (fun _ => false) true (unlookupOps table m) = m :=
  unlookupAux_depth_none table m 0 m

theorem unlookup_depth_toffoli_le (table : List Nat) (m : Nat) :
    Program.depthCostOps Gate.isCcz false (unlookupOps table m) ≤ 32 * m :=
  unlookupAux_depth_toffoli_le table m 0 m

theorem roundTrip_toffoli_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).toffoliCount.hi ≤ 32 + 32 * m := by
  simp only [roundTripProgram, Program.toffoliCount, Program.weighOps_append]
  rw [lookup_toffoli_exact]
  have hu := unlookup_toffoli_hi_le table m
  simp only [Range.add, Range.point]
  omega

theorem roundTrip_gates_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).gateCount.hi ≤ 144 + 162 * m := by
  simp only [roundTripProgram, Program.gateCount, Program.weighOps_append]
  have hl := lookup_gates_hi_le table m
  have hu := unlookup_gates_hi_le table m
  simp only [Range.add]
  omega

theorem roundTrip_measure_exact (table : List Nat) (m : Nat) :
    (roundTripProgram table m).measureCount = Range.point m := by
  change Program.tallyOps measurementCost
      (gateOps (lookupGates table m) ++ unlookupOps table m) = Range.point m
  rw [Program.tallyOps_append, measure_gateOps, unlookup_measure_exact]
  simp [Range.add, Range.point]

theorem roundTrip_reset_exact (table : List Nat) (m : Nat) :
    (roundTripProgram table m).resetCount = Range.point 0 := by
  change Program.tallyOps resetCost
      (gateOps (lookupGates table m) ++ unlookupOps table m) = Range.point 0
  rw [Program.tallyOps_append, reset_gateOps, unlookup_reset_exact]
  rfl

theorem roundTrip_classical_exact (table : List Nat) (m : Nat) :
    (roundTripProgram table m).classicalOpCount = Range.point (2 * m) := by
  change Program.classicalOpCountOps
      (gateOps (lookupGates table m) ++ unlookupOps table m) = Range.point (2 * m)
  rw [Program.classicalOpCountOps_append, classical_gateOps,
    unlookup_classical_exact]
  simp [Range.add, Range.point]

theorem roundTrip_depthCost_le (table : List Nat) (m : Nat) :
    Program.depthCostOps (fun _ => true) true (roundTripProgram table m).ops ≤
      144 + 163 * m := by
  simp only [roundTripProgram, Program.depthCostOps_append, depth_gateOps_all,
    lookupGates_ccx]
  have hl := lookupGates_length_le table m
  have hu := unlookup_depth_all_le table m
  omega

theorem roundTrip_measurementCost (table : List Nat) (m : Nat) :
    Program.depthCostOps (fun _ => false) true (roundTripProgram table m).ops = m := by
  simp only [roundTripProgram, Program.depthCostOps_append, depth_gateOps_none,
    unlookup_depth_none, Nat.zero_add]

theorem roundTrip_toffoliCost_le (table : List Nat) (m : Nat) :
    Program.depthCostOps Gate.isCcz false (roundTripProgram table m).ops ≤
      32 + 32 * m := by
  simp only [roundTripProgram, Program.depthCostOps_append,
    depth_gateOps_toffoli, lookupGates_ccx]
  have hu := unlookup_depth_toffoli_le table m
  omega

theorem roundTrip_depth_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).depthRange.hi ≤ 144 + 163 * m := by
  rw [Program.depthRange]
  exact Nat.le_trans (Program.depthRangeOf_hi_le_depthCost _ _ _)
    (roundTrip_depthCost_le table m)

theorem roundTrip_toffoliDepth_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).toffoliDepthRange.hi ≤ 32 + 32 * m := by
  rw [Program.toffoliDepthRange]
  exact Nat.le_trans (Program.depthRangeOf_hi_le_depthCost _ _ _)
    (roundTrip_toffoliCost_le table m)

theorem roundTrip_measurementDepth_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).measurementDepthRange.hi ≤ m := by
  rw [Program.measurementDepthRange]
  exact Nat.le_trans (Program.depthRangeOf_hi_le_depthCost _ _ _)
    (Nat.le_of_eq (roundTrip_measurementCost table m))

theorem roundTrip_feedForwardDepth_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).feedForwardDepthRange.hi ≤ m := by
  exact Nat.le_trans (Program.feedForwardDepthRange_hi_le_depthCost _)
    (Nat.le_of_eq (roundTrip_measurementCost table m))

theorem roundTrip_classicalDepth_hi_le (table : List Nat) (m : Nat) :
    (roundTripProgram table m).classicalDepthRange.hi ≤ 2 * m := by
  exact Nat.le_trans (Program.classicalDepthRange_hi_le_classicalOpCount _)
    (by rw [roundTrip_classical_exact]; exact Nat.le_refl _)

theorem roundTrip_width (table : List Nat) (m : Nat) :
    (roundTripProgram table m).width = m + 5 := by
  simp [roundTripProgram, width, outputOffset, addressWidth]
  omega

theorem roundTrip_localBits_le_one (table : List Nat) (m : Nat) :
    (roundTripProgram table m).cbits ≤ 1 := by
  by_cases hm : m = 0 <;> simp [roundTripProgram, hm]

end Lookup3
end VQ
