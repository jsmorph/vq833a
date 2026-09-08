import VQMathlib.Algorithms.QFT.Approximate
import VQMathlib.Semantics.Approximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped Matrix.Norms.L2Operator

namespace VQ.Tests.ApproximateQFT

open VQ VQ.Algebra VQ.Semantics

noncomputable def phaseAngle (k : Nat) : ℝ :=
  2 * Real.pi / 2 ^ k

noncomputable def cphaseIdeal (width k a b : Nat) :
    Matrix (Fin (2 ^ width)) (Fin (2 ^ width)) ℂ :=
  Matrix.diagonal fun j =>
    if (j : Nat).testBit a = true ∧ (j : Nat).testBit b = true then
      Complex.exp (Complex.I * (phaseAngle k : ℂ))
    else 1

theorem cmat_cphase {level width k a b : Nat} (hk : 2 ≤ k)
    (hkl : k + 1 ≤ level) (ha : a < width) (hb : b < width) (hab : a ≠ b) :
    VQBridge.cmat level width (Circuit.cphase k a b) =
      cphaseIdeal width k a b := by
  ext i j
  change VQBridge.dtoC
      (runGates level width (Circuit.cphase k a b)
        (basis (j : Nat) : Vec (deg level)) (i : Nat)) = _
  have hrun := congrFun
    (VQ.Tests.QFT.run_cphase_basis (level := level) (width := width)
      (k := k) (a := a) (b := b) (j := (j : Nat)) hk hkl ha hb hab) (i : Nat)
  rw [hrun]
  simp only [Bool.and_eq_true]
  by_cases hbits : (j : Nat).testBit a = true ∧ (j : Nat).testBit b = true
  · rw [if_pos hbits, Vec.smul_apply,
      VQBridge.dtoC_mul (VQBridge.deg_pos level), VQBridge.dtoC_phase (by omega) (by omega)]
    by_cases hij : i = j
    · subst i
      rw [VQBridge.dtoC_basis (VQBridge.deg_pos level), if_pos rfl,
        cphaseIdeal, Matrix.diagonal_apply_eq, if_pos hbits, mul_one]
      congr 1
      rw [phaseAngle]
      push_cast
      ring
    · rw [VQBridge.dtoC_basis (VQBridge.deg_pos level), if_neg (fun h => hij (Fin.ext h)),
        mul_zero, cphaseIdeal, Matrix.diagonal_apply_ne _ hij]
  · rw [if_neg hbits]
    by_cases hij : i = j
    · subst i
      rw [VQBridge.dtoC_basis (VQBridge.deg_pos level), if_pos rfl,
        cphaseIdeal, Matrix.diagonal_apply_eq, if_neg hbits]
    · rw [VQBridge.dtoC_basis (VQBridge.deg_pos level), if_neg (fun h => hij (Fin.ext h)),
        cphaseIdeal, Matrix.diagonal_apply_ne _ hij]

theorem phaseAngle_nonneg (k : Nat) : 0 ≤ phaseAngle k := by
  rw [phaseAngle]
  exact div_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (by positivity)

theorem cphaseIdeal_sub_one (width k a b : Nat) :
    cphaseIdeal width k a b - 1 = Matrix.diagonal (fun j : Fin (2 ^ width) =>
      if (j : Nat).testBit a = true ∧ (j : Nat).testBit b = true then
        Complex.exp (Complex.I * (phaseAngle k : ℂ)) - 1
      else 0) := by
  ext i j
  by_cases hij : i = j <;>
    by_cases hbits : (j : Nat).testBit a = true ∧ (j : Nat).testBit b = true <;>
    simp [cphaseIdeal, hij, hbits]

theorem cphaseIdeal_sub_one_norm_le (width k a b : Nat) :
    ‖cphaseIdeal width k a b - 1‖ ≤ phaseAngle k := by
  rw [cphaseIdeal_sub_one, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (phaseAngle_nonneg k)).2
  intro i
  by_cases hbits : (i : Nat).testBit a = true ∧ (i : Nat).testBit b = true
  · rw [if_pos hbits]
    simpa [Real.norm_eq_abs, abs_of_nonneg (phaseAngle_nonneg k)] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := phaseAngle k))
  · simp [hbits, phaseAngle_nonneg k]

theorem cmat_cphase_sub_one_norm_le {level width k a b : Nat} (hk : 2 ≤ k)
    (hkl : k + 1 ≤ level) (ha : a < width) (hb : b < width) (hab : a ≠ b) :
    ‖VQBridge.cmat level width (Circuit.cphase k a b) - 1‖ ≤ phaseAngle k := by
  rw [cmat_cphase hk hkl ha hb hab]
  exact cphaseIdeal_sub_one_norm_le width k a b

def fullPhaseRows : List Nat → Nat → Nat → List Gate
  | [], _, _ => []
  | r :: rest, start, q =>
      Circuit.cphase (start + 2) r q ++ fullPhaseRows rest (start + 1) q

noncomputable def rowError (cutoff : Nat) : Nat → Nat → ℝ
  | _, 0 => 0
  | start, count + 1 =>
      rowError cutoff (start + 1) count +
        if start + 2 ≤ cutoff then 0 else phaseAngle (start + 2)

theorem fullPhaseRows_wellFormedAt {level width start q : Nat}
    (rest : List Nat) (hq : q < width)
    (hrest : ∀ r ∈ rest, r < width) (hneq : q ∉ rest)
    (hlevel : start + rest.length + 2 ≤ level) :
    (fullPhaseRows rest start q).all (Gate.wellFormedAt level width) = true := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.length_cons] at hlevel
      have hr : r < width := hrest r (by simp)
      have hrq : r ≠ q := by
        intro h
        apply hneq
        simp [h]
      have hrest' : ∀ s ∈ rest, s < width := by
        intro s hs
        exact hrest s (by simp [hs])
      have hneq' : q ∉ rest := by
        intro h
        exact hneq (by simp [h])
      have hcphase : (Circuit.cphase (start + 2) r q).all
          (Gate.wellFormedAt level width) = true :=
        VQ.Tests.QFT.cphase_wellFormedAt (by omega) (by omega) hr hq hrq
      simp only [fullPhaseRows, List.all_append]
      rw [hcphase, ih hrest' hneq' (by omega)]
      rfl

theorem phaseRows_wellFormedAt_of_fullLevel {level width cutoff start q : Nat}
    (rest : List Nat) (hq : q < width)
    (hrest : ∀ r ∈ rest, r < width) (hneq : q ∉ rest)
    (hlevel : start + rest.length + 2 ≤ level) :
    (phaseRows cutoff rest start q).all (Gate.wellFormedAt level width) = true := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.length_cons] at hlevel
      have hr : r < width := hrest r (by simp)
      have hrq : r ≠ q := by
        intro h
        apply hneq
        simp [h]
      have hrest' : ∀ s ∈ rest, s < width := by
        intro s hs
        exact hrest s (by simp [hs])
      have hneq' : q ∉ rest := by
        intro h
        exact hneq (by simp [h])
      have htail := ih hrest' hneq' (start := start + 1) (by omega)
      by_cases hkeep : start + 2 ≤ cutoff
      · have hcphase : (Circuit.cphase (start + 2) r q).all
            (Gate.wellFormedAt level width) = true :=
          VQ.Tests.QFT.cphase_wellFormedAt (by omega) (by omega) hr hq hrq
        simp [phaseRows, hkeep, hcphase, htail]
      · simp [phaseRows, hkeep, htail]

theorem norm_cmat_eq_one {level width : Nat} {gs : List Gate}
    (hgs : gs.all (Gate.wellFormedAt level width) = true) :
    ‖VQBridge.cmat level width gs‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary
    (Matrix.mem_unitaryGroup_iff'.mpr
      (VQBridge.unitary_cmat fun g hg => List.all_eq_true.mp hgs g hg))

theorem cmat_append_error_le {level width : Nat} (a b c d : List Gate)
    (ha : a.all (Gate.wellFormedAt level width) = true)
    (hd : d.all (Gate.wellFormedAt level width) = true) :
    ‖VQBridge.cmat level width (a ++ b) - VQBridge.cmat level width (c ++ d)‖ ≤
      ‖VQBridge.cmat level width b - VQBridge.cmat level width d‖ +
        ‖VQBridge.cmat level width a - VQBridge.cmat level width c‖ := by
  rw [VQBridge.cmat_append, VQBridge.cmat_append]
  calc
    _ ≤ ‖VQBridge.cmat level width b - VQBridge.cmat level width d‖ *
          ‖VQBridge.cmat level width a‖ +
        ‖VQBridge.cmat level width d‖ *
          ‖VQBridge.cmat level width a - VQBridge.cmat level width c‖ :=
      VQ.Tests.Approximation.l2_opNorm_mul_sub_mul_le _ _ _ _
    _ = _ := by rw [norm_cmat_eq_one ha, norm_cmat_eq_one hd]; ring

theorem phaseRows_error {level width cutoff start q : Nat}
    (rest : List Nat) (hq : q < width)
    (hrest : ∀ r ∈ rest, r < width) (hneq : q ∉ rest)
    (hlevel : start + rest.length + 2 ≤ level) :
    ‖VQBridge.cmat level width (phaseRows cutoff rest start q) -
        VQBridge.cmat level width (fullPhaseRows rest start q)‖ ≤
      rowError cutoff start rest.length := by
  induction rest generalizing start with
  | nil => simp [phaseRows, fullPhaseRows, rowError]
  | cons r rest ih =>
      simp only [List.length_cons] at hlevel
      have hr : r < width := hrest r (by simp)
      have hrq : r ≠ q := by
        intro h
        apply hneq
        simp [h]
      have hrest' : ∀ s ∈ rest, s < width := by
        intro s hs
        exact hrest s (by simp [hs])
      have hneq' : q ∉ rest := by
        intro h
        exact hneq (by simp [h])
      have hlevel' : start + 1 + rest.length + 2 ≤ level := by
        omega
      have htail := ih hrest' hneq' (start := start + 1) hlevel'
      have hfullTail := fullPhaseRows_wellFormedAt rest hq hrest' hneq' hlevel'
      by_cases hkeep : start + 2 ≤ cutoff
      · have hhead : (Circuit.cphase (start + 2) r q).all
            (Gate.wellFormedAt level width) = true :=
          VQ.Tests.QFT.cphase_wellFormedAt (by omega) (by omega) hr hq hrq
        calc
          _ ≤ ‖VQBridge.cmat level width (phaseRows cutoff rest (start + 1) q) -
                VQBridge.cmat level width (fullPhaseRows rest (start + 1) q)‖ +
              ‖VQBridge.cmat level width (Circuit.cphase (start + 2) r q) -
                VQBridge.cmat level width (Circuit.cphase (start + 2) r q)‖ := by
            rw [phaseRows, fullPhaseRows, if_pos hkeep]
            exact cmat_append_error_le _ _ _ _ hhead hfullTail
          _ ≤ rowError cutoff (start + 1) rest.length + 0 := by
            simpa using add_le_add htail (norm_nonneg
              (VQBridge.cmat level width (Circuit.cphase (start + 2) r q) -
                VQBridge.cmat level width (Circuit.cphase (start + 2) r q)))
          _ = rowError cutoff start (List.length (r :: rest)) := by
            simp [rowError, hkeep]
      · have hempty : ([] : List Gate).all (Gate.wellFormedAt level width) = true := rfl
        have hlocal :
            ‖VQBridge.cmat level width [] -
                VQBridge.cmat level width (Circuit.cphase (start + 2) r q)‖ ≤
              phaseAngle (start + 2) := by
          rw [VQBridge.cmat_nil]
          have heq :
              (1 : Matrix (Fin (2 ^ width)) (Fin (2 ^ width)) ℂ) -
                  VQBridge.cmat level width (Circuit.cphase (start + 2) r q) =
                -(VQBridge.cmat level width (Circuit.cphase (start + 2) r q) - 1) := by
            module
          rw [heq, norm_neg]
          exact cmat_cphase_sub_one_norm_le (level := level) (width := width)
            (k := start + 2) (a := r) (b := q) (by omega) (by omega) hr hq hrq
        calc
          _ ≤ ‖VQBridge.cmat level width (phaseRows cutoff rest (start + 1) q) -
                VQBridge.cmat level width (fullPhaseRows rest (start + 1) q)‖ +
              ‖VQBridge.cmat level width [] -
                VQBridge.cmat level width (Circuit.cphase (start + 2) r q)‖ := by
            rw [phaseRows, fullPhaseRows, if_neg hkeep]
            exact cmat_append_error_le _ _ _ _ hempty hfullTail
          _ ≤ rowError cutoff (start + 1) rest.length + phaseAngle (start + 2) :=
            add_le_add htail hlocal
          _ = rowError cutoff start (List.length (r :: rest)) := by
            simp [rowError, hkeep]

def fullNoSwap : List Nat → List Gate
  | [] => []
  | q :: rest => Gate.h q :: fullPhaseRows rest 0 q ++ fullNoSwap rest

noncomputable def noSwapError (cutoff : Nat) : Nat → ℝ
  | 0 => 0
  | n + 1 => noSwapError cutoff n + rowError cutoff 0 n

theorem fullPhaseRows_eq (rest : List Nat) (start q : Nat) :
    fullPhaseRows rest start q =
      (rest.zipIdx start |>.flatMap fun ri => Circuit.cphase (ri.2 + 2) ri.1 q) := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      simp only [fullPhaseRows, List.zipIdx_cons, List.flatMap_cons]
      rw [ih]

theorem fullNoSwap_eq_qftNoSwap (wires : List Nat) :
    fullNoSwap wires = Circuit.qftNoSwap wires := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change Gate.h q :: fullPhaseRows rest 0 q ++ fullNoSwap rest =
        Gate.h q ::
          ((rest.zipIdx.flatMap fun ri => Circuit.cphase (ri.2 + 2) ri.1 q) ++
            Circuit.qftNoSwap rest)
      rw [fullPhaseRows_eq, ih]
      simp

theorem noSwap_wellFormedAt_of_fullLevel {level width cutoff : Nat}
    (wires : List Nat) (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup)
    (hl3 : 3 ≤ level) (hlevel : wires.length + 1 ≤ level) :
    (noSwap cutoff wires).all (Gate.wellFormedAt level width) = true := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      simp only [List.length_cons] at hlevel
      have hq : q < width := hw q (by simp)
      have hrest : ∀ r ∈ rest, r < width := by
        intro r hr
        exact hw r (by simp [hr])
      have hsplit : q ∉ rest ∧ rest.Nodup := by simpa using hnodup
      have hrowLevel : 0 + rest.length + 2 ≤ level := by omega
      have hphase := phaseRows_wellFormedAt_of_fullLevel (cutoff := cutoff)
        (start := 0) rest hq hrest hsplit.1 hrowLevel
      have htail := ih hrest hsplit.2 (by omega)
      simp [noSwap, Gate.wellFormedAt, hq, hl3, hphase, htail]

theorem noSwap_error {level width cutoff : Nat} (wires : List Nat)
    (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup)
    (hl3 : 3 ≤ level) (hlevel : wires.length + 1 ≤ level) :
    ‖VQBridge.cmat level width (noSwap cutoff wires) -
        VQBridge.cmat level width (fullNoSwap wires)‖ ≤
      noSwapError cutoff wires.length := by
  induction wires with
  | nil => simp [noSwap, fullNoSwap, noSwapError]
  | cons q rest ih =>
      simp only [List.length_cons] at hlevel
      have hq : q < width := hw q (by simp)
      have hrest : ∀ r ∈ rest, r < width := by
        intro r hr
        exact hw r (by simp [hr])
      have hsplit : q ∉ rest ∧ rest.Nodup := by simpa using hnodup
      have hphase := phaseRows_error (level := level) (width := width)
        (cutoff := cutoff) (start := 0) rest hq hrest hsplit.1 (by omega)
      have hphaseApprox := phaseRows_wellFormedAt_of_fullLevel (level := level)
        (cutoff := cutoff) (start := 0) rest hq hrest hsplit.1 (by omega)
      have hphaseFull := fullPhaseRows_wellFormedAt (level := level)
        (start := 0) rest hq hrest hsplit.1 (by omega)
      have hh : ([Gate.h q] : List Gate).all (Gate.wellFormedAt level width) = true := by
        simp [Gate.wellFormedAt, hq, hl3]
      have hheadApprox : (Gate.h q :: phaseRows cutoff rest 0 q).all
          (Gate.wellFormedAt level width) = true := by
        simp [Gate.wellFormedAt, hq, hl3, hphaseApprox]
      have hfullTail : (fullNoSwap rest).all (Gate.wellFormedAt level width) = true := by
        rw [fullNoSwap_eq_qftNoSwap]
        exact VQ.Tests.QFT.qftNoSwap_wellFormedAt rest hrest hsplit.2 hl3 (by omega)
      have hheadError :
          ‖VQBridge.cmat level width (Gate.h q :: phaseRows cutoff rest 0 q) -
              VQBridge.cmat level width (Gate.h q :: fullPhaseRows rest 0 q)‖ ≤
            rowError cutoff 0 rest.length := by
        calc
          _ ≤ ‖VQBridge.cmat level width (phaseRows cutoff rest 0 q) -
                VQBridge.cmat level width (fullPhaseRows rest 0 q)‖ +
              ‖VQBridge.cmat level width [Gate.h q] -
                VQBridge.cmat level width [Gate.h q]‖ := by
            change ‖VQBridge.cmat level width ([Gate.h q] ++ phaseRows cutoff rest 0 q) -
                VQBridge.cmat level width ([Gate.h q] ++ fullPhaseRows rest 0 q)‖ ≤ _
            exact cmat_append_error_le _ _ _ _ hh hphaseFull
          _ ≤ rowError cutoff 0 rest.length + 0 := by
            simpa using add_le_add hphase (norm_nonneg
              (VQBridge.cmat level width [Gate.h q] -
                VQBridge.cmat level width [Gate.h q]))
          _ = rowError cutoff 0 rest.length := add_zero _
      have htail := ih hrest hsplit.2 (by omega)
      calc
        _ ≤ ‖VQBridge.cmat level width (noSwap cutoff rest) -
              VQBridge.cmat level width (fullNoSwap rest)‖ +
            ‖VQBridge.cmat level width (Gate.h q :: phaseRows cutoff rest 0 q) -
              VQBridge.cmat level width (Gate.h q :: fullPhaseRows rest 0 q)‖ := by
          rw [noSwap, fullNoSwap]
          exact cmat_append_error_le _ _ _ _ hheadApprox hfullTail
        _ ≤ noSwapError cutoff rest.length + rowError cutoff 0 rest.length :=
          add_le_add htail hheadError
        _ = noSwapError cutoff (List.length (q :: rest)) := by
          simp [noSwapError]

theorem gates_error {level width cutoff : Nat} (wires : List Nat)
    (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup)
    (hl3 : 3 ≤ level) (hlevel : wires.length + 1 ≤ level) :
    ‖VQBridge.cmat level width (gates cutoff wires) -
        VQBridge.cmat level width (Circuit.qft wires)‖ ≤
      noSwapError cutoff wires.length := by
  have happrox := noSwap_wellFormedAt_of_fullLevel
    (level := level) (cutoff := cutoff) wires hw hnodup hl3 hlevel
  have hswaps := VQ.Tests.QFT.qftSwaps_wellFormedAt
    (level := level) wires hw hnodup
  have hnoSwap := noSwap_error (level := level) (cutoff := cutoff)
    wires hw hnodup hl3 hlevel
  change ‖VQBridge.cmat level width (noSwap cutoff wires ++ VQ.Tests.QFT.qftSwaps wires) -
      VQBridge.cmat level width
        (Circuit.qftNoSwap wires ++ VQ.Tests.QFT.qftSwaps wires)‖ ≤ _
  rw [← fullNoSwap_eq_qftNoSwap wires]
  calc
    _ ≤ ‖VQBridge.cmat level width (VQ.Tests.QFT.qftSwaps wires) -
          VQBridge.cmat level width (VQ.Tests.QFT.qftSwaps wires)‖ +
        ‖VQBridge.cmat level width (noSwap cutoff wires) -
          VQBridge.cmat level width (fullNoSwap wires)‖ :=
      cmat_append_error_le _ _ _ _ happrox hswaps
    _ ≤ 0 + noSwapError cutoff wires.length := by
      simpa using add_le_add
        (norm_nonneg (VQBridge.cmat level width (VQ.Tests.QFT.qftSwaps wires) -
          VQBridge.cmat level width (VQ.Tests.QFT.qftSwaps wires))) hnoSwap
    _ = noSwapError cutoff wires.length := zero_add _

theorem circuit_error {level n cutoff : Nat}
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    ‖VQBridge.cmat level n (circuit n cutoff).gates -
        VQBridge.cmat level n (VQ.Tests.QFT.qftCircuit n).gates‖ ≤
      noSwapError cutoff n := by
  change ‖VQBridge.cmat level n (gates cutoff (List.range n).reverse) -
      VQBridge.cmat level n (Circuit.qft (List.range n).reverse)‖ ≤ _
  have h := gates_error (level := level) (width := n) (cutoff := cutoff)
    (List.range n).reverse
    (by intro q hq; simpa using List.mem_range.mp (List.mem_reverse.mp hq))
    (List.nodup_reverse.mpr List.nodup_range) hl3 (by simpa using hlevel)
  simpa using h

theorem noSwapError_three_two : noSwapError 2 3 = Real.pi / 4 := by
  simp [noSwapError, rowError, phaseAngle]
  ring

/-- info: 'VQ.Tests.ApproximateQFT.cmat_cphase_sub_one_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmat_cphase_sub_one_norm_le

/-- info: 'VQ.Tests.ApproximateQFT.phaseRows_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phaseRows_error

/-- info: 'VQ.Tests.ApproximateQFT.noSwap_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noSwap_error

/-- info: 'VQ.Tests.ApproximateQFT.circuit_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circuit_error

/-- info: 'VQ.Tests.ApproximateQFT.noSwapError_three_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noSwapError_three_two

end VQ.Tests.ApproximateQFT
