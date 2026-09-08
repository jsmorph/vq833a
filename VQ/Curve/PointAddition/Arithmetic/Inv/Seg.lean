import VQ.Curve.PointAddition.Arithmetic.Inv.Round1
import VQ.Curve.PointAddition.Arithmetic.Inv.State

/-!
# Round segments

`roundGates` is eight segments.  Each is proved here as one rewrite on the state
abstraction, and the round's correctness is their composition.

Every segment carries the same geometric side conditions: the registers are
pairwise disjoint and all fit below the circuit's width.  `geo` bundles them,
since spelling them out at each of the twenty steps would dominate the file.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The offsets, unfolded, for the arithmetic that discharges disjointness. -/
theorem off_vals (n : Nat) :
    aU n = 2 * n ∧ aV n = 3 * n + 1 ∧ aR n = 4 * n + 2 ∧ aS n = 5 * n + 3 ∧
      aTU n = 6 * n + 4 ∧ aTR n = 7 * n + 5 ∧ aA n = 8 * n + 6 ∧ aT n = 8 * n + 7 ∧
      aGt n = 8 * n + 8 ∧ aC n = 8 * n + 9 ∧ aNZ n = 8 * n + 10 ∧
      aM n = 8 * n + 11 ∧ aZ n = 10 * n + 11 ∧ bw n = n + 1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] <;> omega


/-! ## Zero-test semantics

Load one into the scratch register, compare, unload, negate.  `v < 1` is `v = 0`,
so the kept bit ends holding `v ≠ 0`. -/

theorem seg_zero {n t I u v r s a bo gt m : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hv : v < 2 ^ n) :
    actGates (segZero n t)
      (ks n t I u v r s 0 0 a bo gt 0 m 0)
      = ks n t I u v r s 0 0 a bo gt 0 m (if v = 0 then 0 else 1) := by
  have hvred : v % 2 ^ (bw n) = v := by
    have h1 : (2 : Nat) ^ n < 2 ^ (bw n) := by
      refine Nat.pow_lt_pow_right (by decide) ?_
      simp only [bw]; omega
    exact Nat.mod_eq_of_lt (by omega)
  have hsc : readField (ks n t I u v r s 0 0 a bo gt 0 m 0) (aTR n) (bw n) = 0 := by
    rw [ks_read_TR ht, Nat.zero_mod]
  have hz : readField (ks n t I u v r s 0 0 a bo gt 0 m 0) (aZ n + t) 1 = 0 := by
    rw [ks_read_Z ht]
  have hsrc : readField (ks n t I u v r s 0 0 a bo gt 0 m 0) (aV n) (bw n) = v := by
    rw [ks_read_V ht]; exact hvred
  show actGates (nzTest (aV n) (aTR n) (aZ n + t) (bw n)) _ = _
  rw [nzTest_act (Wd := totalWidth n) (by simp only [bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega)
      _ hsc, hsrc, ← readField_one, hz, ks_write_Z ht]
  refine congrArg (fun q => ks n t I u v r s 0 0 a bo gt 0 m q) ?_
  by_cases h : v = 0
  · rw [if_pos h]
  · rw [if_neg h]

theorem seg_dispatch {n t I u v r s tr m z : Nat} (ht : t < 2 * n) :
    actGates (segDispatch n t)
      (ks n t I u v r s 0 tr 0 0 0 0 m z)
      = ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0
          ((m % 2 + u % 2 + u % 2 * (v % 2)) % 2) z := by
  unfold segDispatch
  -- `a` is set, then cleared again when `u` is odd.
  have e1 : actGates [RGate.x (aA n)] (ks n t I u v r s 0 tr 0 0 0 0 m z)
      = ks n t I u v r s 0 tr 1 0 0 0 m z := by
    show RGate.act (RGate.x (aA n)) _ = _
    rw [act_x, ← readField_one, ks_read_A ht, Nat.pow_one, ks_write_A ht]
  have e2 : actGates [RGate.cx (aU n) (aA n)] (ks n t I u v r s 0 tr 1 0 0 0 m z)
      = ks n t I u v r s 0 tr ((u % 2 + 1) % 2) 0 0 0 m z := by
    show RGate.act (RGate.cx (aU n) (aA n)) _ = _
    rw [act_cx, ← readField_one, ks_read_A ht, Nat.pow_one, ks_bit_U ht, ks_write_A ht]
    refine congrArg (fun q => ks n t I u v r s 0 tr q 0 0 0 m z) ?_
    omega
  -- `both odd`.
  have e3 : actGates [RGate.ccx (aU n) (aV n) (aT n)]
      (ks n t I u v r s 0 tr ((u % 2 + 1) % 2) 0 0 0 m z)
      = ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0 m z := by
    show RGate.act (RGate.ccx (aU n) (aV n) (aT n)) _ = _
    rw [act_ccx, ← readField_one, ks_read_T ht, Nat.pow_one, ks_bit_U ht, ks_bit_V ht,
      ks_write_T ht]
    refine congrArg (fun q => ks n t I u v r s 0 tr ((u % 2 + 1) % 2) q 0 0 m z) ?_
    have hu2 : u % 2 = 0 ∨ u % 2 = 1 := by omega
    have hv2 : v % 2 = 0 ∨ v % 2 = 1 := by omega
    cases hu2 with
    | inl h => rw [h]; simp
    | inr h => cases hv2 with
      | inl h' => rw [h, h']
      | inr h' => rw [h, h']
  -- `m` picks up `u` odd, then `both odd`.
  have e4 : actGates [RGate.cx (aU n) (aM n + t)]
      (ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0 m z)
      = ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0
          ((m % 2 + u % 2) % 2) z := by
    show RGate.act (RGate.cx (aU n) (aM n + t)) _ = _
    rw [act_cx, ← readField_one, ks_read_M ht, Nat.pow_one, ks_bit_U ht, ks_write_M ht]
  have e5 : actGates [RGate.cx (aT n) (aM n + t)]
      (ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0
        ((m % 2 + u % 2) % 2) z)
      = ks n t I u v r s 0 tr ((u % 2 + 1) % 2) (u % 2 * (v % 2)) 0 0
          ((m % 2 + u % 2 + u % 2 * (v % 2)) % 2) z := by
    show RGate.act (RGate.cx (aT n) (aM n + t)) _ = _
    rw [act_cx, ← readField_one, ks_read_M ht, Nat.pow_one, ← readField_one, ks_read_T ht,
      Nat.pow_one, ks_write_M ht]
    refine congrArg (fun q => ks n t I u v r s 0 tr ((u % 2 + 1) % 2)
      (u % 2 * (v % 2)) 0 0 q z) ?_
    have hu2 : u % 2 = 0 ∨ u % 2 = 1 := by omega
    have hv2 : v % 2 = 0 ∨ v % 2 = 1 := by omega
    cases hu2 with
    | inl h => rw [h]; simp
    | inr h => cases hv2 with
      | inl h' => rw [h, h']; simp
      | inr h' => rw [h, h']; omega
  rw [actGates_append, actGates_append]
  show actGates _ (actGates _ (actGates [RGate.x (aA n), RGate.cx (aU n) (aA n)] _)) = _
  rw [show [RGate.x (aA n), RGate.cx (aU n) (aA n)]
        = [RGate.x (aA n)] ++ [RGate.cx (aU n) (aA n)] from rfl,
    show [RGate.cx (aU n) (aM n + t), RGate.cx (aT n) (aM n + t)]
        = [RGate.cx (aU n) (aM n + t)] ++ [RGate.cx (aT n) (aM n + t)] from rfl,
    actGates_append, actGates_append, e1, e2, e3, e4, e5]

/-! ## Comparison semantics

`v < u` decides between the two both-odd branches.  It is computed, used by two
Toffolis, and computed again, which clears it because `u` and `v` have not
moved. -/

/-- The comparison, once. -/
theorem cmp_uv {n t I u v r s tr a bo gt cy m z : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hcy : cy = 0) :
    actGates (cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n))
      (ks n t I u v r s 0 tr a bo gt cy m z)
      = ks n t I u v r s 0 tr a bo ((gt % 2 + if v < u then 1 else 0) % 2) cy m z := by
  subst hcy
  have hred : ∀ x : Nat, x < 2 ^ n → x % 2 ^ (bw n) = x := by
    intro x hx
    have h1 : (2 : Nat) ^ n < 2 ^ (bw n) :=
      Nat.pow_lt_pow_right (by decide) (by simp only [bw]; omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hr0 : readField (ks n t I u v r s 0 tr a bo gt 0 m z) (aU n) (bw n) = u := by
    rw [ks_read_U ht]; exact hred u hu
  have hr1 : readField (ks n t I u v r s 0 tr a bo gt 0 m z) (aV n) (bw n) = v := by
    rw [ks_read_V ht]; exact hred v hv
  have hr2 : readField (ks n t I u v r s 0 tr a bo gt 0 m z) (aC n) 1 = 0 := by
    rw [ks_read_C ht]
  have hr3 : readField (ks n t I u v r s 0 tr a bo gt 0 m z) (aGt n) 1 = gt % 2 := by
    rw [ks_read_Gt ht, Nat.pow_one]
  have hpn : (2 : Nat) ^ n < 2 ^ (bw n) :=
    Nat.pow_lt_pow_right (by decide) (by simp only [bw]; omega)
  have := cmpMaj_act (w := bw n) (ou := aU n) (ov := aV n) (oc := aC n) (og := aGt n)
    (I := ks n t I u v r s 0 tr a bo gt 0 m z) (u := u) (v := v) (g := gt % 2)
    (Wd := totalWidth n)
    (by simp only [bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega)
    hr0 hr1 hr2 hr3 (by omega) (by omega)
  rw [this, ks_write_Gt ht]

/-- The comparison feeds both dispatch bits and is then cleared. -/
theorem seg_compare {n t I u v r s tr a bo m z : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) :
    actGates (segCompare n t)
      (ks n t I u v r s 0 tr a bo 0 0 m z)
      = ks n t I u v r s 0 tr
          ((a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) bo 0 0
          ((m % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) z := by
  rw [segCompare_act ht]
  unfold segCompareOld cmpUse
  have hgtlt : (if v < u then 1 else 0) < 2 := by
    by_cases h : v < u
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  have e1 := cmp_uv (I := I) (r := r) (s := s) (tr := tr) (a := a) (bo := bo) (gt := 0)
    (m := m) (z := z) hn ht hu hv rfl
  have e2 : actGates [RGate.ccx (aT n) (aGt n) (aA n)]
      (ks n t I u v r s 0 tr a bo (if v < u then 1 else 0) 0 m z)
      = ks n t I u v r s 0 tr ((a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) bo
          (if v < u then 1 else 0) 0 m z := by
    show RGate.act (RGate.ccx (aT n) (aGt n) (aA n)) _ = _
    rw [act_ccx, ← readField_one, ks_read_A ht, Nat.pow_one, ← readField_one, ks_read_T ht,
      Nat.pow_one, ← readField_one, ks_read_Gt ht, Nat.pow_one, ks_write_A ht]
    refine congrArg (fun q => ks n t I u v r s 0 tr q bo (if v < u then 1 else 0) 0 m z) ?_
    rw [Nat.mod_eq_of_lt hgtlt]
  have e3 : actGates [RGate.ccx (aT n) (aGt n) (aM n + t)]
      (ks n t I u v r s 0 tr ((a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) bo
        (if v < u then 1 else 0) 0 m z)
      = ks n t I u v r s 0 tr ((a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) bo
          (if v < u then 1 else 0) 0
          ((m % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) z := by
    show RGate.act (RGate.ccx (aT n) (aGt n) (aM n + t)) _ = _
    rw [act_ccx, ← readField_one, ks_read_M ht, Nat.pow_one, ← readField_one, ks_read_T ht,
      Nat.pow_one, ← readField_one, ks_read_Gt ht, Nat.pow_one, ks_write_M ht]
    refine congrArg (fun q => ks n t I u v r s 0 tr
      ((a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) bo (if v < u then 1 else 0) 0 q z) ?_
    rw [Nat.mod_eq_of_lt hgtlt]
  have e4 := cmp_uv (I := I) (r := r) (s := s) (tr := tr)
    (a := (a % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) (bo := bo)
    (gt := if v < u then 1 else 0)
    (m := (m % 2 + bo % 2 * (if v < u then 1 else 0)) % 2) (z := z)
    hn ht hu hv rfl
  have hclear : ((if v < u then 1 else 0) % 2 + if v < u then 1 else 0) % 2 = 0 := by
    by_cases hlt : v < u
    · rw [if_pos hlt]
    · rw [if_neg hlt]
  have hz0 : ((0 : Nat) % 2 + if v < u then 1 else 0) % 2 = if v < u then 1 else 0 := by
    by_cases hlt : v < u
    · rw [if_pos hlt]
    · rw [if_neg hlt]
  rw [hz0] at e1
  rw [hclear] at e4
  rw [actGates_append, actGates_append,
    show [RGate.ccx (aT n) (aGt n) (aA n), RGate.ccx (aT n) (aGt n) (aM n + t)]
      = [RGate.ccx (aT n) (aGt n) (aA n)] ++ [RGate.ccx (aT n) (aGt n) (aM n + t)] from rfl,
    actGates_append, e1, e2, e3, e4]

/-! ## Swap semantics

`u` with `v` and `r` with `s`, under `a`.  Two cases, since the swap gate is
proved separately for a clear and a set control. -/

theorem seg_swap {n t I u v r s tr a bo gt cy m z : Nat} (ht : t < 2 * n)
    (hured : u % 2 ^ (bw n) = u) (hvred : v % 2 ^ (bw n) = v)
    (hrred : r % 2 ^ (bw n) = r) (hsred : s % 2 ^ (bw n) = s) :
    actGates (segSwap n)
      (ks n t I u v r s 0 tr a bo gt cy m z)
      = if a % 2 = 1 then ks n t I v u s r 0 tr a bo gt cy m z
        else ks n t I u v r s 0 tr a bo gt cy m z := by
  unfold segSwap
  have hbit : bv (ks n t I u v r s 0 tr a bo gt cy m z) (aA n) = a % 2 := by
    rw [← readField_one, ks_read_A ht, Nat.pow_one]
  by_cases hset : a % 2 = 1
  · rw [if_pos hset]
    have h1 : actGates (swapC (aA n) (aU n) (aV n) (bw n))
        (ks n t I u v r s 0 tr a bo gt cy m z)
        = ks n t I v u r s 0 tr a bo gt cy m z := by
      rw [swapC_on (bw n) (aU n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by rw [hbit]; exact hset),
        ks_read_V ht, ks_read_U ht, hured, hvred, ks_write_U ht, ks_write_V ht]
    have hbit2 : bv (ks n t I v u r s 0 tr a bo gt cy m z) (aA n) = a % 2 := by
      rw [← readField_one, ks_read_A ht, Nat.pow_one]
    have h2 : actGates (swapC (aA n) (aR n) (aS n) (bw n))
        (ks n t I v u r s 0 tr a bo gt cy m z)
        = ks n t I v u s r 0 tr a bo gt cy m z := by
      rw [swapC_on (bw n) (aR n) (aS n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by rw [hbit2]; exact hset),
        ks_read_S ht, ks_read_R ht, hrred, hsred, ks_write_R ht, ks_write_S ht]
    rw [actGates_append, h1, h2]
  · rw [if_neg hset]
    have hz : bv (ks n t I u v r s 0 tr a bo gt cy m z) (aA n) = 0 := by
      rw [hbit]; omega
    have h1 : actGates (swapC (aA n) (aU n) (aV n) (bw n))
        (ks n t I u v r s 0 tr a bo gt cy m z)
        = ks n t I u v r s 0 tr a bo gt cy m z :=
      swapC_off (bw n) (aU n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) hz
    have h2 : actGates (swapC (aA n) (aR n) (aS n) (bw n))
        (ks n t I u v r s 0 tr a bo gt cy m z)
        = ks n t I u v r s 0 tr a bo gt cy m z :=
      swapC_off (bw n) (aR n) (aS n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) hz
    rw [actGates_append, h1, h2]

/-! ## Conditional-arithmetic semantics

`v := v - u` and `s := s + r`, under `both odd`.  A Cuccaro adder cannot take an
extra control, so each addend is copied into scratch under the bit and the adder
runs unconditionally.  The copy is then repeated, which clears the scratch. -/

theorem seg_arith {n t I u v r s a bo gt m z : Nat} (ht : t < 2 * n)
    (hured : u % 2 ^ (bw n) = u) (hvred : v % 2 ^ (bw n) = v)
    (hrred : r % 2 ^ (bw n) = r) (hsred : s % 2 ^ (bw n) = s) (hbo : bo % 2 = 1) :
    actGates (segArith n)
      (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r ((r + s) % 2 ^ (bw n))
          0 0 a bo gt 0 m z := by
  unfold segArith
  have hbit : ∀ x y r' s' tu' tr' cy', bv (ks n t I x y r' s' tu' tr' a bo gt cy' m z) (aT n)
      = 1 := by
    intro x y r' s' tu' tr' cy'
    rw [← readField_one, ks_read_T ht, Nat.pow_one, hbo]
  -- Copy `u` into scratch under the bit.
  have e1 : actGates (copyC (aT n) (aU n) (aTU n) (bw n)) (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u v r s u 0 a bo gt 0 m z := by
    rw [copyC_act (bw n) (aU n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), ks_read_TU ht, ks_read_U ht,
      hured, hbit u v r s 0 0 0, Nat.one_mul, Nat.zero_mod, Nat.zero_xor, ks_write_TU ht]
  -- Subtract it from `v`.
  have e2 : actGates (subAt (bw n) (aTU n) (aV n) (aC n)) (ks n t I u v r s u 0 a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s u 0 a bo gt 0 m z := by
    have hr0 : readField (ks n t I u v r s u 0 a bo gt 0 m z) (aTU n) (bw n) = u := by
      rw [ks_read_TU ht]; exact hured
    have hr1 : readField (ks n t I u v r s u 0 a bo gt 0 m z) (aV n) (bw n) = v := by
      rw [ks_read_V ht]; exact hvred
    have hr2 : readField (ks n t I u v r s u 0 a bo gt 0 m z) (aC n) 1 = 0 := by
      rw [ks_read_C ht]
    rw [subAt_act (Wd := totalWidth n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) hr0 hr1 hr2,
      ks_write_V ht]
  -- Clear the scratch.
  have e3 : actGates (copyC (aT n) (aU n) (aTU n) (bw n))
      (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s u 0 a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 0 a bo gt 0 m z := by
    rw [copyC_act (bw n) (aU n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), ks_read_TU ht, ks_read_U ht,
      hured, hbit u _ r s u 0 0, Nat.one_mul, Nat.xor_self, ks_write_TU ht]
  -- The same three steps on `r` and `s`, with an addition.
  have e4 : actGates (copyC (aT n) (aR n) (aTR n) (bw n))
      (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 0 a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 r a bo gt 0 m z := by
    rw [copyC_act (bw n) (aR n) (aTR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), ks_read_TR ht, ks_read_R ht,
      hrred, hbit u _ r s 0 0 0, Nat.one_mul, Nat.zero_mod, Nat.zero_xor, ks_write_TR ht]
  have e5 : actGates (addAt (bw n) (aTR n) (aS n) (aC n))
      (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 r a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r ((r + s) % 2 ^ (bw n))
          0 r a bo gt 0 m z := by
    have hr0 : readField (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 r a bo gt 0 m z)
        (aTR n) (bw n) = r := by
      rw [ks_read_TR ht]; exact hrred
    have hr1 : readField (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 r a bo gt 0 m z)
        (aS n) (bw n) = s := by
      rw [ks_read_S ht]; exact hsred
    have hr2 : readField (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r s 0 r a bo gt 0 m z)
        (aC n) 1 = 0 := by
      rw [ks_read_C ht]
    rw [addAt_act (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) hr0 hr1 hr2, ks_write_S ht]
  have e6 : actGates (copyC (aT n) (aR n) (aTR n) (bw n))
      (ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r ((r + s) % 2 ^ (bw n))
        0 r a bo gt 0 m z)
      = ks n t I u ((v + (2 ^ (bw n) - u)) % 2 ^ (bw n)) r ((r + s) % 2 ^ (bw n))
          0 0 a bo gt 0 m z := by
    rw [copyC_act (bw n) (aR n) (aTR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), ks_read_TR ht, ks_read_R ht,
      hrred, hbit u _ r _ 0 r 0, Nat.one_mul, Nat.xor_self, ks_write_TR ht]
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    e1, e2, e3, e4, e5, e6]

/-! ## Shift semantics

`v` halves and `r` doubles, both under `z`.  Each needs its own precondition:
`v` is even at this point, and `r` is below half its register. -/

theorem seg_shift {n t I u v r s a bo gt m z : Nat} (ht : t < 2 * n) (hz : z % 2 = 1)
    (hveven : v % 2 = 0) (hrtop : r < 2 ^ n) (hrred : r % 2 ^ (bw n) = r)
    (hvred : v % 2 ^ (bw n) = v) :
    actGates (segShift n t)
      (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u (v / 2) (2 * r) s 0 0 a bo gt 0 m z := by
  unfold segShift
  have hbit : ∀ x y r' s', bv (ks n t I x y r' s' 0 0 a bo gt 0 m z) (aZ n + t) = 1 := by
    intro x y r' s'
    rw [← readField_one, ks_read_Z ht, Nat.pow_one, hz]
  -- `v` is even, so the wrapped bit is clear.
  have hvz : bv (ks n t I u v r s 0 0 a bo gt 0 m z) (aV n) = 0 := by
    rw [ks_bit_V ht, hveven]
  have e1 : actGates (shiftRU (aV n) (bw n)) (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u (v / 2) r s 0 0 a bo gt 0 m z := by
    rw [shiftRU_eq (c := aZ n + t) (bw n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (hbit u v r s),
      shiftR_on (bw n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (hbit u v r s) hvz, ks_read_V ht, hvred,
      ks_write_V ht]
  -- `r` is below half its register, so its top bit is clear.
  have hrz : bv (ks n t I u (v / 2) r s 0 0 a bo gt 0 m z) (aR n + bw n - 1) = 0 := by
    have hoff : aR n + bw n - 1 = aR n + n := by simp only [bw]; omega
    rw [hoff, ← readField_one]
    have hnar : readField (ks n t I u (v / 2) r s 0 0 a bo gt 0 m z) (aR n) (bw n) = r := by
      rw [ks_read_R ht]; exact hrred
    have hbitr : readField (ks n t I u (v / 2) r s 0 0 a bo gt 0 m z) (aR n) (bw n)
        / 2 ^ n % 2 = readField (ks n t I u (v / 2) r s 0 0 a bo gt 0 m z) (aR n + n) 1 := by
      rw [readField_one, show bw n = n + 1 from rfl] at *
      exact readField_top _ (aR n) n
    rw [← hbitr, hnar, Nat.div_eq_of_lt hrtop]
  have e2 : actGates (shiftL (aZ n + t) (aR n) (bw n))
      (ks n t I u (v / 2) r s 0 0 a bo gt 0 m z)
      = ks n t I u (v / 2) (2 * r) s 0 0 a bo gt 0 m z := by
    rw [shiftL_on (bw n) (aR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (hbit u (v / 2) r s) hrz, ks_read_R ht, hrred,
      ks_write_R ht]
  rw [actGates_append, e1, e2]

/-! ## Control cleanup

`both odd` clears against the two retained bits because it is their
exclusive-nor.  The Euclidean invariant proves that exactly one of `r` and `s`
is even, allowing `bswap` to clear against the parity of the new `r`. -/

theorem seg_clear {n t I u v r s a bo gt m z : Nat} (ht : t < 2 * n)
    (hbo : bo % 2 = (1 + a % 2 + m % 2) % 2) (ha : a % 2 = (z % 2) * (r % 2)) :
    actGates (segClear n t)
      (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u v r s 0 0 0 0 gt 0 m z := by
  unfold segClear
  have e1 : actGates [RGate.cx (aA n) (aT n)] (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u v r s 0 0 a ((bo % 2 + a % 2) % 2) gt 0 m z := by
    show RGate.act (RGate.cx (aA n) (aT n)) _ = _
    rw [act_cx, ← readField_one, ks_read_T ht, Nat.pow_one, ← readField_one, ks_read_A ht,
      Nat.pow_one, ks_write_T ht]
  have e2 : actGates [RGate.cx (aM n + t) (aT n)]
      (ks n t I u v r s 0 0 a ((bo % 2 + a % 2) % 2) gt 0 m z)
      = ks n t I u v r s 0 0 a ((bo % 2 + a % 2 + m % 2) % 2) gt 0 m z := by
    show RGate.act (RGate.cx (aM n + t) (aT n)) _ = _
    rw [act_cx, ← readField_one, ks_read_T ht, Nat.pow_one, ← readField_one, ks_read_M ht,
      Nat.pow_one, ks_write_T ht]
    refine congrArg (fun q => ks n t I u v r s 0 0 a q gt 0 m z) ?_
    omega
  have e3 : actGates [RGate.x (aT n)]
      (ks n t I u v r s 0 0 a ((bo % 2 + a % 2 + m % 2) % 2) gt 0 m z)
      = ks n t I u v r s 0 0 a 0 gt 0 m z := by
    show RGate.act (RGate.x (aT n)) _ = _
    rw [act_x, ← readField_one, ks_read_T ht, Nat.pow_one, ks_write_T ht]
    refine congrArg (fun q => ks n t I u v r s 0 0 a q gt 0 m z) ?_
    omega
  have e4 : actGates [RGate.ccx (aZ n + t) (aR n) (aA n)]
      (ks n t I u v r s 0 0 a 0 gt 0 m z)
      = ks n t I u v r s 0 0 0 0 gt 0 m z := by
    show RGate.act (RGate.ccx (aZ n + t) (aR n) (aA n)) _ = _
    rw [act_ccx, ← readField_one, ks_read_A ht, Nat.pow_one, ← readField_one, ks_read_Z ht,
      Nat.pow_one, ks_bit_R ht, ks_write_A ht]
    refine congrArg (fun q => ks n t I u v r s 0 0 q 0 gt 0 m z) ?_
    rw [ha]
    have h1 : z % 2 = 0 ∨ z % 2 = 1 := by omega
    have h2 : r % 2 = 0 ∨ r % 2 = 1 := by omega
    cases h1 with
    | inl h => rw [h]; simp
    | inr h => cases h2 with
      | inl h' => rw [h, h']
      | inr h' => rw [h, h']
  rw [actGates_append,
    show [RGate.cx (aA n) (aT n), RGate.cx (aM n + t) (aT n), RGate.x (aT n)]
      = [RGate.cx (aA n) (aT n)] ++ [RGate.cx (aM n + t) (aT n)] ++ [RGate.x (aT n)] from rfl,
    actGates_append, actGates_append, e1, e2, e3, e4]

/-! ## Composition arithmetic -/

/-- Subtraction in a register is exact when it does not borrow. -/
theorem sub_exact {w x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ w) :
    (x + (2 ^ w - y)) % 2 ^ w = x - y := by
  have hpos := Nat.two_pow_pos w
  have he : x + (2 ^ w - y) = 2 ^ w + (x - y) := by omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- Doubling stays inside the register when the value is below half. -/
theorem two_mul_red {n x : Nat} (h : x < 2 ^ n) : 2 * x % 2 ^ (bw n) = 2 * x := by
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  exact Nat.mod_eq_of_lt (by omega)

/-- A value below `2 ^ n` is already reduced in a register of `n + 1` wires. -/
theorem red_of_lt {n x : Nat} (h : x < 2 ^ n) : x % 2 ^ (bw n) = x := by
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  exact Nat.mod_eq_of_lt (by omega)

/-! ## Boundary cases

With `both odd` clear the arithmetic is the identity, and with the termination
bit clear the shifts are. -/

theorem seg_arith_off {n t I u v r s a bo gt m z : Nat} (ht : t < 2 * n)
    (hured : u % 2 ^ (bw n) = u) (hvred : v % 2 ^ (bw n) = v)
    (hrred : r % 2 ^ (bw n) = r) (hsred : s % 2 ^ (bw n) = s) (hbo : bo % 2 = 0) :
    actGates (segArith n)
      (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u v r s 0 0 a bo gt 0 m z := by
  unfold segArith
  have hbit : bv (ks n t I u v r s 0 0 a bo gt 0 m z) (aT n) = 0 := by
    rw [← readField_one, ks_read_T ht, Nat.pow_one, hbo]
  have hid : ∀ src dst : Nat, (dst + bw n ≤ src ∨ src + bw n ≤ dst) →
      (aT n < dst ∨ dst + bw n ≤ aT n) →
      actGates (copyC (aT n) src dst (bw n)) (ks n t I u v r s 0 0 a bo gt 0 m z)
        = ks n t I u v r s 0 0 a bo gt 0 m z := by
    intro src dst h1 h2
    rw [copyC_act (bw n) src dst _ h1 h2, hbit, Nat.zero_mul, Nat.xor_zero,
      Reversible.writeField_read]
  have hpos := Nat.two_pow_pos (bw n)
  have e2 : actGates (subAt (bw n) (aTU n) (aV n) (aC n))
      (ks n t I u v r s 0 0 a bo gt 0 m z) = ks n t I u v r s 0 0 a bo gt 0 m z := by
    have hr0 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aTU n) (bw n) = 0 := by
      rw [ks_read_TU ht, Nat.zero_mod]
    have hr1 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aV n) (bw n) = v := by
      rw [ks_read_V ht]; exact hvred
    have hr2 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aC n) 1 = 0 := by
      rw [ks_read_C ht]
    rw [subAt_act (Wd := totalWidth n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw, totalWidth]; omega) hr0 hr1 hr2,
      Nat.sub_zero, Nat.add_mod_right, hvred, ks_write_V ht]
  have e5 : actGates (addAt (bw n) (aTR n) (aS n) (aC n))
      (ks n t I u v r s 0 0 a bo gt 0 m z) = ks n t I u v r s 0 0 a bo gt 0 m z := by
    have hr0 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aTR n) (bw n) = 0 := by
      rw [ks_read_TR ht, Nat.zero_mod]
    have hr1 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aS n) (bw n) = s := by
      rw [ks_read_S ht]; exact hsred
    have hr2 : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aC n) 1 = 0 := by
      rw [ks_read_C ht]
    rw [addAt_act (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) hr0 hr1 hr2, Nat.zero_add, hsred, ks_write_S ht]
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    hid (aU n) (aTU n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), e2, hid (aU n) (aTU n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    hid (aR n) (aTR n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), e5, hid (aR n) (aTR n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]

theorem seg_shift_off {n t I u v r s a bo gt m z : Nat} (ht : t < 2 * n) (hz : z % 2 = 0)
    (hv0 : v = 0) :
    actGates (segShift n t)
      (ks n t I u v r s 0 0 a bo gt 0 m z)
      = ks n t I u v r s 0 0 a bo gt 0 m z := by
  unfold segShift
  have hbit : bv (ks n t I u v r s 0 0 a bo gt 0 m z) (aZ n + t) = 0 := by
    rw [← readField_one, ks_read_Z ht, Nat.pow_one, hz]
  have hvfield : readField (ks n t I u v r s 0 0 a bo gt 0 m z) (aV n) (bw n) = 0 := by
    rw [ks_read_V ht, hv0, Nat.zero_mod]
  rw [actGates_append, shiftRU_zero (bw n) (aV n) _ hvfield,
    shiftL_off (bw n) (aR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) hbit]

end VQ.Curve.PointAddition.Arithmetic.Inv
