import VQ.Curve.PointAddition.Arithmetic.Inv.Counts
import VQ.Curve.ReversibleSpec
import VQMathlib.Curve.Laws

/-!
# Kaliski inversion circuit

This reversible circuit implements Kaliski's binary extended Euclidean
inversion in the secp256k1 base field.

`VQMathlib.Curve.Laws` supplies two Mathlib-dependent facts about the prime.
`VQBridge.Curve.inverseLaw` proves that `inv a = a ^ (p - 2)` inverts every
nonzero field value.  `VQBridge.Prime.prime_p` supplies the primality theorem
used by the local `PrimeFactor` proof.  Importing `VQMathlib` places Mathlib's
curve theorems on this module's dependency path.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible

/-- The prime's irreducibility, in the form the round's extraction needs. -/
theorem primeFactor : PrimeFactor modulus := by
  intro a b hab
  have hp : Nat.Prime VQ.Curve.p := VQBridge.Prime.prime_p
  have hdvd : a ∣ VQ.Curve.p := ⟨b, hab.symm⟩
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp a hdvd) with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [h] at hab
    have hpos : 0 < VQ.Curve.p := VQ.Curve.p_pos
    have : VQ.Curve.p * b = VQ.Curve.p * 1 := by rw [Nat.mul_one]; exact hab
    exact Nat.eq_of_mul_eq_mul_left hpos this

/-- The claim.  The circuit writes the inverse of the input field into the
output field, at every width the prime fits in. -/
theorem inverts : ∀ n : Nat,
    VQ.Reversible.InvertsField (13 + n * 10) n (VQ.Curve.PointAddition.Arithmetic.Inv.gen n) := by
  intro n a i _ h0 h1 h2 hpn ha
  have hws : 13 + n * 10 = wsWidth n := by
    calc
      13 + n * 10 = n * 10 + 13 := Nat.add_comm _ _
      _ = 10 * n + 13 := by rw [Nat.mul_comm n 10]
      _ = wsWidth n := rfl
  rw [hws] at h2
  have hn : 0 < n := by
    have h2n : (2 : Nat) ^ 0 ≤ 2 ^ n → 1 ≤ 2 ^ n := by simp
    have hp1 : 1 < VQ.Curve.p := by decide
    cases Nat.eq_zero_or_pos n with
    | inr h => exact h
    | inl h =>
      exfalso
      rw [h] at hpn
      simp at hpn
      omega
  have e0 : readField i 0 n = a := h0
  have e1 : readField i n n = 0 := by
    have : readField i (n + 0) n = 0 := h1
    rwa [Nat.add_zero] at this
  have e2 : readField i (2 * n) (wsWidth n) = 0 := by
    have : readField i (n + (n + 0)) (wsWidth n) = 0 := h2
    rwa [show n + (n + 0) = 2 * n from by omega] at this
  show act (VQ.Curve.PointAddition.Arithmetic.Inv.gen n) i = writeField i (n + 0) n (VQ.Curve.inv a)
  rw [Nat.add_zero]
  exact gen_act hn hpn VQBridge.Curve.inverseLaw primeFactor ha e0 e1 e2

/-! ## Well-formedness and resources

Every gate lies below the declared width, so the compiled circuit touches at
most `14 n + 11` wires.  The Toffoli count is exact rather than bounded, and the
gate count follows from it: a Toffoli compiles to three primitives and every
other gate to one. -/

theorem all_reverse {gs : List RGate} {w : Nat} (h : gs.all (RGate.wellFormed w) = true) :
    gs.reverse.all (RGate.wellFormed w) = true :=
  List.all_eq_true.mpr fun g hg => List.all_eq_true.mp h g (List.mem_reverse.mp hg)

theorem wf : ∀ n : Nat, VQ.Reversible.RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.Inv.gen n) = true := by
  intro n
  cases Nat.eq_zero_or_pos n with
  | inl h => subst h; rfl
  | inr hn =>
    show (fwdGates n ++ copyC (aNZ n) (aTU n) n n ++ (fwdGates n).reverse).all
      (RGate.wellFormed (totalWidth n)) = true
    have hf := fwdGates_wf hn
    have hcp : (copyC (aNZ n) (aTU n) n n).all (RGate.wellFormed (totalWidth n)) = true :=
      copyC_wf n (aTU n) n (totalWidth n)
        (by simp only [aU, aV, aR, aS, aTU, bw]; omega)
        (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw]; omega)
        (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw]; omega)
        (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw, totalWidth]; omega)
        (by simp only [aU, aV, aR, aS, aTU, bw, totalWidth]; omega)
        (by simp only [totalWidth]; omega)
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨⟨hf, hcp⟩, all_reverse hf⟩

/-- The Toffoli bound derived from `VQ.Curve.PointAddition.Arithmetic.Inv.gen_ccx`. -/
theorem toffoli_le : ∀ n : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.gen n)) ≤ 16 + n * (117 + n * 88) := by
  intro n
  rw [VQ.Reversible.toffoliCount_compile, gen_ccx, Nat.mul_add]
  have h : 88 * n * n = n * (n * 88) := by
    rw [Nat.mul_comm 88 n, Nat.mul_comm n (n * 88)]
  omega

/-- The wire count.  Nothing reaches past the declared width. -/
theorem wires_le : ∀ n : Nat,
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.gen n)) ≤ 13 + n * 12 := by
  intro n
  have h := VQ.Reversible.usedWires_compile_le_width (wf n)
  have hw : (VQ.Curve.PointAddition.Arithmetic.Inv.gen n).width = totalWidth n := rfl
  rw [hw] at h
  simpa [totalWidth, Nat.mul_comm, Nat.add_comm] using h

/-- The gate count.  A Toffoli compiles to three primitives and every other
gate to one, so the compiled length is the reversible length plus twice the
Toffoli count.  At `n = 256` the bound is `29786476`. -/
theorem gates_le : ∀ n : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.gen n)) ≤ 108 + n * (641 + n * 452) := by
  intro n
  rw [VQ.Reversible.gateCount_compile, gen_ccx]
  have hl := gen_len n
  have h1 : 88 * n * n = 88 * (n * n) := Nat.mul_assoc 88 n n
  have h2 : 276 * n * n = 276 * (n * n) := Nat.mul_assoc 276 n n
  have hr : n * (641 + n * 452) = 641 * n + 452 * (n * n) := by
    rw [Nat.mul_add, Nat.mul_comm n 641, Nat.mul_comm n (n * 452), Nat.mul_comm n 452,
      Nat.mul_assoc]
  omega

end VQ.Curve.PointAddition.Arithmetic.Inv
