/-
`VQ.Curve` defines the secp256k1 prime, curve equation, and affine addition over
`Nat`.  This module proves that
those formulas agree with Mathlib's elliptic-curve definitions.

`VQBridge.Prime.prime_p` proves `Nat.Prime p` from a Pratt certificate.  The
agreement theorems use that result to discharge their primality hypotheses.
-/
import VQ.Curve.Spec
import VQMathlib.Curve.PrimeCert
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic

namespace VQBridge
namespace Curve

open VQ.Curve WeierstrassCurve

/-- secp256k1 as a Weierstrass curve: `y^2 = x^3 + 7`. -/
def W : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, 0, 7⟩

instance : NeZero p := ⟨by decide⟩

/-- Injectivity of `Nat.cast` below the prime transfers a `ZMod p` equation to
the corresponding `Nat` equation in `VQ.Curve`. -/
theorem natCast_inj_of_lt {u v : Nat} (hu : u < p) (hv : v < p)
    (h : (u : ZMod p) = (v : ZMod p)) : u = v := by
  have hv' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hu, ZMod.val_cast_of_lt hv] at hv'

theorem cast_add (a b : Nat) : ((add a b : Nat) : ZMod p) = (a : ZMod p) + b := by
  rw [add, ZMod.natCast_mod]
  push_cast
  ring

theorem cast_mul (a b : Nat) : ((mul a b : Nat) : ZMod p) = (a : ZMod p) * b := by
  rw [mul, ZMod.natCast_mod]
  push_cast
  ring

/-- Truncated subtraction is real subtraction here because `b % p ≤ p`, and
`p` casts to zero. -/
theorem cast_sub (a b : Nat) : ((sub a b : Nat) : ZMod p) = (a : ZMod p) - b := by
  rw [sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ p_pos)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem cast_powMod (a e : Nat) : ((powMod a e : Nat) : ZMod p) = (a : ZMod p) ^ e := by
  rw [powMod_eq, ZMod.natCast_mod]
  push_cast
  ring

-- The certified secp256k1 primality theorem resolves the instance below.
example : Nat.Prime p := VQBridge.Prime.prime_p

/-- Fermat's little theorem gives the field inverse.  `inv 0` is `0` on both
sides, which is the convention `ZMod` already uses. -/
theorem cast_inv (a : Nat) : ((inv a : Nat) : ZMod p) = ((a : ZMod p))⁻¹ := by
  rcases eq_or_ne (a : ZMod p) 0 with h | h
  · rw [inv, cast_powMod, h, zero_pow (by decide), _root_.inv_zero]
  · have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    have hone : (a : ZMod p) ^ (p - 1) = 1 := by
      have hf := FiniteField.pow_card_sub_one_eq_one (a : ZMod p) h
      rwa [hcard] at hf
    have hp : p - 2 + 1 = p - 1 := by decide
    rw [inv, cast_powMod]
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, hp, hone]

/-- `VQ.Curve.InverseLaw` for the certified secp256k1 prime.  The point-addition
assembly accepts this law as an argument because `VQ/` excludes Mathlib.
`VQBridge.Prime.prime_p` and its `Fact` instance supply `Nat.Prime p`. -/
theorem inverseLaw : VQ.Curve.InverseLaw := by
  intro a ha ha0
  refine natCast_inj_of_lt (Nat.mod_lt _ p_pos) (by decide) ?_
  have hne : (a : ZMod p) ≠ 0 := by
    intro h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_cast_of_lt ha, ZMod.val_zero] at hval
    exact ha0 hval
  rw [cast_mul, cast_inv, Nat.cast_one, inv_mul_cancel₀ hne]

theorem onCurve_iff (x y : Nat) :
    OnCurve x y = true ↔ W.toAffine.Equation (x : ZMod p) (y : ZMod p) := by
  rw [OnCurve, Affine.equation_iff, beq_iff_eq]
  simp only [W]
  constructor
  · intro h
    have hc := congrArg (fun n : Nat => (n : ZMod p)) h
    simp only [cast_mul, cast_add] at hc
    push_cast at hc ⊢
    linear_combination hc
  · intro h
    refine natCast_inj_of_lt (mul_lt _ _) (add_lt _ _) ?_
    simp only [cast_mul, cast_add]
    push_cast at h ⊢
    linear_combination h

/-- The agreement theorem: `VQ.Curve.addPoint` computes the coordinates
Mathlib's affine addition formula gives.

Stated at the level of `addX` and `addY` rather than of `Affine.Point.add`,
because those are the formulas the group operation is defined by and they carry
no case split. -/
theorem addPoint_eq {x₁ y₁ x₂ y₂ : Nat} (hx : (x₁ : ZMod p) ≠ (x₂ : ZMod p)) :
    (((addPoint x₁ y₁ x₂ y₂).1 : Nat) : ZMod p)
        = W.toAffine.addX (x₁ : ZMod p) (x₂ : ZMod p)
            (W.toAffine.slope (x₁ : ZMod p) (x₂ : ZMod p) (y₁ : ZMod p) (y₂ : ZMod p))
      ∧ (((addPoint x₁ y₁ x₂ y₂).2 : Nat) : ZMod p)
        = W.toAffine.addY (x₁ : ZMod p) (x₂ : ZMod p) (y₁ : ZMod p)
            (W.toAffine.slope (x₁ : ZMod p) (x₂ : ZMod p) (y₁ : ZMod p) (y₂ : ZMod p)) := by
  have hsub : (x₁ : ZMod p) - (x₂ : ZMod p) ≠ 0 := sub_ne_zero.2 hx
  rw [Affine.slope_of_X_ne hx]
  simp only [addPoint, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, W,
    cast_sub, cast_mul, cast_inv, div_eq_mul_inv]
  constructor
  · ring
  · ring

/-! ## In-place point-addition identities

`VQ.Curve.Alg1PrefixLaw` bundles the field identities used before slope
recovery in Algorithm 1.  The proof uses `field_simp`, `ring`, the certified
primality theorem, and the nonzero input-difference hypothesis. -/

theorem cast_slope (x y ax ay : Nat) :
    ((slope x y ax ay : Nat) : ZMod p)
      = ((y : ZMod p) - (ay : ZMod p)) * ((x : ZMod p) - (ax : ZMod p))⁻¹ := by
  rw [slope, cast_mul, cast_sub, cast_inv, cast_sub]

theorem cast_addPoint_fst (x y ax ay : Nat) :
    (((addPoint x y ax ay).1 : Nat) : ZMod p)
      = ((slope x y ax ay : Nat) : ZMod p) ^ 2 - (x : ZMod p) - (ax : ZMod p) := by
  rw [addPoint_fst, cast_sub, cast_sub, cast_mul]
  ring

theorem cast_addPoint_snd (x y ax ay : Nat) :
    (((addPoint x y ax ay).2 : Nat) : ZMod p)
      = ((slope x y ax ay : Nat) : ZMod p)
          * ((x : ZMod p) - (((addPoint x y ax ay).1 : Nat) : ZMod p)) - (y : ZMod p) := by
  rw [addPoint_snd, cast_sub, cast_mul, cast_sub]

/-- `VQ.Curve.Alg1PrefixLaw` for secp256k1. -/
theorem alg1PrefixLaw : VQ.Curve.Alg1PrefixLaw := by
  intro ax ay x y hax hay hx hy hne
  have hd1 : (x : ZMod p) - (ax : ZMod p) ≠ 0 :=
    sub_ne_zero.2 (fun h => hne (natCast_inj_of_lt hx hax h))
  refine ⟨?_, ?_⟩
  · refine natCast_inj_of_lt (add_lt _ _) (sub_lt _ _) ?_
    rw [cast_add, cast_sub, cast_sub, cast_sub, cast_mul, cast_mul, cast_addPoint_fst]
    push_cast
    ring
  · refine natCast_inj_of_lt (mul_lt _ _) (add_lt _ _) ?_
    rw [cast_mul, cast_sub, cast_add, cast_addPoint_snd, cast_addPoint_fst, cast_slope]
    field_simp
    ring

/-- `VQ.Curve.Alg1Law` for the ordinary recovery domain. -/
theorem alg1Law : VQ.Curve.Alg1Law := alg1PrefixLaw.toAlg1Law

end Curve
end VQBridge
