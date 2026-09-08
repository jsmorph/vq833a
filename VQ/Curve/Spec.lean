/-
The secp256k1 point addition specification.

The secp256k1 point-addition specification fixes the prime, curve equation,
addition formula, and input domains used by correctness theorems.

The two domains differ on purpose.  `Representable` is syntactic and holds of
any pair of register values below the prime.  It is the domain over which a
circuit must return its workspace to zero.  `Addable` is smaller, requiring
both points to lie on the curve with distinct x-coordinates, and it is the
domain over which the output must be the sum.  Affine coordinates cannot
represent the point at infinity, so the formula is undefined when the
x-coordinates agree, which covers both the doubling case and the case where the
sum is the identity.  A specification that used one domain for both clauses
would permit dirty workspace on the exceptional inputs.  Dirty workspace on a
small-amplitude branch entangles the workspace with the data register.

`VQ.Reversible.AddsPoint` does not reach the full `Representable` domain on its
workspace clause: it excludes the inputs where the x-coordinates agree and the
inputs `Recoverable` rejects, because the published in-place construction leaves
the slope register dirty on both.  `AddsPointTotal` is the claim without either
exclusion.  It states the stronger cleanup requirement for constructions that
handle both exceptional classes.
-/
import VQ.Curve.Field

namespace VQ
namespace Curve

/-- Both coordinates name a field element.  A 256-bit register holds values up
to `2 ^ 256 - 1`, which exceeds the prime, so this is a real restriction. -/
def Representable (x y : Nat) : Bool := decide (x < p) && decide (y < p)

/-- `y ^ 2 = x ^ 3 + 7`, the secp256k1 curve equation.  Every operation
reduces, so this is correct on unreduced arguments as well. -/
def OnCurve (x y : Nat) : Bool := mul y y == add (mul (mul x x) x) 7

/-- The domain of the addition formula: two representable curve points with
distinct x-coordinates. -/
def Addable (x₁ y₁ x₂ y₂ : Nat) : Bool :=
  Representable x₁ y₁ && Representable x₂ y₂ &&
    OnCurve x₁ y₁ && OnCurve x₂ y₂ && (x₁ != x₂)

/-- The affine sum of two points.  Total as a function.  It is the curve sum
exactly on `Addable`. -/
def addPoint (x₁ y₁ x₂ y₂ : Nat) : Nat × Nat :=
  let l := mul (sub y₁ y₂) (inv (sub x₁ x₂))
  let x₃ := sub (sub (mul l l) x₁) x₂
  (x₃, sub (mul l (sub x₁ x₃)) y₁)

/-- The sum's x-coordinate differs from the offset's.

The in-place affine construction needs this and `Addable` does not imply it.
Algorithm 1 of Roetteler, Naehrig, Svore, and Lauter recovers the slope from the
result by adding `-P₂`, using

    (y₁ - y₂) / (x₁ - x₂) = -(y₃ + y₂) / (x₃ - x₂),

and that recovery divides by `x₃ - x₂`.  Where it is zero the slope is not
uncomputed and the workspace is left holding it.  `x₃ = x₂` means `P₃ = ±P₂`,
and `P₃ = P₂` forces `P₁` to be the point at infinity, so the case is exactly
`P₁ = -2 P₂`.  Measured at the secp256k1 prime on `P₁ = -2G` and `P₂ = G`: both
output coordinates come out right and the slope register is not cleared. -/
def Recoverable (x₁ y₁ x₂ y₂ : Nat) : Bool := (addPoint x₁ y₁ x₂ y₂).1 != x₂

theorem add_lt (a b : Nat) : add a b < p := Nat.mod_lt _ p_pos

theorem sub_lt (a b : Nat) : sub a b < p := Nat.mod_lt _ p_pos

theorem mul_lt (a b : Nat) : mul a b < p := Nat.mod_lt _ p_pos

theorem powMod_lt (a e : Nat) : powMod a e < p := Nat.mod_lt _ p_pos

theorem inv_lt (a : Nat) : inv a < p := powMod_lt _ _

/-- Every operation in `addPoint` reduces its result, so the output is
representable for every input.  Composed claims may use this range result at
each subsequent step. -/
theorem representable_addPoint (x₁ y₁ x₂ y₂ : Nat) :
    Representable (addPoint x₁ y₁ x₂ y₂).1 (addPoint x₁ y₁ x₂ y₂).2 = true := by
  simp [Representable, addPoint, sub_lt]

/-! ## The arithmetic of the in-place assembly

Algorithm 1 of Roetteler, Naehrig, Svore, and Lauter computes the affine sum in
place using four identities.  `VQ/` cannot prove them: each needs `inv` to
invert, which is Fermat's little theorem and needs `p` prime, and the additive
one needs a ring normal form that core Lean has no tactic for.  So the assembly
takes the bundle as a hypothesis and `VQBridge.Curve.alg1Law` discharges it from
`Nat.Prime p`, which `VQBridge.PrimeCert` proves by a Pratt certificate.

The Mathlib-dependent bridge discharges the arithmetic laws while this module
retains an executable core specification. -/

/-- The slope the affine formula uses, with the quantum point first.  This is
the `l` inside `addPoint x y ax ay`. -/
def slope (x y ax ay : Nat) : Nat := mul (sub y ay) (inv (sub x ax))

theorem slope_lt (x y ax ay : Nat) : slope x y ax ay < p := mul_lt _ _

/-- Both output coordinates are reduced. -/
theorem representable_addPoint_fst (x y ax ay : Nat) : (addPoint x y ax ay).1 < p := by
  have h := representable_addPoint x y ax ay
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem representable_addPoint_snd (x y ax ay : Nat) : (addPoint x y ax ay).2 < p := by
  have h := representable_addPoint x y ax ay
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- `addPoint`'s own slope is `slope`, so its coordinates read in these terms. -/
theorem addPoint_fst (x y ax ay : Nat) :
    (addPoint x y ax ay).1 = sub (sub (mul (slope x y ax ay) (slope x y ax ay)) x) ax := rfl

theorem addPoint_snd (x y ax ay : Nat) :
    (addPoint x y ax ay).2
      = sub (mul (slope x y ax ay) (sub x (addPoint x y ax ay).1)) y := rfl

/-- The two identities the in-place assembly needs and `VQ/` cannot prove.

Both are additive rearrangements of the affine formula, which core Lean has no
normal-form tactic for, and `yShift` also needs the inverse to cancel.  The other
two identities the assembly uses — that the y register clears at step 5 and the
slope register clears at step 13 — follow from these and `InverseLaw`, and are
proved below rather than assumed. -/
structure Algebra (ax ay x y : Nat) : Prop where
  /-- Step 9: subtracting the square and adding three times the offset leaves
  `ax - x₃` in the x register. -/
  xShift : add (sub (sub x ax) (mul (slope x y ax ay) (slope x y ax ay))) (mul 3 ax)
             = sub ax (addPoint x y ax ay).1
  /-- Step 11: the slope times `ax - x₃` is `y₃ + ay`. -/
  yShift : mul (slope x y ax ay) (sub ax (addPoint x y ax ay).1)
             = add (addPoint x y ax ay).2 ay

/-- The algebra used before the slope-recovery step. -/
def Alg1PrefixLaw : Prop :=
  ∀ ax ay x y, ax < p → ay < p → x < p → y < p →
    x ≠ ax → Algebra ax ay x y

/-- The algebra over the ordinary recovery domain. -/
def Alg1Law : Prop :=
  ∀ ax ay x y, ax < p → ay < p → x < p → y < p →
    x ≠ ax → (addPoint x y ax ay).1 ≠ ax → Algebra ax ay x y

theorem Alg1PrefixLaw.toAlg1Law (h : Alg1PrefixLaw) : Alg1Law := by
  intro ax ay x y hax hay hx hy hne _
  exact h ax ay x y hax hay hx hy hne

/-- Step 5 clears the y register.  The slope times the reduced x-difference
is the reduced y-difference, because the slope is their quotient.  This needs
only the inverse law. -/
theorem slope_cancel (hlaw : InverseLaw) {ax ay x y : Nat}
    (hax : ax < p) (hx : x < p) (hne : x ≠ ax) :
    mul (slope x y ax ay) (sub x ax) = sub y ay := by
  show mul (mul (sub y ay) (inv (sub x ax))) (sub x ax) = sub y ay
  exact mul_inv_cancel hlaw (sub_lt _ _) (sub_lt _ _)
    (sub_ne_zero_of_ne hx hax hne)

/-- Step 13 recovers the slope from the result by dividing `y₃ + ay` by
`ax - x₃`, then clears the slope register.  The hypothesis `x₃ ≠ ax` ensures
that the denominator has an inverse. -/
theorem slope_recover (hlaw : InverseLaw) {ax ay x y : Nat}
    (halg : Algebra ax ay x y) (hax : ax < p) (hrec : (addPoint x y ax ay).1 ≠ ax) :
    mul (inv (sub ax (addPoint x y ax ay).1)) (add (addPoint x y ax ay).2 ay)
      = slope x y ax ay := by
  rw [← halg.yShift]
  exact inv_mul_cancel hlaw (slope_lt _ _ _ _) (sub_lt _ _)
    (sub_ne_zero_of_ne hax (representable_addPoint_fst x y ax ay) (Ne.symm hrec))

/-- Subtracting a fixed exceptional slope when the recovery denominator is
zero makes the ordinary recovery identity valid on both denominator cases. -/
theorem slope_recover_zero_correction (hlaw : InverseLaw) {ax ay x y e : Nat}
    (halg : Algebra ax ay x y) (hax : ax < p) (he : e < p)
    (hexception : sub ax (addPoint x y ax ay).1 = 0 → slope x y ax ay = e) :
    mul (inv (sub ax (addPoint x y ax ay).1)) (add (addPoint x y ax ay).2 ay) =
      if sub ax (addPoint x y ax ay).1 = 0 then
        add (slope x y ax ay) (neg e)
      else slope x y ax ay := by
  by_cases hzero : sub ax (addPoint x y ax ay).1 = 0
  · have hy : add (addPoint x y ax ay).2 ay = 0 := by
      rw [← halg.yShift, hzero, mul_zero]
    have hslope : add (slope x y ax ay) (neg e) = 0 := by
      change (slope x y ax ay + neg e) % p = 0
      rw [add_neg_eq_sub he, hexception hzero, sub_self he]
    rw [if_pos hzero, hzero, hy, Curve.inv_zero, mul_zero, hslope]
  · have hrec : (addPoint x y ax ay).1 ≠ ax := by
      intro heq
      apply hzero
      rw [heq, sub_self hax]
    rw [if_neg hzero]
    exact slope_recover hlaw halg hax hrec

end Curve
end VQ
