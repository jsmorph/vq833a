/-
Specifications for secp256k1 inversion and point addition.
The declarations remain in the VQ.Reversible namespace for source compatibility.
-/
import VQ.Reversible.ArithmeticSpec
import VQ.Curve.Spec

namespace VQ
namespace Reversible

/-- Target x, target y, and a workspace.  The offset is classical, so it is a
parameter of the generator rather than a field. -/
def curveLayout (ws : Nat) : Layout := [256, 256, ws]

/-- The circuit overwrites the target with its sum with the classical point
`(ax, ay)` on secp256k1, over `curveLayout ws`.

The value clause uses `VQ.Curve.Addable`, where the affine formula is defined.
The workspace clause uses the larger `VQ.Curve.Representable` domain.  Published
in-place affine constructions require the narrower domain stated by `AddsPoint`.
-/
def AddsPointTotal (ax ay ws : Nat) (r : RCircuit) : Prop :=
  ∀ x y i, i < 2 ^ (curveLayout ws).width →
    (curveLayout ws).read i 0 = x →
    (curveLayout ws).read i 1 = y →
    (curveLayout ws).read i 2 = 0 →
    (Curve.Addable x y ax ay = true →
        act r i = (curveLayout ws).write ((curveLayout ws).write i 0
          (Curve.addPoint x y ax ay).1) 1 (Curve.addPoint x y ax ay).2) ∧
      (Curve.Representable x y = true → (curveLayout ws).read (act r i) 2 = 0)

/-- The circuit overwrites the target with its sum with the classical point
`(ax, ay)` on secp256k1, over `curveLayout ws`, on the inputs the in-place affine
construction reaches.

`AddsPointTotal` uses the same clauses without a `Recoverable` guard.  Algorithm
1 of Roetteler, Naehrig, Svore, and Lauter leaves the slope in the workspace
when `P₁ = -2 P₂`.  The value clause equates complete basis indices, so this
residual slope also violates that clause.  `Curve.Recoverable` excludes the
exceptional input.  A construction handling the exceptional branch satisfies
`AddsPointTotal`, and `addsPointTotal_addsPoint` derives the guarded claim.

The workspace clause carries two exclusions.  `Recoverable` is the
`P₁ = -2 P₂` case described above.  `x ≠ ax` is the other: where the two
x-coordinates agree, the construction's first inversion is of zero, the slope is
never formed, and the register it would have occupied is not cleared either.
`Addable` excludes that case from the value clause.  The workspace clause must
state it separately because `Representable` includes such inputs. -/
def AddsPoint (ax ay ws : Nat) (r : RCircuit) : Prop :=
  ∀ x y i, i < 2 ^ (curveLayout ws).width →
    (curveLayout ws).read i 0 = x →
    (curveLayout ws).read i 1 = y →
    (curveLayout ws).read i 2 = 0 →
    (Curve.Addable x y ax ay = true → Curve.Recoverable x y ax ay = true →
        act r i = (curveLayout ws).write ((curveLayout ws).write i 0
          (Curve.addPoint x y ax ay).1) 1 (Curve.addPoint x y ax ay).2) ∧
      (Curve.Representable x y = true → x ≠ ax → Curve.Recoverable x y ax ay = true →
        (curveLayout ws).read (act r i) 2 = 0)

/-- The stronger claim implies the weaker one. -/
theorem addsPointTotal_addsPoint {ax ay ws : Nat} {r : RCircuit}
    (h : AddsPointTotal ax ay ws r) : AddsPoint ax ay ws r := by
  intro x y i hi h₀ h₁ h₂
  exact ⟨fun ha _ => (h x y i hi h₀ h₁ h₂).1 ha,
         fun hr _ _ => (h x y i hi h₀ h₁ h₂).2 hr⟩

theorem p_lt_two_pow : Curve.p < 2 ^ 256 := by decide

/-- `AddsPoint` places the sum coordinates in fields zero and one.  Field two
remains zero.  The result uses the `Addable` and `Recoverable` preconditions. -/
theorem addsPoint_read {ax ay ws : Nat} {r : RCircuit} (h : AddsPoint ax ay ws r)
    {x y i : Nat} (hi : i < 2 ^ (curveLayout ws).width)
    (h₀ : (curveLayout ws).read i 0 = x)
    (h₁ : (curveLayout ws).read i 1 = y)
    (h₂ : (curveLayout ws).read i 2 = 0)
    (ha : Curve.Addable x y ax ay = true)
    (hg : Curve.Recoverable x y ax ay = true) :
    (curveLayout ws).read (act r i) 0 = (Curve.addPoint x y ax ay).1 ∧
      (curveLayout ws).read (act r i) 1 = (Curve.addPoint x y ax ay).2 ∧
      (curveLayout ws).read (act r i) 2 = 0 := by
  have hrep := Curve.representable_addPoint x y ax ay
  simp only [Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] at hrep
  have hx : (Curve.addPoint x y ax ay).1 < 2 ^ (curveLayout ws).size 0 :=
    Nat.lt_trans hrep.1 p_lt_two_pow
  have hy : (Curve.addPoint x y ax ay).2 < 2 ^ (curveLayout ws).size 1 :=
    Nat.lt_trans hrep.2 p_lt_two_pow
  have heq := (h x y i hi h₀ h₁ h₂).1 ha hg
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), Layout.read_write_self hx]
  · rw [heq, Layout.read_write_self hy]
  · rw [heq, Layout.read_write_ne (by decide), Layout.read_write_ne (by decide), h₂]

/-! ## Field inversion

Inversion is stated at the curve prime rather than at a modulus parameter.
`VQ.Curve.inv` is `a ^ (p - 2) % p`, `VQ.Curve.powMod_eq` proves that, and
`VQBridge.Curve` proves it is Mathlib's field inverse under the primality
hypothesis the bridge carries.  So the value already has its meaning
established, and no primality hypothesis enters `VQ/`.

A modulus-parametric equation using `a ^ (m - 2) % m` fails to specify an
inverse when `m` is composite.  An existential value `v` satisfying
`a * v % m = 1` applies to every invertible residue, but it does not fix the
workspace through an equation between basis indices.  Such a specification
would require a workspace clause.

A modulus-parametric version would replace `Curve.p` with `m`, replace
`Curve.inv` with modular exponentiation, and require primality wherever the
result is identified as an inverse. -/

/-- The circuit writes the inverse of the first field in the secp256k1 base
field into the second, over `unaryLayout n ws`.

The circuit preserves the input for later assembly steps and writes the inverse
to a clear output field.  One equation between basis indices fixes the input,
output, and workspace together.

`Curve.inv 0 = 0`, as computed by `a ^ (p - 2)`, so the specification covers
zero and every other representable input.  The affine-addition caller supplies
the nonzero condition required to use the result as a multiplicative inverse. -/
def InvertsField (ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (unaryLayout n ws).width →
    (unaryLayout n ws).read i 0 = a →
    (unaryLayout n ws).read i 1 = 0 →
    (unaryLayout n ws).read i 2 = 0 →
    Curve.p ≤ 2 ^ n → a < Curve.p →
      act r i = (unaryLayout n ws).write i 1 (Curve.inv a)

/-- `InvertsField` preserves the input field.  The output field contains its
inverse.  The workspace remains zero. -/
theorem invertsField_read {ws n : Nat} {r : RCircuit} (h : InvertsField ws n r)
    {a i : Nat} (hi : i < 2 ^ (unaryLayout n ws).width)
    (h₀ : (unaryLayout n ws).read i 0 = a)
    (h₁ : (unaryLayout n ws).read i 1 = 0)
    (h₂ : (unaryLayout n ws).read i 2 = 0)
    (hp : Curve.p ≤ 2 ^ n) (ha : a < Curve.p) :
    (unaryLayout n ws).read (act r i) 0 = a ∧
      (unaryLayout n ws).read (act r i) 1 = Curve.inv a ∧
      (unaryLayout n ws).read (act r i) 2 = 0 := by
  have hv : Curve.inv a < 2 ^ (unaryLayout n ws).size 1 :=
    Nat.lt_of_lt_of_le (Curve.inv_lt a) hp
  have heq := h a i hi h₀ h₁ h₂ hp ha
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hv]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

/-- The circuit writes `c` times the inverse of the first field into the second,
over `unaryLayout n ws`, with `c` a classical constant of the claim.

`InvertsField` above is the case `c = 1`, and `invertsFieldScaled_one` is the
equivalence.  The scale exists because the published inversion does not compute
`Curve.inv`.  Roetteler, Naehrig, Svore, and Lauter invert with Kaliski's binary
extended Euclidean algorithm, which produces the *Montgomery* inverse
`a⁻¹ · 2ⁿ mod p`.  Häner, Jaques, Naehrig, Roetteler, and Soeken state it exactly
in their section 4.2, where the `2n` rounds leave a pseudo-inverse
`a⁻¹ · 2^(k - n)` and a counter holding `2n - k`, and `2n - k` controlled
doublings correct it.  A circuit computing that value satisfies
`InvertsFieldScaled` with `c = 2 ^ 256 % p`.

The scale is a classical constant, so it costs no qubit and no gate, exactly as
the modulus and the constant operand of `AddsConstMod` do.  The claim reads
register values as natural numbers and introduces no separate representation.
The scale therefore supplies the complete
the difference.

Two circuits with different scales are not comparable by their resource figures
alone, since one may be doing work the other leaves to its caller.  The
comparison that survives is at the assembly, where `AddsPoint` is stated in
ordinary register values whatever its components do inside. -/
def InvertsFieldScaled (c ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (unaryLayout n ws).width →
    (unaryLayout n ws).read i 0 = a →
    (unaryLayout n ws).read i 1 = 0 →
    (unaryLayout n ws).read i 2 = 0 →
    Curve.p ≤ 2 ^ n → a < Curve.p →
      act r i = (unaryLayout n ws).write i 1 (Curve.inv a * c % Curve.p)

/-- Scale one is the unscaled claim. -/
theorem invertsFieldScaled_one {ws n : Nat} {r : RCircuit} :
    InvertsFieldScaled 1 ws n r ↔ InvertsField ws n r := by
  constructor
  · intro h a i hi h₀ h₁ h₂ hp ha
    have := h a i hi h₀ h₁ h₂ hp ha
    rwa [Nat.mul_one, Nat.mod_eq_of_lt (Curve.inv_lt a)] at this
  · intro h a i hi h₀ h₁ h₂ hp ha
    have := h a i hi h₀ h₁ h₂ hp ha
    rwa [Nat.mul_one, Nat.mod_eq_of_lt (Curve.inv_lt a)]

/-- `InvertsFieldScaled` preserves the input field.  The output field contains
the scaled inverse.  The workspace remains zero. -/
theorem invertsFieldScaled_read {c ws n : Nat} {r : RCircuit}
    (h : InvertsFieldScaled c ws n r)
    {a i : Nat} (hi : i < 2 ^ (unaryLayout n ws).width)
    (h₀ : (unaryLayout n ws).read i 0 = a)
    (h₁ : (unaryLayout n ws).read i 1 = 0)
    (h₂ : (unaryLayout n ws).read i 2 = 0)
    (hp : Curve.p ≤ 2 ^ n) (ha : a < Curve.p) :
    (unaryLayout n ws).read (act r i) 0 = a ∧
      (unaryLayout n ws).read (act r i) 1 = Curve.inv a * c % Curve.p ∧
      (unaryLayout n ws).read (act r i) 2 = 0 := by
  have hv : Curve.inv a * c % Curve.p < 2 ^ (unaryLayout n ws).size 1 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ Curve.p_pos) hp
  have heq := h a i hi h₀ h₁ h₂ hp ha
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hv]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

end Reversible
end VQ
