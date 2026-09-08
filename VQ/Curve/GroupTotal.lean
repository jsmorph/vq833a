/-
Group-total secp256k1 translation on encoded coordinate pairs.

The pair `(0, 0)` encodes the point at infinity.  Reduced affine curve points
use their ordinary coordinates, and every other pair is invalid.  Translation
fixes invalid targets and becomes the identity when its offset is invalid.
-/
import VQ.Curve.Total

namespace VQ
namespace Curve

/-- Whether a coordinate pair is the point-at-infinity sentinel. -/
def IsInfinity (x y : Nat) : Bool := x == 0 && y == 0

/-- Whether a coordinate pair encodes a secp256k1 group element. -/
def GroupRepresentable (x y : Nat) : Bool :=
  IsInfinity x y || (Representable x y && OnCurve x y)

/-- Whether two affine coordinate pairs are additive inverses. -/
def IsInverse (x y ax ay : Nat) : Bool := x == ax && y == neg ay

/-- Group translation on encoded coordinate pairs. -/
def groupAdd (x y ax ay : Nat) : Nat × Nat :=
  if GroupRepresentable x y && GroupRepresentable ax ay then
    if IsInfinity ax ay then
      (x, y)
    else if IsInfinity x y then
      (ax, ay)
    else if IsInverse x y ax ay then
      (0, 0)
    else
      totalAdd x y ax ay
  else
    (x, y)

/-- Inverse group translation.  The original offset is checked before its
affine y-coordinate is reduced by negation. -/
def groupSub (x y ax ay : Nat) : Nat × Nat :=
  if GroupRepresentable ax ay then
    if IsInfinity ax ay then
      (x, y)
    else
      groupAdd x y ax (neg ay)
  else
    (x, y)

/-- The coordinate value `-2P`, computed as `(-P) - P`. -/
def negativeDoublePoint (x y : Nat) : Nat × Nat :=
  groupSub x (neg y) x y

/-- The affine slope from `-2P` to `P`. -/
def negativeDoubleSlope (x y : Nat) : Nat :=
  let q := negativeDoublePoint x y
  slope q.1 q.2 x y

theorem negativeDoubleSlope_lt (x y : Nat) : negativeDoubleSlope x y < p := by
  exact slope_lt _ _ _ _

/-- Exchange the infinity sentinel and a fixed coordinate pair. -/
def swapInfinityOffset (target offset : Nat × Nat) : Nat × Nat :=
  if IsInfinity target.1 target.2 then
    offset
  else if target = offset then
    (0, 0)
  else
    target

theorem isInfinity_iff {x y : Nat} : IsInfinity x y = true ↔ x = 0 ∧ y = 0 := by
  simp [IsInfinity]

theorem isInverse_iff {x y ax ay : Nat} :
    IsInverse x y ax ay = true ↔ x = ax ∧ y = neg ay := by
  simp [IsInverse]

theorem infinity_groupRepresentable : GroupRepresentable 0 0 = true := by
  rfl

theorem groupRepresentable_cases {x y : Nat} (h : GroupRepresentable x y = true) :
    IsInfinity x y = true ∨ (Representable x y = true ∧ OnCurve x y = true) := by
  simpa [GroupRepresentable, Bool.or_eq_true, Bool.and_eq_true] using h

theorem representable_of_groupRepresentable {x y : Nat}
    (h : GroupRepresentable x y = true) : Representable x y = true := by
  rcases groupRepresentable_cases h with hi | haffine
  · rcases isInfinity_iff.mp hi with ⟨rfl, rfl⟩
    rfl
  · exact haffine.1

end Curve
end VQ
