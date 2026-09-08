/-
A total affine permutation for runtime point addition.

Affine translation sends `-O` to the point at infinity, which the two-coordinate
register cannot represent.  On curve points this extension sends `-O` to `O`,
sends `O` to `2O`, and uses ordinary affine addition elsewhere.  It fixes every
off-curve coordinate pair.  The inverse is the same extension at `-O`.
-/
import VQ.Curve.Spec

namespace VQ
namespace Curve

/-- Affine negation. -/
def negPoint (x y : Nat) : Nat × Nat := (x, neg y)

/-- Affine doubling on secp256k1.  The function is total through `inv 0 = 0`.
The total extension selects it only for an on-curve point not equal to its
negation. -/
def doublePoint (x y : Nat) : Nat × Nat :=
  let l := mul (mul 3 (mul x x)) (inv (mul 2 y))
  let x₃ := sub (mul l l) (mul 2 x)
  (x₃, sub (mul l (sub x x₃)) y)

/-- Total affine translation on coordinate pairs. -/
def totalAdd (x y ax ay : Nat) : Nat × Nat :=
  if OnCurve x y && OnCurve ax ay then
    if x == ax && y == neg ay then
      (ax, ay)
    else if x == ax && y == ay then
      doublePoint ax ay
    else
      addPoint x y ax ay
  else
    (x, y)

/-- The proposed inverse of `totalAdd`: translate by the negated offset. -/
def totalSub (x y ax ay : Nat) : Nat × Nat :=
  totalAdd x y ax (neg ay)

theorem negPoint_fst (x y : Nat) : (negPoint x y).1 = x := rfl

theorem negPoint_snd (x y : Nat) : (negPoint x y).2 = neg y := rfl

theorem representable_negPoint {x y : Nat} (h : Representable x y = true) :
    Representable (negPoint x y).1 (negPoint x y).2 = true := by
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, neg_lt y⟩

theorem representable_doublePoint (x y : Nat) :
    Representable (doublePoint x y).1 (doublePoint x y).2 = true := by
  simp [doublePoint, Representable, sub_lt]

/-- The total extension agrees definitionally with affine addition on its value
domain. -/
theorem totalAdd_of_addable {x y ax ay : Nat}
    (h : Addable x y ax ay = true) : totalAdd x y ax ay = addPoint x y ax ay := by
  simp only [Addable, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨_, _⟩, hxy⟩, hoa⟩, hne⟩ := h
  simp [totalAdd, hxy, hoa, hne]

/-- A representable target remains representable under the total extension. -/
theorem representable_totalAdd {x y ax ay : Nat}
    (ht : Representable x y = true) (ho : Representable ax ay = true) :
    Representable (totalAdd x y ax ay).1 (totalAdd x y ax ay).2 = true := by
  rw [totalAdd]
  split
  · split
    · exact ho
    · split
      · exact representable_doublePoint ax ay
      · exact representable_addPoint x y ax ay
  · exact ht

end Curve
end VQ
