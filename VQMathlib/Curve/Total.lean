/-
The total affine translation agrees with the secp256k1 group law.
-/
import VQ.Curve.Total
import VQMathlib.Curve.Laws
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace VQBridge
namespace Curve

open VQ.Curve WeierstrassCurve

instance : W.IsElliptic where
  isUnit := by
    rw [isUnit_iff_ne_zero]
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    decide

/-- Translation restricted to the nonzero points, with the missing group zero
replaced by the offset point. -/
def puncturedAdd {G : Type*} [AddCommGroup G] [DecidableEq G] (offset target : G) : G :=
  if target = -offset then offset else target + offset

/-- The inverse translation on the nonzero points. -/
def puncturedSub {G : Type*} [AddCommGroup G] [DecidableEq G] (offset target : G) : G :=
  puncturedAdd (-offset) target

theorem puncturedSub_puncturedAdd {G : Type*} [AddCommGroup G] [DecidableEq G]
    {offset target : G} (ht : target ≠ 0) :
    puncturedSub offset (puncturedAdd offset target) = target := by
  by_cases hneg : target = -offset
  · simp [puncturedSub, puncturedAdd, hneg]
  · have hsum : target + offset ≠ offset := by
      intro h
      apply ht
      apply add_right_cancel (b := offset)
      simpa using h
    simp [puncturedSub, puncturedAdd, hneg, hsum, _root_.add_assoc]

theorem cast_neg (a : Nat) : ((neg a : Nat) : ZMod p) = -(a : ZMod p) := by
  rw [neg, cast_sub]
  push_cast
  ring

def pointOf {x y : Nat} (h : OnCurve x y = true) : W.toAffine.Point :=
  .mk ((onCurve_iff x y).mp h)

theorem pointOf_ne_zero {x y : Nat} (h : OnCurve x y = true) : pointOf h ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem pointOf_injective {x₁ y₁ x₂ y₂ : Nat}
    (hr₁ : Representable x₁ y₁ = true) (hr₂ : Representable x₂ y₂ = true)
    (h₁ : OnCurve x₁ y₁ = true) (h₂ : OnCurve x₂ y₂ = true)
    (h : pointOf h₁ = pointOf h₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  simp only [pointOf, WeierstrassCurve.Affine.Point.mk,
    WeierstrassCurve.Affine.Point.some.injEq] at h
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at hr₁ hr₂
  exact ⟨natCast_inj_of_lt hr₁.1 hr₂.1 h.1,
    natCast_inj_of_lt hr₁.2 hr₂.2 h.2⟩

theorem onCurve_neg {x y : Nat} (h : OnCurve x y = true) : OnCurve x (neg y) = true := by
  apply (onCurve_iff x (neg y)).mpr
  rw [cast_neg]
  have heq := (onCurve_iff x y).mp h
  simpa [W, WeierstrassCurve.Affine.negY] using
    (W.toAffine.equation_neg (x : ZMod p) (y : ZMod p)).mpr heq

theorem onCurve_neg_eq (x y : Nat) : OnCurve x (neg y) = OnCurve x y := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply (onCurve_iff x y).mpr
    have heq := (onCurve_iff x (neg y)).mp h
    rw [cast_neg] at heq
    apply (W.toAffine.equation_neg (x : ZMod p) (y : ZMod p)).mp
    simpa [W, WeierstrassCurve.Affine.negY] using heq
  · exact onCurve_neg

theorem pointOf_neg {x y : Nat} (h : OnCurve x y = true) :
    pointOf (onCurve_neg h) = -pointOf h := by
  unfold pointOf WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨trivial, by simpa [W, WeierstrassCurve.Affine.negY] using cast_neg y⟩

theorem doublePoint_eq {x y : Nat}
    (hy : (y : ZMod p) ≠ W.toAffine.negY (x : ZMod p) (y : ZMod p)) :
    (((doublePoint x y).1 : Nat) : ZMod p)
        = W.toAffine.addX (x : ZMod p) (x : ZMod p)
            (W.toAffine.slope (x : ZMod p) (x : ZMod p) (y : ZMod p) (y : ZMod p))
      ∧ (((doublePoint x y).2 : Nat) : ZMod p)
        = W.toAffine.addY (x : ZMod p) (x : ZMod p) (y : ZMod p)
            (W.toAffine.slope (x : ZMod p) (x : ZMod p) (y : ZMod p) (y : ZMod p)) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp only [doublePoint, W, cast_mul, cast_inv, cast_sub,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, div_eq_mul_inv]
  constructor <;> ring

theorem onCurve_double {x y : Nat} (h : OnCurve x y = true)
    (hy : (y : ZMod p) ≠ W.toAffine.negY (x : ZMod p) (y : ZMod p)) :
    OnCurve (doublePoint x y).1 (doublePoint x y).2 = true := by
  apply (onCurve_iff _ _).mpr
  have hd := doublePoint_eq hy
  rw [hd.1, hd.2]
  exact W.toAffine.equation_add ((onCurve_iff x y).mp h) ((onCurve_iff x y).mp h)
    (by exact fun hxy ↦ hy hxy.2)

theorem pointOf_double {x y : Nat} (h : OnCurve x y = true)
    (hy : (y : ZMod p) ≠ W.toAffine.negY (x : ZMod p) (y : ZMod p)) :
    pointOf (onCurve_double h hy) = pointOf h + pointOf h := by
  unfold pointOf WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact doublePoint_eq hy

theorem onCurve_addPoint {x₁ y₁ x₂ y₂ : Nat}
    (h₁ : OnCurve x₁ y₁ = true) (h₂ : OnCurve x₂ y₂ = true)
    (hx : (x₁ : ZMod p) ≠ (x₂ : ZMod p)) :
    OnCurve (addPoint x₁ y₁ x₂ y₂).1 (addPoint x₁ y₁ x₂ y₂).2 = true := by
  apply (onCurve_iff _ _).mpr
  have ha := addPoint_eq (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂) hx
  rw [ha.1, ha.2]
  exact W.toAffine.equation_add ((onCurve_iff x₁ y₁).mp h₁) ((onCurve_iff x₂ y₂).mp h₂)
    (by exact fun hxy ↦ hx hxy.1)

theorem pointOf_addPoint {x₁ y₁ x₂ y₂ : Nat}
    (h₁ : OnCurve x₁ y₁ = true) (h₂ : OnCurve x₂ y₂ = true)
    (hx : (x₁ : ZMod p) ≠ (x₂ : ZMod p)) :
    pointOf (onCurve_addPoint h₁ h₂ hx) = pointOf h₁ + pointOf h₂ := by
  unfold pointOf WeierstrassCurve.Affine.Point.mk
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact addPoint_eq hx

private theorem representable_parts {x y : Nat} (h : Representable x y = true) :
    x < p ∧ y < p := by
  simpa only [Representable, Bool.and_eq_true, decide_eq_true_eq] using h

theorem y_eq_or_neg_of_x_eq {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true)
    (ht : OnCurve x y = true) (ho : OnCurve ax ay = true) (hx : x = ax) :
    y = ay ∨ y = neg ay := by
  have hc := W.toAffine.Y_eq_of_X_eq ((onCurve_iff x y).mp ht)
    ((onCurve_iff ax ay).mp ho) (by simp [hx])
  rcases hc with heq | hneg
  · exact Or.inl (natCast_inj_of_lt (representable_parts hr).2 (representable_parts hro).2 heq)
  · apply Or.inr
    apply natCast_inj_of_lt (representable_parts hr).2 (neg_lt ay)
    rw [cast_neg]
    simpa [W, WeierstrassCurve.Affine.negY] using hneg

theorem pointOf_eq_neg_iff {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true)
    (ht : OnCurve x y = true) (ho : OnCurve ax ay = true) :
    pointOf ht = -pointOf ho ↔ x = ax ∧ y = neg ay := by
  constructor
  · intro h
    rw [← pointOf_neg ho] at h
    exact pointOf_injective hr (representable_negPoint hro) ht (onCurve_neg ho) h
  · rintro ⟨rfl, rfl⟩
    exact pointOf_neg ho

private theorem cast_ne_neg_of_ne {x y ax ay : Nat}
    (hr : Representable x y = true) (h : y ≠ neg ay) :
    (y : ZMod p) ≠ W.toAffine.negY (ax : ZMod p) (ay : ZMod p) := by
  intro hc
  apply h
  apply natCast_inj_of_lt (representable_parts hr).2 (neg_lt ay)
  rw [cast_neg]
  simpa [W, WeierstrassCurve.Affine.negY] using hc

theorem totalAdd_onCurve {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true)
    (ht : OnCurve x y = true) (ho : OnCurve ax ay = true) :
    OnCurve (totalAdd x y ax ay).1 (totalAdd x y ax ay).2 = true := by
  by_cases hx : x = ax
  · by_cases hneg : y = neg ay
    · have hnegc := onCurve_neg ho
      simp [totalAdd, ho, hnegc, hx, hneg]
    · have hy : y = ay := (y_eq_or_neg_of_x_eq hr hro ht ho hx).resolve_right hneg
      have hayneg : ay ≠ neg ay := by simpa [hy] using hneg
      have hyc := cast_ne_neg_of_ne (x := ax) (y := ay) (ax := ax) (ay := ay) hro hayneg
      simpa [totalAdd, ht, ho, hx, hneg, hy, hayneg] using onCurve_double ho hyc
  · have hxc : (x : ZMod p) ≠ (ax : ZMod p) := by
      intro hc
      exact hx (natCast_inj_of_lt (representable_parts hr).1 (representable_parts hro).1 hc)
    simpa [totalAdd, ht, ho, hx] using onCurve_addPoint ht ho hxc

theorem pointOf_totalAdd {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true)
    (ht : OnCurve x y = true) (ho : OnCurve ax ay = true) :
    pointOf (totalAdd_onCurve hr hro ht ho) = puncturedAdd (pointOf ho) (pointOf ht) := by
  by_cases hx : x = ax
  · by_cases hneg : y = neg ay
    · have hpneg : pointOf ht = -pointOf ho :=
        (pointOf_eq_neg_iff hr hro ht ho).mpr ⟨hx, hneg⟩
      rw [puncturedAdd, if_pos hpneg]
      have hnegc := onCurve_neg ho
      simp [totalAdd, ho, hnegc, hx, hneg, pointOf]
    · have hy : y = ay := (y_eq_or_neg_of_x_eq hr hro ht ho hx).resolve_right hneg
      have hpneg : pointOf ht ≠ -pointOf ho := by
        intro hp
        exact hneg ((pointOf_eq_neg_iff hr hro ht ho).mp hp).2
      subst x
      subst y
      have hyc := cast_ne_neg_of_ne (x := ax) (y := ay) (ax := ax) (ay := ay) hro hneg
      rw [puncturedAdd, if_neg hpneg]
      simpa [totalAdd, ht, ho, hneg, pointOf] using pointOf_double ho hyc
  · have hpneg : pointOf ht ≠ -pointOf ho := by
      intro hp
      exact hx ((pointOf_eq_neg_iff hr hro ht ho).mp hp).1
    have hxc : (x : ZMod p) ≠ (ax : ZMod p) := by
      intro hc
      exact hx (natCast_inj_of_lt (representable_parts hr).1 (representable_parts hro).1 hc)
    rw [puncturedAdd, if_neg hpneg]
    simpa [totalAdd, ht, ho, hx, pointOf] using pointOf_addPoint ht ho hxc

theorem totalSub_totalAdd {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true)
    (ht : OnCurve x y = true) (ho : OnCurve ax ay = true) :
    totalSub (totalAdd x y ax ay).1 (totalAdd x y ax ay).2 ax ay = (x, y) := by
  let sum := totalAdd x y ax ay
  have hsumr : Representable sum.1 sum.2 = true := representable_totalAdd hr hro
  have hsumc : OnCurve sum.1 sum.2 = true := totalAdd_onCurve hr hro ht ho
  have hnegr : Representable ax (neg ay) = true := representable_negPoint hro
  have hnegc : OnCurve ax (neg ay) = true := onCurve_neg ho
  have hbackc : OnCurve (totalAdd sum.1 sum.2 ax (neg ay)).1
      (totalAdd sum.1 sum.2 ax (neg ay)).2 = true :=
    totalAdd_onCurve hsumr hnegr hsumc hnegc
  have hbackr : Representable (totalAdd sum.1 sum.2 ax (neg ay)).1
      (totalAdd sum.1 sum.2 ax (neg ay)).2 = true :=
    representable_totalAdd hsumr hnegr
  have hp : pointOf hbackc = pointOf ht := by
    rw [pointOf_totalAdd hsumr hnegr hsumc hnegc, pointOf_neg ho,
      pointOf_totalAdd hr hro ht ho]
    exact puncturedSub_puncturedAdd (pointOf_ne_zero ht)
  have hc := pointOf_injective hbackr hr hbackc ht hp
  change totalAdd sum.1 sum.2 ax (neg ay) = (x, y)
  exact Prod.ext hc.1 hc.2

/-- The total extension is a permutation on every representable coordinate
pair.  Off-curve targets and offsets take the identity branch. -/
theorem totalSub_totalAdd_representable {x y ax ay : Nat}
    (hr : Representable x y = true) (hro : Representable ax ay = true) :
    totalSub (totalAdd x y ax ay).1 (totalAdd x y ax ay).2 ax ay = (x, y) := by
  by_cases ht : OnCurve x y = true
  · by_cases ho : OnCurve ax ay = true
    · exact totalSub_totalAdd hr hro ht ho
    · simp [totalSub, totalAdd, ht, ho, onCurve_neg_eq]
  · simp [totalSub, totalAdd, ht]

end Curve
end VQBridge
