/-
The group-total coordinate operation implements secp256k1 translation.

The proof decodes the infinity sentinel as the affine point-group zero and
ordinary valid coordinates as nonzero affine points.  Closure and injectivity
then reduce both inverse laws to the additive group laws supplied by Mathlib.
-/
import VQ.Curve.GroupTotal
import VQMathlib.Curve.Total

namespace VQBridge
namespace Curve

open VQ.Curve WeierstrassCurve

/-- Decode a coordinate pair into the secp256k1 affine point group. -/
noncomputable def groupPoint (x y : Nat) : W.toAffine.Point :=
  if h : OnCurve x y = true then pointOf h else 0

theorem onCurve_infinity : OnCurve 0 0 = false := by
  decide

theorem isInfinity_false_of_onCurve {x y : Nat} (h : OnCurve x y = true) :
    IsInfinity x y = false := by
  cases hi : IsInfinity x y with
  | false => rfl
  | true =>
      have hxy := isInfinity_iff.mp hi
      rw [hxy.1, hxy.2] at h
      simp [onCurve_infinity] at h

@[simp] theorem groupPoint_infinity : groupPoint 0 0 = 0 := by
  simp [groupPoint, onCurve_infinity]

theorem groupPoint_of_onCurve {x y : Nat} (h : OnCurve x y = true) :
    groupPoint x y = pointOf h := by
  simp [groupPoint, h]

theorem groupPoint_injective {x₁ y₁ x₂ y₂ : Nat}
    (h₁ : GroupRepresentable x₁ y₁ = true)
    (h₂ : GroupRepresentable x₂ y₂ = true)
    (h : groupPoint x₁ y₁ = groupPoint x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  rcases groupRepresentable_cases h₁ with hi₁ | ⟨hr₁, hc₁⟩
  · rcases isInfinity_iff.mp hi₁ with ⟨rfl, rfl⟩
    rcases groupRepresentable_cases h₂ with hi₂ | ⟨hr₂, hc₂⟩
    · exact ⟨(isInfinity_iff.mp hi₂).1.symm, (isInfinity_iff.mp hi₂).2.symm⟩
    · rw [groupPoint_infinity, groupPoint_of_onCurve hc₂] at h
      exact False.elim (pointOf_ne_zero hc₂ h.symm)
  · rcases groupRepresentable_cases h₂ with hi₂ | ⟨hr₂, hc₂⟩
    · rcases isInfinity_iff.mp hi₂ with ⟨rfl, rfl⟩
      rw [groupPoint_of_onCurve hc₁, groupPoint_infinity] at h
      exact False.elim (pointOf_ne_zero hc₁ h)
    · rw [groupPoint_of_onCurve hc₁, groupPoint_of_onCurve hc₂] at h
      exact pointOf_injective hr₁ hr₂ hc₁ hc₂ h

theorem groupRepresentable_groupAdd {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    GroupRepresentable (groupAdd x y ax ay).1 (groupAdd x y ax ay).2 = true := by
  rcases groupRepresentable_cases ht with hit | ⟨hrt, hct⟩
  · rcases isInfinity_iff.mp hit with ⟨rfl, rfl⟩
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      exact infinity_groupRepresentable
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      have hi0 : IsInfinity 0 0 = true := rfl
      have hg : groupAdd 0 0 ax ay = (ax, ay) := by
        simp [groupAdd, infinity_groupRepresentable, ho, hi0, hio]
      simpa [hg] using ho
  · have hit : IsInfinity x y = false := isInfinity_false_of_onCurve hct
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      simp [groupAdd, ht, infinity_groupRepresentable, IsInfinity]
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      cases hinv : IsInverse x y ax ay with
      | true =>
          simp [groupAdd, ht, ho, hit, hio, hinv, infinity_groupRepresentable]
      | false =>
          have hr := representable_totalAdd hrt hro
          have hc := totalAdd_onCurve hrt hro hct hco
          rw [show groupAdd x y ax ay = totalAdd x y ax ay by
            simp [groupAdd, ht, ho, hit, hio, hinv]]
          simp [GroupRepresentable, hr, hc]

theorem groupPoint_groupAdd {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    groupPoint (groupAdd x y ax ay).1 (groupAdd x y ax ay).2
      = groupPoint x y + groupPoint ax ay := by
  rcases groupRepresentable_cases ht with hit | ⟨hrt, hct⟩
  · rcases isInfinity_iff.mp hit with ⟨rfl, rfl⟩
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      have hg : groupAdd 0 0 0 0 = (0, 0) := by
        simp [groupAdd, infinity_groupRepresentable, show IsInfinity 0 0 = true from rfl]
      simp [hg]
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      have hi0 : IsInfinity 0 0 = true := rfl
      have hg : groupAdd 0 0 ax ay = (ax, ay) := by
        simp [groupAdd, infinity_groupRepresentable, ho, hi0, hio]
      simp [hg, groupPoint_of_onCurve hco]
  · have hit : IsInfinity x y = false := isInfinity_false_of_onCurve hct
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      simp [groupAdd, ht, infinity_groupRepresentable, IsInfinity,
        groupPoint_of_onCurve hct]
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      cases hinv : IsInverse x y ax ay with
      | true =>
          have hxy := isInverse_iff.mp hinv
          have hpneg : pointOf hct = -pointOf hco :=
            (pointOf_eq_neg_iff hrt hro hct hco).mpr hxy
          simp [groupAdd, ht, ho, hit, hio, hinv, groupPoint_of_onCurve hct,
            groupPoint_of_onCurve hco, hpneg]
      | false =>
          have hpneg : pointOf hct ≠ -pointOf hco := by
            intro hp
            have hi : IsInverse x y ax ay = true := isInverse_iff.mpr
              ((pointOf_eq_neg_iff hrt hro hct hco).mp hp)
            rw [hinv] at hi
            exact Bool.false_ne_true hi
          have hc := totalAdd_onCurve hrt hro hct hco
          rw [show groupAdd x y ax ay = totalAdd x y ax ay by
            simp [groupAdd, ht, ho, hit, hio, hinv]]
          rw [groupPoint_of_onCurve hc, pointOf_totalAdd hrt hro hct hco]
          simp [puncturedAdd, hpneg, groupPoint_of_onCurve hct,
            groupPoint_of_onCurve hco]

theorem swapInfinityOffset_totalAdd {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    swapInfinityOffset (totalAdd x y ax ay) (ax, ay) = groupAdd x y ax ay := by
  rcases groupRepresentable_cases ht with hit | ⟨hrt, hct⟩
  · rcases isInfinity_iff.mp hit with ⟨rfl, rfl⟩
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      simp [swapInfinityOffset, totalAdd, groupAdd, onCurve_infinity,
        infinity_groupRepresentable, IsInfinity]
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      simp [swapInfinityOffset, totalAdd, groupAdd, onCurve_infinity,
        infinity_groupRepresentable, ho, hio]
  · have hit : IsInfinity x y = false := isInfinity_false_of_onCurve hct
    rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
    · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
      have hxy : ¬ (x = 0 ∧ y = 0) := by
        rintro ⟨rfl, rfl⟩
        simp [IsInfinity] at hit
      simp [swapInfinityOffset, totalAdd, groupAdd, hct, onCurve_infinity,
        infinity_groupRepresentable, hxy, IsInfinity]
    · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
      cases hinv : IsInverse x y ax ay with
      | true =>
          rcases isInverse_iff.mp hinv with ⟨rfl, rfl⟩
          have hnegc : OnCurve x (neg ay) = true := onCurve_neg hco
          have hnegr : GroupRepresentable x (neg ay) = true :=
            by simp [GroupRepresentable, hrt, hnegc]
          have hneginf : IsInfinity x (neg ay) = false :=
            isInfinity_false_of_onCurve hnegc
          have hinv' : IsInverse x (neg ay) x ay = true := by
            simp [IsInverse]
          have hadd : totalAdd x (neg ay) x ay = (x, ay) := by
            simp [totalAdd, hnegc, hco]
          have hgroup : groupAdd x (neg ay) x ay = (0, 0) := by
            simp [groupAdd, hnegr, ho, hneginf, hio, hinv']
          rw [hadd, hgroup]
          simp [swapInfinityOffset, hio]
      | false =>
          have hpneg : pointOf hct ≠ -pointOf hco := by
            intro hp
            have hi : IsInverse x y ax ay = true := isInverse_iff.mpr
              ((pointOf_eq_neg_iff hrt hro hct hco).mp hp)
            rw [hinv] at hi
            exact Bool.false_ne_true hi
          have hc := totalAdd_onCurve hrt hro hct hco
          have hiresult :
              IsInfinity (totalAdd x y ax ay).1 (totalAdd x y ax ay).2 = false :=
            isInfinity_false_of_onCurve hc
          have hne : totalAdd x y ax ay ≠ (ax, ay) := by
            intro heq
            have hpEq := congrArg
              (fun q : Nat × Nat ↦ groupPoint q.1 q.2) heq
            rw [groupPoint_of_onCurve hc, groupPoint_of_onCurve hco] at hpEq
            have hpAdd : pointOf hc = pointOf hct + pointOf hco := by
              rw [pointOf_totalAdd hrt hro hct hco]
              simp [puncturedAdd, hpneg]
            have hcancel : pointOf hct + pointOf hco = 0 + pointOf hco := by
              rw [← hpAdd, hpEq, _root_.zero_add]
            exact pointOf_ne_zero hct (add_right_cancel hcancel)
          rw [show groupAdd x y ax ay = totalAdd x y ax ay by
            simp [groupAdd, ht, ho, hit, hio, hinv]]
          simp [swapInfinityOffset, hiresult, hne]

theorem negated_groupRepresentable {x y : Nat}
    (hr : Representable x y = true) (hc : OnCurve x y = true) :
    GroupRepresentable x (neg y) = true := by
  have hrn : Representable x (neg y) = true := by
    simpa [negPoint] using representable_negPoint hr
  have hcn := onCurve_neg hc
  simp [GroupRepresentable, hrn, hcn]

theorem groupRepresentable_groupSub {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    GroupRepresentable (groupSub x y ax ay).1 (groupSub x y ax ay).2 = true := by
  rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
  · simp [groupSub, ho, hio, ht]
  · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
    have hon := negated_groupRepresentable hro hco
    simpa [groupSub, ho, hio] using groupRepresentable_groupAdd ht hon

theorem groupPoint_groupSub {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    groupPoint (groupSub x y ax ay).1 (groupSub x y ax ay).2
      = groupPoint x y - groupPoint ax ay := by
  rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
  · rcases isInfinity_iff.mp hio with ⟨rfl, rfl⟩
    simp [groupSub, infinity_groupRepresentable, IsInfinity]
  · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
    have hon := negated_groupRepresentable hro hco
    rw [show groupSub x y ax ay = groupAdd x y ax (neg ay) by
      simp [groupSub, ho, hio]]
    rw [groupPoint_groupAdd ht hon, groupPoint_of_onCurve (onCurve_neg hco),
      pointOf_neg hco, groupPoint_of_onCurve hco]
    rfl

theorem groupSub_groupAdd_valid {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    groupSub (groupAdd x y ax ay).1 (groupAdd x y ax ay).2 ax ay = (x, y) := by
  let sum := groupAdd x y ax ay
  have hsum : GroupRepresentable sum.1 sum.2 = true := groupRepresentable_groupAdd ht ho
  have hback : GroupRepresentable (groupSub sum.1 sum.2 ax ay).1
      (groupSub sum.1 sum.2 ax ay).2 = true := groupRepresentable_groupSub hsum ho
  have hp : groupPoint (groupSub sum.1 sum.2 ax ay).1
      (groupSub sum.1 sum.2 ax ay).2 = groupPoint x y := by
    rw [groupPoint_groupSub hsum ho, groupPoint_groupAdd ht ho]
    abel
  exact Prod.ext (groupPoint_injective hback ht hp).1
    (groupPoint_injective hback ht hp).2

theorem groupAdd_groupSub_valid {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true) (ho : GroupRepresentable ax ay = true) :
    groupAdd (groupSub x y ax ay).1 (groupSub x y ax ay).2 ax ay = (x, y) := by
  let difference := groupSub x y ax ay
  have hdiff : GroupRepresentable difference.1 difference.2 = true :=
    groupRepresentable_groupSub ht ho
  have hback : GroupRepresentable (groupAdd difference.1 difference.2 ax ay).1
      (groupAdd difference.1 difference.2 ax ay).2 = true :=
    groupRepresentable_groupAdd hdiff ho
  have hp : groupPoint (groupAdd difference.1 difference.2 ax ay).1
      (groupAdd difference.1 difference.2 ax ay).2 = groupPoint x y := by
    rw [groupPoint_groupAdd hdiff ho, groupPoint_groupSub ht ho]
    abel
  exact Prod.ext (groupPoint_injective hback ht hp).1
    (groupPoint_injective hback ht hp).2

theorem groupSub_groupAdd (x y ax ay : Nat) :
    groupSub (groupAdd x y ax ay).1 (groupAdd x y ax ay).2 ax ay = (x, y) := by
  by_cases ht : GroupRepresentable x y = true
  · by_cases ho : GroupRepresentable ax ay = true
    · exact groupSub_groupAdd_valid ht ho
    · have hof : GroupRepresentable ax ay = false := Bool.eq_false_of_not_eq_true ho
      simp [groupAdd, groupSub, ht, hof]
  · have htf : GroupRepresentable x y = false := Bool.eq_false_of_not_eq_true ht
    by_cases ho : GroupRepresentable ax ay = true
    · rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
      · simp [groupAdd, groupSub, htf, ho, hio]
      · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
        have hon := negated_groupRepresentable hro hco
        simp [groupAdd, groupSub, htf, ho, hio, hon]
    · have hof : GroupRepresentable ax ay = false := Bool.eq_false_of_not_eq_true ho
      simp [groupAdd, groupSub, htf, hof]

theorem groupAdd_groupSub (x y ax ay : Nat) :
    groupAdd (groupSub x y ax ay).1 (groupSub x y ax ay).2 ax ay = (x, y) := by
  by_cases ht : GroupRepresentable x y = true
  · by_cases ho : GroupRepresentable ax ay = true
    · exact groupAdd_groupSub_valid ht ho
    · have hof : GroupRepresentable ax ay = false := Bool.eq_false_of_not_eq_true ho
      simp [groupAdd, groupSub, ht, hof]
  · have htf : GroupRepresentable x y = false := Bool.eq_false_of_not_eq_true ht
    by_cases ho : GroupRepresentable ax ay = true
    · rcases groupRepresentable_cases ho with hio | ⟨hro, hco⟩
      · simp [groupAdd, groupSub, htf, ho, hio]
      · have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
        have hon := negated_groupRepresentable hro hco
        simp [groupAdd, groupSub, htf, ho, hio, hon]
    · have hof : GroupRepresentable ax ay = false := Bool.eq_false_of_not_eq_true ho
      simp [groupAdd, groupSub, htf, hof]

/-- `negativeDoublePoint` represents `-(P + P)` for an affine curve point
`P`. -/
theorem groupPoint_negativeDoublePoint {x y : Nat}
    (hr : Representable x y = true) (hc : OnCurve x y = true) :
    groupPoint (negativeDoublePoint x y).1 (negativeDoublePoint x y).2 =
      -(groupPoint x y + groupPoint x y) := by
  have hg : GroupRepresentable x y = true := by
    simp [GroupRepresentable, hr, hc]
  have hn := negated_groupRepresentable hr hc
  rw [negativeDoublePoint, groupPoint_groupSub hn hg,
    groupPoint_of_onCurve (onCurve_neg hc), pointOf_neg hc,
    groupPoint_of_onCurve hc]
  abel

/-- An affine addition input that prevents ordinary slope recovery is `-2P`,
where `P` is the fixed offset. -/
theorem nonrecoverable_eq_negativeDoublePoint {x y ax ay : Nat}
    (hadd : Addable x y ax ay = true)
    (hrec : Recoverable x y ax ay = false) :
    (x, y) = negativeDoublePoint ax ay := by
  have hparts := hadd
  simp only [Addable, Bool.and_eq_true, bne_iff_ne] at hparts
  obtain ⟨⟨⟨⟨htr, hor⟩, htc⟩, hoc⟩, hne⟩ := hparts
  have htg : GroupRepresentable x y = true := by
    simp [GroupRepresentable, htr, htc]
  have hog : GroupRepresentable ax ay = true := by
    simp [GroupRepresentable, hor, hoc]
  have hti : IsInfinity x y = false := isInfinity_false_of_onCurve htc
  have hoi : IsInfinity ax ay = false := isInfinity_false_of_onCurve hoc
  have hinv : IsInverse x y ax ay = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hi
    exact hne (isInverse_iff.mp hi).1
  have hsum : groupAdd x y ax ay = totalAdd x y ax ay := by
    simp [groupAdd, htg, hog, hti, hoi, hinv]
  have hsumAdd : groupAdd x y ax ay = addPoint x y ax ay :=
    hsum.trans (totalAdd_of_addable hadd)
  have hsumRepresentable :
      Representable (groupAdd x y ax ay).1 (groupAdd x y ax ay).2 = true := by
    rw [hsum]
    exact representable_totalAdd htr hor
  have hsumOnCurve :
      OnCurve (groupAdd x y ax ay).1 (groupAdd x y ax ay).2 = true := by
    rw [hsum]
    exact totalAdd_onCurve htr hor htc hoc
  have hxadd : (addPoint x y ax ay).1 = ax := by
    simpa [Recoverable] using hrec
  have hx : (groupAdd x y ax ay).1 = ax := by
    rw [hsumAdd]
    exact hxadd
  have hyCases := y_eq_or_neg_of_x_eq hsumRepresentable hor hsumOnCurve hoc hx
  have hy : (groupAdd x y ax ay).2 = neg ay := by
    rcases hyCases with hy | hy
    · have hpair : groupAdd x y ax ay = (ax, ay) := Prod.ext hx hy
      have hpoint := groupPoint_groupAdd htg hog
      have hcancel : groupPoint x y + groupPoint ax ay =
          0 + groupPoint ax ay := by
        rw [← hpoint, hpair]
        rfl
      have hzero : groupPoint x y = 0 := add_right_cancel hcancel
      rw [groupPoint_of_onCurve htc] at hzero
      exact (pointOf_ne_zero htc hzero).elim
    · exact hy
  have hpair : groupAdd x y ax ay = (ax, neg ay) := Prod.ext hx hy
  change (x, y) = groupSub ax (neg ay) ax ay
  calc
    (x, y) = groupSub (groupAdd x y ax ay).1
        (groupAdd x y ax ay).2 ax ay :=
      (groupSub_groupAdd x y ax ay).symm
    _ = groupSub ax (neg ay) ax ay := by rw [hpair]

/-- The retained affine slope on the nonrecoverable input equals the fixed
exceptional slope determined by the offset. -/
theorem nonrecoverable_slope_eq_negativeDoubleSlope {x y ax ay : Nat}
    (hadd : Addable x y ax ay = true)
    (hrec : Recoverable x y ax ay = false) :
    slope x y ax ay = negativeDoubleSlope ax ay := by
  simpa [negativeDoubleSlope] using congrArg
    (fun q : Nat × Nat ↦ slope q.1 q.2 ax ay)
    (nonrecoverable_eq_negativeDoublePoint hadd hrec)

theorem slope_eq_negativeDoubleSlope_of_sub_eq_zero {x y ax ay : Nat}
    (hadd : Addable x y ax ay = true)
    (hzero : sub ax (addPoint x y ax ay).1 = 0) :
    slope x y ax ay = negativeDoubleSlope ax ay := by
  have hparts := hadd
  simp only [Addable, Bool.and_eq_true] at hparts
  have hfixed := hparts.1.1.1.2
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at hfixed
  have hx3 : (addPoint x y ax ay).1 = ax := by
    by_contra hne
    exact (sub_ne_zero_of_ne hfixed.1 (representable_addPoint_fst x y ax ay)
      (Ne.symm hne)) hzero
  apply nonrecoverable_slope_eq_negativeDoubleSlope hadd
  simp [Recoverable, hx3]

theorem groupAdd_bijective (ax ay : Nat) :
    Function.Bijective (fun q : Nat × Nat ↦ groupAdd q.1 q.2 ax ay) := by
  constructor
  · intro a b h
    have := congrArg (fun q : Nat × Nat ↦ groupSub q.1 q.2 ax ay) h
    simpa [groupSub_groupAdd] using this
  · intro q
    exact ⟨groupSub q.1 q.2 ax ay, by simp [groupAdd_groupSub]⟩

end Curve
end VQBridge
