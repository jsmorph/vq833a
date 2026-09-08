/-
Value semantics for the packed-affine point-translation schedule.
-/
import VQMathlib.Curve.GroupTotal
import VQMathlib.Curve.LuoPointAddition

namespace VQBridge
namespace Curve
namespace PackedAffine

open VQ.Curve

def nonzeroOrOne (x : Nat) : Nat := if x = 0 then 1 else x

def divisionInput (x ax : Nat) : Nat := sub x ax

def quotient (control : Bool) (x y ax ay : Nat) : Nat :=
  mul (if control then sub y ay else y) (inv (nonzeroOrOne (divisionInput x ax)))

def multiplicationInput (control : Bool) (x y ax ay : Nat) : Nat :=
  if control then
    add (sub (divisionInput x ax)
      (mul (quotient control x y ax ay) (quotient control x y ax ay)))
      (mul 3 ax)
  else
    divisionInput x ax

def rawAction (control : Bool) (x y ax ay : Nat) : Nat × Nat :=
  let q := quotient control x y ax ay
  let u := multiplicationInput control x y ax ay
  let v := mul q (nonzeroOrOne u)
  if control then (add (neg u) ax, sub v ay) else (add u ax, v)

theorem nonzeroOrOne_pos (x : Nat) : 0 < nonzeroOrOne x := by
  simp only [nonzeroOrOne]
  split <;> omega

theorem nonzeroOrOne_lt {x : Nat} (hx : x < p) : nonzeroOrOne x < p := by
  simp only [nonzeroOrOne]
  split
  · decide
  · exact hx

theorem nonzeroOrOne_ne_zero (x : Nat) : nonzeroOrOne x ≠ 0 := by
  exact Nat.ne_of_gt (nonzeroOrOne_pos x)

theorem nonzeroOrOne_of_ne {x : Nat} (h : x ≠ 0) : nonzeroOrOne x = x := by
  simp [nonzeroOrOne, h]

theorem nonzeroOrOne_zero : nonzeroOrOne 0 = 1 := by
  rfl

theorem quotient_mul_nonzeroOrOne
    {z d : Nat} (hz : z < p) (hd : d < p) :
    mul (mul z (inv (nonzeroOrOne d))) (nonzeroOrOne d) = z := by
  exact mul_inv_cancel inverseLaw hz (nonzeroOrOne_lt hd)
    (nonzeroOrOne_ne_zero d)

theorem disabled_action {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) :
    rawAction false x y ax ay = (x, y) := by
  let d := divisionInput x ax
  have hd : d < p := sub_lt x ax
  have hq : mul (quotient false x y ax ay) (nonzeroOrOne d) = y := by
    exact quotient_mul_nonzeroOrOne hy hd
  have hdx : add d ax = x := by
    exact sub_add_cancel hx hax
  simp only [rawAction, multiplicationInput, Bool.false_eq_true, if_false]
  rw [show divisionInput x ax = d from rfl, hdx]
  simpa [d] using hq

theorem quotient_of_divisionInput_ne_zero {control : Bool} {x y ax ay : Nat}
    (hd : divisionInput x ax ≠ 0) :
    quotient control x y ax ay =
      VQBridge.Curve.LuoPointAddition.quotient control x y ax ay := by
  have hd' : sub x ax ≠ 0 := by
    simpa [divisionInput] using hd
  simp [quotient, VQBridge.Curve.LuoPointAddition.quotient,
    VQBridge.Curve.LuoPointAddition.divisionInput, divisionInput,
    nonzeroOrOne_of_ne hd']

theorem multiplicationInput_of_divisionInput_ne_zero
    {control : Bool} {x y ax ay : Nat}
    (hd : divisionInput x ax ≠ 0) :
    multiplicationInput control x y ax ay =
      VQBridge.Curve.LuoPointAddition.multiplicationInput control x y ax ay := by
  simp only [multiplicationInput,
    VQBridge.Curve.LuoPointAddition.multiplicationInput]
  rw [quotient_of_divisionInput_ne_zero hd]
  rfl

theorem rawAction_of_nonzero {control : Bool} {x y ax ay : Nat}
    (hd : divisionInput x ax ≠ 0)
    (hu : multiplicationInput control x y ax ay ≠ 0) :
    rawAction control x y ax ay =
      VQBridge.Curve.LuoPointAddition.action control x y ax ay := by
  have hmu : nonzeroOrOne (multiplicationInput control x y ax ay) =
      multiplicationInput control x y ax ay := nonzeroOrOne_of_ne hu
  simp only [rawAction, VQBridge.Curve.LuoPointAddition.action]
  rw [hmu, quotient_of_divisionInput_ne_zero hd,
    multiplicationInput_of_divisionInput_ne_zero hd]

theorem enabled_generic {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hay : ay < p)
    (hne : x ≠ ax) (hrecoverable : (addPoint x y ax ay).1 ≠ ax) :
    rawAction true x y ax ay = addPoint x y ax ay := by
  have hd : divisionInput x ax ≠ 0 :=
    VQBridge.Curve.LuoPointAddition.divisionInput_nonzero hx hax hne
  have hu : multiplicationInput true x y ax ay ≠ 0 := by
    rw [multiplicationInput_of_divisionInput_ne_zero hd]
    exact VQBridge.Curve.LuoPointAddition.enabled_multiplicationInput_nonzero
      hx hy hax hay hne hrecoverable
  rw [rawAction_of_nonzero hd hu]
  exact VQBridge.Curve.LuoPointAddition.enabled_action hx hy hax hay hne

def Exceptional (x y ax ay : Nat) : Prop :=
  (x, y) = (0, 0) ∨
  (x, y) = (ax, ay) ∨
  (x, y) = (ax, neg ay) ∨
  (x, y) = negativeDoublePoint ax ay

noncomputable instance exceptionalDecidable (x y ax ay : Nat) :
    Decidable (Exceptional x y ax ay) := by
  classical
  infer_instance

theorem x_ne_offset_of_not_exceptional
    {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true)
    (hco : OnCurve ax ay = true)
    (hne : ¬ Exceptional x y ax ay) : x ≠ ax := by
  rcases groupRepresentable_cases ht with hinfinity | ⟨hrt, hct⟩
  · exact False.elim (hne (Or.inl (Prod.ext
      (isInfinity_iff.mp hinfinity).1 (isInfinity_iff.mp hinfinity).2)))
  · intro hx
    rcases y_eq_or_neg_of_x_eq hrt hro hct hco hx with hy | hy
    · exact hne (Or.inr (Or.inl (Prod.ext hx hy)))
    · exact hne (Or.inr (Or.inr (Or.inl (Prod.ext hx hy))))

theorem recoverable_of_not_exceptional
    {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true)
    (hco : OnCurve ax ay = true)
    (hne : ¬ Exceptional x y ax ay) :
    (addPoint x y ax ay).1 ≠ ax := by
  rcases groupRepresentable_cases ht with hinfinity | ⟨hrt, hct⟩
  · exact False.elim (hne (Or.inl (Prod.ext
      (isInfinity_iff.mp hinfinity).1 (isInfinity_iff.mp hinfinity).2)))
  · have hx : x ≠ ax := x_ne_offset_of_not_exceptional ht hro hco hne
    have hadd : Addable x y ax ay = true := by
      simp [Addable, hrt, hro, hct, hco, hx]
    intro hresult
    have hrec : Recoverable x y ax ay = false := by
      simp [Recoverable, hresult]
    exact hne (Or.inr (Or.inr (Or.inr
      (nonrecoverable_eq_negativeDoublePoint hadd hrec))))

theorem rawAction_eq_groupAdd_of_not_exceptional
    {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true)
    (hco : OnCurve ax ay = true)
    (hne : ¬ Exceptional x y ax ay) :
    rawAction true x y ax ay = groupAdd x y ax ay := by
  rcases groupRepresentable_cases ht with hinfinity | ⟨hrt, hct⟩
  · exact False.elim (hne (Or.inl (Prod.ext
      (isInfinity_iff.mp hinfinity).1 (isInfinity_iff.mp hinfinity).2)))
  · have hx : x ≠ ax := x_ne_offset_of_not_exceptional ht hro hco hne
    have hrecoverable := recoverable_of_not_exceptional ht hro hco hne
    have hrt' : x < p ∧ y < p := by
      simpa [Representable] using hrt
    have hro' : ax < p ∧ ay < p := by
      simpa [Representable] using hro
    have hraw := enabled_generic
      hrt'.1 hrt'.2 hro'.1 hro'.2
      hx hrecoverable
    have ho : GroupRepresentable ax ay = true := by
      simp [GroupRepresentable, hro, hco]
    have hit : IsInfinity x y = false := isInfinity_false_of_onCurve hct
    have hio : IsInfinity ax ay = false := isInfinity_false_of_onCurve hco
    have hinv : IsInverse x y ax ay = false := by
      simp [IsInverse, hx]
    have hadd : Addable x y ax ay = true := by
      simp [Addable, hrt, hro, hct, hco, hx]
    rw [hraw]
    simp [groupAdd, ht, ho, hit, hio, hinv, totalAdd_of_addable hadd]

noncomputable def correctedAction (x y ax ay : Nat) : Nat × Nat :=
  if Exceptional x y ax ay then groupAdd x y ax ay
  else rawAction true x y ax ay

theorem correctedAction_eq_groupAdd
    {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true)
    (hco : OnCurve ax ay = true) :
    correctedAction x y ax ay = groupAdd x y ax ay := by
  by_cases h : Exceptional x y ax ay
  · simp [correctedAction, h]
  · simp [correctedAction, h,
      rawAction_eq_groupAdd_of_not_exceptional ht hro hco h]

end PackedAffine
end Curve
end VQBridge
