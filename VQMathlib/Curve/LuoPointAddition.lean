import VQMathlib.Curve.Laws

namespace VQBridge.Curve.LuoPointAddition

open VQ.Curve

/-- The divisor present after the first unconditional subtraction in Figure 14. -/
def divisionInput (x ax : Nat) : Nat := sub x ax

/-- The quotient held in the y-coordinate register after in-place division. -/
def quotient (control : Bool) (x y ax ay : Nat) : Nat :=
  mul (if control then sub y ay else y) (inv (divisionInput x ax))

/-- The x-coordinate register immediately before in-place multiplication. -/
def multiplicationInput (control : Bool) (x y ax ay : Nat) : Nat :=
  if control then
    add (sub (divisionInput x ax) (mul (quotient control x y ax ay)
      (quotient control x y ax ay))) (mul 3 ax)
  else
    divisionInput x ax

/-- The field-register action of the Figure 14 schedule, assuming the abstract
in-place division and multiplication interfaces perform their stated maps. -/
def action (control : Bool) (x y ax ay : Nat) : Nat × Nat :=
  let q := quotient control x y ax ay
  let u := multiplicationInput control x y ax ay
  let v := mul q u
  if control then (add (neg u) ax, sub v ay) else (add u ax, v)

theorem divisionInput_nonzero {x ax : Nat} (hx : x < p) (hax : ax < p)
    (hne : x ≠ ax) : divisionInput x ax ≠ 0 :=
  sub_ne_zero_of_ne hx hax hne

theorem disabled_multiplicationInput (x y ax ay : Nat) :
    multiplicationInput false x y ax ay = divisionInput x ax := rfl

theorem disabled_action {x y ax ay : Nat} (hx : x < p) (hy : y < p)
    (hax : ax < p) (hne : x ≠ ax) :
    action false x y ax ay = (x, y) := by
  have hd : divisionInput x ax ≠ 0 := divisionInput_nonzero hx hax hne
  have hq : mul (quotient false x y ax ay) (divisionInput x ax) = y := by
    exact mul_inv_cancel inverseLaw hy (sub_lt x ax) hd
  have hdx : add (divisionInput x ax) ax = x := by
    exact sub_add_cancel hx hax
  simp only [action, multiplicationInput, Bool.false_eq_true, if_false]
  rw [hdx, hq]

theorem enabled_quotient (x y ax ay : Nat) :
    quotient true x y ax ay = slope x y ax ay := rfl

theorem enabled_multiplicationInput {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hay : ay < p)
    (hne : x ≠ ax) :
    multiplicationInput true x y ax ay = sub ax (addPoint x y ax ay).1 := by
  exact (alg1PrefixLaw ax ay x y hax hay hx hy hne).xShift

theorem enabled_action {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hay : ay < p)
    (hne : x ≠ ax) :
    action true x y ax ay = addPoint x y ax ay := by
  have halg := alg1PrefixLaw ax ay x y hax hay hx hy hne
  have hu : multiplicationInput true x y ax ay =
      sub ax (addPoint x y ax ay).1 := halg.xShift
  have hv : mul (quotient true x y ax ay)
      (multiplicationInput true x y ax ay) =
      add (addPoint x y ax ay).2 ay := by
    rw [enabled_quotient, hu]
    exact halg.yShift
  rw [hu] at hv
  simp only [action, if_true]
  rw [hu, hv, neg_sub hax (representable_addPoint_fst x y ax ay),
    sub_add_cancel (representable_addPoint_fst x y ax ay) hax,
    add_sub_cancel (representable_addPoint_snd x y ax ay) hay]

theorem enabled_multiplicationInput_nonzero {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hay : ay < p)
    (hne : x ≠ ax) (hrec : (addPoint x y ax ay).1 ≠ ax) :
    multiplicationInput true x y ax ay ≠ 0 := by
  rw [enabled_multiplicationInput hx hy hax hay hne]
  exact sub_ne_zero_of_ne hax (representable_addPoint_fst x y ax ay) (Ne.symm hrec)

theorem enabled_domain {x y ax ay : Nat}
    (hadd : Addable x y ax ay = true) (hrec : Recoverable x y ax ay = true) :
    divisionInput x ax ≠ 0 ∧
      multiplicationInput true x y ax ay ≠ 0 ∧
      action true x y ax ay = addPoint x y ax ay := by
  simp only [Addable, Bool.and_eq_true, Representable, decide_eq_true_eq,
    bne_iff_ne] at hadd
  simp only [Recoverable, bne_iff_ne] at hrec
  obtain ⟨⟨⟨⟨⟨hx, hy⟩, ⟨hax, hay⟩⟩, _⟩, _⟩, hne⟩ := hadd
  exact ⟨divisionInput_nonzero hx hax hne,
    enabled_multiplicationInput_nonzero hx hy hax hay hne hrec,
    enabled_action hx hy hax hay hne⟩

theorem disabled_domain {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hne : x ≠ ax) :
    divisionInput x ax ≠ 0 ∧
      multiplicationInput false x y ax ay ≠ 0 ∧
      action false x y ax ay = (x, y) := by
  have hd := divisionInput_nonzero hx hax hne
  exact ⟨hd, by simpa only [disabled_multiplicationInput] using hd,
    disabled_action hx hy hax hne⟩

theorem divisionInput_same_x {x : Nat} (hx : x < p) : divisionInput x x = 0 :=
  sub_self hx

theorem enabled_multiplicationInput_exception {x y ax ay : Nat}
    (hx : x < p) (hy : y < p) (hax : ax < p) (hay : ay < p)
    (hne : x ≠ ax) (hexception : (addPoint x y ax ay).1 = ax) :
    multiplicationInput true x y ax ay = 0 := by
  rw [enabled_multiplicationInput hx hy hax hay hne, hexception, sub_self hax]

end VQBridge.Curve.LuoPointAddition
