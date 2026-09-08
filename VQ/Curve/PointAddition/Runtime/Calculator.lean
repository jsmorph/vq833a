import VQ.Curve.PointAddition.Runtime.SelectPoint
import VQMathlib.Curve.Total

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def logicalOffsetY (inverse : Bool) : Nat := if inverse then 35 else 5

def equalFlag (inverse : Bool) : Nat := if inverse then 4 else 3

def negFlag (inverse : Bool) : Nat := if inverse then 3 else 4

def prepareTail (offsetY equalFlag negFlag : Nat) : List RGate :=
  ordinary offsetY ++ doubling ++ selector equalFlag negFlag ++ selection offsetY

def prepare (inverse : Bool) : List RGate :=
  setup ++ prepareTail (logicalOffsetY inverse) (equalFlag inverse) (negFlag inverse)

theorem boolNat_mod_two (b : Bool) : boolNat b % 2 = boolNat b := by
  cases b <;> rfl

theorem neg_neg_of_lt {a : Nat} (ha : a < VQ.Curve.p) :
    VQ.Curve.neg (VQ.Curve.neg a) = a := by
  calc
    VQ.Curve.neg (VQ.Curve.neg a) = VQ.Curve.neg (VQ.Curve.sub 0 a) := rfl
    _ = VQ.Curve.sub a 0 := VQ.Curve.neg_sub VQ.Curve.p_pos ha
    _ = VQ.Curve.add (VQ.Curve.sub a 0) 0 :=
      (VQ.Curve.add_zero (VQ.Curve.sub_lt a 0)).symm
    _ = a := VQ.Curve.sub_add_cancel ha VQ.Curve.p_pos

theorem setupFields_preserved {v : Nat → Nat} {i : Nat}
    (h8 : i ≠ 8) (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11)
    (h12 : i ≠ 12) (h13 : i ≠ 13) (h35 : i ≠ 35) :
    setupFields v i = v i := by
  simp [setupFields, setAt, h8, h9, h10, h11, h12, h13, h35]

theorem setupFlags_preserved {v flags : Nat → Nat} {i : Nat}
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3)
    (h4 : i ≠ 4) : setupFlags v flags i = flags i := by
  simp [setupFlags, setAt, h0, h1, h2, h3, h4]

theorem State.stepPrepareTail {I offsetY equalFlag negFlag logicalY : Nat}
    {v flags : Nat → Nat} (s : State I v flags)
    (hyIndex : offsetY = 5 ∨ offsetY = 35)
    (hindices : (equalFlag = 3 ∧ negFlag = 4) ∨
      (equalFlag = 4 ∧ negFlag = 3))
    (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (hax : v 4 < VQ.Curve.p) (hlogicalY : v offsetY = logicalY)
    (hlogicalYLt : logicalY < VQ.Curve.p)
    (hresultClear : v 6 = 0 ∧ v 7 = 0)
    (hordinaryClear : ∀ i, 14 ≤ i → i ≤ 22 → v i = 0)
    (hdoubleClear : ∀ i, 23 ≤ i → i ≤ 34 → v i = 0)
    (h0 : flags 0 = boolNat (VQ.Curve.OnCurve (v 0) (v 1)))
    (h1 : flags 1 = boolNat (VQ.Curve.OnCurve (v 4) logicalY))
    (h2 : flags 2 = boolNat (v 0 == v 4))
    (heq : flags equalFlag = boolNat (v 1 == logicalY))
    (hneg : flags negFlag = boolNat (v 1 == VQ.Curve.neg logicalY))
    (hselectorClear : ∀ i, 5 ≤ i → i ≤ 13 → flags i = 0) :
    ∃ v' flags',
      State (actGates (prepareTail offsetY equalFlag negFlag) I) v' flags' ∧
      (v' 6, v' 7) = VQ.Curve.totalAdd (v 0) (v 1) (v 4) logicalY := by
  obtain ⟨vOrd, sOrd, hordX, hordY, hordKeep⟩ :=
    s.stepOrdinary hyIndex hx hy hax
      (by simpa [hlogicalY] using hlogicalYLt)
      (hordinaryClear 14 (by decide) (by decide))
      (hordinaryClear 15 (by decide) (by decide))
      (hordinaryClear 16 (by decide) (by decide))
      (hordinaryClear 17 (by decide) (by decide))
      (hordinaryClear 18 (by decide) (by decide))
      (hordinaryClear 19 (by decide) (by decide))
      (hordinaryClear 20 (by decide) (by decide))
      (hordinaryClear 21 (by decide) (by decide))
      (hordinaryClear 22 (by decide) (by decide))
  obtain ⟨vDouble, sDouble, hdoubleX, hdoubleY, hdoubleKeep⟩ :=
    sOrd.stepDoubling
      (by rw [hordKeep 0 (by decide) (Or.inl (by decide))]; exact hx)
      (by rw [hordKeep 1 (by decide) (Or.inl (by decide))]; exact hy)
      (by rw [hordKeep 23 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 23 (by decide) (by decide))
      (by rw [hordKeep 24 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 24 (by decide) (by decide))
      (by rw [hordKeep 25 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 25 (by decide) (by decide))
      (by rw [hordKeep 26 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 26 (by decide) (by decide))
      (by rw [hordKeep 27 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 27 (by decide) (by decide))
      (by rw [hordKeep 28 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 28 (by decide) (by decide))
      (by rw [hordKeep 29 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 29 (by decide) (by decide))
      (by rw [hordKeep 30 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 30 (by decide) (by decide))
      (by rw [hordKeep 31 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 31 (by decide) (by decide))
      (by rw [hordKeep 32 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 32 (by decide) (by decide))
      (by rw [hordKeep 33 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 33 (by decide) (by decide))
      (by rw [hordKeep 34 (by decide) (Or.inr (by decide))];
          exact hdoubleClear 34 (by decide) (by decide))
  have sSelector := sDouble.stepSelector hindices
  have sSelection := sSelector.stepSelection hyIndex
  have hactive := selectorFlags_active hindices h0 h1 h2 heq hneg
    (hselectorClear 5 (by decide) (by decide))
    (hselectorClear 6 (by decide) (by decide))
    (hselectorClear 7 (by decide) (by decide))
    (hselectorClear 8 (by decide) (by decide))
    (hselectorClear 9 (by decide) (by decide))
    (hselectorClear 10 (by decide) (by decide))
    (hselectorClear 11 (by decide) (by decide))
    (hselectorClear 12 (by decide) (by decide))
    (hselectorClear 13 (by decide) (by decide))
  let negActive := VQ.Curve.OnCurve (v 0) (v 1) &&
    VQ.Curve.OnCurve (v 4) logicalY && ((v 0 == v 4) && (v 1 == VQ.Curve.neg logicalY))
  let doubleActive := VQ.Curve.OnCurve (v 0) (v 1) &&
    VQ.Curve.OnCurve (v 4) logicalY && !((v 0 == v 4) && (v 1 == VQ.Curve.neg logicalY)) &&
      ((v 0 == v 4) && (v 1 == logicalY))
  let ordinaryActive := VQ.Curve.OnCurve (v 0) (v 1) &&
    VQ.Curve.OnCurve (v 4) logicalY && !((v 0 == v 4) && (v 1 == VQ.Curve.neg logicalY)) &&
      !((v 0 == v 4) && (v 1 == logicalY))
  have hexclusive := branchFlags_exclusive
    (VQ.Curve.OnCurve (v 0) (v 1) && VQ.Curve.OnCurve (v 4) logicalY)
    ((v 0 == v 4) && (v 1 == VQ.Curve.neg logicalY))
    ((v 0 == v 4) && (v 1 == logicalY))
  have hselected := selectionFields_active
    (offsetY := offsetY) (v := vDouble)
    (flags := selectorFlags equalFlag negFlag flags)
    (negActive := negActive) (doubleActive := doubleActive)
    (ordinaryActive := ordinaryActive) hyIndex
    (by
      rw [hdoubleKeep 6 (by decide) (Or.inl (by decide))]
      rw [hordKeep 6 (by decide) (Or.inl (by decide))]
      exact hresultClear.1)
    (by
      rw [hdoubleKeep 7 (by decide) (Or.inl (by decide))]
      rw [hordKeep 7 (by decide) (Or.inl (by decide))]
      exact hresultClear.2)
    (by simpa [negActive] using hactive.1)
    (by simpa [doubleActive] using hactive.2.1)
    (by simpa [ordinaryActive] using hactive.2.2)
    hexclusive.1 hexclusive.2.1 hexclusive.2.2
  refine ⟨selectionFields offsetY vDouble (selectorFlags equalFlag negFlag flags),
    selectorFlags equalFlag negFlag flags, ?_, ?_⟩
  · simpa [prepareTail, actGates_append] using sSelection
  · rw [hselected]
    have hsourceX : vDouble 0 = v 0 := by
      rw [hdoubleKeep 0 (by decide) (Or.inl (by decide)),
        hordKeep 0 (by decide) (Or.inl (by decide))]
    have hsourceY : vDouble 1 = v 1 := by
      rw [hdoubleKeep 1 (by decide) (Or.inl (by decide)),
        hordKeep 1 (by decide) (Or.inl (by decide))]
    have hoffsetX : vDouble 4 = v 4 := by
      rw [hdoubleKeep 4 (by decide) (Or.inl (by decide)),
        hordKeep 4 (by decide) (Or.inl (by decide))]
    have hoffsetY : vDouble offsetY = logicalY := by
      have hoffsetField : offsetY < fieldCount := by
        rcases hyIndex with rfl | rfl <;> decide
      have hoffsetDouble : offsetY < 23 ∨ 34 < offsetY := by
        rcases hyIndex with rfl | rfl <;> simp
      have hoffsetOrdinary : offsetY < 14 ∨ 22 < offsetY := by
        rcases hyIndex with rfl | rfl <;> simp
      rw [hdoubleKeep offsetY hoffsetField hoffsetDouble,
        hordKeep offsetY hoffsetField hoffsetOrdinary, hlogicalY]
    have hordX' : vDouble 19 =
        (VQ.Curve.addPoint (v 0) (v 1) (v 4) logicalY).1 := by
      rw [hdoubleKeep 19 (by decide) (Or.inl (by decide)), hordX, hlogicalY]
    have hordY' : vDouble 22 =
        (VQ.Curve.addPoint (v 0) (v 1) (v 4) logicalY).2 := by
      rw [hdoubleKeep 22 (by decide) (Or.inl (by decide)), hordY, hlogicalY]
    have hordSourceX : vOrd 0 = v 0 := by
      rw [hordKeep 0 (by decide) (Or.inl (by decide))]
    have hordSourceY : vOrd 1 = v 1 := by
      rw [hordKeep 1 (by decide) (Or.inl (by decide))]
    have hdoubleX' : vDouble 32 =
        (VQ.Curve.doublePoint (v 0) (v 1)).1 := by
      rw [hdoubleX, hordSourceX, hordSourceY]
    have hdoubleY' : vDouble 34 =
        (VQ.Curve.doublePoint (v 0) (v 1)).2 := by
      rw [hdoubleY, hordSourceX, hordSourceY]
    rw [hsourceX, hsourceY, hoffsetX, hoffsetY, hordX', hordY',
      hdoubleX', hdoubleY']
    exact selectedPoint_totalAdd (v 0) (v 1) (v 4) logicalY

theorem State.stepPrepareAdd {I : Nat} {v flags : Nat → Nat}
    (s : State I v flags)
    (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (hax : v 4 < VQ.Curve.p) (hay : v 5 < VQ.Curve.p)
    (hclear : ∀ i, 6 ≤ i → i < fieldCount → v i = 0)
    (hflags : ∀ i, i < flagCount → flags i = 0) :
    ∃ v' flags', State (actGates (prepare false) I) v' flags' ∧
      (v' 6, v' 7) = VQ.Curve.totalAdd (v 0) (v 1) (v 4) (v 5) := by
  have sSetup := s.stepSetup hx hy hax hay
    (hclear 8 (by decide) (by decide)) (hclear 9 (by decide) (by decide))
    (hclear 10 (by decide) (by decide)) (hclear 11 (by decide) (by decide))
    (hclear 12 (by decide) (by decide)) (hclear 13 (by decide) (by decide))
    (hclear 35 (by decide) (by decide)) (hclear 36 (by decide) (by decide))
    (hclear 37 (by decide) (by decide))
  obtain ⟨v', flags', stail, hvalue⟩ := sSetup.stepPrepareTail
    (logicalY := v 5) (Or.inl rfl)
    (Or.inl ⟨rfl, rfl⟩ : (3 = 3 ∧ 4 = 4) ∨ (3 = 4 ∧ 4 = 3))
    (by simpa [setupFields, setAt] using hx)
    (by simpa [setupFields, setAt] using hy)
    (by simpa [setupFields, setAt] using hax)
    (by simp [setupFields, setAt]) hay
    (by
      constructor
      · rw [setupFields_preserved (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hclear 6 (by decide) (by decide)
      · rw [setupFields_preserved (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hclear 7 (by decide) (by decide))
    (by
      intro i hi hlo
      rw [setupFields_preserved (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact hclear i (by omega) (by simp [fieldCount]; omega))
    (by
      intro i hi hlo
      rw [setupFields_preserved (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact hclear i (by omega) (by simp [fieldCount]; omega))
    (by simp [setupFlags, setupFields, setAt, hflags 0 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 1 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 2 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 3 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 4 (by decide), boolNat_mod_two])
    (by
      intro i hi hlo
      rw [setupFlags_preserved (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hflags i (by simp [flagCount]; omega))
  refine ⟨v', flags', ?_, ?_⟩
  · simpa [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      actGates_append] using stail
  · simpa [setupFields, setAt] using hvalue

theorem State.stepPrepareSub {I : Nat} {v flags : Nat → Nat}
    (s : State I v flags)
    (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (hax : v 4 < VQ.Curve.p) (hay : v 5 < VQ.Curve.p)
    (hclear : ∀ i, 6 ≤ i → i < fieldCount → v i = 0)
    (hflags : ∀ i, i < flagCount → flags i = 0) :
    ∃ v' flags', State (actGates (prepare true) I) v' flags' ∧
      (v' 6, v' 7) = VQ.Curve.totalSub (v 0) (v 1) (v 4) (v 5) := by
  have sSetup := s.stepSetup hx hy hax hay
    (hclear 8 (by decide) (by decide)) (hclear 9 (by decide) (by decide))
    (hclear 10 (by decide) (by decide)) (hclear 11 (by decide) (by decide))
    (hclear 12 (by decide) (by decide)) (hclear 13 (by decide) (by decide))
    (hclear 35 (by decide) (by decide)) (hclear 36 (by decide) (by decide))
    (hclear 37 (by decide) (by decide))
  have hnegneg : VQ.Curve.neg (VQ.Curve.neg (v 5)) = v 5 := neg_neg_of_lt hay
  obtain ⟨v', flags', stail, hvalue⟩ := sSetup.stepPrepareTail
    (logicalY := VQ.Curve.neg (v 5)) (Or.inr rfl)
    (Or.inr ⟨rfl, rfl⟩ : (4 = 3 ∧ 3 = 4) ∨ (4 = 4 ∧ 3 = 3))
    (by simpa [setupFields, setAt] using hx)
    (by simpa [setupFields, setAt] using hy)
    (by simpa [setupFields, setAt] using hax)
    (by simp [setupFields, setAt, hclear 35 (by decide) (by decide)])
    (VQ.Curve.neg_lt (v 5))
    (by
      constructor
      · rw [setupFields_preserved (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hclear 6 (by decide) (by decide)
      · rw [setupFields_preserved (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hclear 7 (by decide) (by decide))
    (by
      intro i hi hlo
      rw [setupFields_preserved (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact hclear i (by omega) (by simp [fieldCount]; omega))
    (by
      intro i hi hlo
      rw [setupFields_preserved (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact hclear i (by omega) (by simp [fieldCount]; omega))
    (by simp [setupFlags, setupFields, setAt, hflags 0 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 1 (by decide), boolNat_mod_two,
        VQBridge.Curve.onCurve_neg_eq])
    (by simp [setupFlags, setupFields, setAt, hflags 2 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 4 (by decide), boolNat_mod_two])
    (by simp [setupFlags, setupFields, setAt, hflags 3 (by decide), boolNat_mod_two,
        hnegneg])
    (by
      intro i hi hlo
      rw [setupFlags_preserved (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hflags i (by simp [flagCount]; omega))
  refine ⟨v', flags', ?_, ?_⟩
  · simpa [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      actGates_append] using stail
  · simpa [setupFields, setAt, VQ.Curve.totalSub] using hvalue

end VQ.Curve.PointAddition.Runtime
