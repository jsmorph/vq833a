import VQ.Curve.PointAddition.Runtime.Select

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def selection (offsetY : Nat) : List RGate :=
  C 0 6 ++ C 1 7 ++
  K 7 0 6 ++ K 7 4 6 ++ K 7 1 7 ++ K 7 offsetY 7 ++
  K 11 0 6 ++ K 11 32 6 ++ K 11 1 7 ++ K 11 34 7 ++
  K 13 0 6 ++ K 13 19 6 ++ K 13 1 7 ++ K 13 22 7

def selectionFields (offsetY : Nat) (v flags : Nat → Nat) : Nat → Nat :=
  let v1 := setAt v 6 (v 6 ^^^ v 0)
  let v2 := setAt v1 7 (v1 7 ^^^ v1 1)
  let v3 := setAt v2 6 (v2 6 ^^^ flags 7 * v2 0)
  let v4 := setAt v3 6 (v3 6 ^^^ flags 7 * v3 4)
  let v5 := setAt v4 7 (v4 7 ^^^ flags 7 * v4 1)
  let v6 := setAt v5 7 (v5 7 ^^^ flags 7 * v5 offsetY)
  let v7 := setAt v6 6 (v6 6 ^^^ flags 11 * v6 0)
  let v8 := setAt v7 6 (v7 6 ^^^ flags 11 * v7 32)
  let v9 := setAt v8 7 (v8 7 ^^^ flags 11 * v8 1)
  let v10 := setAt v9 7 (v9 7 ^^^ flags 11 * v9 34)
  let v11 := setAt v10 6 (v10 6 ^^^ flags 13 * v10 0)
  let v12 := setAt v11 6 (v11 6 ^^^ flags 13 * v11 19)
  let v13 := setAt v12 7 (v12 7 ^^^ flags 13 * v12 1)
  setAt v13 7 (v13 7 ^^^ flags 13 * v13 22)

theorem State.stepSelection {I offsetY : Nat} {v flags : Nat → Nat}
    (s : State I v flags) (hyIndex : offsetY = 5 ∨ offsetY = 35) :
    State (actGates (selection offsetY) I) (selectionFields offsetY v flags) flags := by
  have hyf : offsetY < fieldCount := by rcases hyIndex with rfl | rfl <;> decide
  have hy7 : offsetY ≠ 7 := by omega
  have s1 := s.stepC (by decide : 0 < fieldCount) (by decide : 6 < fieldCount)
    (by decide)
  have s2 := s1.stepC (by decide : 1 < fieldCount) (by decide : 7 < fieldCount)
    (by decide)
  have s3 := s2.stepK (by decide : 7 < flagCount) (by decide : 0 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s4 := s3.stepK (by decide : 7 < flagCount) (by decide : 4 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s5 := s4.stepK (by decide : 7 < flagCount) (by decide : 1 < fieldCount)
    (by decide : 7 < fieldCount) (by decide)
  have s6 := s5.stepK (by decide : 7 < flagCount) hyf
    (by decide : 7 < fieldCount) hy7
  have s7 := s6.stepK (by decide : 11 < flagCount) (by decide : 0 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s8 := s7.stepK (by decide : 11 < flagCount) (by decide : 32 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s9 := s8.stepK (by decide : 11 < flagCount) (by decide : 1 < fieldCount)
    (by decide : 7 < fieldCount) (by decide)
  have s10 := s9.stepK (by decide : 11 < flagCount) (by decide : 34 < fieldCount)
    (by decide : 7 < fieldCount) (by decide)
  have s11 := s10.stepK (by decide : 13 < flagCount) (by decide : 0 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s12 := s11.stepK (by decide : 13 < flagCount) (by decide : 19 < fieldCount)
    (by decide : 6 < fieldCount) (by decide)
  have s13 := s12.stepK (by decide : 13 < flagCount) (by decide : 1 < fieldCount)
    (by decide : 7 < fieldCount) (by decide)
  have s14 := s13.stepK (by decide : 13 < flagCount) (by decide : 22 < fieldCount)
    (by decide : 7 < fieldCount) (by decide)
  simpa [selection, selectionFields, actGates_append] using s14

def selectedPoint (negActive doubleActive ordinaryActive : Bool)
    (source offset doubled ordinary : Nat × Nat) : Nat × Nat :=
  if negActive then offset
  else if doubleActive then doubled
  else if ordinaryActive then ordinary
  else source

theorem selectionFields_active {offsetY : Nat} {v flags : Nat → Nat}
    {negActive doubleActive ordinaryActive : Bool}
    (hyIndex : offsetY = 5 ∨ offsetY = 35)
    (h6 : v 6 = 0) (h7 : v 7 = 0)
    (hn : flags 7 = boolNat negActive)
    (hd : flags 11 = boolNat doubleActive)
    (ho : flags 13 = boolNat ordinaryActive)
    (hnd : negActive = true → doubleActive = false)
    (hno : negActive = true → ordinaryActive = false)
    (hdo : doubleActive = true → ordinaryActive = false) :
    (selectionFields offsetY v flags 6, selectionFields offsetY v flags 7) =
      selectedPoint negActive doubleActive ordinaryActive
        (v 0, v 1) (v 4, v offsetY) (v 32, v 34) (v 19, v 22) := by
  rcases hyIndex with rfl | rfl <;>
    cases negActive <;> cases doubleActive <;> cases ordinaryActive <;>
    simp_all [selectionFields, selectedPoint, boolNat, setAt]

theorem branchFlags_exclusive (both negCase equalCase : Bool) :
    ((both && negCase) = true → (both && !negCase && equalCase) = false) ∧
    ((both && negCase) = true → (both && !negCase && !equalCase) = false) ∧
    ((both && !negCase && equalCase) = true →
      (both && !negCase && !equalCase) = false) := by
  cases both <;> cases negCase <;> cases equalCase <;> simp

theorem selectedPoint_totalAdd (x y ax ay : Nat) :
    selectedPoint
        (VQ.Curve.OnCurve x y && VQ.Curve.OnCurve ax ay &&
          ((x == ax) && (y == VQ.Curve.neg ay)))
        (VQ.Curve.OnCurve x y && VQ.Curve.OnCurve ax ay &&
          !((x == ax) && (y == VQ.Curve.neg ay)) && ((x == ax) && (y == ay)))
        (VQ.Curve.OnCurve x y && VQ.Curve.OnCurve ax ay &&
          !((x == ax) && (y == VQ.Curve.neg ay)) && !((x == ax) && (y == ay)))
        (x, y) (ax, ay) (VQ.Curve.doublePoint x y)
        (VQ.Curve.addPoint x y ax ay) =
      VQ.Curve.totalAdd x y ax ay := by
  rw [VQ.Curve.totalAdd]
  split <;> rename_i hboth
  · split <;> rename_i hneg
    · simp [selectedPoint, hboth, hneg]
    · split <;> rename_i hequal
      · have hequal' : x = ax ∧ y = ay := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using hequal
        rcases hequal' with ⟨rfl, rfl⟩
        have hboth' : VQ.Curve.OnCurve x y = true ∧ VQ.Curve.OnCurve x y = true := by
          simpa only [Bool.and_eq_true] using hboth
        have hon := hboth'.1
        have hyneg : y ≠ VQ.Curve.neg y := by
          intro h
          apply hneg
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨trivial, h⟩
        have hnegCase : ((x == x) && (y == VQ.Curve.neg y)) = false := by
          rw [show (x == x) = true by simp,
            beq_eq_false_iff_ne.mpr hyneg]
          decide
        have hequalCase : ((x == x) && (y == y)) = true := by simp
        have hnActive :
            (VQ.Curve.OnCurve x y && VQ.Curve.OnCurve x y &&
              ((x == x) && (y == VQ.Curve.neg y))) = false := by
          simp only [hnegCase, Bool.and_false]
        have hdActive :
            (VQ.Curve.OnCurve x y && VQ.Curve.OnCurve x y &&
              !((x == x) && (y == VQ.Curve.neg y)) && ((x == x) && (y == y))) =
              true := by
          simp only [hon, hnegCase, hequalCase, Bool.not_false, Bool.and_self]
        have hnNot :
            ¬(VQ.Curve.OnCurve x y && VQ.Curve.OnCurve x y &&
              ((x == x) && (y == VQ.Curve.neg y))) = true := by
          rw [hnActive]
          decide
        unfold selectedPoint
        rw [if_neg hnNot, if_pos hdActive]
      · simp [selectedPoint, hboth, hneg, hequal]
  · simp [selectedPoint, hboth]

end VQ.Curve.PointAddition.Runtime
