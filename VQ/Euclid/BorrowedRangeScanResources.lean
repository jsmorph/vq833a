import VQ.Euclid.BorrowedRangeScan

namespace VQ.Euclid.BorrowedRangeScan

open Reversible RangeZero

theorem upperRelation_wellFormed
    {j workWidth endpointWidth : Nat} (hj : j + 1 < workWidth) :
    (upperRelation j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply BorrowedRangeZero.maskedNotAnd_wellFormed <;>
    simp [accumulatorWire, temporaryWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire] <;>
    omega

theorem upperBase_wellFormed
    {j workWidth endpointWidth : Nat} (hj : j < workWidth) :
    (upperBase j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply BorrowedRangeZero.maskedNotBit_wellFormed <;>
    simp [accumulatorWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.outerWire] <;>
    omega

theorem lowerRelation_wellFormed
    {j workWidth endpointWidth : Nat} (hjpos : 0 < j) (hj : j < workWidth) :
    (lowerRelation j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply BorrowedRangeZero.maskedNotAnd_wellFormed <;>
    simp [accumulatorWire, temporaryWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire] <;>
    omega

theorem upperForward_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (upperForward workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨upperBase_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩
      | succ count =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨⟨upperRelation_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩,
            ih (label := label + 1) (j := j + 1) (by omega)⟩

theorem upperReverseEdges_wellFormed
    {workWidth endpointWidth topLabel topIndex count : Nat}
    (hindices : count ≤ topIndex) (hwork : topIndex < workWidth) :
    (upperReverseEdges workWidth endpointWidth topLabel topIndex count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing topLabel topIndex with
  | zero => rfl
  | succ count ih =>
      simp only [upperReverseEdges, List.all_append, Bool.and_eq_true]
      exact ⟨⟨endpointToggle_wellFormed (topLabel - 1) workWidth endpointWidth,
        upperRelation_wellFormed (by omega)⟩,
        ih (topLabel := topLabel - 1) (topIndex := topIndex - 1)
          (by omega) (by omega)⟩

theorem lowerForward_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (lowerForward workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨upperBase_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩
      | succ count =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨⟨lowerRelation_wellFormed (by omega) (by omega),
            endpointToggle_wellFormed (label + count + 1)
              workWidth endpointWidth⟩,
            ih (label := label) (j := j) (by omega)⟩

theorem lowerReverse_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (lowerReverse workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [lowerReverse, List.all_append, Bool.and_eq_true]
          exact ⟨⟨ih (label := label) (j := j) (by omega),
            endpointToggle_wellFormed (label + count + 1)
              workWidth endpointWidth⟩,
            lowerRelation_wellFormed (by omega) (by omega)⟩

theorem upperGates_wellFormed (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      simp only [upperGates, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨⟨boundaryControl_wellFormed (count + 1) endpointWidth,
          upperForward_wellFormed (by omega)⟩,
        endpointToggle_wellFormed (start + count) (count + 1) endpointWidth⟩,
        upperReverseEdges_wellFormed (by omega) (by omega)⟩,
        boundaryControl_wellFormed (count + 1) endpointWidth⟩

theorem lowerGates_wellFormed (start workWidth endpointWidth : Nat) :
    (lowerGates start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      simp only [lowerGates, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨⟨boundaryControl_wellFormed (count + 1) endpointWidth,
          lowerForward_wellFormed (by omega)⟩,
        endpointToggle_wellFormed start (count + 1) endpointWidth⟩,
        lowerReverse_wellFormed (by omega)⟩,
        boundaryControl_wellFormed (count + 1) endpointWidth⟩

theorem upperRelation_ccx (j workWidth endpointWidth : Nat) :
    (upperRelation j workWidth endpointWidth).countP RGate.isCcx =
      (RangeZero.upperRelation j workWidth endpointWidth).countP RGate.isCcx + 1 := by
  simp only [upperRelation, RangeZero.upperRelation, BorrowedRangeZero.maskedNotAnd_ccx,
    RangeZero.maskedNotAndGates_ccx]

theorem upperBase_ccx (j workWidth endpointWidth : Nat) :
    (upperBase j workWidth endpointWidth).countP RGate.isCcx + 1 =
      (RangeZero.upperBase j workWidth endpointWidth).countP RGate.isCcx := by
  simp only [upperBase, RangeZero.upperBase, BorrowedRangeZero.maskedNotBit_ccx,
    RangeZero.maskedNotBitGates_ccx]

theorem lowerRelation_ccx (j workWidth endpointWidth : Nat) :
    (lowerRelation j workWidth endpointWidth).countP RGate.isCcx =
      (RangeZero.lowerRelation j workWidth endpointWidth).countP RGate.isCcx + 1 := by
  simp only [lowerRelation, RangeZero.lowerRelation, BorrowedRangeZero.maskedNotAnd_ccx,
    RangeZero.maskedNotAndGates_ccx]

theorem upperForward_ccx (workWidth endpointWidth : Nat) : ∀ count label j,
    (upperForward workWidth endpointWidth label j (count + 1)).countP RGate.isCcx + 2 =
      (RangeZero.upperForward workWidth endpointWidth label j (count + 1)).countP RGate.isCcx + count + 1 := by
  intro count
  induction count with
  | zero =>
    intro label j
    simp only [upperForward, RangeZero.upperForward, List.countP_append]
    have h := upperBase_ccx j workWidth endpointWidth
    omega
  | succ count ih =>
    intro label j
    simp only [upperForward, RangeZero.upperForward, List.countP_append, upperRelation_ccx]
    have h := ih (label + 1) (j + 1)
    omega

theorem upperReverseEdges_ccx (workWidth endpointWidth : Nat) : ∀ count label j,
    (upperReverseEdges workWidth endpointWidth label j count).countP RGate.isCcx =
      (RangeZero.upperReverseEdges workWidth endpointWidth label j count).countP RGate.isCcx + count := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro label j
    simp only [upperReverseEdges, RangeZero.upperReverseEdges, List.countP_append,
      upperRelation_ccx, ih]
    omega

theorem lowerForward_ccx (workWidth endpointWidth : Nat) : ∀ count label j,
    (lowerForward workWidth endpointWidth label j (count + 1)).countP RGate.isCcx + 2 =
      (RangeZero.lowerForward workWidth endpointWidth label j (count + 1)).countP RGate.isCcx + count + 1 := by
  intro count
  induction count with
  | zero =>
    intro label j
    simp only [lowerForward, RangeZero.lowerForward, List.countP_append]
    have h := upperBase_ccx j workWidth endpointWidth
    omega
  | succ count ih =>
    intro label j
    simp only [lowerForward, RangeZero.lowerForward, List.countP_append, lowerRelation_ccx]
    have h := ih label j
    omega

theorem lowerReverse_ccx (workWidth endpointWidth : Nat) : ∀ count label j,
    (lowerReverse workWidth endpointWidth label j count).countP RGate.isCcx =
      (RangeZero.lowerReverse workWidth endpointWidth label j count).countP RGate.isCcx + (count - 1) := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro label j
    cases count with
    | zero => rfl
    | succ count =>
      simp only [lowerReverse, RangeZero.lowerReverse, List.countP_append,
        lowerRelation_ccx, ih]
      omega

theorem upperGates_ccx (start count endpointWidth : Nat) :
    (upperGates start (count + 1) endpointWidth).countP RGate.isCcx + 3 =
      (RangeZero.upperGates start (count + 1) endpointWidth).countP RGate.isCcx + 2 * (count + 1) := by
  simp only [upperGates, RangeZero.upperGates, List.countP_append, upperReverseEdges_ccx]
  have h := upperForward_ccx (count + 1) endpointWidth count start 0
  omega

theorem lowerGates_ccx (start count endpointWidth : Nat) :
    (lowerGates start (count + 1) endpointWidth).countP RGate.isCcx + 3 =
      (RangeZero.lowerGates start (count + 1) endpointWidth).countP RGate.isCcx + 2 * (count + 1) := by
  simp only [lowerGates, RangeZero.lowerGates, List.countP_append, lowerReverse_ccx]
  have h := lowerForward_ccx (count + 1) endpointWidth count start 0
  omega

theorem upperGates_reverse_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperGates start workWidth endpointWidth).reverse
      (upperGates start workWidth endpointWidth).reverse :=
  (upperGates_equiv start workWidth endpointWidth).reverse
    (RangeZero.upperGates_wellFormed start workWidth endpointWidth)
    (upperGates_wellFormed start workWidth endpointWidth)

theorem lowerGates_reverse_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.lowerGates start workWidth endpointWidth).reverse
      (lowerGates start workWidth endpointWidth).reverse :=
  (lowerGates_equiv start workWidth endpointWidth).reverse
    (RangeZero.lowerGates_wellFormed start workWidth endpointWidth)
    (lowerGates_wellFormed start workWidth endpointWidth)

end VQ.Euclid.BorrowedRangeScan
