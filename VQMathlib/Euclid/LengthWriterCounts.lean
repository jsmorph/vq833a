import VQ.Euclid.LengthWriter

namespace VQMathlib.Euclid.LengthWriterCounts

open VQ VQ.Euclid VQ.Reversible

theorem endpointToggle_ccx (value workWidth : Nat) :
    (RangeZero.endpointToggle value workWidth 9).countP RGate.isCcx = 31 := by
  unfold RangeZero.endpointToggle Interval.leftToggle Interval.endpointGates
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)]
  change (Endpoint.gates value 9).countP RGate.isCcx = 31
  simp only [Endpoint.gates, Endpoint.selectorGates, List.countP_append,
    Placed.selector_ccx, Selector.circuit, Selector.gates, List.countP_reverse,
    Selector.masks_ccx, Selector.conjunction_ccx, List.length_range]
  rfl

theorem upperForward_ccx (workWidth label j count : Nat) :
    (RangeZero.upperForward workWidth 9 label j count).countP RGate.isCcx =
      34 * count - 1 := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero =>
      simp [RangeZero.upperForward, RangeZero.upperBase,
        RangeZero.maskedNotBitGates_ccx, endpointToggle_ccx]
    | succ count =>
      simp only [RangeZero.upperForward, List.countP_append,
        RangeZero.upperRelation, RangeZero.maskedNotAndGates_ccx,
        endpointToggle_ccx, ih]
      omega

theorem upperReverseEdges_ccx (workWidth label j count : Nat) :
    (RangeZero.upperReverseEdges workWidth 9 label j count).countP
      RGate.isCcx = 34 * count := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
    simp only [RangeZero.upperReverseEdges, List.countP_append,
      RangeZero.upperRelation, RangeZero.maskedNotAndGates_ccx,
      endpointToggle_ccx, ih]
    omega

theorem lowerForward_ccx (workWidth label j count : Nat) :
    (RangeZero.lowerForward workWidth 9 label j count).countP RGate.isCcx =
      34 * count - 1 := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero =>
      simp [RangeZero.lowerForward, RangeZero.upperBase,
        RangeZero.maskedNotBitGates_ccx, endpointToggle_ccx]
    | succ count =>
      simp only [RangeZero.lowerForward, List.countP_append,
        RangeZero.lowerRelation, RangeZero.maskedNotAndGates_ccx,
        endpointToggle_ccx, ih]
      omega

theorem lowerReverse_ccx (workWidth label j count : Nat) :
    (RangeZero.lowerReverse workWidth 9 label j count).countP RGate.isCcx =
      34 * (count - 1) := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [RangeZero.lowerReverse, List.countP_append,
        RangeZero.lowerRelation, RangeZero.maskedNotAndGates_ccx,
        endpointToggle_ccx, ih]
      omega

theorem upperZero_ccx (start workWidth : Nat) :
    (RangeZero.upperGates start workWidth 9).countP RGate.isCcx =
      68 * workWidth - 4 := by
  cases workWidth with
  | zero => rfl
  | succ count =>
    simp only [RangeZero.upperGates, List.countP_append, upperForward_ccx,
      upperReverseEdges_ccx, endpointToggle_ccx, List.countP_cons,
      List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
    omega

theorem lowerZero_ccx (start workWidth : Nat) :
    (RangeZero.lowerGates start workWidth 9).countP RGate.isCcx =
      68 * workWidth - 4 := by
  cases workWidth with
  | zero => rfl
  | succ count =>
    simp only [RangeZero.lowerGates, List.countP_append, lowerForward_ccx,
      lowerReverse_ccx, endpointToggle_ccx, List.countP_cons,
      List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
    omega

def selectedBits : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value =>
    (if value % 2 = 1 then 1 else 0) + selectedBits width (value / 2)

theorem doubleControlledXor_ccx (first second target width value : Nat) :
    (doubleControlledXorGates first second target width value).countP
      RGate.isCcx = selectedBits width value := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
    simp only [doubleControlledXorGates, List.countP_append, selectedBits, ih]
    split <;> simp [RGate.isCcx]

def dirtyCount (delta : Nat → Nat) (width : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => selectedBits width (delta count) + dirtyCount delta width count

theorem dirtyWrite_ccx (delta : Nat → Nat)
    (control dirty target width count : Nat) :
    (LengthWriter.dirtyWriteGates delta control dirty target width count).countP
      RGate.isCcx = dirtyCount delta width count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [LengthWriter.dirtyWriteGates, List.countP_append,
      doubleControlledXor_ccx, ih, dirtyCount]

theorem dirtyWriteAscending_ccx (delta : Nat → Nat)
    (control dirty target width count : Nat) :
    (LengthWriter.dirtyWriteGatesAscending delta control dirty target width
      count).countP RGate.isCcx = dirtyCount delta width count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [LengthWriter.dirtyWriteGatesAscending, List.countP_append,
      doubleControlledXor_ccx, ih, dirtyCount, Nat.add_comm]

theorem upperGates_ccx (start workWidth : Nat) :
    (LengthWriter.upperGates start workWidth 9).countP RGate.isCcx =
      2 * dirtyCount (LengthWriter.upperDelta start 9) 9 workWidth +
        2 * (68 * workWidth - 4) := by
  simp only [LengthWriter.upperGates, List.countP_append,
    controlledXorGates_ccx, LengthWriter.upperDirtyGates, dirtyWrite_ccx,
    upperZero_ccx]
  omega

theorem lowerGates_ccx (n start workWidth : Nat) :
    (LengthWriter.lowerGates n start workWidth 9).countP RGate.isCcx =
      2 * dirtyCount (LengthWriter.lowerDelta n start workWidth 9) 9 workWidth +
        2 * (68 * workWidth - 4) := by
  simp only [LengthWriter.lowerGates, List.countP_append,
    controlledXorGates_ccx, LengthWriter.lowerDirtyGates, dirtyWriteAscending_ccx,
    lowerZero_ccx]
  omega

end VQMathlib.Euclid.LengthWriterCounts
