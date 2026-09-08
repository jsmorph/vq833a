import VQMathlib.Euclid.LengthWriterCounts
import VQ.Euclid.PackedInputPreparation

namespace VQMathlib.Euclid.PackedInputCounts

open VQ VQ.Euclid VQ.Reversible
open LengthWriterCounts

theorem endpointToggle_ccx (value workWidth : Nat) :
    (RangeZero.endpointToggle value workWidth 8).countP RGate.isCcx = 27 := by
  unfold RangeZero.endpointToggle Interval.leftToggle Interval.endpointGates
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)]
  change (Endpoint.gates value 8).countP RGate.isCcx = 27
  simp only [Endpoint.gates, Endpoint.selectorGates, List.countP_append,
    Placed.selector_ccx, Selector.circuit, Selector.gates, List.countP_reverse,
    Selector.masks_ccx, Selector.conjunction_ccx, List.length_range]
  rfl

theorem upperForward_ccx (workWidth label j count : Nat) :
    (RangeZero.upperForward workWidth 8 label j count).countP RGate.isCcx =
      30 * count - 1 := by
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
    (RangeZero.upperReverseEdges workWidth 8 label j count).countP
      RGate.isCcx = 30 * count := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
    simp only [RangeZero.upperReverseEdges, List.countP_append,
      RangeZero.upperRelation, RangeZero.maskedNotAndGates_ccx,
      endpointToggle_ccx, ih]
    omega

theorem upperZero_ccx (start workWidth : Nat) :
    (RangeZero.upperGates start workWidth 8).countP RGate.isCcx =
      60 * workWidth - 4 := by
  cases workWidth with
  | zero => rfl
  | succ count =>
    simp only [RangeZero.upperGates, List.countP_append, upperForward_ccx,
      upperReverseEdges_ccx, endpointToggle_ccx, List.countP_cons,
      List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
    omega

theorem upperGates_ccx (start workWidth : Nat) :
    (LengthWriter.upperGates start workWidth 8).countP RGate.isCcx =
      2 * dirtyCount (LengthWriter.upperDelta start 8) 8 workWidth +
        2 * (60 * workWidth - 4) := by
  simp only [LengthWriter.upperGates, List.countP_append,
    controlledXorGates_ccx, LengthWriter.upperDirtyGates, dirtyWrite_ccx,
    upperZero_ccx]
  omega

set_option maxRecDepth 4096 in
theorem length_ccx : PackedInputLength.gates.countP RGate.isCcx = 31610 := by
  simp only [PackedInputLength.gates, PackedInputLength.setupGates,
    PackedInputLength.coreGates, List.countP_append, List.countP_reverse,
    constantXorGates_no_ccx, LengthWriterPlaced.gates_ccx,
    PackedInputLength.workWidth, PackedInputLength.endpointWidth,
    upperGates_ccx, List.countP_cons, List.countP_nil, RGate.isCcx,
    Bool.false_eq_true, if_false]
  decide +kernel

theorem comparison_ccx (p : Nat) :
    (PackedInputNormalization.compareGates p).countP RGate.isCcx = 1024 := by
  simp only [PackedInputNormalization.compareGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    PackedInputNormalization.compareLocalGates,
    PackedInputNormalization.compareComputeGates, List.countP_append,
    List.countP_reverse, constantXorGates_no_ccx, Adder.carryGates_ccx,
    List.countP_cons, List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
  rfl

theorem normalization_ccx (p : Nat) :
    (PackedInputNormalization.normalizeGates p).countP RGate.isCcx = 2570 := by
  simp only [PackedInputNormalization.normalizeGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    PackedInputNormalization.normalizeLocalCircuit, Reversible.control,
    PackedInputNormalization.normalizeSource, ccx_controlGates,
    ConstantArithmetic.constMinusGates_ccx, ConstantArithmetic.constMinusGates_cx]
  rfl

theorem encoding_ccx (p : Nat) :
    (PackedInputEncoding.gates p).countP RGate.isCcx = 0 := by
  simp only [PackedInputEncoding.gates, PackedInputEncoding.moveGates,
    PackedInputEncoding.fixedGates, List.countP_append,
    InputPreparation.moveReverseGates_ccx, constantXorGates_no_ccx,
    Nat.add_zero]

theorem gates_ccx (p : Nat) :
    (PackedInputPreparation.gates p).countP RGate.isCcx = 35204 := by
  simp only [PackedInputPreparation.gates, PackedInputNormalization.gates,
    List.countP_append, comparison_ccx, normalization_ccx, length_ccx,
    encoding_ccx]

end VQMathlib.Euclid.PackedInputCounts
