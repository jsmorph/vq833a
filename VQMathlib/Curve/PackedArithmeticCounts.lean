import VQ.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQMathlib.Curve.PackedArithmeticCounts

open VQ VQ.Reversible
open VQ.Curve.PackedModularProduct VQ.Curve.PackedReversibleGapCorrection
open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

theorem controlledCarry_ccx (width : Nat) :
    (controlledCarryCircuit width).gates.countP RGate.isCcx = 10 * width + 1 := by
  simp only [controlledCarryCircuit, Reversible.control, ccx_controlGates,
    Adder.carryCircuit, Adder.carryGates_cx, Adder.carryGates_ccx]
  omega

theorem controlledBorrow_ccx (width : Nat) :
    (controlledBorrowCircuit width).gates.countP RGate.isCcx = 10 * width + 1 := by
  simp only [controlledBorrowCircuit, Reversible.control, ccx_controlGates,
    RCircuit.reverse, Adder.carryCircuit, List.countP_reverse,
    Adder.carryGates_cx, Adder.carryGates_ccx]
  omega

theorem carryProbe_ccx (value width : Nat) :
    (carryProbeGates value width).countP RGate.isCcx = 2 * (10 * width + 1) := by
  simp only [carryProbeGates, carryComputeGates, List.countP_append,
    List.countP_reverse, constantXorGates_no_ccx, controlledCarry_ccx,
    List.countP_cons, List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
  omega

theorem chunkAdd_ccx (value width : Nat) :
    (chunkAddGates value width).countP RGate.isCcx = 10 * width + 1 := by
  simp only [chunkAddGates, carryComputeGates, List.countP_append,
    constantXorGates_no_ccx, controlledCarry_ccx, Nat.zero_add, Nat.add_zero]

theorem borrowProbe_ccx (value width : Nat) :
    (borrowProbeGates value width).countP RGate.isCcx = 2 * (10 * width + 1) := by
  simp only [borrowProbeGates, borrowComputeGates, List.countP_append,
    List.countP_reverse, constantXorGates_no_ccx, controlledBorrow_ccx,
    List.countP_cons, List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false]
  omega

theorem detectionChunk_ccx (chunk : Nat) :
    (detectionChunkGates chunk).countP RGate.isCcx =
      2 * (10 * chunkWidthAt chunk + 1) := by
  simp only [detectionChunkGates, placedCarryProbeGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), carryProbe_ccx]

theorem additionChunk_ccx (chunk : Nat) :
    (additionChunkGates chunk).countP RGate.isCcx = 10 * chunkWidthAt chunk + 1 := by
  simp only [additionChunkGates, placedChunkAddGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), chunkAdd_ccx]

theorem borrowChunk_ccx (chunk : Nat) :
    (borrowChunkGates chunk).countP RGate.isCcx =
      2 * (10 * chunkWidthAt chunk + 1) := by
  simp only [borrowChunkGates, placedBorrowProbeGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), borrowProbe_ccx]

theorem detectionGates_ccx : detectionGates.countP RGate.isCcx = 10272 := by
  simp only [detectionGates, detectionComputeGates, detectionChunks,
    List.countP_append, List.countP_reverse, detectionChunk_ccx]
  decide +kernel

theorem correctionGates_ccx : correctionGates.countP RGate.isCcx = 7704 := by
  simp only [correctionGates, additionChunks, borrowChunks,
    List.countP_append, additionChunk_ccx, borrowChunk_ccx]
  decide +kernel

theorem variableAdd_ccx (width : Nat) :
    (VQ.Curve.PackedModularAddition.variableAddGates width).countP RGate.isCcx =
      10 * width + 1 := by
  simp only [VQ.Curve.PackedModularAddition.variableAddGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), controlledCarry_ccx]

theorem flagErase_ccx (width : Nat) :
    (VQ.Curve.PackedModularAddition.flagEraseGates width).countP RGate.isCcx =
      4 * width + 1 := by
  simp only [VQ.Curve.PackedModularAddition.flagEraseGates,
    VQ.Curve.PackedModularAddition.compareComputeGates, List.countP_append,
    List.countP_reverse, countP_map_gates (fun g => RGate.isCcx_map _ g),
    Adder.carryGates_ccx, List.countP_cons, List.countP_nil, RGate.isCcx,
    if_true]
  omega

theorem modularAddGates_ccx : modularAddGates.countP RGate.isCcx = 21562 := by
  simp only [modularAddGates, List.countP_append, variableAdd_ccx, flagErase_ccx,
    placedDetectionGates, placedCorrectionGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), detectionGates_ccx,
    correctionGates_ccx]
  decide +kernel

theorem modularDoubleGates_ccx : modularDoubleGates.countP RGate.isCcx = 17976 := by
  simp only [modularDoubleGates, VQ.Curve.PackedModularDoubling.doubleShiftGates,
    List.countP_append, placedDetectionGates, placedCorrectionGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), detectionGates_ccx,
    correctionGates_ccx, rotateLeftGates_ccx]
  decide +kernel

end VQMathlib.Curve.PackedArithmeticCounts
