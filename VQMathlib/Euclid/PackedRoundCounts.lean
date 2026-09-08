import VQMathlib.Euclid.LuoWindowedOwnershipRoundCircuit
import VQMathlib.Euclid.IntervalCounts

namespace VQMathlib.Euclid.PackedRoundCounts

open VQ VQ.Euclid VQ.Reversible
open VQ.Euclid.LuoWindowedOwnership
open VQMathlib.LuoSchedule.WindowedOwnership

theorem remainderReverse_ccx :
    PackedStepLayout.remainderIntervalReverseGates.countP RGate.isCcx =
      33929 := by
  simp only [PackedStepLayout.remainderIntervalReverseGates,
    PackedStepLayout.placed, CompactIntervalVariants.bigEndianReverseCircuit,
    CompactIntervalVariants.bigEndianReverseSource, RCircuit.relabel,
    countP_map_gates (fun g => RGate.isCcx_map _ g), List.countP_reverse]
  exact (IntervalCounts.gates_ccx 259).trans (by decide)

theorem remainderNoSign_ccx :
    PackedStepLayout.remainderIntervalNoSignGates.countP RGate.isCcx =
      33929 := by
  simp only [PackedStepLayout.remainderIntervalNoSignGates,
    PackedStepLayout.placed, CompactIntervalVariants.bigEndianNoSignCircuit,
    IntervalBigEndian.noSignCircuit, RCircuit.relabel,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact (IntervalCounts.noSignGates_ccx 259).trans (by decide)

theorem coefficientGates_ccx :
    CompactCoefficientDirty.gates.countP RGate.isCcx = 5780 := by
  have hadd : (LuoCoefficientPass.prefixAddGates CompactCoefficientDirty.count).countP
      RGate.isCcx = 2823 :=
    (LuoCoefficientPass.prefixAddGates_resources (by decide) (by decide)).2.1
  have hsub : (LuoCoefficientPass.prefixSubGates CompactCoefficientDirty.count).countP
      RGate.isCcx = 2823 :=
    (LuoCoefficientPass.prefixSubGates_resources (by decide) (by decide)).2.1
  simp only [CompactCoefficientDirty.gates, CompactCoefficientDirty.middleGates,
    CompactCoefficientDirty.subtractBlockGates, Step.around,
    LuoCoefficientPass.addBlockGates, List.countP_append, List.countP_reverse,
    LuoCoefficientPass.prepareGates_ccx, LuoCoefficientPass.restoreGates_ccx,
    hadd, hsub]
  decide +kernel

theorem shiftGates_ccx :
    PackedStepLayout.shiftGates.countP RGate.isCcx = 966 := by
  simp only [PackedStepLayout.shiftGates, PackedStepLayout.placed,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact (Shift.circuit_ccx 259 9).trans (by decide +kernel)

theorem selectSwapGates_ccx :
    PackedStepLayout.selectSwapGates.countP RGate.isCcx = 789 := by
  simp only [PackedStepLayout.selectSwapGates, PackedStepLayout.placed,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact CompactSelectSwap.gates_ccx.trans (by decide +kernel)

private theorem roundFixedCount_decomposition (predicate : RGate → Bool) :
    roundFixedCount predicate =
      PackedTerminalEpoch.entryGates.countP predicate +
        PackedTerminalEpoch.prefixRemainderGates.countP predicate +
        PackedStepLayout.coefficientGates.countP predicate +
        PackedShift.postShiftGates.countP predicate +
        PackedTerminalEpoch.phaseGates.countP predicate +
        PackedTerminalEpoch.exitGates.countP predicate := by
  simp only [roundFixedCount, roundPrefixGates, List.countP_append]

set_option maxRecDepth 8192 in
theorem roundFixedCount_ccx : roundFixedCount RGate.isCcx = 77405 := by
  have h := roundFixedCount_decomposition RGate.isCcx
  simp only [
    PackedTerminalEpoch.entryGates, PackedTerminalEpoch.prefixRemainderGates,
    PackedTerminalEpoch.phaseGates, PackedTerminalEpoch.exitGates,
    PackedTerminalEpoch.paddingGates, PackedTerminalEpoch.phaseCorrectionGates,
    PackedPhaseFourPrefix.preShiftBlock, PackedShift.postShiftGates,
    PackedPhaseFourPrefix.remainderBlocks,
    PackedPhaseFourPrefix.remainderSubBlock, PackedPhaseFourPrefix.remainderAddBlock,
    PackedPhaseFourPrefix.remainderSubBody, PackedPhaseFourPrefix.remainderAddBody,
    PackedPhaseFourPrefix.swapBlock, PackedPhaseFourPrefix.swapBody, Step.around,
    remainderReverse_ccx, remainderNoSign_ccx, shiftGates_ccx, selectSwapGates_ccx,
    PackedStepLayout.coefficientGates, PackedStepLayout.phaseGates,
    PackedStepLayout.placed, List.countP_append, List.countP_reverse,
    countP_map_gates (fun g => RGate.isCcx_map _ g), coefficientGates_ccx] at h
  exact h.trans (by decide +kernel)

end VQMathlib.Euclid.PackedRoundCounts
