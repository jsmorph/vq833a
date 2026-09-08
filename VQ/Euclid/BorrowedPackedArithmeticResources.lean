import VQ.Euclid.BorrowedPackedArithmetic

namespace VQ.Euclid.BorrowedPackedArithmetic

open Reversible PackedStepLayout

theorem remainderIntervalReverseGates_ccx :
    remainderIntervalReverseGates.countP RGate.isCcx =
      PackedStepLayout.remainderIntervalReverseGates.countP RGate.isCcx + 518 := by
  simp only [remainderIntervalReverseGates, PackedStepLayout.remainderIntervalReverseGates,
    placed, compactBigEndianGates, reverse_source, List.countP_reverse,
    countP_map_gates (RGate.isCcx_map _), CompactIntervalVariants.bigEndianCircuit,
    RCircuit.relabel, IntervalBigEndian.circuit, CompactIntervalVariants.intervalWorkWidth,
    CompactIntervalVariants.intervalEndpointWidth, CompactInterval.workWidth, CompactInterval.endpointWidth]
  exact BorrowedIntervalBigEndian.gates_ccx 259 9

theorem remainderIntervalNoSignGates_ccx :
    remainderIntervalNoSignGates.countP RGate.isCcx =
      PackedStepLayout.remainderIntervalNoSignGates.countP RGate.isCcx + 518 := by
  simp only [remainderIntervalNoSignGates, PackedStepLayout.remainderIntervalNoSignGates,
    placed, compactBigEndianNoSignGates,
    countP_map_gates (RGate.isCcx_map _), CompactIntervalVariants.bigEndianNoSignCircuit,
    RCircuit.relabel, IntervalBigEndian.noSignCircuit, CompactIntervalVariants.intervalWorkWidth,
    CompactIntervalVariants.intervalEndpointWidth, CompactInterval.workWidth, CompactInterval.endpointWidth]
  exact BorrowedIntervalBigEndian.noSignGates_ccx 259 9

theorem coefficientGates_ccx : coefficientGates.countP RGate.isCcx =
    PackedStepLayout.coefficientGates.countP RGate.isCcx + 1028 := by
  simp only [coefficientGates, PackedStepLayout.coefficientGates, placed,
    countP_map_gates (RGate.isCcx_map _), BorrowedCoefficient.gates_ccx]

theorem phaseGates_ccx : phaseGates.countP RGate.isCcx =
    PackedStepLayout.phaseGates.countP RGate.isCcx + 6 := by
  simp only [phaseGates, PackedStepLayout.phaseGates, placed,
    countP_map_gates (RGate.isCcx_map _), BorrowedPhase.compactGates_ccx]
  have h : CompactPhase.gates.countP RGate.isCcx = 94 := by native_decide
  omega

end VQ.Euclid.BorrowedPackedArithmetic
