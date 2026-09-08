import VQ.Euclid.BorrowedIntervalBigEndian
import VQ.Euclid.BorrowedCoefficientResources
import VQ.Euclid.BorrowedPhaseProjection
import VQ.Euclid.PackedStepLayout

namespace VQ.Euclid.BorrowedPackedArithmetic

open Reversible PackedStepLayout

def compactBigEndianGates : List RGate :=
  (BorrowedIntervalBigEndian.gates 259 9).map (RGate.map CompactInterval.packWire)

def compactBigEndianNoSignGates : List RGate :=
  (BorrowedIntervalBigEndian.noSignGates 259 9).map (RGate.map CompactInterval.packWire)

theorem compactBigEndian_equiv :
    BorrowedEquivalent 549 CompactIntervalVariants.bigEndianCircuit.gates
      compactBigEndianGates := by
  simp only [CompactIntervalVariants.bigEndianCircuit, CompactIntervalVariants.intervalWorkWidth,
    CompactIntervalVariants.intervalEndpointWidth, CompactInterval.workWidth,
    CompactInterval.endpointWidth, RCircuit.relabel, IntervalBigEndian.circuit,
    compactBigEndianGates]
  exact (BorrowedIntervalBigEndian.gates_equiv 259 9).map CompactInterval.packWire_injective
    (List.all_eq_true.mp (IntervalBigEndian.circuit_wellFormed 259 9))
    (List.all_eq_true.mp (BorrowedIntervalBigEndian.gates_wellFormed 259 9)) (by decide)

theorem compactBigEndianNoSign_equiv :
    BorrowedEquivalent 549 CompactIntervalVariants.bigEndianNoSignCircuit.gates
      compactBigEndianNoSignGates := by
  simp only [CompactIntervalVariants.bigEndianNoSignCircuit, CompactIntervalVariants.intervalWorkWidth,
    CompactIntervalVariants.intervalEndpointWidth, CompactInterval.workWidth,
    CompactInterval.endpointWidth, RCircuit.relabel, IntervalBigEndian.noSignCircuit,
    compactBigEndianNoSignGates]
  exact (BorrowedIntervalBigEndian.noSignGates_equiv 259 9).map CompactInterval.packWire_injective
    (List.all_eq_true.mp (IntervalBigEndian.noSignCircuit_wellFormed 259 9))
    (List.all_eq_true.mp (BorrowedIntervalBigEndian.noSignGates_wellFormed 259 9)) (by decide)

theorem compactBigEndian_wellFormed :
    compactBigEndianGates.all (RGate.wellFormed 550) = true := by native_decide

theorem compactBigEndianNoSign_wellFormed :
    compactBigEndianNoSignGates.all (RGate.wellFormed 550) = true := by native_decide

end VQ.Euclid.BorrowedPackedArithmetic
