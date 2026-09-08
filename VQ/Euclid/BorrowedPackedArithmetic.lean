import VQ.Euclid.BorrowedCompactInterval

namespace VQ.Euclid.BorrowedPackedArithmetic

open Reversible PackedStepLayout

def remainderIntervalReverseGates : List RGate :=
  placed intervalLayout remainderIntervalWiring compactBigEndianGates.reverse

def remainderIntervalNoSignGates : List RGate :=
  placed intervalLayout remainderIntervalWiring compactBigEndianNoSignGates

def coefficientGates : List RGate :=
  placed coefficientLayout coefficientWiring BorrowedCoefficient.gates

def phaseGates : List RGate :=
  placed phaseLayout phaseWiring BorrowedPhase.compactGates

theorem reverse_source :
    CompactIntervalVariants.bigEndianReverseCircuit.gates =
      CompactIntervalVariants.bigEndianCircuit.gates.reverse := by
  simp only [CompactIntervalVariants.bigEndianReverseCircuit,
    CompactIntervalVariants.bigEndianReverseSource, CompactIntervalVariants.bigEndianCircuit,
    IntervalBigEndian.circuit, RCircuit.relabel, List.map_reverse]

theorem remainderIntervalReverseGates_equiv :
    BorrowedEquivalent 570 PackedStepLayout.remainderIntervalReverseGates
      remainderIntervalReverseGates := by
  have hr := compactBigEndian_equiv.reverse
    CompactIntervalVariants.bigEndianCircuit_wellFormed compactBigEndian_wellFormed
  have hp := hr.map (place_inj (by decide) remainderInterval_disjoint)
    (List.all_eq_true.mp (show CompactIntervalVariants.bigEndianCircuit.gates.reverse.all
      (RGate.wellFormed intervalLayout.width) = true by
        rw [List.all_reverse]
        exact CompactIntervalVariants.bigEndianCircuit_wellFormed))
    (List.all_eq_true.mp (show compactBigEndianGates.reverse.all
      (RGate.wellFormed intervalLayout.width) = true by
        rw [List.all_reverse]
        exact compactBigEndian_wellFormed)) (by decide)
  rw [← reverse_source] at hp
  exact hp

theorem remainderIntervalNoSignGates_equiv :
    BorrowedEquivalent 570 PackedStepLayout.remainderIntervalNoSignGates
      remainderIntervalNoSignGates :=
  compactBigEndianNoSign_equiv.map (place_inj (by decide) remainderInterval_disjoint)
    (List.all_eq_true.mp CompactIntervalVariants.bigEndianNoSignCircuit_wellFormed)
    (List.all_eq_true.mp compactBigEndianNoSign_wellFormed) (by decide)

theorem coefficientGates_equiv :
    BorrowedEquivalent 570 PackedStepLayout.coefficientGates coefficientGates :=
  (show BorrowedEquivalent BorrowedCoefficient.borrowed CompactCoefficientDirty.gates
    BorrowedCoefficient.gates from
      ⟨BorrowedCoefficient.gates_clear, BorrowedCoefficient.gates_preserves⟩).map
    (place_inj (by decide) coefficient_disjoint)
    (List.all_eq_true.mp CompactCoefficientDirty.circuit_wellFormed)
    (List.all_eq_true.mp BorrowedCoefficient.gates_wellFormed) (by decide)

theorem phaseGates_equiv :
    BorrowedEquivalent 570 PackedStepLayout.phaseGates phaseGates :=
  (show BorrowedEquivalent 41 CompactPhase.gates BorrowedPhase.compactGates from
    ⟨BorrowedPhase.compactGates_projection, BorrowedPhase.compactGates_borrowed⟩).map
    (place_inj (by decide) phase_disjoint)
    (List.all_eq_true.mp CompactPhase.circuit_wellFormed)
    (List.all_eq_true.mp BorrowedPhase.compactGates_wellFormed) (by decide)

theorem remainderIntervalReverseGates_wellFormed :
    remainderIntervalReverseGates.all (RGate.wellFormed 571) = true := by
  apply wellFormed_placeGates remainderInterval_disjoint (by decide) remainderInterval_bound
  exact List.all_eq_true.mp (by rw [List.all_reverse]; exact compactBigEndian_wellFormed)

theorem remainderIntervalNoSignGates_wellFormed :
    remainderIntervalNoSignGates.all (RGate.wellFormed 571) = true :=
  wellFormed_placeGates remainderInterval_disjoint (by decide) remainderInterval_bound
    (List.all_eq_true.mp compactBigEndianNoSign_wellFormed)

theorem coefficientGates_wellFormed : coefficientGates.all (RGate.wellFormed 571) = true :=
  wellFormed_placeGates coefficient_disjoint (by decide) coefficient_bound
    (List.all_eq_true.mp BorrowedCoefficient.gates_wellFormed)

theorem phaseGates_wellFormed : phaseGates.all (RGate.wellFormed 571) = true :=
  wellFormed_placeGates phase_disjoint (by decide) phase_bound
    (List.all_eq_true.mp BorrowedPhase.compactGates_wellFormed)

end VQ.Euclid.BorrowedPackedArithmetic
