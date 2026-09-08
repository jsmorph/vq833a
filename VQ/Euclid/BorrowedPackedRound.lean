import VQ.Euclid.BorrowedPackedArithmeticResources
import VQ.Euclid.BorrowedOwnership
import VQ.Euclid.LuoWindowedOwnershipSchedule

namespace VQ.Euclid.BorrowedPackedRound

open Reversible

def remainderSubBody : List RGate :=
  PackedStepLayout.remainderPrepareGates ++
    BorrowedPackedArithmetic.remainderIntervalReverseGates ++ PackedStepLayout.remainderCleanupGates

def remainderAddBody : List RGate :=
  PackedStepLayout.remainderPrepareGates ++
    BorrowedPackedArithmetic.remainderIntervalNoSignGates ++ PackedStepLayout.remainderCleanupGates

def remainderSubBlock : List RGate :=
  Step.around PackedPhaseFourPrefix.remainderSubControlGates remainderSubBody

def remainderAddBlock : List RGate :=
  Step.around PackedPhaseFourPrefix.remainderAddControlGates remainderAddBody

def remainderBlocks : List RGate :=
  Step.around PackedPhaseFourPrefix.rPrimeSelectorGates
    (remainderSubBlock ++ PackedPhaseFourPrefix.remainderFlipGates ++ remainderAddBlock)

def prefixRemainderGates : List RGate :=
  remainderBlocks ++ PackedPhaseFourPrefix.quotientIncrementBlock ++
    PackedPhaseFourPrefix.swapBlock ++ PackedPhaseFourPrefix.quotientDecrementBlock

def phaseGates : List RGate :=
  BorrowedPackedArithmetic.phaseGates ++ PackedTerminalEpoch.phaseCorrectionGates

def roundPrefixGates : List RGate :=
  PackedTerminalEpoch.entryGates ++ prefixRemainderGates ++
    BorrowedPackedArithmetic.coefficientGates ++ PackedShift.postShiftGates ++ phaseGates

def roundGates (step : Nat) : List RGate :=
  roundPrefixGates ++ BorrowedWindowedOwnership.ownershipGates step ++ PackedTerminalEpoch.exitGates

def roundsGatesFrom : Nat → Nat → List RGate
  | _, 0 => []
  | first, count + 1 => roundGates first ++ roundsGatesFrom (first + 1) count

def roundsGates (count : Nat) : List RGate := roundsGatesFrom 1 count

private theorem entry_below : PackedTerminalEpoch.entryGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem prepare_below : PackedStepLayout.remainderPrepareGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem subControl_below : PackedPhaseFourPrefix.remainderSubControlGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem addControl_below : PackedPhaseFourPrefix.remainderAddControlGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem selector_below : PackedPhaseFourPrefix.rPrimeSelectorGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem flip_below : PackedPhaseFourPrefix.remainderFlipGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem quotientIncrement_below : PackedPhaseFourPrefix.quotientIncrementBlock.all (RGate.wellFormed 570) = true := by native_decide

private theorem swap_below : PackedPhaseFourPrefix.swapBlock.all (RGate.wellFormed 570) = true := by native_decide

private theorem quotientDecrement_below : PackedPhaseFourPrefix.quotientDecrementBlock.all (RGate.wellFormed 570) = true := by native_decide

private theorem postShift_below : PackedShift.postShiftGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem phaseCorrection_below : PackedTerminalEpoch.phaseCorrectionGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem exit_below : PackedTerminalEpoch.exitGates.all (RGate.wellFormed 570) = true := by native_decide

private theorem equiv_of_below {gs : List RGate} (h : gs.all (RGate.wellFormed 570) = true) :
    BorrowedEquivalent 570 gs gs :=
  BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)

private theorem around_equiv {control old new : List RGate}
    (hc : control.all (RGate.wellFormed 570) = true) (h : BorrowedEquivalent 570 old new) :
    BorrowedEquivalent 570 (Step.around control old) (Step.around control new) :=
  ((equiv_of_below hc).append h).append ((equiv_of_below hc).reverse hc hc)

theorem remainderSubBody_equiv :
    BorrowedEquivalent 570 PackedPhaseFourPrefix.remainderSubBody remainderSubBody :=
  ((equiv_of_below prepare_below).append
    BorrowedPackedArithmetic.remainderIntervalReverseGates_equiv).append
    ((equiv_of_below prepare_below).reverse prepare_below prepare_below)

theorem remainderAddBody_equiv :
    BorrowedEquivalent 570 PackedPhaseFourPrefix.remainderAddBody remainderAddBody :=
  ((equiv_of_below prepare_below).append
    BorrowedPackedArithmetic.remainderIntervalNoSignGates_equiv).append
    ((equiv_of_below prepare_below).reverse prepare_below prepare_below)

theorem remainderBlocks_equiv :
    BorrowedEquivalent 570 PackedPhaseFourPrefix.remainderBlocks remainderBlocks :=
  around_equiv selector_below
    (((around_equiv subControl_below remainderSubBody_equiv).append
      (equiv_of_below flip_below)).append (around_equiv addControl_below remainderAddBody_equiv))

theorem prefixRemainderGates_equiv :
    BorrowedEquivalent 570 PackedTerminalEpoch.prefixRemainderGates prefixRemainderGates :=
  ((remainderBlocks_equiv.append (equiv_of_below quotientIncrement_below)).append
    (equiv_of_below swap_below)).append (equiv_of_below quotientDecrement_below)

theorem phaseGates_equiv :
    BorrowedEquivalent 570 PackedTerminalEpoch.phaseGates phaseGates :=
  BorrowedPackedArithmetic.phaseGates_equiv.append (equiv_of_below phaseCorrection_below)

theorem roundPrefixGates_equiv :
    BorrowedEquivalent 570 LuoWindowedOwnership.roundPrefixGates roundPrefixGates :=
  ((((equiv_of_below entry_below).append prefixRemainderGates_equiv).append
    BorrowedPackedArithmetic.coefficientGates_equiv).append
    (equiv_of_below postShift_below)).append phaseGates_equiv

theorem roundGates_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.roundGates step) (roundGates step) :=
  (roundPrefixGates_equiv.append (BorrowedWindowedOwnership.ownershipGates_equiv hstep)).append
    (equiv_of_below exit_below)

theorem roundsGatesFrom_equiv {first count : Nat} (hbound : first + count ≤ 1621) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.roundsGatesFrom first count)
      (roundsGatesFrom first count) := by
  induction count generalizing first with
  | zero => exact BorrowedEquivalent.nil _
  | succ count ih => exact (roundGates_equiv (by omega)).append (ih (by omega))

theorem roundsGates_equiv {count : Nat} (hbound : count ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.roundsGates count) (roundsGates count) :=
  roundsGatesFrom_equiv (by omega)

private theorem weaken {gs : List RGate} (h : gs.all (RGate.wellFormed 570) = true) :
    gs.all (RGate.wellFormed 571) = true :=
  List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
    (List.all_eq_true.mp h g hg))

theorem roundPrefixGates_wellFormed : roundPrefixGates.all (RGate.wellFormed 571) = true := by
  simp only [roundPrefixGates, prefixRemainderGates, remainderBlocks,
    remainderSubBlock, remainderAddBlock, remainderSubBody, remainderAddBody,
    phaseGates, Step.around, List.all_append, List.all_reverse,
    PackedStepLayout.remainderCleanupGates,
    weaken entry_below,
    weaken prepare_below,
    weaken subControl_below,
    weaken addControl_below,
    weaken selector_below,
    weaken flip_below,
    weaken quotientIncrement_below,
    weaken swap_below,
    weaken quotientDecrement_below,
    weaken postShift_below,
    weaken phaseCorrection_below,
    BorrowedPackedArithmetic.remainderIntervalReverseGates_wellFormed,
    BorrowedPackedArithmetic.remainderIntervalNoSignGates_wellFormed,
    BorrowedPackedArithmetic.coefficientGates_wellFormed,
    BorrowedPackedArithmetic.phaseGates_wellFormed, Bool.and_self]

theorem roundGates_wellFormed {step : Nat} (hstep : step ≤ 1620) :
    (roundGates step).all (RGate.wellFormed 571) = true := by
  simp only [roundGates, List.all_append, roundPrefixGates_wellFormed,
    BorrowedWindowedOwnership.ownershipGates_wellFormed hstep, weaken exit_below, Bool.and_self]

theorem roundsGatesFrom_wellFormed {first count : Nat} (hbound : first + count ≤ 1621) :
    (roundsGatesFrom first count).all (RGate.wellFormed 571) = true := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    simp only [roundsGatesFrom, List.all_append, Bool.and_eq_true]
    exact ⟨roundGates_wellFormed (by omega), ih (by omega)⟩

theorem roundsGates_wellFormed {count : Nat} (hbound : count ≤ 1620) :
    (roundsGates count).all (RGate.wellFormed 571) = true :=
  roundsGatesFrom_wellFormed (by omega)

theorem roundsGates_reverse_equiv {count : Nat} (hbound : count ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.roundsGates count).reverse
      (roundsGates count).reverse :=
  (roundsGates_equiv hbound).reverse (LuoWindowedOwnership.roundsGates_wellFormed hbound)
    (roundsGates_wellFormed hbound)

end VQ.Euclid.BorrowedPackedRound
