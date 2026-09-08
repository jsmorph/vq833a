import VQ.Euclid.BorrowedPackedRound

namespace VQ.Euclid.BorrowedPackedRound

open Reversible

theorem roundPrefixGates_ccx : roundPrefixGates.countP RGate.isCcx =
    LuoWindowedOwnership.roundPrefixGates.countP RGate.isCcx + 2070 := by
  simp only [roundPrefixGates, LuoWindowedOwnership.roundPrefixGates,
    prefixRemainderGates, PackedTerminalEpoch.prefixRemainderGates,
    remainderBlocks, PackedPhaseFourPrefix.remainderBlocks,
    remainderSubBlock, PackedPhaseFourPrefix.remainderSubBlock,
    remainderAddBlock, PackedPhaseFourPrefix.remainderAddBlock,
    remainderSubBody, PackedPhaseFourPrefix.remainderSubBody,
    remainderAddBody, PackedPhaseFourPrefix.remainderAddBody,
    phaseGates, PackedTerminalEpoch.phaseGates, Step.around,
    List.countP_append, List.countP_reverse,
    BorrowedPackedArithmetic.remainderIntervalReverseGates_ccx,
    BorrowedPackedArithmetic.remainderIntervalNoSignGates_ccx,
    BorrowedPackedArithmetic.coefficientGates_ccx, BorrowedPackedArithmetic.phaseGates_ccx]
  omega

def addedToffoli (step : Nat) : Nat :=
  2047 + 8 * (LuoWindowedOwnership.ownershipUpperWorkWidth step +
    LuoWindowedOwnership.ownershipLowerWorkWidth step)

theorem roundGates_ccx {step : Nat} (hstep : step ≤ 1620) :
    (roundGates step).countP RGate.isCcx =
      (LuoWindowedOwnership.roundGates step).countP RGate.isCcx + addedToffoli step := by
  simp only [roundGates, LuoWindowedOwnership.roundGates, List.countP_append,
    roundPrefixGates_ccx, addedToffoli]
  have h := BorrowedWindowedOwnership.ownershipGates_ccx hstep
  omega

def addedFrom : Nat → Nat → Nat
  | _, 0 => 0
  | first, count + 1 => addedToffoli first + addedFrom (first + 1) count

theorem roundsGatesFrom_ccx {first count : Nat} (hbound : first + count ≤ 1621) :
    (roundsGatesFrom first count).countP RGate.isCcx =
      (LuoWindowedOwnership.roundsGatesFrom first count).countP RGate.isCcx + addedFrom first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    simp only [roundsGatesFrom, LuoWindowedOwnership.roundsGatesFrom, List.countP_append, addedFrom]
    rw [roundGates_ccx (by omega), ih (by omega)]
    omega

theorem roundsGates_ccx {count : Nat} (hbound : count ≤ 1620) :
    (roundsGates count).countP RGate.isCcx =
      (LuoWindowedOwnership.roundsGates count).countP RGate.isCcx + addedFrom 1 count :=
  roundsGatesFrom_ccx (by omega)

theorem fullSchedule_added : addedFrom 1 1620 = 7341124 := by native_decide

theorem fullSchedule_ccx : (roundsGates 1620).countP RGate.isCcx =
    (LuoWindowedOwnership.roundsGates 1620).countP RGate.isCcx + 7341124 := by
  rw [roundsGates_ccx (by decide), fullSchedule_added]

end VQ.Euclid.BorrowedPackedRound
