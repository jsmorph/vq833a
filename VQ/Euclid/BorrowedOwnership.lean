import VQ.Euclid.BorrowedWindowedOwnershipResources
import VQ.Reversible.BorrowedPermutationProjection

namespace VQ.Euclid.BorrowedWindowedOwnership

open Reversible LuoWindowedOwnership

def ownershipMaskGates : List RGate :=
  BorrowedPermutation.swap PackedStepLayout.extensionWire PackedStepLayout.signWire
    PackedOwnership.controlWire PackedStepLayout.phaseOneWire 570

def ownershipGates (step : Nat) : List RGate :=
  PackedPhaseFourPrefix.rPrimeSelectorGates ++
    PackedOwnership.prepareGates ++ ownershipMaskGates ++
    PackedPhaseFourPrefix.rPrimeSelectorGates.reverse ++
    ownershipBodyGates step ++ PackedTerminalEpoch.ownershipRestoreGates ++
    PackedOwnership.prepareGates

private theorem selector_below : PackedPhaseFourPrefix.rPrimeSelectorGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem prepare_below : PackedOwnership.prepareGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem phaseClear_below : PackedOwnership.phaseClearGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem phaseRestore_below : PackedOwnership.phaseRestoreGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem iteration_below : PackedOwnership.iterationGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem restore_below : PackedTerminalEpoch.ownershipRestoreGates.all
    (RGate.wellFormed 570) = true := by native_decide

private theorem equiv_of_below {gs : List RGate}
    (h : gs.all (RGate.wellFormed 570) = true) : BorrowedEquivalent 570 gs gs :=
  BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)

theorem ownershipMaskGates_equiv :
    BorrowedEquivalent 570 PackedTerminalEpoch.ownershipMaskGates ownershipMaskGates :=
  BorrowedPermutation.swap_equiv (by decide) (by decide)
    (by unfold BorrowedPermutation.Valid; decide)

theorem ownershipBodyGates_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.ownershipBodyGates step)
      (ownershipBodyGates step) :=
  (((equiv_of_below phaseClear_below).append (swapLengthGates_equiv hstep)).append
    (equiv_of_below phaseRestore_below)).append (equiv_of_below iteration_below)

theorem ownershipGates_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.ownershipGates step)
      (ownershipGates step) := by
  have hs := equiv_of_below selector_below
  have hp := equiv_of_below prepare_below
  exact (((((hs.append hp).append ownershipMaskGates_equiv).append
    (hs.reverse selector_below selector_below)).append
    (ownershipBodyGates_equiv hstep)).append (equiv_of_below restore_below)).append hp

theorem ownershipMaskGates_wellFormed :
    ownershipMaskGates.all (RGate.wellFormed 571) = true := by decide

private theorem weaken {gs : List RGate} (h : gs.all (RGate.wellFormed 570) = true) :
    gs.all (RGate.wellFormed 571) = true :=
  List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
    (List.all_eq_true.mp h g hg))

theorem ownershipGates_wellFormed {step : Nat} (hstep : step ≤ 1620) :
    (ownershipGates step).all (RGate.wellFormed 571) = true := by
  have hw := swapLengthGates_wellFormed hstep
  rw [PackedStepLayout.layout_width] at hw
  simp only [ownershipGates, ownershipBodyGates, List.all_append, List.all_reverse,
    weaken selector_below, weaken prepare_below, ownershipMaskGates_wellFormed,
    weaken phaseClear_below, weaken phaseRestore_below, weaken iteration_below,
    weaken restore_below, hw, Bool.and_self]

theorem ownershipGates_reverse_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.ownershipGates step).reverse
      (ownershipGates step).reverse :=
  (ownershipGates_equiv hstep).reverse
    (LuoWindowedOwnership.ownershipGates_wellFormed hstep)
    (ownershipGates_wellFormed hstep)

theorem ownershipMaskGates_ccx : ownershipMaskGates.countP RGate.isCcx =
    PackedTerminalEpoch.ownershipMaskGates.countP RGate.isCcx + 1 := by decide

theorem ownershipGates_ccx {step : Nat} (hstep : step ≤ 1620) :
    (ownershipGates step).countP RGate.isCcx + 23 =
      (LuoWindowedOwnership.ownershipGates step).countP RGate.isCcx +
        8 * (ownershipUpperWorkWidth step + ownershipLowerWorkWidth step) := by
  simp only [ownershipGates, LuoWindowedOwnership.ownershipGates,
    ownershipBodyGates, LuoWindowedOwnership.ownershipBodyGates,
    List.countP_append, List.countP_reverse, ownershipMaskGates_ccx]
  have h := swapLengthGates_ccx hstep
  omega

end VQ.Euclid.BorrowedWindowedOwnership
