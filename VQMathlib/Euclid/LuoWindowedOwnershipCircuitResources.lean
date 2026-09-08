import VQMathlib.Euclid.LuoWindowedOwnershipScheduleResources

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

theorem upperWriterGates_ccx
    (source dirty boundary target step : Nat) :
    (upperWriterGates source dirty boundary target step).countP RGate.isCcx =
      ownershipUpperWriterToffoli step := by
  simp only [upperWriterGates]
  rw [LengthWriterPlaced.gates_ccx]
  rfl

theorem lowerWriterGates_ccx
    (source dirty boundary target step : Nat) :
    (lowerWriterGates source dirty boundary target step).countP RGate.isCcx =
      ownershipLowerWriterToffoli step := by
  simp only [lowerWriterGates]
  rw [LengthWriterPlaced.gates_ccx]
  rfl

theorem ownershipGates_ccx (step : Nat) :
    (ownershipGates step).countP RGate.isCcx =
      windowedOwnershipToffoli step := by
  simp only [ownershipGates, ownershipBodyGates, swapLengthGates,
    swapLengthOwnershipGates, upperBlockGates, lowerBlockGates,
    upperCancelGates, upperNewGates, lowerCancelGates, lowerNewGates,
    List.countP_append, List.countP_reverse, PackedSwapLength.placed,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    upperWriterGates_ccx, lowerWriterGates_ccx]
  rw [show
      PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
        PackedOwnership.prepareGates.countP RGate.isCcx +
        PackedTerminalEpoch.ownershipMaskGates.countP RGate.isCcx +
        PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
        (PackedOwnership.phaseClearGates.countP RGate.isCcx +
          ((SwapLength.fullSwap fullWidth endpointWidth).countP RGate.isCcx +
            ((SwapLength.upperPreparation 256 fullWidth endpointWidth).countP
                RGate.isCcx + ownershipUpperWriterToffoli step +
              ownershipUpperWriterToffoli step +
              (SwapLength.upperPreparation 256 fullWidth endpointWidth).countP
                RGate.isCcx) +
            ((SwapLength.lowerPreparation fullWidth endpointWidth).countP
              RGate.isCcx + ownershipLowerWriterToffoli step +
            ownershipLowerWriterToffoli step +
            (SwapLength.lowerPreparation fullWidth endpointWidth).countP
              RGate.isCcx) +
          PackedSwapLength.normalizationGates.countP RGate.isCcx) +
        PackedOwnership.phaseRestoreGates.countP RGate.isCcx +
        PackedOwnership.iterationGates.countP RGate.isCcx) +
        PackedTerminalEpoch.ownershipRestoreGates.countP RGate.isCcx +
        PackedOwnership.prepareGates.countP RGate.isCcx =
      ownershipFixedToffoli + ownershipWritersToffoli step by
    unfold ownershipFixedToffoli ownershipWritersToffoli
    omega]
  unfold windowedOwnershipToffoli
  rw [ownershipFixedToffoli_eq, fixedOwnershipToffoli_eq]

theorem roundGates_ccx (step : Nat) :
    (roundGates step).countP RGate.isCcx =
      roundToffoli step := by
  unfold roundToffoli
  unfold roundFixedToffoli
  exact roundGates_countP_of RGate.isCcx step _ (ownershipGates_ccx step)

end VQMathlib.LuoSchedule.WindowedOwnership
