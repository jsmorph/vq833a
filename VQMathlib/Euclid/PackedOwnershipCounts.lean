import VQ.Euclid.PackedTerminalEpoch

namespace VQMathlib.Euclid.PackedOwnershipCounts

open VQ VQ.Euclid VQ.Reversible

def fixedCount : Nat :=
  PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
    PackedOwnership.prepareGates.countP RGate.isCcx +
    PackedTerminalEpoch.ownershipMaskGates.countP RGate.isCcx +
    PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
    PackedOwnership.phaseClearGates.countP RGate.isCcx +
    (SwapLength.fullSwap 259 9).countP RGate.isCcx +
    2 * (SwapLength.upperPreparation 256 259 9).countP RGate.isCcx +
    2 * (SwapLength.lowerPreparation 259 9).countP RGate.isCcx +
    PackedSwapLength.normalizationGates.countP RGate.isCcx +
    PackedOwnership.phaseRestoreGates.countP RGate.isCcx +
    PackedOwnership.iterationGates.countP RGate.isCcx +
    PackedTerminalEpoch.ownershipRestoreGates.countP RGate.isCcx +
    PackedOwnership.prepareGates.countP RGate.isCcx

set_option maxRecDepth 4096 in
theorem fixedCount_eq : fixedCount = 512 := by
  decide +kernel

private theorem collectCounts
    (r p mask clear swap up low normal restore iter finish u l : Nat) :
    r + p + mask + r +
        (clear + (swap + (up + u + u + up) + (low + l + l + low) + normal) +
          restore + iter) + finish + p =
      (r + p + mask + r + clear + swap + 2 * up + 2 * low + normal +
        restore + iter + finish + p) + (2 * u + 2 * l) := by
  omega

private theorem ownershipGates_ccx_of_counts (upper lower fixed : Nat)
    (hupper : (LengthWriter.upperGates 1 259 9).countP RGate.isCcx = upper)
    (hlower : (LengthWriter.lowerGates 256 1 259 9).countP RGate.isCcx = lower)
    (hfixed : fixedCount = fixed) :
    PackedTerminalEpoch.ownershipGates.countP RGate.isCcx =
      fixed + (2 * upper + 2 * lower) := by
  have h : PackedTerminalEpoch.ownershipGates.countP RGate.isCcx =
      fixedCount + (2 * upper + 2 * lower) := by
    simp only [PackedTerminalEpoch.ownershipGates,
      PackedTerminalEpoch.ownershipBodyGates, PackedSwapLength.gates,
      PackedSwapLength.ownershipGates, PackedSwapLength.placed,
      countP_map_gates (fun g => RGate.isCcx_map _ g), SwapLength.gates,
      SwapLength.upperBlock, SwapLength.lowerBlock, SwapLength.upperCancel,
      SwapLength.upperNew, SwapLength.lowerCancel, SwapLength.lowerNew,
      List.countP_append, List.countP_reverse, LengthWriterPlaced.gates_ccx,
      hupper, hlower]
    simp only [fixedCount]
    exact collectCounts
      (PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx)
      (PackedOwnership.prepareGates.countP RGate.isCcx)
      (PackedTerminalEpoch.ownershipMaskGates.countP RGate.isCcx)
      (PackedOwnership.phaseClearGates.countP RGate.isCcx)
      ((SwapLength.fullSwap 259 9).countP RGate.isCcx)
      ((SwapLength.upperPreparation 256 259 9).countP RGate.isCcx)
      ((SwapLength.lowerPreparation 259 9).countP RGate.isCcx)
      (PackedSwapLength.normalizationGates.countP RGate.isCcx)
      (PackedOwnership.phaseRestoreGates.countP RGate.isCcx)
      (PackedOwnership.iterationGates.countP RGate.isCcx)
      (PackedTerminalEpoch.ownershipRestoreGates.countP RGate.isCcx)
      upper lower
  exact h.trans (congrArg (fun n => n + (2 * upper + 2 * lower)) hfixed)

theorem ownershipGates_ccx :
    PackedTerminalEpoch.ownershipGates.countP RGate.isCcx =
      512 + (2 * (LengthWriter.upperGates 1 259 9).countP RGate.isCcx +
        2 * (LengthWriter.lowerGates 256 1 259 9).countP RGate.isCcx) :=
  ownershipGates_ccx_of_counts _ _ 512 rfl rfl fixedCount_eq

private theorem difference (whole writers : Nat)
    (h : whole = 512 + writers) : whole - writers = 512 := by
  omega

theorem ownershipGates_fixedDifference :
    PackedTerminalEpoch.ownershipGates.countP RGate.isCcx -
      (2 * (LengthWriter.upperGates 1 259 9).countP RGate.isCcx +
        2 * (LengthWriter.lowerGates 256 1 259 9).countP RGate.isCcx) = 512 :=
  difference _ _ ownershipGates_ccx

end VQMathlib.Euclid.PackedOwnershipCounts
