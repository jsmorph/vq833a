import VQMathlib.Euclid.LuoWindowedOwnershipRoundCircuit
import VQMathlib.Euclid.PackedOwnershipCounts
import VQMathlib.Euclid.PackedRoundCounts

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

def ownershipFixedToffoli : Nat :=
  PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
    PackedOwnership.prepareGates.countP RGate.isCcx +
    PackedTerminalEpoch.ownershipMaskGates.countP RGate.isCcx +
    PackedPhaseFourPrefix.rPrimeSelectorGates.countP RGate.isCcx +
    PackedOwnership.phaseClearGates.countP RGate.isCcx +
    (SwapLength.fullSwap fullWidth endpointWidth).countP RGate.isCcx +
    2 * (SwapLength.upperPreparation 256 fullWidth endpointWidth).countP
      RGate.isCcx +
    2 * (SwapLength.lowerPreparation fullWidth endpointWidth).countP
      RGate.isCcx +
    PackedSwapLength.normalizationGates.countP RGate.isCcx +
    PackedOwnership.phaseRestoreGates.countP RGate.isCcx +
    PackedOwnership.iterationGates.countP RGate.isCcx +
    PackedTerminalEpoch.ownershipRestoreGates.countP RGate.isCcx +
    PackedOwnership.prepareGates.countP RGate.isCcx

set_option maxRecDepth 4096 in
theorem ownershipFixedToffoli_eq : ownershipFixedToffoli = 512 := by
  exact VQMathlib.Euclid.PackedOwnershipCounts.fixedCount_eq

def roundFixedToffoli : Nat :=
  roundFixedCount RGate.isCcx

theorem roundFixedToffoli_eq : roundFixedToffoli = 77405 := by
  exact VQMathlib.Euclid.PackedRoundCounts.roundFixedCount_ccx

end VQMathlib.LuoSchedule.WindowedOwnership
