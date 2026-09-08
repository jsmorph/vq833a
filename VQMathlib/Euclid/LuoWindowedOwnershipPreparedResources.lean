import VQMathlib.Euclid.LuoWindowedOwnershipResources
import VQMathlib.Euclid.PackedInputPreparationResources

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

theorem preparedScheduleToffoli_eq :
    35204 +
      (1620 * roundFixedToffoli + windowedOwnershipScheduleToffoli) =
        267127424 := by
  rw [roundScheduleToffoli_eq]

theorem preparedRoundsGates_ccx (rounds : Nat) :
    (PackedInputPreparation.gates VQ.Curve.p ++
      roundsGates rounds).countP RGate.isCcx =
        35204 +
          ((List.range rounds).map (fun index =>
            roundToffoli (index + 1))).sum := by
  rw [List.countP_append, VQMathlib.Euclid.packedInputPreparationGates_ccx,
    roundsGates_ccx]

theorem preparedRoundsGates_ccx_decomposed (rounds : Nat) :
    (PackedInputPreparation.gates VQ.Curve.p ++
      roundsGates rounds).countP RGate.isCcx =
        35204 +
          (rounds * roundFixedToffoli +
            ((List.range rounds).map (fun index =>
              windowedOwnershipToffoli (index + 1))).sum) := by
  rw [preparedRoundsGates_ccx, roundToffoliSchedule_eq]

private theorem preparedRoundsGates_ccx_of_counts
    (rounds ownership total : Nat)
    (hownership : ((List.range rounds).map (fun index =>
      windowedOwnershipToffoli (index + 1))).sum = ownership)
    (htotal : 35204 + (rounds * roundFixedToffoli + ownership) = total) :
    (PackedInputPreparation.gates VQ.Curve.p ++
      roundsGates rounds).countP RGate.isCcx = total := by
  rw [preparedRoundsGates_ccx_decomposed, hownership, htotal]

theorem preparedRoundsGates_ccx_1620 :
    (PackedInputPreparation.gates VQ.Curve.p ++
      roundsGates 1620).countP RGate.isCcx = 267127424 := by
  exact preparedRoundsGates_ccx_of_counts 1620 141696120 267127424
    windowedOwnershipScheduleToffoli_eq
    (by rw [roundFixedToffoli_eq])

end VQMathlib.LuoSchedule.WindowedOwnership
