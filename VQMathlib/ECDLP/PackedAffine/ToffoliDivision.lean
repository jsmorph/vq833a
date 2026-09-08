import VQMathlib.ECDLP.PackedAffine.ToffoliComponents

namespace VQ.Tests.PackedAffineECDLP.ToffoliResources

open VQ VQ.Reversible
open VQ.Tests.PackedAffineECDLP.ToffoliComponents

abbrev gateWeight (gate : Gate) : Nat :=
  if gate.isCcz then 1 else 0

private theorem gateOps_toffoli (gates : List RGate) :
    Program.weighOps gateWeight (Lookup3.gateOps gates) =
      Range.point (gates.countP RGate.isCcx) := by
  exact VQ.Lookup.Unary.gateOps_toffoli gates

private theorem measurementOps_toffoli (offset bit count : Nat) :
    Program.weighOps gateWeight
        (VQ.Lookup.BatchedReconstruction.measureOps offset bit count) =
      Range.point 0 := by
  simpa [gateWeight, VQ.Lookup.BatchedReconstruction.measureOps] using
    VQ.Lookup.BatchedUncompute.measureOutputOps_toffoli offset bit count

private theorem divisionPhaseRepairOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedDivision.phaseRepairOps =
      Range.point 20207504 := by
  simpa [gateWeight,
    VQ.Curve.PackedAffineRetainedDivision.phaseRepairOps,
    VQ.Lookup.BatchedReconstruction.repairAtOps,
    VQ.Lookup.BatchedReconstruction.repairOps,
    VQ.Curve.PackedAffineProduct.circuit, affineProductGates_ccx] using
      VQ.Lookup.BatchedReconstruction.repairOps_toffoli
        VQ.Curve.PackedAffineProduct.circuit
        VQ.Curve.PackedAffineProduct.targetOffset 256

private theorem terminalOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedDivision.terminalOps =
      Range.point 10114234 := by
  simp only [VQ.Curve.PackedAffineRetainedDivision.terminalOps,
    VQ.Curve.PackedAffineRetainedDivision.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, preQuotientGates_ccx,
    gateOps_toffoli, affineTerminalProductGates_ccx,
    measurementOps_toffoli, gateOps_toffoli, cleanupGates_ccx]
  norm_num [Range.add, Range.point]

private theorem postForwardOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedDivision.postForwardOps =
      Range.point 297449162 := by
  simp only [VQ.Curve.PackedAffineRetainedDivision.postForwardOps,
    VQ.Curve.PackedAffineRetainedDivision.gateOps,
    Program.weighOps_append]
  rw [terminalOps_toffoli, gateOps_toffoli, reversalGates_ccx,
    divisionPhaseRepairOps_toffoli]
  norm_num [Range.add, Range.point]

private theorem selectedDivisionOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps =
      Range.point 564576586 := by
  simp only [VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps,
    VQ.Curve.PackedAffineRetainedDivision.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, scheduleGates_ccx, postForwardOps_toffoli]
  norm_num [Range.add, Range.point]

theorem totalDivisionOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps =
      Range.point 564578626 := by
  simp only [VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps,
    VQ.Curve.PackedAffineRetainedDivision.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, numeratorMoveGates_ccx,
    gateOps_toffoli, fieldPrepareGates_ccx,
    selectedDivisionOps_toffoli,
    gateOps_toffoli, fieldRestoreGates_ccx,
    gateOps_toffoli, quotientMoveGates_ccx]
  norm_num [Range.add, Range.point]

end VQ.Tests.PackedAffineECDLP.ToffoliResources
