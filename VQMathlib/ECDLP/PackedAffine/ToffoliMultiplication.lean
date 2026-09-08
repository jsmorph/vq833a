import VQMathlib.ECDLP.PackedAffine.ToffoliDivision
import VQ.Curve.PackedAffineRetainedMultiplication

namespace VQ.Tests.PackedAffineECDLP.ToffoliResources

open VQ VQ.Reversible
open VQ.Tests.PackedAffineECDLP.ToffoliComponents

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

private theorem multiplicationPhaseRepairOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.phaseRepairOps =
      Range.point 20207504 := by
  simpa [gateWeight,
    VQ.Curve.PackedAffineRetainedMultiplication.phaseRepairOps,
    VQ.Lookup.BatchedReconstruction.repairAtOps,
    VQ.Lookup.BatchedReconstruction.repairOps,
    VQ.Curve.PackedAffineTerminalProduct.terminalCircuit,
    affineTerminalProductGates_ccx] using
      VQ.Lookup.BatchedReconstruction.repairOps_toffoli
        VQ.Curve.PackedAffineTerminalProduct.terminalCircuit
        VQ.Curve.PackedAffineTerminalProduct.targetOffset 256

private theorem productMeasurementOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.productMeasurementOps =
      Range.point 0 := by
  simpa [VQ.Curve.PackedAffineRetainedMultiplication.productMeasurementOps]
    using measurementOps_toffoli
      VQ.Euclid.PackedStepLayout.workTwoOffset 0 256

private theorem reconstructionOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.reconstructionOps =
      Range.point 20217986 := by
  simp only [VQ.Curve.PackedAffineRetainedMultiplication.reconstructionOps,
    VQ.Curve.PackedAffineRetainedMultiplication.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, preQuotientGates_ccx,
    multiplicationPhaseRepairOps_toffoli,
    gateOps_toffoli, List.countP_reverse, preQuotientGates_ccx]
  norm_num [Range.add, Range.point]

private theorem postMeasurementOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps =
      Range.point 554472834 := by
  simp only [VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps,
    VQ.Curve.PackedAffineRetainedMultiplication.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, scheduleGates_ccx, reconstructionOps_toffoli,
    gateOps_toffoli, List.countP_reverse, scheduleGates_ccx]
  norm_num [Range.add, Range.point]

private theorem selectedMultiplicationOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps =
      Range.point 564576586 := by
  simp only [VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps,
    VQ.Curve.PackedAffineRetainedMultiplication.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, List.countP_reverse, numeratorMoveGates_ccx,
    gateOps_toffoli, affineInputProductGates_ccx,
    productMeasurementOps_toffoli, postMeasurementOps_toffoli]
  norm_num [Range.add, Range.point]

theorem totalMultiplicationOps_toffoli :
    Program.weighOps gateWeight
        VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps =
      Range.point 564578626 := by
  simp only [VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps,
    VQ.Curve.PackedAffineRetainedMultiplication.gateOps,
    Program.weighOps_append]
  rw [gateOps_toffoli, numeratorMoveGates_ccx,
    gateOps_toffoli, fieldPrepareGates_ccx,
    selectedMultiplicationOps_toffoli,
    gateOps_toffoli, fieldRestoreGates_ccx,
    gateOps_toffoli, quotientMoveGates_ccx]
  norm_num [Range.add, Range.point]

end VQ.Tests.PackedAffineECDLP.ToffoliResources
