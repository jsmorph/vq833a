import VQMathlib.ECDLP.PackedAffine.ToffoliTranslation
import VQMathlib.ECDLP.PackedAffine.ProgramResources

namespace VQ.Tests.PackedAffineECDLP.ToffoliResources

open VQ VQ.Reversible

private theorem phaseGates_toffoli (k control : Nat) :
    Program.weighOps gateWeight
        ((VQ.Circuit.phase k control).map Op.gate) = Range.point 0 := by
  rcases k with (_ | _ | _ | _ | k) <;>
    rfl

private theorem correctionOps_toffoli
    (resultOffset control count : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset control count) = Range.point 0 := by
  induction count generalizing resultOffset with
  | zero => rfl
  | succ count ih =>
      rw [VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps,
        Program.weighOps_append, ih]
      simp [Program.weighOps, Program.weighOp, phaseGates_toffoli,
        Range.add, Range.choice, Range.point]

private theorem measureAndClearOps_toffoli (control resultBit : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarStep.measureAndClearOps
          control resultBit) = Range.point 0 := by
  simp [VQ.Tests.PackedAffineECDLP.ScalarStep.measureAndClearOps,
    Program.weighOps, Program.weighOp, gateWeight, Gate.isCcz,
    Range.add, Range.choice, Range.point]

private theorem finalizeOps_toffoli (resultBit : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarProgram.finalizeOps resultBit) =
      Range.point 0 := by
  rw [VQ.Tests.PackedAffineECDLP.ScalarProgram.finalizeOps,
    Program.weighOps_append, measureAndClearOps_toffoli]
  rfl

private theorem stepOps_toffoli (resultOffset count offset : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
          resultOffset count offset) = Range.point 1149514576 := by
  simp only [VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps,
    Program.weighOps_append]
  rw [translationOps_toffoli, correctionOps_toffoli, finalizeOps_toffoli]
  norm_num [Program.weighOps, Program.weighOp, gateWeight, Gate.isCcz,
    Range.add, Range.point]

private theorem scalarOps_toffoli
    (resultOffset count : Nat) (offsets : List Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
          resultOffset count offsets) =
      Range.point (offsets.length * 1149514576) := by
  induction offsets generalizing count with
  | nil => rfl
  | cons offset offsets ih =>
      rw [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps,
        Program.weighOps_append, stepOps_toffoli, ih]
      simp [Range.add, Range.point, Nat.succ_mul, Nat.add_comm]

private theorem fullScalarOps_toffoli (resultOffset m point : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.ScalarLoop.fullScalarOps
          resultOffset m point) =
      Range.point (m * 1149514576) := by
  rw [VQ.Tests.PackedAffineECDLP.ScalarLoop.fullScalarOps,
    scalarOps_toffoli,
    VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets_length]

theorem twoScalarOps_toffoli (pointQ : Nat) :
    Program.weighOps gateWeight
        (VQ.Tests.PackedAffineECDLP.TwoScalarLoop.ops pointQ) =
      Range.point 588551462912 := by
  rw [VQ.Tests.PackedAffineECDLP.TwoScalarLoop.ops,
    Program.weighOps_append,
    fullScalarOps_toffoli, fullScalarOps_toffoli]
  norm_num [VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth,
    Range.add, Range.point]

theorem program_toffoliCount (pointQ : Nat) :
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ).toffoliCount =
      Range.point 588551462912 := by
  exact twoScalarOps_toffoli pointQ

theorem program_report_toffoli (pointQ : Nat) :
    (Program.resourceReport
      (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ)).toffoli =
        Range.point 588551462912 := by
  exact program_toffoliCount pointQ

end VQ.Tests.PackedAffineECDLP.ToffoliResources
