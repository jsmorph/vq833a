import VQMathlib.ECDLP.PackedAffine.ToffoliMultiplication
import VQMathlib.Curve.PackedAffineTranslation

namespace VQ.Tests.PackedAffineECDLP.ToffoliResources

open VQ VQ.Reversible
open VQ.Tests.PackedAffineECDLP.ToffoliComponents

private theorem gateOps_toffoli (gates : List RGate) :
    Program.weighOps gateWeight (Lookup3.gateOps gates) =
      Range.point (gates.countP RGate.isCcx) := by
  exact VQ.Lookup.Unary.gateOps_toffoli gates

private theorem squareSubtractAddGates_ccx :
    VQ.Curve.PackedAffineSquareSubtract.addGates.countP RGate.isCcx =
      21562 := by
  rw [VQ.Curve.PackedAffineSquareSubtract.addGates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    modularAddGates_ccx]

private theorem constantAdditionGates_ccx (constant : Nat) :
    (VQ.Curve.PackedAffineConstantAddition.gates constant).countP
        RGate.isCcx = 21562 := by
  simp only [VQ.Curve.PackedAffineConstantAddition.gates,
    VQ.Curve.PackedAffineConstantAddition.loadGates,
    VQ.Curve.PackedAffineConstantAddition.controlledAddGates,
    VQ.Curve.PackedAffineSquareSubtract.controlToggleGates,
    List.countP_append, List.countP_reverse, List.countP_cons, List.countP_nil,
    squareSubtractAddGates_ccx, constantXorGates_no_ccx, RGate.isCcx]
  decide +kernel

private theorem unconditionalAdditionGates_ccx (constant : Nat) :
    (VQ.Curve.PackedAffineConstantAddition.unconditionalGates constant).countP
        RGate.isCcx = 21562 := by
  simp only [VQ.Curve.PackedAffineConstantAddition.unconditionalGates,
    VQ.Curve.PackedAffineConstantAddition.loadGates,
    VQ.Curve.PackedAffineConstantAddition.unconditionalAddGates,
    VQ.Curve.PackedAffineConstantAddition.unconditionalControlGates,
    List.countP_append, List.countP_reverse, List.countP_cons, List.countP_nil,
    squareSubtractAddGates_ccx, constantXorGates_no_ccx, RGate.isCcx]
  decide +kernel

private theorem secondSubtractionAddGates_ccx :
    VQ.Curve.PackedAffineSecondConstantSubtraction.addGates.countP
        RGate.isCcx = 21562 := by
  rw [VQ.Curve.PackedAffineSecondConstantSubtraction.addGates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    modularAddGates_ccx]

private theorem secondSubtractionGates_ccx (constant : Nat) :
    (VQ.Curve.PackedAffineSecondConstantSubtraction.gates constant).countP
        RGate.isCcx = 21562 := by
  simp only [VQ.Curve.PackedAffineSecondConstantSubtraction.gates,
    VQ.Curve.PackedAffineSecondConstantSubtraction.loadGates,
    VQ.Curve.PackedAffineSecondConstantSubtraction.subtractGates,
    VQ.Curve.PackedAffineSecondConstantSubtraction.controlToggleGates,
    List.countP_append, List.countP_reverse, List.countP_cons, List.countP_nil,
    secondSubtractionAddGates_ccx, constantXorGates_no_ccx, RGate.isCcx]
  decide +kernel

private theorem squareSubtractGates_ccx :
    VQ.Curve.PackedAffineSquareSubtract.gates.countP RGate.isCcx =
      20229066 := by
  simp only [VQ.Curve.PackedAffineSquareSubtract.gates,
    VQ.Curve.PackedAffineSquareSubtract.subtractGates,
    VQ.Curve.PackedAffineSquareSubtract.controlToggleGates,
    List.countP_append, List.countP_reverse, List.countP_cons, List.countP_nil,
    affineSquareGates_ccx, squareSubtractAddGates_ccx, RGate.isCcx]
  decide +kernel

theorem rawTranslationOps_toffoli (ax ay : Nat) :
    Program.weighOps gateWeight
        (VQ.Curve.PackedAffineRawTranslation.ops ax ay) =
      Range.point 1149502310 := by
  simp only [VQ.Curve.PackedAffineRawTranslation.ops,
    VQ.Curve.PackedAffineRawTranslation.gateOps,
    Program.weighOps_append]
  simp_rw [gateOps_toffoli]
  rw [unconditionalAdditionGates_ccx, unconditionalAdditionGates_ccx,
    secondSubtractionGates_ccx,
    totalDivisionOps_toffoli,
    squareSubtractGates_ccx, constantAdditionGates_ccx,
    totalMultiplicationOps_toffoli,
    negationGates_ccx]
  norm_num [Range.add, Range.point]

theorem translationOps_toffoli (ax ay : Nat) :
    Program.weighOps gateWeight
        (VQ.Curve.PackedAffineTranslation.ops ax ay) =
      Range.point 1149514576 := by
  simp only [VQ.Curve.PackedAffineTranslation.ops,
    VQ.Curve.PackedAffineTranslation.gateOps,
    Program.weighOps_append]
  simp_rw [gateOps_toffoli]
  rw [tagAllGates_ccx,
    rawTranslationOps_toffoli,
    correctionAndEraseGates_ccx]
  norm_num [Range.add, Range.point]

end VQ.Tests.PackedAffineECDLP.ToffoliResources
