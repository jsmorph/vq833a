import VQMathlib.ECDLP.PackedAffine.ProgramMarginal

namespace VQ.Tests.PackedAffineECDLP.ProgramMarginal

open VQ VQ.Algebra VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPAlgorithm
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition
open VQ.Tests.Secp256k1Order

theorem dtoC_packedScalarPairEventProb_eq_normalizedNormSq
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    VQBridge.dtoC (packedScalarPairEventProb level pointQ input o) =
      VQBridge.dtoC
        (normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
          (normalizedPairState level pointQ o.1.val o.2.val)) := by
  have hprob := congrArg
    (fun value : Dy (deg level) => VQBridge.dtoC value)
    (packedScalarPairEventProb_eq_scaledNormSq
      (level := level) (d := d) (pointQ := pointQ) (input := input)
      (by omega) (by
        simp [TwoScalarLoop.scalarWidth]
        omega)
      hpointQ hdpos hd hQ o)
  exact hprob.trans
    (internal_scale_cancel_mul (level := level)
      (by omega) (2 * TwoScalarLoop.scalarWidth)
      (normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
        (normalizedPairState level pointQ o.1.val o.2.val)))

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
