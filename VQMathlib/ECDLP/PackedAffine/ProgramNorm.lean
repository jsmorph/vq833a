import VQMathlib.ECDLP.PackedAffine.ProgramScale

namespace VQ.Tests.PackedAffineECDLP.ProgramMarginal

open VQ VQ.Algebra VQ.Semantics
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.Secp256k1Order

theorem dtoC_packedScalarPairEventProb_re_eq_normalizedNormSq
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    (VQBridge.dtoC
      (packedScalarPairEventProb level pointQ input o)).re =
      (VQBridge.dtoC
        (normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
          (normalizedPairState level pointQ o.1.val o.2.val))).re :=
  congrArg (fun value : ℂ => value.re)
    (dtoC_packedScalarPairEventProb_eq_normalizedNormSq
      hlevel hpointQ hdpos hd hQ o)

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
