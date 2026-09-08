import VQMathlib.ECDLP.PackedAffine.ProgramNorm
import VQMathlib.ECDLP.PackedAffine.AnalyticNorm

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
open VQ.Tests.ProgramObservation
open VQ.Tests.Secp256k1Order

theorem dtoC_packedScalarPairEventProb_re_eq_analytic
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    (VQBridge.dtoC
      (packedScalarPairEventProb level pointQ input o)).re =
      scalarPairMarginal (emittedState level pointQ) o :=
  (dtoC_packedScalarPairEventProb_re_eq_normalizedNormSq
      hlevel hpointQ hdpos hd hQ o).trans
    (normalizedNormSq_eq_analytic hlevel hpointQ hQ o)

theorem packedScalarPairEventDistribution_eq_analytic
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    (fun o : ScalarIndex × ScalarIndex =>
      (VQBridge.dtoC
        (packedScalarPairEventProb level pointQ input o)).re) =
      scalarPairMarginal (emittedState level pointQ) := by
  funext o
  exact dtoC_packedScalarPairEventProb_re_eq_analytic
    hlevel hpointQ hdpos hd hQ o

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
