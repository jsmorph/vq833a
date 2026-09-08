import VQMathlib.ECDLP.PackedAffine.PackedMarginal
import VQMathlib.ECDLP.PackedAffine.ScalarLoop

namespace VQ.Tests.PackedAffineECDLP.ProgramMarginal

open VQ VQ.Algebra VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.Secp256k1Order

theorem dtoC_normSq_re_eq_norm_cvec_sq
    (level width : Nat) (u : Vec (deg level)) :
    (VQBridge.dtoC (normSq (2 ^ width) u)).re =
      ‖VQ.Tests.Approximation.cvec level width u‖ ^ 2 := by
  simpa only [Complex.ofReal_re] using
    congrArg (fun value : ℂ => value.re)
      (VQ.Tests.Approximation.cvec_norm_sq level width u).symm

theorem normalizedNormSq_eq_analytic
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    (VQBridge.dtoC
        (normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
          (normalizedPairState level pointQ o.1.val o.2.val))).re =
      scalarPairMarginal (emittedState level pointQ) o :=
  (dtoC_normSq_re_eq_norm_cvec_sq level
      VQ.Curve.PackedAffineLayout.width
      (normalizedPairState level pointQ o.1.val o.2.val)).trans
    (scalarPairMarginal_eq_norm_cvec_normalizedPairState
      hlevel hpointQ hQ o).symm

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
