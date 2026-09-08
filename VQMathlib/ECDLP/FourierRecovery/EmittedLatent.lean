import VQMathlib.ECDLP.FourierRecovery.CharacterCollapse
import VQMathlib.ECDLP.FourierRecovery.EmittedProjection

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

opaque stateEq_trans
    {B : Type*} (source middle target : B)
    (hsource : source = middle) (htarget : middle = target) :
    source = target := by
  exact hsource.trans htarget

set_option linter.defProp false in
def emittedPairEventState_eq_pairLatentState
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :=
  stateEq_trans
    (scalarPairEventState o (emittedState level pointQ))
    (pairBasisState level d o) (pairLatentState d o)
    (emittedPairEventState_eq_pairBasisState hlevel hpointQ hQ o)
    (pairBasisState_eq_pairLatentState hlevel o)

attribute [irreducible] emittedPairEventState_eq_pairLatentState

end VQ.Tests.ECDLPFourierRecovery
