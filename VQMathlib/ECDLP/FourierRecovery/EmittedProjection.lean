import VQMathlib.ECDLP.FourierRecovery.EmittedTerminal
import VQMathlib.ECDLP.FourierRecovery.FourierProjection

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

opaque observedState_eq
    {B : Type*} (observe : B → B) (emitted terminal projected : B)
    (hemit : emitted = terminal) (hproject : observe terminal = projected) :
    observe emitted = projected := by
  exact (congrArg observe hemit).trans hproject

set_option linter.defProp false in
def emittedPairEventState_eq_pairBasisState
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :=
  observedState_eq (scalarPairEventState o)
    (emittedState level pointQ)
    (Approximation.cvec level circuitWidth (terminalState level d))
    (pairBasisState level d o)
    (emittedState_eq_cvec_terminalState hlevel hpointQ hQ)
    (scalarPairEventState_terminalState_eq_pairBasisState o)

attribute [irreducible] emittedPairEventState_eq_pairBasisState

end VQ.Tests.ECDLPFourierRecovery
