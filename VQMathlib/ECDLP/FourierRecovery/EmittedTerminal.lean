import VQMathlib.ECDLP.FourierRecovery.TerminalObservation
import VQMathlib.ECDLP.FourierRecovery.TerminalState

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

opaque mappedState_eq
    {A B : Type*} (map : A → B) (source : B)
    (executed terminal : A) (hsource : source = map executed)
    (hexecute : executed = terminal) :
    source = map terminal := by
  exact hsource.trans (congrArg map hexecute)

set_option linter.defProp false in
def emittedState_eq_cvec_terminalState
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator) :=
  mappedState_eq (Approximation.cvec level circuitWidth)
    (emittedState level pointQ)
    (run level (circuit generator pointQ) (basis 0 : Vec (deg level)))
    (terminalState level d) (emittedState_eq_cvec_run level pointQ)
    (run_ecdlpCircuit_zero_eq_terminalState hlevel hpointQ hQ)

attribute [irreducible] emittedState_eq_cvec_terminalState

end VQ.Tests.ECDLPFourierRecovery
