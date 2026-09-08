import VQMathlib.ECDLP.FourierRecovery.MarginalWeight

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem scalarPairMarginal_eq_uniformComponentSum_of_eventState_eq
    {d : Nat} {state : FullComplexState}
    (hevent : ∀ o : ScalarIndex × ScalarIndex,
      scalarPairEventState o state = pairLatentState d o)
    (o : ScalarIndex × ScalarIndex) :
    scalarPairMarginal state o =
      ∑ k : Fin q, uniformComponentWeight scalarCard q d q_prime.pos k o := by
  rw [scalarPairMarginal_eq_norm_eventState_sq, hevent,
    pairLatentState_weight_eq_uniformComponentSum]

theorem emittedScalarPairMarginal_eq_uniformComponentSum
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    scalarPairMarginal (emittedState level pointQ) o =
      ∑ k : Fin q, uniformComponentWeight scalarCard q d q_prime.pos k o := by
  apply scalarPairMarginal_eq_uniformComponentSum_of_eventState_eq
  intro event
  exact emittedPairEventState_eq_pairLatentState
    hlevel hpointQ hQ event

end VQ.Tests.ECDLPFourierRecovery
