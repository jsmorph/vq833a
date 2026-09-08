import VQMathlib.ECDLP.FourierRecovery.LatentSupport
import VQMathlib.ECDLP.FourierRecovery.MarginalIdentity
import VQMathlib.ECDLP.FourierRecovery.SelectedSum

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open ECDLPSpectral
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem emittedSelectedContribution_lower_bound
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator) :
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedContribution scalarCard q d q_prime.pos
        q_lt_two_pow_256.le
        (scalarPairMarginal (emittedState level pointQ)) := by
  apply selectedContribution_lower_bound q_prime.pos
    q_lt_two_pow_256.le
  intro o
  exact emittedScalarPairMarginal_eq_uniformComponentSum
    hlevel hpointQ hQ o

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.emittedPairEventState_eq_pairLatentState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.emittedPairEventState_eq_pairLatentState

/-- info: 'VQ.Tests.ECDLPFourierRecovery.emittedScalarPairMarginal_eq_uniformComponentSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.emittedScalarPairMarginal_eq_uniformComponentSum

/-- info: 'VQ.Tests.ECDLPFourierRecovery.emittedSelectedContribution_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.emittedSelectedContribution_lower_bound
