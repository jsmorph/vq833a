import VQMathlib.ECDLP.PackedAffine.ProgramSuccessProbability
import VQMathlib.ECDLP.PackedAffine.SelectedProbabilityBound

open scoped BigOperators

namespace VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability

open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.ProgramMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.PackedAffineECDLP.SelectedProbabilityBound
open VQ.Tests.Secp256k1Order

noncomputable section

theorem oneRunSelectedProbability_le_one
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    oneRunSelectedProbability level d pointQ input ≤ 1 := by
  have hdistribution :=
    packedScalarPairEventDistribution_eq_analytic
      (input := input) hlevel hpointQ hdpos hd hQ
  calc
    oneRunSelectedProbability level d pointQ input =
        selectedContribution scalarCard q d q_prime.pos
          q_lt_two_pow_256.le
          (scalarPairMarginal (emittedState level pointQ)) := by
      unfold oneRunSelectedProbability programOutcomeMass
      exact congrArg
        (selectedContribution scalarCard q d q_prime.pos
          q_lt_two_pow_256.le) hdistribution
    _ ≤ 1 := by
      refine selectedContribution_le_one
        q_prime.pos q_lt_two_pow_256.le
        (scalarPairMarginal (emittedState level pointQ)) ?_ ?_
      · intro outcome
        change 0 ≤ Approximation.acceptanceWeight _ _
        rw [ApproximationProbability.acceptanceWeight_eq_norm_eventState_sq]
        positivity
      · exact sum_emittedScalarPairMarginal_eq_one hlevel

end

end VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability
