import VQMathlib.ECDLP.PackedAffine.ProgramRecovery

namespace VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability

open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.ProgramMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.Secp256k1Order

noncomputable section

abbrev Outcome := ScalarIndex × ScalarIndex

def programOutcomeMass (level pointQ input : Nat) (outcome : Outcome) : ℝ :=
  (VQBridge.dtoC
    (packedScalarPairEventProb level pointQ input outcome)).re

def oneRunSelectedProbability
    (level d pointQ input : Nat) : ℝ :=
  selectedContribution scalarCard q d q_prime.pos
    q_lt_two_pow_256.le (programOutcomeMass level pointQ input)

theorem oneRunSelectedProbability_lower_bound
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      oneRunSelectedProbability level d pointQ input := by
  exact (packedProgramSelectedRecoveryGuarantee
    hlevel hpointQ hdpos hd hQ).1

end

end VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability
