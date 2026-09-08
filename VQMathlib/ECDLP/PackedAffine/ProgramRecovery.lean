import VQMathlib.ECDLP.PackedAffine.MarginalEquality
import VQMathlib.ECDLP.FourierRecovery.RecoveryGuarantee

open scoped BigOperators

namespace VQ.Tests.PackedAffineECDLP.ProgramMarginal

open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem packedProgramSelectedRecoveryGuarantee
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    ((((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedContribution scalarCard q d q_prime.pos
        q_lt_two_pow_256.le
        (fun o : ScalarIndex × ScalarIndex =>
          (VQBridge.dtoC
            (packedScalarPairEventProb level pointQ input o)).re)) ∧
      ∀ o ∈ selectedObservables scalarCard q d q_prime.pos
          q_lt_two_pow_256.le,
        let k := decode q scalarCard o.1.val
        let v := decode q scalarCard o.2.val
        ECDLPRecovery.checkedNatural q k v = some d ∧
          ECDLPRecovery.publicAccepts q decodedGenerator
            (decodePoint pointQ) d := by
  have hanalytic :=
    VQ.Tests.ECDLPFourierRecovery.emittedSelectedRecoveryGuarantee
      hlevel hpointQ hd hQ
  have hdistribution :=
    packedScalarPairEventDistribution_eq_analytic
      (input := input) hlevel hpointQ hdpos hd hQ
  constructor
  · calc
      (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
          selectedContribution scalarCard q d q_prime.pos
            q_lt_two_pow_256.le
            (scalarPairMarginal (emittedState level pointQ)) := hanalytic.1
      _ = selectedContribution scalarCard q d q_prime.pos
            q_lt_two_pow_256.le
            (fun o : ScalarIndex × ScalarIndex =>
              (VQBridge.dtoC
                (packedScalarPairEventProb level pointQ input o)).re) :=
        congrArg
          (selectedContribution scalarCard q d q_prime.pos
            q_lt_two_pow_256.le)
          hdistribution.symm
  · exact hanalytic.2

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
