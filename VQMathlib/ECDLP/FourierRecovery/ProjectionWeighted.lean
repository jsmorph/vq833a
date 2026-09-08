import VQMathlib.ECDLP.FourierRecovery.FourierProjectionCore
import VQMathlib.ECDLP.FourierRecovery.GenericProjection

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem terminalProjectionWeightedSum_apply
    {level d : Nat} (o : ScalarIndex × ScalarIndex) (i : FullIndex) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) i)
        (terminalProjectionWeightedSum level d o) =
      terminalProjectionWeightedCoordinate level d o i := by
  simpa only [terminalProjectionWeightedSum,
    terminalProjectionWeightedCoordinate] using
      (terminalProjectionWeightedData level d o).projection_apply i

theorem terminalProjectionWeightedCoordinate_eq_sum
    {level d : Nat} (o : ScalarIndex × ScalarIndex) (i : FullIndex) :
    terminalProjectionWeightedCoordinate level d o i =
      ∑ inputA ∈ Finset.range scalarCard,
        ∑ inputB ∈ Finset.range scalarCard,
          (terminalProjectionWeightLeft level o inputA *
            terminalProjectionWeightRight level o inputB) •
              terminalProjectionState d o inputA inputB i := by
  simp only [terminalProjectionWeightedCoordinate,
    terminalProjectionWeightedData,
    euclideanDoubleWeightedProjectionData_pointwiseCoordinate]

end VQ.Tests.ECDLPFourierRecovery
