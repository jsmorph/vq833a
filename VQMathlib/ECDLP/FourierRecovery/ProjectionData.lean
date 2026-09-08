import VQMathlib.ECDLP.FourierRecovery.ProjectionCoordinates

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

set_option linter.defProp false in
def terminalProjectionMiddleEquality {level d : Nat}
    (o : ScalarIndex × ScalarIndex) :
    terminalProjectionRangeSum level d o =
      terminalProjectionWeightedSum level d o := by
  apply euclideanState_eq_of_projection_eq
  intro i
  rw [terminalProjectionRangeSum_apply,
    terminalProjectionWeightedSum_apply]
  exact terminalProjectionRangeCoordinate_eq_weightedCoordinate o i

set_option linter.defProp false in
def terminalProjectionData {level d : Nat}
    (o : ScalarIndex × ScalarIndex) :
    terminalProjectionRangeSum level d o =
      terminalProjectionWeightedSum level d o :=
  terminalProjectionMiddleEquality o

attribute [irreducible]
  terminalProjectionData terminalProjectionMiddleEquality

end VQ.Tests.ECDLPFourierRecovery
