import VQMathlib.ECDLP.FourierRecovery.ProjectionData

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication

theorem terminalProjectionWeightedSum_eq_pairBasisState
    {level d : Nat} (o : ScalarIndex × ScalarIndex) :
    terminalProjectionWeightedSum level d o =
      pairBasisState level d o := by
  classical
  simp only [terminalProjectionWeightedSum,
    terminalProjectionWeightedData,
    euclideanDoubleWeightedProjectionData_summedState,
    terminalProjectionWeightLeft,
    terminalProjectionWeightRight, terminalProjectionState]
  rw [pairBasisState, scalarIndex_sum_eq_range]
  apply Finset.sum_congr rfl
  intro inputA _
  rw [scalarIndex_sum_eq_range]

set_option linter.defProp false in
def terminalProjectionAlgebra {level d : Nat}
    (o : ScalarIndex × ScalarIndex) :
    terminalProjectionSource level d o =
      pairBasisState level d o := by
  exact
    (scalarPairEventState_terminalState_eq_terminalProjectionRangeSum o).trans
      ((terminalProjectionMiddleEquality o).trans
        (terminalProjectionWeightedSum_eq_pairBasisState o))

attribute [irreducible] terminalProjectionAlgebra

end VQ.Tests.ECDLPFourierRecovery
