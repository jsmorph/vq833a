import VQMathlib.ECDLP.FourierRecovery.ProjectionRange
import VQMathlib.ECDLP.FourierRecovery.ProjectionWeighted

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem terminalProjectionRangeCoordinate_eq_weightedCoordinate
    {level d : Nat} (o : ScalarIndex × ScalarIndex) (i : FullIndex) :
    terminalProjectionRangeCoordinate level d o i =
      terminalProjectionWeightedCoordinate level d o i := by
  rw [terminalProjectionWeightedCoordinate_eq_sum]
  unfold terminalProjectionRangeCoordinate
  exact nestedModuleProjectionSum
    (I := Nat) (J := Nat) (M := ℂ)
    (s := Finset.range scalarCard)
    (t := Finset.range scalarCard)
    (u := VQBridge.dtoC (uniformScalarCoefficient level))
    (term := fun inputA inputB =>
      terminalProjectionTerm level d o inputA inputB i)
    (state := fun inputA inputB =>
      terminalProjectionState d o inputA inputB i)
    (left := terminalProjectionLeft level o)
    (right := terminalProjectionRight level o)
    (weightLeft := terminalProjectionWeightLeft level o)
    (weightRight := terminalProjectionWeightRight level o)
    (hterm := by
      intro inputA _ inputB _
      exact terminalProjectionTerm_apply_eq o inputA inputB i)
    (hleft := by
      intro inputA _
      exact terminalProjectionWeightLeft_eq o inputA)
    (hright := by
      intro inputB _
      exact terminalProjectionWeightRight_eq o inputB)

end VQ.Tests.ECDLPFourierRecovery
