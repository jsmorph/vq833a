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

noncomputable def terminalProjectionRangeCoordinate
    (level d : Nat) (o : ScalarIndex × ScalarIndex)
    (i : FullIndex) : ℂ :=
  ∑ inputA ∈ Finset.range scalarCard,
    VQBridge.dtoC (uniformScalarCoefficient level) •
      ∑ inputB ∈ Finset.range scalarCard,
        VQBridge.dtoC (uniformScalarCoefficient level) •
          terminalProjectionTerm level d o inputA inputB i

attribute [irreducible] terminalProjectionRangeCoordinate

theorem terminalProjectionRangeSum_apply
    {level d : Nat} (o : ScalarIndex × ScalarIndex) (i : FullIndex) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) i)
        (terminalProjectionRangeSum level d o) =
      terminalProjectionRangeCoordinate level d o i := by
  unfold terminalProjectionRangeSum terminalProjectionRangeCoordinate
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputA _
  rw [map_smul]
  apply congrArg (fun z : ℂ =>
    VQBridge.dtoC (uniformScalarCoefficient level) • z)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputB _
  rw [map_smul]
  rw [euclideanProjection_apply]

end VQ.Tests.ECDLPFourierRecovery
