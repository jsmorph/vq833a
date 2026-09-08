import VQMathlib.ECDLP.SubgroupEmbedding.Complex.State

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

@[simp]
theorem subgroupBasis_apply (a b : ScalarIndex) (t : ZMod q)
    (i : FullIndex) :
    subgroupBasis a b t i =
      if i = subgroupFullIndex a b t then 1 else 0 := by
  simp [subgroupBasis, PiLp.single_apply]

theorem embedSubgroup_apply_image (a b : ScalarIndex)
    (v : CyclicState q) (t : ZMod q) :
    embedSubgroup a b v (subgroupFullIndex a b t) = v t := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).apply_image v t

theorem embedSubgroup_apply_of_not_mem (a b : ScalarIndex)
    (v : CyclicState q) (i : FullIndex)
    (hi : i ∉ Set.range (subgroupFullIndex a b)) :
    embedSubgroup a b v i = 0 := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).apply_of_not_mem v i hi

theorem embedSubgroup_support_subset (a b : ScalarIndex)
    (v : CyclicState q) :
    Function.support (embedSubgroup a b v) ⊆
      Set.range (subgroupFullIndex a b) := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).support_subset v

theorem embedSubgroup_basis (a b : ScalarIndex) (t : ZMod q) :
    embedSubgroup a b (PiLp.single 2 t 1) = subgroupBasis a b t := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear, subgroupBasis,
    finiteEmbeddingBasis] using
    (subgroupEmbeddingData a b).basis t

theorem subgroupBasis_weighted_sum {ι : Type} [Fintype ι]
    (a b : ScalarIndex) (t : ZMod q) (c : ℂ) (weight : ι → ℂ)
    (v : ι → CyclicState q)
    (h : PiLp.single 2 t 1 = c • ∑ j, weight j • v j) :
    subgroupBasis a b t =
      c • ∑ j, weight j • embedSubgroup a b (v j) := by
  simpa only [subgroupBasis, finiteEmbeddingBasis, embedSubgroup,
    subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).basis_weighted_sum t c weight v h

theorem subgroupBasis_weighted_sum_as {ι : Type} [Fintype ι]
    (a b : ScalarIndex) (t : ZMod q) (c : ℂ) (weight : ι → ℂ)
    (v : ι → CyclicState q) (w : ι → FullComplexState)
    (hw : ∀ j, embedSubgroup a b (v j) = w j)
    (h : PiLp.single 2 t 1 = c • ∑ j, weight j • v j) :
    subgroupBasis a b t = c • ∑ j, weight j • w j := by
  simpa only [subgroupBasis, finiteEmbeddingBasis, embedSubgroup,
    subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).basis_weighted_sum_as t c weight v w hw h

end VQ.Tests.ECDLPSubgroupEmbedding
