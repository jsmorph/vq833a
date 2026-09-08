import VQMathlib.ECDLP.SubgroupEmbedding.Complex.LinearMap

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

@[simp]
theorem embedSubgroup_add (a b : ScalarIndex) (u v : CyclicState q) :
    embedSubgroup a b (u + v) =
      embedSubgroup a b u + embedSubgroup a b v := by
  simpa only [embedSubgroup] using
    (subgroupEmbeddingLinear a b).map_add u v

@[simp]
theorem embedSubgroup_smul (a b : ScalarIndex) (c : ℂ)
    (v : CyclicState q) :
    embedSubgroup a b (c • v) = c • embedSubgroup a b v := by
  simpa only [embedSubgroup] using
    (subgroupEmbeddingLinear a b).map_smul c v

theorem embedSubgroup_sum {ι : Type*} [Fintype ι]
    (a b : ScalarIndex) (v : ι → CyclicState q) :
    embedSubgroup a b (∑ i, v i) = ∑ i, embedSubgroup a b (v i) := by
  simpa only [embedSubgroup] using
    map_sum (subgroupEmbeddingLinear a b) v Finset.univ

theorem embedSubgroup_congr (a b : ScalarIndex)
    {u v : CyclicState q} (h : u = v) :
    embedSubgroup a b u = embedSubgroup a b v := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).map_eq h

theorem embedSubgroup_weighted_sum {ι : Type} [Fintype ι]
    (a b : ScalarIndex) (c : ℂ) (weight : ι → ℂ)
    (v : ι → CyclicState q) :
    embedSubgroup a b (c • ∑ i, weight i • v i) =
      c • ∑ i, weight i • embedSubgroup a b (v i) := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).weighted_sum c weight v

end VQ.Tests.ECDLPSubgroupEmbedding
