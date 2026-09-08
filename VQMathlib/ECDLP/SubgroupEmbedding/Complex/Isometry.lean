import VQMathlib.ECDLP.SubgroupEmbedding.Complex.Coordinates

open scoped BigOperators ComplexConjugate

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem subgroupBasis_orthonormal (a b : ScalarIndex) :
    Orthonormal ℂ (subgroupBasis a b) := by
  have h := (subgroupEmbeddingData a b).basis_orthonormal
  change Orthonormal ℂ
    (fun t : ZMod q =>
      EuclideanSpace.single (subgroupFullIndex a b t) (1 : ℂ)) at h
  change Orthonormal ℂ
    (fun t : ZMod q =>
      EuclideanSpace.single (subgroupFullIndex a b t) (1 : ℂ))
  exact h

theorem embedSubgroup_inner (a b : ScalarIndex) (u v : CyclicState q) :
    inner ℂ (embedSubgroup a b u) (embedSubgroup a b v) =
      inner ℂ u v := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).inner u v

theorem embedSubgroup_norm (a b : ScalarIndex) (v : CyclicState q) :
    ‖embedSubgroup a b v‖ = ‖v‖ := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear] using
    (subgroupEmbeddingData a b).norm v

noncomputable def subgroupEmbedding (a b : ScalarIndex) :
    CyclicState q →ₗᵢ[ℂ] FullComplexState :=
  LinearMap.isometryOfInner (subgroupEmbeddingLinear a b)
    (embedSubgroup_inner a b)

end VQ.Tests.ECDLPSubgroupEmbedding
