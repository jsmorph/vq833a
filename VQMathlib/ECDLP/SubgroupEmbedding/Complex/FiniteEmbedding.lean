import Mathlib.Analysis.InnerProductSpace.PiL2

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

noncomputable def finiteEmbeddingBasis
    {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (i : ι) :
    EuclideanSpace ℂ κ :=
  PiLp.single 2 (f i) 1

noncomputable def finiteEmbeddingLinear
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ where
  toFun v := ∑ i : ι, v i • finiteEmbeddingBasis f i
  map_add' u v := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]

@[simp]
theorem finiteEmbeddingLinear_add
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (u v : EuclideanSpace ℂ ι) :
    finiteEmbeddingLinear f (u + v) =
      finiteEmbeddingLinear f u + finiteEmbeddingLinear f v :=
  (finiteEmbeddingLinear f).map_add u v

@[simp]
theorem finiteEmbeddingLinear_smul
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    finiteEmbeddingLinear f (c • v) =
      c • finiteEmbeddingLinear f v :=
  (finiteEmbeddingLinear f).map_smul c v

theorem finiteEmbeddingLinear_sum
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] (f : ι → κ) (v : μ → EuclideanSpace ℂ ι) :
    finiteEmbeddingLinear f (∑ j, v j) =
      ∑ j, finiteEmbeddingLinear f (v j) := by
  rw [map_sum]

end VQ.Tests.ECDLPSubgroupEmbedding
