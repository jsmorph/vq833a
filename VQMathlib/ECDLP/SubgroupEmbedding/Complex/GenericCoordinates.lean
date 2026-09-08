import VQMathlib.ECDLP.SubgroupEmbedding.Complex.FiniteEmbedding

namespace VQ.Tests.ECDLPSubgroupEmbedding

theorem finiteEmbeddingLinear_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (v : EuclideanSpace ℂ ι) (j : κ) :
    finiteEmbeddingLinear f v j =
      ∑ i : ι, if j = f i then v i else 0 := by
  classical
  simp [finiteEmbeddingLinear, finiteEmbeddingBasis, Pi.single_apply]

theorem finiteEmbeddingLinear_apply_image
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f)
    (v : EuclideanSpace ℂ ι) (i : ι) :
    finiteEmbeddingLinear f v (f i) = v i := by
  classical
  rw [finiteEmbeddingLinear_apply]
  simp [hf.eq_iff]

theorem finiteEmbeddingLinear_apply_of_not_mem
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (v : EuclideanSpace ℂ ι) (j : κ)
    (hj : j ∉ Set.range f) :
    finiteEmbeddingLinear f v j = 0 := by
  classical
  rw [finiteEmbeddingLinear_apply]
  have hne : ∀ i : ι, j ≠ f i := by
    intro i h
    exact hj ⟨i, h.symm⟩
  simp [hne]

theorem finiteEmbeddingLinear_support_subset
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (v : EuclideanSpace ℂ ι) :
    Function.support (finiteEmbeddingLinear f v) ⊆ Set.range f := by
  intro j hj
  by_contra hmem
  exact hj (finiteEmbeddingLinear_apply_of_not_mem f v j hmem)

theorem finiteEmbeddingLinear_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (i : ι) :
    finiteEmbeddingLinear f (PiLp.single 2 i 1) =
      finiteEmbeddingBasis f i := by
  ext j
  by_cases hj : j ∈ Set.range f
  · rcases hj with ⟨x, rfl⟩
    rw [finiteEmbeddingLinear_apply_image f hf]
    simp [finiteEmbeddingBasis, PiLp.single_apply, hf.eq_iff]
  · rw [finiteEmbeddingLinear_apply_of_not_mem f _ j hj]
    have hne : j ≠ f i := by
      intro h
      exact hj ⟨i, h.symm⟩
    simp [finiteEmbeddingBasis, hne]

end VQ.Tests.ECDLPSubgroupEmbedding
