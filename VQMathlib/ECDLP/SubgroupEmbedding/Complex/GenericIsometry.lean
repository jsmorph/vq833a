import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericCoordinates

open scoped BigOperators ComplexConjugate

namespace VQ.Tests.ECDLPSubgroupEmbedding

theorem finiteEmbeddingBasis_orthonormal
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) :
    Orthonormal ℂ (finiteEmbeddingBasis f) := by
  change Orthonormal ℂ (fun i => EuclideanSpace.single (f i) (1 : ℂ))
  simpa only [Function.comp_def] using
    (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := κ)).comp f hf

theorem finiteEmbeddingLinear_inner
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f)
    (u v : EuclideanSpace ℂ ι) :
    inner ℂ (finiteEmbeddingLinear f u) (finiteEmbeddingLinear f v) =
      inner ℂ u v := by
  have hcomb :
      inner ℂ
          (∑ i : ι, u i • finiteEmbeddingBasis f i)
          (∑ i : ι, v i • finiteEmbeddingBasis f i) =
        ∑ i : ι, conj (u i) * v i := by
    simpa using
      (finiteEmbeddingBasis_orthonormal f hf).inner_sum u v Finset.univ
  have hsource :
      inner ℂ u v = ∑ i : ι, conj (u i) * v i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
  change inner ℂ
      (∑ i : ι, u i • finiteEmbeddingBasis f i)
      (∑ i : ι, v i • finiteEmbeddingBasis f i) = inner ℂ u v
  exact hcomb.trans hsource.symm

theorem finiteEmbeddingLinear_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f)
    (v : EuclideanSpace ℂ ι) :
    ‖finiteEmbeddingLinear f v‖ = ‖v‖ := by
  calc
    ‖finiteEmbeddingLinear f v‖ =
        Real.sqrt (inner ℂ (finiteEmbeddingLinear f v)
          (finiteEmbeddingLinear f v)).re :=
      norm_eq_sqrt_re_inner (𝕜 := ℂ) _
    _ = Real.sqrt (inner ℂ v v).re := by
      rw [finiteEmbeddingLinear_inner f hf]
    _ = ‖v‖ := (norm_eq_sqrt_re_inner (𝕜 := ℂ) v).symm

theorem finiteEmbeddingLinear_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) {u v : EuclideanSpace ℂ ι} (h : u = v) :
    finiteEmbeddingLinear f u = finiteEmbeddingLinear f v :=
  congrArg (finiteEmbeddingLinear f) h

theorem finiteEmbeddingLinear_weighted_sum
    {ι κ : Type*} {μ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Fintype μ]
    (f : ι → κ) (c : ℂ) (weight : μ → ℂ)
    (v : μ → EuclideanSpace ℂ ι) :
    finiteEmbeddingLinear f (c • ∑ j, weight j • v j) =
      c • ∑ j, weight j • finiteEmbeddingLinear f (v j) := by
  calc
    finiteEmbeddingLinear f (c • ∑ j, weight j • v j) =
        c • finiteEmbeddingLinear f (∑ j, weight j • v j) :=
      (finiteEmbeddingLinear f).map_smul c _
    _ = c • ∑ j, finiteEmbeddingLinear f (weight j • v j) := by
      rw [map_sum]
    _ = c • ∑ j, weight j • finiteEmbeddingLinear f (v j) := by
      apply congrArg (fun x : EuclideanSpace ℂ κ => c • x)
      apply Finset.sum_congr rfl
      intro j _
      exact (finiteEmbeddingLinear f).map_smul (weight j) (v j)

theorem finiteEmbeddingLinear_basis_weighted_sum
    {ι κ : Type*} {μ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype μ]
    (f : ι → κ) (hf : Function.Injective f) (i : ι)
    (c : ℂ) (weight : μ → ℂ) (v : μ → EuclideanSpace ℂ ι)
    (h : PiLp.single 2 i 1 = c • ∑ j, weight j • v j) :
    finiteEmbeddingBasis f i =
      c • ∑ j, weight j • finiteEmbeddingLinear f (v j) := by
  calc
    finiteEmbeddingBasis f i =
        finiteEmbeddingLinear f (PiLp.single 2 i 1) :=
      (finiteEmbeddingLinear_basis f hf i).symm
    _ = finiteEmbeddingLinear f (c • ∑ j, weight j • v j) :=
      finiteEmbeddingLinear_eq f h
    _ = c • ∑ j, weight j • finiteEmbeddingLinear f (v j) :=
      finiteEmbeddingLinear_weighted_sum f c weight v

theorem finiteEmbeddingLinear_basis_weighted_sum_as
    {ι κ : Type*} {μ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype μ]
    (f : ι → κ) (hf : Function.Injective f) (i : ι)
    (c : ℂ) (weight : μ → ℂ) (v : μ → EuclideanSpace ℂ ι)
    (w : μ → EuclideanSpace ℂ κ)
    (hw : ∀ j, finiteEmbeddingLinear f (v j) = w j)
    (h : PiLp.single 2 i 1 = c • ∑ j, weight j • v j) :
    finiteEmbeddingBasis f i = c • ∑ j, weight j • w j := by
  calc
    finiteEmbeddingBasis f i =
        c • ∑ j, weight j • finiteEmbeddingLinear f (v j) :=
      finiteEmbeddingLinear_basis_weighted_sum f hf i c weight v h
    _ = c • ∑ j, weight j • w j := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j]

structure FiniteEmbeddingSpec
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) where
  linear : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ
  apply_image : ∀ (v : EuclideanSpace ℂ ι) (i : ι),
    linear v (f i) = v i
  apply_of_not_mem : ∀ (v : EuclideanSpace ℂ ι) (j : κ),
    j ∉ Set.range f → linear v j = 0
  support_subset : ∀ v : EuclideanSpace ℂ ι,
    Function.support (linear v) ⊆ Set.range f
  basis_orthonormal : Orthonormal ℂ (finiteEmbeddingBasis f)
  inner : ∀ u v : EuclideanSpace ℂ ι,
    inner ℂ (linear u) (linear v) = inner ℂ u v
  norm : ∀ v : EuclideanSpace ℂ ι, ‖linear v‖ = ‖v‖
  basis : ∀ i : ι,
    linear (PiLp.single 2 i 1) = finiteEmbeddingBasis f i
  map_eq : ∀ {u v : EuclideanSpace ℂ ι}, u = v → linear u = linear v
  weighted_sum : ∀ {μ : Type} [Fintype μ]
    (c : ℂ) (weight : μ → ℂ) (v : μ → EuclideanSpace ℂ ι),
    linear (c • ∑ j, weight j • v j) =
      c • ∑ j, weight j • linear (v j)
  basis_weighted_sum : ∀ {μ : Type} [Fintype μ]
    (i : ι) (c : ℂ) (weight : μ → ℂ) (v : μ → EuclideanSpace ℂ ι),
    PiLp.single 2 i 1 = c • ∑ j, weight j • v j →
      finiteEmbeddingBasis f i = c • ∑ j, weight j • linear (v j)
  basis_weighted_sum_as : ∀ {μ : Type} [Fintype μ]
    (i : ι) (c : ℂ) (weight : μ → ℂ) (v : μ → EuclideanSpace ℂ ι)
    (w : μ → EuclideanSpace ℂ κ),
    (∀ j, linear (v j) = w j) →
    PiLp.single 2 i 1 = c • ∑ j, weight j • v j →
      finiteEmbeddingBasis f i = c • ∑ j, weight j • w j

noncomputable def finiteEmbeddingSpec
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) :
    FiniteEmbeddingSpec ι κ f where
  linear := finiteEmbeddingLinear f
  apply_image := finiteEmbeddingLinear_apply_image f hf
  apply_of_not_mem := finiteEmbeddingLinear_apply_of_not_mem f
  support_subset := finiteEmbeddingLinear_support_subset f
  basis_orthonormal := finiteEmbeddingBasis_orthonormal f hf
  inner := finiteEmbeddingLinear_inner f hf
  norm := finiteEmbeddingLinear_norm f hf
  basis := finiteEmbeddingLinear_basis f hf
  map_eq := finiteEmbeddingLinear_eq f
  weighted_sum := finiteEmbeddingLinear_weighted_sum f
  basis_weighted_sum := finiteEmbeddingLinear_basis_weighted_sum f hf
  basis_weighted_sum_as := finiteEmbeddingLinear_basis_weighted_sum_as f hf

end VQ.Tests.ECDLPSubgroupEmbedding
