import VQMathlib.ECDLP.FourierRecovery.Mixture
import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericIsometry
import VQMathlib.ECDLP.Spectral.Orthogonality

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open ECDLPSpectral

noncomputable section

structure CyclicMixtureSpec (q : Nat) [NeZero q] : Prop where
  orthonormal_fin : Orthonormal ℂ
    (fun k : Fin q => shiftEigen q (ZMod.finEquiv q k))
  scale_norm_sq : ‖invSqrtCard q‖ ^ 2 = 1 / (q : ℝ)

opaque cyclicMixtureSpec (q : Nat) [NeZero q] (hq : 0 < q) :
    CyclicMixtureSpec q := by
  refine ⟨(shiftEigen_orthonormal hq).comp
    (ZMod.finEquiv q) (ZMod.finEquiv q).injective, ?_⟩
  rw [invSqrtCard, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _)),
    div_pow, one_pow, Real.sq_sqrt (by positivity)]

opaque finiteEmbeddingShiftEigenMixtureWeightAs
    {q : Nat} [NeZero q] (cyclic : CyclicMixtureSpec q)
    {K : Type*} [Fintype K] [DecidableEq K]
    (f : ZMod q → K)
    (embedding : FiniteEmbeddingSpec (ZMod q) K f)
    {J L : Type*} (output : Fin q → EuclideanSpace ℂ K)
    (houtput : ∀ k,
      embedding.linear (shiftEigen q (ZMod.finEquiv q k)) = output k)
    (A : Fin q → J → ℂ) (B : Fin q → L → ℂ)
    (j : J) (l : L) (result : ℝ)
    (hresult : (1 / (q : ℝ)) *
      ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2 = result) :
    mixtureWeight (invSqrtCard q) A B output j l = result := by
  have hsource := cyclic.orthonormal_fin
  have hout : Orthonormal ℂ output := by
    rw [orthonormal_iff_ite] at hsource ⊢
    intro k m
    rw [← houtput k, ← houtput m, embedding.inner]
    exact hsource k m
  exact (mixtureWeight_eq_of_norm_sq (invSqrtCard q) A B output hout
    (1 / (q : ℝ)) cyclic.scale_norm_sq j l).trans hresult

structure EmbeddedCyclicMixtureSpec (q : Nat) [NeZero q]
    {K : Type} [Fintype K]
    (output : Fin q → EuclideanSpace ℂ K) : Prop where
  weight_eq : ∀ {J L : Type}
    (A : Fin q → J → ℂ) (B : Fin q → L → ℂ) (j : J) (l : L),
    mixtureWeight (invSqrtCard q) A B output j l =
      (1 / (q : ℝ)) * ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2

opaque embeddedCyclicMixtureSpec
    {q : Nat} [NeZero q] (cyclic : CyclicMixtureSpec q)
    {K : Type} [Fintype K] [DecidableEq K]
    (f : ZMod q → K)
    (embedding : FiniteEmbeddingSpec (ZMod q) K f)
    (output : Fin q → EuclideanSpace ℂ K)
    (houtput : ∀ k,
      embedding.linear (shiftEigen q (ZMod.finEquiv q k)) = output k) :
    EmbeddedCyclicMixtureSpec q output := by
  refine ⟨?_⟩
  intro J L A B j l
  exact finiteEmbeddingShiftEigenMixtureWeightAs cyclic f embedding output
    houtput A B j l _ rfl

opaque EmbeddedCyclicMixtureSpec.weightResultAs
    {q : Nat} [NeZero q] {K : Type} [Fintype K]
    {output : Fin q → EuclideanSpace ℂ K}
    (spec : EmbeddedCyclicMixtureSpec q output)
    {J L : Type} (A : Fin q → J → ℂ) (B : Fin q → L → ℂ)
    (j : J) (l : L) (result : ℝ)
    (hresult : (1 / (q : ℝ)) *
      ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2 = result) :
    mixtureWeight (invSqrtCard q) A B output j l = result :=
  (spec.weight_eq A B j l).trans hresult

end

end VQ.Tests.ECDLPFourierRecovery
