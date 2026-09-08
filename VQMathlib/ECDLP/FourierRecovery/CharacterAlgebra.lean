import VQMathlib.ECDLP.FourierRecovery.Mixture
import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericExpansion

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSpectral
open ECDLPSubgroupEmbedding

noncomputable section

opaque finiteEmbeddingFactoredCyclicBasisFinAs
    {q : Nat} [NeZero q] {K : Type*} [Fintype K] [DecidableEq K]
    (f : ZMod q → K) (embedding : FiniteEmbeddingSpec (ZMod q) K f)
    (cyclic : CyclicExpansionSpec q)
    (basis : ZMod q → EuclideanSpace ℂ K)
    (state : Fin q → EuclideanSpace ℂ K)
    (hbasis : ∀ t, finiteEmbeddingBasis f t = basis t)
    (hstate : ∀ k,
      embedding.linear (shiftEigen q (ZMod.finEquiv q k)) = state k)
    (t : ZMod q) (left right : Fin q → ℂ)
    (hfactor : ∀ k,
      ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) =
        left k * right k) :
    basis t =
      ∑ k : Fin q,
        (invSqrtCard q * (left k * right k)) • state k := by
  rw [finiteEmbeddingCyclicBasisFinAs f embedding cyclic basis state
    hbasis hstate t, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul, hfactor]

variable {I J K M : Type*} [Fintype I] [Fintype J] [Fintype K]
  [AddCommMonoid M] [Module ℂ M]

theorem doubleCharacterExpansion
    (inputLeft : I → ℂ) (inputRight : J → ℂ) (scale : ℂ)
    (left : K → I → ℂ) (right : K → J → ℂ)
    (state : K → M) (basis : I → J → M)
    (hbasis : ∀ i j,
      basis i j =
        ∑ k, (scale * (left k i * right k j)) • state k) :
    (∑ i, ∑ j, (inputLeft i * inputRight j) • basis i j) =
      ∑ k,
        (scale * (∑ i, inputLeft i * left k i) *
          (∑ j, inputRight j * right k j)) • state k := by
  simp_rw [hbasis, Finset.smul_sum, smul_smul]
  calc
    ∑ i, ∑ j, ∑ k,
        ((inputLeft i * inputRight j) *
          (scale * (left k i * right k j))) • state k =
      ∑ i, ∑ k, ∑ j,
        ((inputLeft i * inputRight j) *
          (scale * (left k i * right k j))) • state k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j,
        ((inputLeft i * inputRight j) *
          (scale * (left k i * right k j))) • state k := by
      rw [Finset.sum_comm]
    _ = ∑ k,
        (scale * (∑ i, inputLeft i * left k i) *
          (∑ j, inputRight j * right k j)) • state k := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        ∑ i, ∑ j,
            ((inputLeft i * inputRight j) *
              (scale * (left k i * right k j))) • state k =
          ∑ i, (∑ j,
            (inputLeft i * inputRight j) *
              (scale * (left k i * right k j))) • state k := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_smul.symm
        _ = (∑ i, ∑ j,
            (inputLeft i * inputRight j) *
              (scale * (left k i * right k j))) • state k :=
          Finset.sum_smul.symm
        _ = (scale * (∑ i, inputLeft i * left k i) *
            (∑ j, inputRight j * right k j)) • state k := by
          apply congrArg (fun z : ℂ => z • state k)
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring

end

end VQ.Tests.ECDLPFourierRecovery
