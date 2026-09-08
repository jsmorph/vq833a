import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericIsometry
import VQMathlib.ECDLP.Spectral.ExpansionSpec

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral

noncomputable section

opaque finiteEmbeddingCyclicBasisZModAs
    {q : Nat} [NeZero q] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ZMod q → κ) (embedding : FiniteEmbeddingSpec (ZMod q) κ f)
    (cyclic : CyclicExpansionSpec q)
    (basis : ZMod q → EuclideanSpace ℂ κ)
    (w : ZMod q → EuclideanSpace ℂ κ)
    (hbasis : ∀ t, finiteEmbeddingBasis f t = basis t)
    (hw : ∀ k, embedding.linear (shiftEigen q k) = w k)
    (t : ZMod q) :
    basis t =
      invSqrtCard q •
        ∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) • w k := by
  rw [← hbasis t]
  exact embedding.basis_weighted_sum_as t (invSqrtCard q)
    (fun k : ZMod q => ZMod.stdAddChar (-(k * t)))
    (fun k : ZMod q => shiftEigen q k) w hw
    (cyclicExpansionBasisZMod cyclic t)

opaque finiteEmbeddingCyclicBasisFinAs
    {q : Nat} [NeZero q] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ZMod q → κ) (embedding : FiniteEmbeddingSpec (ZMod q) κ f)
    (cyclic : CyclicExpansionSpec q)
    (basis : ZMod q → EuclideanSpace ℂ κ)
    (w : Fin q → EuclideanSpace ℂ κ)
    (hbasis : ∀ t, finiteEmbeddingBasis f t = basis t)
    (hw : ∀ k, embedding.linear (shiftEigen q (ZMod.finEquiv q k)) = w k)
    (t : ZMod q) :
    basis t =
      invSqrtCard q •
        ∑ k : Fin q,
          ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) • w k := by
  rw [← hbasis t]
  exact embedding.basis_weighted_sum_as t (invSqrtCard q)
    (fun k : Fin q =>
      ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)))
    (fun k : Fin q => shiftEigen q (ZMod.finEquiv q k)) w hw
    (cyclicExpansionBasisFin cyclic t)

end

end VQ.Tests.ECDLPSubgroupEmbedding
