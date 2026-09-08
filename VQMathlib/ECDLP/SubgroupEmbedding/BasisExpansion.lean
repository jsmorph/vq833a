import VQMathlib.ECDLP.SubgroupEmbedding.BasisExpansionFin

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

attribute [local irreducible] q
local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem embeddedShiftEigenFin_orthonormal (a b : ScalarIndex) :
    Orthonormal ℂ (embeddedShiftEigenFin a b) := by
  have h := (embeddedShiftEigen_orthonormal a b).comp
    (ZMod.finEquiv q) (ZMod.finEquiv q).injective
  change Orthonormal ℂ
    (fun k : Fin q => embeddedShiftEigen a b (ZMod.finEquiv q k)) at h
  change Orthonormal ℂ
    (fun k : Fin q => embeddedShiftEigen a b (ZMod.finEquiv q k))
  exact h

theorem invSqrtCard_norm_sq {card : Nat} (hcard : 0 < card) :
    ‖invSqrtCard card‖ ^ 2 = 1 / (card : ℝ) := by
  rw [invSqrtCard, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _)),
    div_pow, one_pow, Real.sq_sqrt (by positivity)]

theorem secp256k1_invSqrtCard_norm_sq :
    ‖invSqrtCard q‖ ^ 2 = 1 / (q : ℝ) :=
  invSqrtCard_norm_sq q_prime.pos

end VQ.Tests.ECDLPSubgroupEmbedding
