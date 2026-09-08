import VQMathlib.ECDLP.Spectral.Basic

open WithLp
open scoped BigOperators ComplexConjugate

namespace VQ.Tests.ECDLPSpectral

theorem shiftEigen_inner {q : Nat} [NeZero q] (hq : 0 < q)
    (k l : ZMod q) :
    inner ℂ (shiftEigen q k) (shiftEigen q l) =
      if k = l then 1 else 0 := by
  calc
    inner ℂ (shiftEigen q k) (shiftEigen q l) =
        ∑ t : ZMod q,
          conj (invSqrtCard q * ZMod.stdAddChar (k * t)) *
            (invSqrtCard q * ZMod.stdAddChar (l * t)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply', shiftEigen_apply]
    _ = (invSqrtCard q * invSqrtCard q) *
        ∑ t : ZMod q,
          conj (ZMod.stdAddChar (k * t)) * ZMod.stdAddChar (l * t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul, invSqrtCard_conj]
      ring
    _ = ((q : ℂ)⁻¹) *
        ∑ t : ZMod q, ZMod.stdAddChar (t * (l - k)) := by
      rw [invSqrtCard_mul_self hq]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact conj_character_mul_character q k l t
    _ = if k = l then 1 else 0 := by
      rw [character_sum]
      by_cases hkl : k = l
      · subst l
        simp [hq.ne']
      · have hlk : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkl)
        simp [hkl, hlk]

theorem shiftEigen_orthonormal {q : Nat} [NeZero q] (hq : 0 < q) :
    Orthonormal ℂ (shiftEigen q) := by
  rw [orthonormal_iff_ite]
  exact shiftEigen_inner hq

theorem shiftEigen_norm {q : Nat} [NeZero q] (hq : 0 < q)
    (k : ZMod q) :
    ‖shiftEigen q k‖ = 1 :=
  (shiftEigen_orthonormal hq).norm_eq_one k

end VQ.Tests.ECDLPSpectral
