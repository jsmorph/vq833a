import VQMathlib.ECDLP.Spectral.Orthogonality

open scoped BigOperators

namespace VQ.Tests.ECDLPSpectral

theorem infinity_eq_sum_shiftEigen {q : Nat} [NeZero q] (hq : 0 < q) :
    zeroBasis q =
      invSqrtCard q • ∑ k : ZMod q, shiftEigen q k := by
  ext t
  rw [zeroBasis_apply]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply,
    Finset.sum_apply, shiftEigen_apply]
  change (if t = 0 then 1 else 0) =
    invSqrtCard q *
      ∑ k : ZMod q, invSqrtCard q * ZMod.stdAddChar (k * t)
  rw [← Finset.mul_sum, ← mul_assoc, invSqrtCard_mul_self hq,
    character_sum]
  by_cases ht : t = 0
  · simp [ht, hq.ne']
  · simp [ht]

private theorem character_neg_mul_character {q : Nat} [NeZero q]
    (k t u : ZMod q) :
    ZMod.stdAddChar (-(k * t)) * ZMod.stdAddChar (k * u) =
      ZMod.stdAddChar (k * (u - t)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem basis_character_sum {q : Nat} [NeZero q] (hq : 0 < q)
    (t u : ZMod q) :
    (if u = t then 1 else 0) =
    invSqrtCard q *
      ∑ k : ZMod q,
        ZMod.stdAddChar (-(k * t)) *
          (invSqrtCard q * ZMod.stdAddChar (k * u)) := by
  have hsum :
      (∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) *
            (invSqrtCard q * ZMod.stdAddChar (k * u))) =
        invSqrtCard q *
          ∑ k : ZMod q, ZMod.stdAddChar (k * (u - t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      ZMod.stdAddChar (-(k * t)) *
          (invSqrtCard q * ZMod.stdAddChar (k * u)) =
          invSqrtCard q *
            (ZMod.stdAddChar (-(k * t)) *
              ZMod.stdAddChar (k * u)) := by ring
      _ = invSqrtCard q * ZMod.stdAddChar (k * (u - t)) := by
        rw [character_neg_mul_character]
  rw [hsum, ← mul_assoc, invSqrtCard_mul_self hq, character_sum]
  by_cases hut : u = t
  · subst u
    simp [hq.ne']
  · have hsub : u - t ≠ 0 := sub_ne_zero.mpr hut
    simp [hut, hsub]

theorem basis_eq_sum_shiftEigen {q : Nat} [NeZero q] (hq : 0 < q)
    (t : ZMod q) :
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) • shiftEigen q k := by
  classical
  ext u
  simp only [PiLp.single_apply, WithLp.ofLp_smul, Pi.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, shiftEigen_apply]
  exact basis_character_sum hq t u

end VQ.Tests.ECDLPSpectral
