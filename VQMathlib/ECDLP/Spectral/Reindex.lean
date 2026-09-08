import VQMathlib.ECDLP.Spectral.Expansion

open scoped BigOperators

namespace VQ.Tests.ECDLPSpectral

noncomputable def zmodToFinState (q : Nat) [NeZero q] :
    CyclicState q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ZMod.finEquiv q).symm

@[simp]
theorem zmodToFinState_apply (q : Nat) [NeZero q]
    (v : CyclicState q) (i : Fin q) :
    zmodToFinState q v i = v (ZMod.finEquiv q i) :=
  rfl

theorem sum_fin_comp_finEquiv (q : Nat) [NeZero q]
    (f : ZMod q → ℂ) :
    (∑ k : Fin q, f (ZMod.finEquiv q k)) = ∑ k : ZMod q, f k :=
  Equiv.sum_comp (ZMod.finEquiv q).toEquiv f

theorem basis_character_sum_fin {q : Nat} [NeZero q]
    (hq : 0 < q) (t u : ZMod q) :
    (if u = t then 1 else 0) =
    invSqrtCard q *
      ∑ k : Fin q,
        ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) *
          (invSqrtCard q * ZMod.stdAddChar ((ZMod.finEquiv q k) * u)) := by
  have hreindex :
      (∑ k : Fin q,
          ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) *
            (invSqrtCard q * ZMod.stdAddChar ((ZMod.finEquiv q k) * u))) =
        ∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) *
          (invSqrtCard q * ZMod.stdAddChar (k * u)) :=
    sum_fin_comp_finEquiv q
      (fun k : ZMod q =>
        ZMod.stdAddChar (-(k * t)) *
          (invSqrtCard q * ZMod.stdAddChar (k * u)))
  rw [hreindex]
  exact basis_character_sum hq t u

theorem basis_eq_sum_shiftEigen_fin {q : Nat} [NeZero q]
    (hq : 0 < q) (t : ZMod q) :
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : Fin q,
          ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) •
            shiftEigen q (ZMod.finEquiv q k) := by
  classical
  ext u
  simp only [PiLp.single_apply, WithLp.ofLp_smul, Pi.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, shiftEigen_apply]
  exact basis_character_sum_fin hq t u

end VQ.Tests.ECDLPSpectral
