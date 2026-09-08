import VQMathlib.ECDLP.FourierRecovery.EmittedLatent

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

opaque euclidean_support_sum_smul_subset
    {K I : Type*} [Fintype K]
    (coefficient : K → ℂ)
    (state : K → EuclideanSpace ℂ I) (s : Set I)
    (hstate : ∀ k, Function.support (state k).ofLp ⊆ s) :
    Function.support
      ((∑ k, coefficient k • state k : EuclideanSpace ℂ I).ofLp) ⊆ s := by
  intro i hi
  by_contra his
  apply hi
  simp only [WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk : state k i = 0 := by
    by_contra hki
    exact his (hstate k hki)
  rw [hk, smul_zero]

theorem pairLatentState_support (d : Nat)
    (o : ScalarIndex × ScalarIndex) :
    Function.support (pairLatentState d o) ⊆
      {i | scalarPairEvent o i = true} := by
  change Function.support ((pairLatentMixtureData d o).state) ⊆ _
  rw [pairLatentState_eq_latentMixture_data d o]
  unfold latentMixture
  apply euclidean_support_sum_smul_subset
  intro k i hi
  by_cases himage : i ∈ Set.range (subgroupFullIndex o.1 o.2)
  · rcases himage with ⟨t, rfl⟩
    simp
  · exfalso
    apply hi
    rw [embeddedShiftEigenFin,
      embeddedShiftEigen_apply_of_not_mem o.1 o.2 _ i himage]

end VQ.Tests.ECDLPFourierRecovery
