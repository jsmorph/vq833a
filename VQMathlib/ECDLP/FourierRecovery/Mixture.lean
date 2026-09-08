import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic.Ring

namespace VQ.Tests.ECDLPFourierRecovery

open scoped BigOperators

noncomputable section

variable {κ J L E : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def latentMixture (scale : ℂ) (A : κ → J → ℂ) (B : κ → L → ℂ)
    (χ : κ → E) (j : J) (l : L) : E :=
  ∑ k, (scale * A k j * B k l) • χ k

def mixtureWeight (scale : ℂ) (A : κ → J → ℂ) (B : κ → L → ℂ)
    (χ : κ → E) (j : J) (l : L) : ℝ :=
  ‖latentMixture scale A B χ j l‖ ^ 2

structure LatentMixtureData (scale : ℂ)
    (A : κ → J → ℂ) (B : κ → L → ℂ)
    (χ : κ → E) (j : J) (l : L) where
  state : E
  state_eq : state = latentMixture scale A B χ j l
  weight_eq : ‖state‖ ^ 2 = mixtureWeight scale A B χ j l

opaque latentMixtureData (scale : ℂ)
    (A : κ → J → ℂ) (B : κ → L → ℂ)
    (χ : κ → E) (j : J) (l : L) :
    LatentMixtureData scale A B χ j l :=
  ⟨latentMixture scale A B χ j l, rfl, rfl⟩

theorem norm_sq_sum_orthonormal (χ : κ → E) (hχ : Orthonormal ℂ χ)
    (coefficient : κ → ℂ) :
    ‖∑ k, coefficient k • χ k‖ ^ 2 = ∑ k, ‖coefficient k‖ ^ 2 := by
  simpa using
    (hχ.orthogonalFamily.norm_sum coefficient (Finset.univ : Finset κ))

theorem mixtureWeight_eq (scale : ℂ) (A : κ → J → ℂ) (B : κ → L → ℂ)
    (χ : κ → E) (hχ : Orthonormal ℂ χ) (j : J) (l : L) :
    mixtureWeight scale A B χ j l =
      ‖scale‖ ^ 2 * ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2 := by
  rw [mixtureWeight, latentMixture, norm_sq_sum_orthonormal χ hχ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_mul]
  ring

theorem mixtureWeight_eq_of_norm_sq (scale : ℂ)
    (A : κ → J → ℂ) (B : κ → L → ℂ) (χ : κ → E)
    (hχ : Orthonormal ℂ χ) (normalization : ℝ)
    (hscale : ‖scale‖ ^ 2 = normalization) (j : J) (l : L) :
    mixtureWeight scale A B χ j l =
      normalization * ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2 := by
  rw [mixtureWeight_eq scale A B χ hχ j l, hscale]

structure OrthonormalMixtureSpec (scale : ℂ)
    (A : κ → J → ℂ) (B : κ → L → ℂ) (χ : κ → E)
    (normalization : ℝ) : Prop where
  weight_eq : ∀ j l,
    mixtureWeight scale A B χ j l =
      normalization * ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2

opaque orthonormalMixtureSpec (scale : ℂ)
    (A : κ → J → ℂ) (B : κ → L → ℂ) (χ : κ → E)
    (hχ : Orthonormal ℂ χ) (normalization : ℝ)
    (hscale : ‖scale‖ ^ 2 = normalization) :
    OrthonormalMixtureSpec scale A B χ normalization :=
  ⟨mixtureWeight_eq_of_norm_sq scale A B χ hχ normalization hscale⟩

opaque OrthonormalMixtureSpec.weightResultAs
    {scale : ℂ} {A : κ → J → ℂ} {B : κ → L → ℂ}
    {χ : κ → E} {normalization : ℝ}
    (spec : OrthonormalMixtureSpec scale A B χ normalization)
    (j : J) (l : L) (result : ℝ)
    (hresult : normalization *
      ∑ k, ‖A k j‖ ^ 2 * ‖B k l‖ ^ 2 = result) :
    mixtureWeight scale A B χ j l = result :=
  (spec.weight_eq j l).trans hresult

section SelectedEvents

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
  [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem sum_selected_weights_le_total (selected : Finset κ)
    (selector : κ → Ω) (weight : Ω → ℝ)
    (hselector : Set.InjOn selector selected)
    (hnonneg : ∀ o, 0 ≤ weight o) :
    ∑ k ∈ selected, weight (selector k) ≤ ∑ o, weight o := by
  calc
    ∑ k ∈ selected, weight (selector k) =
        ∑ o ∈ selected.image selector, weight o := by
      rw [Finset.sum_image hselector]
    _ ≤ ∑ o ∈ (Finset.univ : Finset Ω), weight o :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun o _ _ => hnonneg o)
    _ = ∑ o, weight o := rfl

omit [DecidableEq κ] in
theorem sum_selected_component_le_total (selected : Finset κ)
    (selector : κ → Ω) (component : κ → Ω → ℝ)
    (hselector : Set.InjOn selector selected)
    (hnonneg : ∀ k o, 0 ≤ component k o) :
    ∑ k ∈ selected, component k (selector k) ≤
      ∑ o, ∑ k, component k o := by
  calc
    ∑ k ∈ selected, component k (selector k) ≤
        ∑ k ∈ selected, ∑ k', component k' (selector k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      calc
        component k (selector k) =
            ∑ k' ∈ ({k} : Finset κ), component k' (selector k) := by simp
        _ ≤ ∑ k' ∈ (Finset.univ : Finset κ), component k' (selector k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr
            (Finset.mem_univ k)) (fun k' _ _ => hnonneg k' (selector k))
        _ = ∑ k', component k' (selector k) := rfl
    _ ≤ ∑ o, ∑ k, component k o :=
      sum_selected_weights_le_total selected selector
        (fun o => ∑ k, component k o) hselector
        (fun o => Finset.sum_nonneg fun k _ => hnonneg k o)

omit [DecidableEq κ] in
theorem sum_selected_lower_le_total (selected : Finset κ)
    (selector : κ → Ω) (component : κ → Ω → ℝ) (lower : κ → ℝ)
    (hselector : Set.InjOn selector selected)
    (hnonneg : ∀ k o, 0 ≤ component k o)
    (hlower : ∀ k ∈ selected, lower k ≤ component k (selector k)) :
    ∑ k ∈ selected, lower k ≤ ∑ o, ∑ k, component k o := by
  exact (Finset.sum_le_sum hlower).trans
    (sum_selected_component_le_total selected selector component hselector hnonneg)

end SelectedEvents

end

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.mixtureWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms VQ.Tests.ECDLPFourierRecovery.mixtureWeight_eq
