import VQMathlib.ECDLP.FourierRecovery.Mixture
import VQMathlib.ECDLP.FourierRecovery.SelectedPairs

namespace VQ.Tests.ECDLPFourierRecovery

open scoped BigOperators

noncomputable section

theorem sum_selected_lower_le_image_marginal
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq Ω]
    (selected : Finset κ) (selector : κ → Ω)
    (component : κ → Ω → ℝ) (marginal : Ω → ℝ) (lower : κ → ℝ)
    (hselector : Set.InjOn selector selected)
    (hnonneg : ∀ k o, 0 ≤ component k o)
    (hmarginal : ∀ o, marginal o = ∑ k, component k o)
    (hlower : ∀ k ∈ selected, lower k ≤ component k (selector k)) :
    ∑ k ∈ selected, lower k ≤
      ∑ o ∈ selected.image selector, marginal o := by
  calc
    ∑ k ∈ selected, lower k ≤
        ∑ k ∈ selected, component k (selector k) :=
      Finset.sum_le_sum hlower
    _ ≤ ∑ k ∈ selected, marginal (selector k) := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [hmarginal]
      calc
        component k (selector k) =
            ∑ k' ∈ ({k} : Finset κ), component k' (selector k) := by simp
        _ ≤ ∑ k' ∈ (Finset.univ : Finset κ), component k' (selector k) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr (Finset.mem_univ k))
            (fun k' _ _ => hnonneg k' (selector k))
        _ = ∑ k', component k' (selector k) := rfl
    _ = ∑ o ∈ selected.image selector, marginal o := by
      rw [Finset.sum_image hselector]

def uniformComponentWeight (N q d : Nat) (hq : 0 < q)
    (k : Fin q) (o : Fin N × Fin N) : ℝ :=
  (1 / (q : ℝ)) *
    (fourierPeakProbability N q o.1.val k.val *
      fourierPeakProbability N q o.2.val (productLabel q d hq k).val)

def selectedObservables (N q d : Nat) (hq : 0 < q) (hqN : q ≤ N) :
    Finset (Fin N × Fin N) :=
  (nonzeroLabels q hq).image (selectedPair N q d hq hqN)

def selectedContribution (N q d : Nat) (hq : 0 < q) (hqN : q ≤ N)
    (marginal : Fin N × Fin N → ℝ) : ℝ :=
  ∑ o ∈ selectedObservables N q d hq hqN, marginal o

theorem uniformComponentWeight_nonneg {N q d : Nat} (hq : 0 < q)
    (k : Fin q) (o : Fin N × Fin N) :
    0 ≤ uniformComponentWeight N q d hq k o := by
  have hscale : 0 ≤ (1 / (q : ℝ)) := by positivity
  have hfirst : 0 ≤ fourierPeakProbability N q o.1.val k.val := sq_nonneg _
  have hsecond : 0 ≤ fourierPeakProbability N q o.2.val
      (productLabel q d hq k).val := sq_nonneg _
  exact mul_nonneg hscale (mul_nonneg hfirst hsecond)

theorem uniformComponentWeight_selected_lower {N q d : Nat}
    (hq : 0 < q) (hqN : q ≤ N) (k : Fin q) :
    (1 / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      uniformComponentWeight N q d hq k
        (selectedPair N q d hq hqN k) := by
  unfold uniformComponentWeight
  exact mul_le_mul_of_nonneg_left
    (selectedPair_probability_product hq hqN k) (by positivity)

theorem selectedContribution_lower_bound {N q d : Nat}
    (hq : 0 < q) (hqN : q ≤ N)
    (marginal : Fin N × Fin N → ℝ)
    (hmarginal : ∀ o, marginal o =
      ∑ k : Fin q, uniformComponentWeight N q d hq k o) :
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedContribution N q d hq hqN marginal := by
  have hselected :
      ∑ k ∈ nonzeroLabels q hq,
          (1 / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
        selectedContribution N q d hq hqN marginal := by
    rw [selectedContribution, selectedObservables]
    exact sum_selected_lower_le_image_marginal
      (selected := nonzeroLabels q hq)
      (selector := selectedPair N q d hq hqN)
      (component := uniformComponentWeight N q d hq)
      (marginal := marginal)
      (lower := fun _ => (1 / (q : ℝ)) * ((2401 : ℝ) / 14641))
      (selectedPair_injective hq hqN).injOn
      (uniformComponentWeight_nonneg hq) hmarginal
      (fun k _ => uniformComponentWeight_selected_lower hq hqN k)
  calc
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) =
        ((q - 1 : Nat) : ℝ) *
          ((1 / (q : ℝ)) * ((2401 : ℝ) / 14641)) := by ring
    _ = ∑ k ∈ nonzeroLabels q hq,
          (1 / (q : ℝ)) * ((2401 : ℝ) / 14641) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_nonzeroLabels hq]
    _ ≤ selectedContribution N q d hq hqN marginal := hselected

theorem mem_selectedObservables_iff {N q d : Nat}
    (hq : 0 < q) (hqN : q ≤ N) (o : Fin N × Fin N) :
    o ∈ selectedObservables N q d hq hqN ↔
      ∃ k : Fin q, k.val ≠ 0 ∧ selectedPair N q d hq hqN k = o := by
  simp [selectedObservables, mem_nonzeroLabels_iff hq]

theorem decode_mem_selectedObservables {N q d : Nat}
    (hq : 0 < q) (hqN : q ≤ N) {o : Fin N × Fin N}
    (ho : o ∈ selectedObservables N q d hq hqN) :
    decode q N o.1.val < q ∧
      decode q N o.1.val ≠ 0 ∧
      decode q N o.2.val = (d * decode q N o.1.val) % q := by
  obtain ⟨k, hk, rfl⟩ := (mem_selectedObservables_iff hq hqN o).1 ho
  have hdecode := decode_selectedPair (d := d) hq hqN k
  rw [hdecode.1, hdecode.2]
  exact ⟨k.isLt, hk, rfl⟩

end

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.sum_selected_lower_le_image_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms VQ.Tests.ECDLPFourierRecovery.sum_selected_lower_le_image_marginal

/-- info: 'VQ.Tests.ECDLPFourierRecovery.selectedContribution_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms VQ.Tests.ECDLPFourierRecovery.selectedContribution_lower_bound

/-- info: 'VQ.Tests.ECDLPFourierRecovery.decode_mem_selectedObservables' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms VQ.Tests.ECDLPFourierRecovery.decode_mem_selectedObservables
