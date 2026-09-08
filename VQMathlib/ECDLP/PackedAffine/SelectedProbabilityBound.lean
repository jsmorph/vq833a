import VQMathlib.ECDLP.FourierRecovery.SelectedSum

open scoped BigOperators

namespace VQ.Tests.PackedAffineECDLP.SelectedProbabilityBound

open VQ.Tests.ECDLPFourierRecovery

theorem selectedContribution_le_one
    {N q d : Nat} (hq : 0 < q) (hqN : q ≤ N)
    (marginal : Fin N × Fin N → ℝ)
    (hnonneg : ∀ outcome, 0 ≤ marginal outcome)
    (hsum : (∑ outcome, marginal outcome) = 1) :
    selectedContribution N q d hq hqN marginal ≤ 1 := by
  calc
    selectedContribution N q d hq hqN marginal ≤
        ∑ outcome, marginal outcome := by
      unfold selectedContribution
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun outcome _ _ => hnonneg outcome)
    _ = 1 := hsum

end VQ.Tests.PackedAffineECDLP.SelectedProbabilityBound
