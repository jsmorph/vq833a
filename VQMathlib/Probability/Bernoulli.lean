import VQMathlib.Semantics.Approximation

namespace VQ.Tests.Repetition

noncomputable section

open scoped BigOperators

def trialWeight (successProbability : ℝ) (success : Bool) : ℝ :=
  if success then successProbability else 1 - successProbability

def outcomeWeight (successProbability : ℝ) {runs : Nat}
    (outcome : Fin runs → Bool) : ℝ :=
  ∏ i, trialWeight successProbability (outcome i)

def totalWeight (successProbability : ℝ) (runs : Nat) : ℝ :=
  ∑ outcome : Fin runs → Bool, outcomeWeight successProbability outcome

def allFailureWeight (successProbability : ℝ) (runs : Nat) : ℝ :=
  ∑ outcome : Fin runs → Bool,
    if ∀ i, outcome i = false then
      outcomeWeight successProbability outcome
    else 0

def atLeastOneSuccessWeight (successProbability : ℝ) (runs : Nat) : ℝ :=
  ∑ outcome : Fin runs → Bool,
    if ∃ i, outcome i = true then
      outcomeWeight successProbability outcome
    else 0

theorem outcomeWeight_nonneg {successProbability : ℝ}
    (hzero : 0 ≤ successProbability) (hone : successProbability ≤ 1)
    {runs : Nat} (outcome : Fin runs → Bool) :
    0 ≤ outcomeWeight successProbability outcome := by
  apply Finset.prod_nonneg
  intro i _
  unfold trialWeight
  split <;> linarith

theorem totalWeight_eq_one (successProbability : ℝ) (runs : Nat) :
    totalWeight successProbability runs = 1 := by
  unfold totalWeight outcomeWeight
  rw [← Fintype.prod_sum]
  simp [trialWeight]

theorem allFailureWeight_eq (successProbability : ℝ) (runs : Nat) :
    allFailureWeight successProbability runs =
      (1 - successProbability) ^ runs := by
  classical
  unfold allFailureWeight
  rw [Fintype.sum_eq_single (fun _ => false)]
  · simp [outcomeWeight, trialWeight]
  · intro outcome hne
    have hfailure : ¬ ∀ i, outcome i = false := by
      intro h
      apply hne
      funext i
      exact h i
    simp [hfailure]

theorem atLeastOneSuccess_add_allFailure
    (successProbability : ℝ) (runs : Nat) :
    atLeastOneSuccessWeight successProbability runs +
        allFailureWeight successProbability runs =
      totalWeight successProbability runs := by
  classical
  unfold atLeastOneSuccessWeight allFailureWeight totalWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hfailure : ∀ i, outcome i = false
  · simp [hfailure]
  · have hsuccess : ∃ i, outcome i = true := by
      simp only [not_forall] at hfailure
      obtain ⟨i, hi⟩ := hfailure
      exact ⟨i, Bool.eq_true_of_not_eq_false hi⟩
    simp [hfailure, hsuccess]

theorem atLeastOneSuccessWeight_eq (successProbability : ℝ)
    (runs : Nat) :
    atLeastOneSuccessWeight successProbability runs =
      1 - (1 - successProbability) ^ runs := by
  have hsum := atLeastOneSuccess_add_allFailure successProbability runs
  rw [totalWeight_eq_one, allFailureWeight_eq] at hsum
  linarith

theorem atLeastOneSuccessWeight_mem_Icc {successProbability : ℝ}
    (hzero : 0 ≤ successProbability) (hone : successProbability ≤ 1)
    (runs : Nat) :
    atLeastOneSuccessWeight successProbability runs ∈ Set.Icc 0 1 := by
  rw [atLeastOneSuccessWeight_eq]
  have hfailureZero : 0 ≤ (1 - successProbability) ^ runs :=
    pow_nonneg (by linarith) runs
  have hfailureOne : (1 - successProbability) ^ runs ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  constructor <;> linarith

theorem atLeastOneSuccessWeight_ge {lowerBound successProbability : ℝ}
    (hlower : lowerBound ≤ successProbability)
    (hsuccessOne : successProbability ≤ 1) (runs : Nat) :
    1 - (1 - lowerBound) ^ runs ≤
      atLeastOneSuccessWeight successProbability runs := by
  rw [atLeastOneSuccessWeight_eq]
  have hfailure :
      (1 - successProbability) ^ runs ≤ (1 - lowerBound) ^ runs :=
    pow_le_pow_left₀ (by linarith) (by linarith) runs
  linarith

theorem acceptanceWeight_le_one_of_norm_eq_one {index : Type}
    [Fintype index] (accept : index → Bool)
    (state : EuclideanSpace ℂ index) (hnorm : ‖state‖ = 1) :
    Approximation.acceptanceWeight accept state ≤ 1 := by
  have hsum := Approximation.acceptanceWeight_add_rejectionWeight
    accept state
  have hrejection := Approximation.rejectionWeight_nonneg accept state
  rw [hnorm] at hsum
  norm_num at hsum
  linarith

end

/- Axiom guards. -/

/-- info: 'VQ.Tests.Repetition.atLeastOneSuccessWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.Repetition.atLeastOneSuccessWeight_eq

/-- info: 'VQ.Tests.Repetition.atLeastOneSuccessWeight_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.Repetition.atLeastOneSuccessWeight_ge

end VQ.Tests.Repetition
