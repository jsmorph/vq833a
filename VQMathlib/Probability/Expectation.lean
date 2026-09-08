import VQMathlib.Probability.FiniteLaw

namespace VQMathlib.Probability

open scoped BigOperators

noncomputable section

namespace FiniteLaw

variable {α : Type*} [Fintype α]

/-- The expectation of a real-valued function under a finite law. -/
def expectation (law : FiniteLaw α) (value : α → ℝ) : ℝ :=
  ∑ outcome, law.mass outcome * value outcome

@[simp]
theorem expectation_zero (law : FiniteLaw α) :
    law.expectation (fun _ => 0) = 0 := by
  simp [expectation]

@[simp]
theorem expectation_const (law : FiniteLaw α) (value : ℝ) :
    law.expectation (fun _ => value) = value := by
  rw [expectation, ← Finset.sum_mul, law.mass_sum, one_mul]

theorem expectation_add (law : FiniteLaw α) (left right : α → ℝ) :
    law.expectation (fun outcome => left outcome + right outcome) =
      law.expectation left + law.expectation right := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mul_const (law : FiniteLaw α)
    (value : α → ℝ) (constant : ℝ) :
    law.expectation (fun outcome => value outcome * constant) =
      law.expectation value * constant := by
  simp only [expectation, mul_assoc, Finset.sum_mul]

theorem expectation_nonneg (law : FiniteLaw α) {value : α → ℝ}
    (hvalue : ∀ outcome, 0 ≤ value outcome) :
    0 ≤ law.expectation value := by
  unfold expectation
  exact Finset.sum_nonneg fun outcome _ =>
    mul_nonneg (law.mass_nonneg outcome) (hvalue outcome)

theorem expectation_mono (law : FiniteLaw α) {left right : α → ℝ}
    (hle : ∀ outcome, left outcome ≤ right outcome) :
    law.expectation left ≤ law.expectation right := by
  unfold expectation
  apply Finset.sum_le_sum
  intro outcome _
  exact mul_le_mul_of_nonneg_left (hle outcome) (law.mass_nonneg outcome)

theorem expectation_pushforward {β : Type*} [Fintype β] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β) (value : β → ℝ) :
    (law.pushforward f).expectation value =
      law.expectation (fun outcome => value (f outcome)) := by
  exact pushforward_weighted_sum law f value

theorem expectation_ofRatMass (mass : α → ℚ)
    (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1)
    (value : α → ℚ) :
    (ofRatMass mass mass_nonneg mass_sum).expectation
        (fun outcome => (value outcome : ℝ)) =
      ((∑ outcome, mass outcome * value outcome : ℚ) : ℝ) := by
  unfold expectation
  rw [Rat.cast_sum]
  simp only [ofRatMass_mass, Rat.cast_mul]

theorem expectation_empirical {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) (value : β → ℝ) :
    (empirical sample).expectation value =
      (uniformFin n).expectation (fun index => value (sample index)) :=
  expectation_pushforward (uniformFin n) sample value

theorem expectation_empirical_rat {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) (value : β → ℚ) :
    (empirical sample).expectation (fun outcome => (value outcome : ℝ)) =
      (((∑ index, value (sample index) : ℚ) / (n : ℚ) : ℚ) : ℝ) := by
  rw [expectation_empirical]
  unfold expectation
  simp only [uniformFin_mass]
  simp_rw [← Rat.cast_mul]
  rw [← Rat.cast_sum]
  congr 1
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

/-- The mass of inputs whose deterministic cost meets a threshold. -/
def tailWeight (law : FiniteLaw α) (cost : α → ℝ) (threshold : ℝ) : ℝ :=
  law.eventWeight fun outcome => decide (threshold ≤ cost outcome)

theorem tailWeight_nonneg (law : FiniteLaw α)
    (cost : α → ℝ) (threshold : ℝ) :
    0 ≤ law.tailWeight cost threshold :=
  law.eventWeight_nonneg _

theorem tailWeight_le_one (law : FiniteLaw α)
    (cost : α → ℝ) (threshold : ℝ) :
    law.tailWeight cost threshold ≤ 1 :=
  law.eventWeight_le_one _

theorem threshold_mul_tailWeight_le_expectation (law : FiniteLaw α)
    (cost : α → ℝ) (threshold : ℝ)
    (hcost : ∀ outcome, 0 ≤ cost outcome) :
    threshold * law.tailWeight cost threshold ≤ law.expectation cost := by
  rw [tailWeight, eventWeight, expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases htail : threshold ≤ cost outcome
  · simpa [htail, mul_comm] using
      mul_le_mul_of_nonneg_right htail (law.mass_nonneg outcome)
  · simpa [htail] using
      mul_nonneg (law.mass_nonneg outcome) (hcost outcome)

theorem tailWeight_le_expectation_div (law : FiniteLaw α)
    (cost : α → ℝ) (threshold : ℝ)
    (hcost : ∀ outcome, 0 ≤ cost outcome) (hthreshold : 0 < threshold) :
    law.tailWeight cost threshold ≤ law.expectation cost / threshold := by
  apply (le_div_iff₀ hthreshold).2
  simpa [mul_comm] using
    law.threshold_mul_tailWeight_le_expectation cost threshold hcost

end FiniteLaw

end

end VQMathlib.Probability
