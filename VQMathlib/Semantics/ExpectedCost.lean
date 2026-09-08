/-
Exact expected execution costs for programs.

Each semantic branch receives the squared norm of its subnormalised state as a
real weight.  Positionally aligned execution costs then define finite sums over
semantic branches and over an external finite input law.
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import VQ.Program.ExecutionCost
import VQMathlib.Probability.Expectation
import VQMathlib.Semantics.Normalize

namespace VQBridge
namespace ExpectedCost

open VQ VQ.Algebra VQ.Semantics VQMathlib.Probability

noncomputable section

/-- The real probability carried by one semantic branch. -/
def branchWeight (width : Nat) (branch : Branch d) : ℝ :=
  ∑ index ∈ Finset.range (2 ^ width), Complex.normSq (dtoC (branch.state index))

theorem branchWeight_nonneg (width : Nat) (branch : Branch d) :
    0 ≤ branchWeight width branch := by
  unfold branchWeight
  exact Finset.sum_nonneg fun index _ => Complex.normSq_nonneg (dtoC (branch.state index))

theorem dtoC_branchProb (hd : 0 < d) (width : Nat) (branch : Branch d) :
    dtoC (branchProb width branch) = (branchWeight width branch : ℂ) := by
  rw [branchProb, normSq, dtoC_dsum]
  unfold branchWeight
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  rw [absSq, dtoC_mul hd, dtoC_conj hd, mul_comm, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]

theorem dtoC_totalProb (hd : 0 < d) (width : Nat) (branches : List (Branch d)) :
    dtoC (totalProb width branches) =
      (((branches.map (branchWeight width)).sum : ℝ) : ℂ) := by
  induction branches with
  | nil => simp [totalProb, dtoC_zero]
  | cons branch rest ih =>
      rw [totalProb_cons, dtoC_add, dtoC_branchProb hd, List.map_cons, List.sum_cons, ih]
      push_cast
      rfl

theorem branchWeight_eq_half_of_branchProb (hd : 0 < d) (width : Nat)
    (branch : Branch d)
    (hprob : branchProb width branch = Dy.half (Dy.one d)) :
    branchWeight width branch = (1 : ℝ) / 2 := by
  have himage := dtoC_branchProb hd width branch
  rw [hprob, dtoC_half, dtoC_one hd] at himage
  exact Complex.ofReal_injective (by simpa using himage.symm)

theorem branchWeight_sum_runProgram (level : Nat) (program : Program)
    (hprogram : program.wellFormed level = true) (classicalInput basisInput : Nat)
    (hbasis : basisInput < 2 ^ program.width) :
    ((runProgram level program classicalInput (basis basisInput)).map
      (branchWeight program.width)).sum = 1 := by
  have hprob := totalProb_basis level program hprogram classicalInput hbasis
  have himage := congrArg dtoC hprob
  rw [dtoC_totalProb (deg_pos level), dtoC_one (deg_pos level)] at himage
  exact Complex.ofReal_injective (by simpa using himage)

/-- Semantic branches and their aligned execution costs for one basis input. -/
def costPairs (level : Nat) (program : Program) (classicalInput basisInput : Nat) :
    List (Branch (deg level) × CostedShape) :=
  pairRunOpsCosts level program.width program.ops
    (Branch.mk [] 0 (basis basisInput) classicalInput) 0

theorem costPairs_branches (level : Nat) (program : Program)
    (classicalInput basisInput : Nat) :
    (costPairs level program classicalInput basisInput).map Prod.fst =
      runProgram level program classicalInput (basis basisInput) := by
  simpa [costPairs, runProgram] using
    pairRunOpsCosts_branches level program.width program.ops
      (Branch.mk [] 0 (basis basisInput) classicalInput) 0

theorem costPairs_costs (level : Nat) (program : Program)
    (classicalInput basisInput : Nat) :
    (costPairs level program classicalInput basisInput).map Prod.snd =
      program.executionCosts classicalInput := by
  simpa [costPairs, Program.executionCosts] using
    pairRunOpsCosts_costs level program.width program.ops
      (Branch.mk [] 0 (basis basisInput) classicalInput) 0

theorem costPairs_weight_sum (level : Nat) (program : Program)
    (hprogram : program.wellFormed level = true) (classicalInput basisInput : Nat)
    (hbasis : basisInput < 2 ^ program.width) :
    ((costPairs level program classicalInput basisInput).map
      (fun pair => branchWeight program.width pair.1)).sum = 1 := by
  rw [show (costPairs level program classicalInput basisInput).map
      (fun pair => branchWeight program.width pair.1) =
      ((costPairs level program classicalInput basisInput).map Prod.fst).map
        (branchWeight program.width) by
    rw [List.map_map]
    rfl]
  rw [costPairs_branches]
  exact branchWeight_sum_runProgram level program hprogram classicalInput basisInput hbasis

theorem costPair_metric_le (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : Nat)
    {pair : Branch (deg level) × CostedShape}
    (hpair : pair ∈ costPairs level program classicalInput basisInput) :
    metric.value pair.2.cost ≤ (metric.opsRange program.ops).hi := by
  rw [costPairs, pairRunOpsCosts] at hpair
  have hcost : pair.2 ∈ opsExecutionCosts program.ops [] 0 classicalInput 0 :=
    (List.of_mem_zip hpair).2
  have hbound := (executionCostMetric_bounds metric).2 program.ops [] 0 classicalInput 0
    pair.2 hcost
  simpa only [metric.zero_value, Nat.zero_add] using hbound.2

theorem costPair_metric_eq_of_range_point (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (classicalInput basisInput value : Nat)
    (hrange : metric.opsRange program.ops = Range.point value)
    {pair : Branch (deg level) × CostedShape}
    (hpair : pair ∈ costPairs level program classicalInput basisInput) :
    metric.value pair.2.cost = value := by
  rw [costPairs, pairRunOpsCosts] at hpair
  have hcost : pair.2 ∈ opsExecutionCosts program.ops [] 0 classicalInput 0 :=
    (List.of_mem_zip hpair).2
  have hbound := (executionCostMetric_bounds metric).2 program.ops [] 0 classicalInput 0
    pair.2 hcost
  rw [metric.zero_value, Nat.zero_add, hrange] at hbound
  simp only [Range.point] at hbound
  have hlo : value ≤ metric.value pair.2.cost := by
    simpa using hbound.1
  have hhi : metric.value pair.2.cost ≤ value := by
    simpa using hbound.2
  exact Nat.le_antisymm hhi hlo

/-- Expected metric value over the semantic branches of one basis input. -/
def inputExpectation (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : Nat) : ℝ :=
  ((costPairs level program classicalInput basisInput).map fun pair =>
    branchWeight program.width pair.1 * (metric.value pair.2.cost : ℝ)).sum

/-- Probability that one basis input's execution cost meets a real threshold. -/
def inputTailWeight (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : Nat) (threshold : ℝ) : ℝ :=
  ((costPairs level program classicalInput basisInput).map fun pair =>
    if threshold ≤ metric.value pair.2.cost then branchWeight program.width pair.1 else 0).sum

private theorem sum_map_le_sum_map {α : Type*} (values : List α) (left right : α → ℝ)
    (hle : ∀ value ∈ values, left value ≤ right value) :
    (values.map left).sum ≤ (values.map right).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hle value (by simp))
        (ih (fun item hitem => hle item (by simp [hitem])))

private theorem weighted_sum_le_constant {α : Type*} (values : List α)
    (weight value : α → ℝ) (constant : ℝ)
    (hweight : ∀ item ∈ values, 0 ≤ weight item)
    (hvalue : ∀ item ∈ values, value item ≤ constant) :
    (values.map fun item => weight item * value item).sum ≤
      (values.map weight).sum * constant := by
  induction values with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hvalue item (by simp)) (hweight item (by simp)))
        (ih (fun value hmem => hweight value (by simp [hmem]))
          (fun value hmem => hvalue value (by simp [hmem])))

private theorem weighted_sum_eq_constant {α : Type*} (values : List α)
    (weight value : α → ℝ) (constant : ℝ)
    (hvalue : ∀ item ∈ values, value item = constant) :
    (values.map fun item => weight item * value item).sum =
      (values.map weight).sum * constant := by
  induction values with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      rw [hvalue item (by simp),
        ih (fun value hmem => hvalue value (by simp [hmem]))]

private theorem mul_sum_map {α : Type*} (constant : ℝ) (values : List α)
    (value : α → ℝ) :
    constant * (values.map value).sum =
      (values.map fun item => constant * value item).sum := by
  induction values with
  | nil => simp
  | cons item rest ih => simp [ih, mul_add]

theorem inputExpectation_nonneg (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : Nat) :
    0 ≤ inputExpectation metric level program classicalInput basisInput := by
  unfold inputExpectation
  apply List.sum_nonneg
  intro value hvalue
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hvalue
  exact mul_nonneg (branchWeight_nonneg program.width pair.1) (Nat.cast_nonneg _)

theorem inputExpectation_le_static (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput : Nat) (hbasis : basisInput < 2 ^ program.width) :
    inputExpectation metric level program classicalInput basisInput ≤
      (metric.opsRange program.ops).hi := by
  unfold inputExpectation
  calc
    ((costPairs level program classicalInput basisInput).map fun pair =>
        branchWeight program.width pair.1 * (metric.value pair.2.cost : ℝ)).sum ≤
        ((costPairs level program classicalInput basisInput).map fun pair =>
          branchWeight program.width pair.1).sum * (metric.opsRange program.ops).hi := by
      apply weighted_sum_le_constant
      · intro pair _
        exact branchWeight_nonneg program.width pair.1
      · intro pair hpair
        exact_mod_cast costPair_metric_le metric level program classicalInput basisInput hpair
    _ = (metric.opsRange program.ops).hi := by
      rw [costPairs_weight_sum level program hprogram classicalInput basisInput hbasis]
      simp

theorem inputExpectation_eq_of_range_point (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput value : Nat) (hbasis : basisInput < 2 ^ program.width)
    (hrange : metric.opsRange program.ops = Range.point value) :
    inputExpectation metric level program classicalInput basisInput = value := by
  unfold inputExpectation
  calc
    ((costPairs level program classicalInput basisInput).map fun pair =>
        branchWeight program.width pair.1 * (metric.value pair.2.cost : ℝ)).sum =
        ((costPairs level program classicalInput basisInput).map fun pair =>
          branchWeight program.width pair.1).sum * value := by
      apply weighted_sum_eq_constant
      intro pair hpair
      exact_mod_cast costPair_metric_eq_of_range_point metric level program classicalInput
        basisInput value hrange hpair
    _ = value := by
      rw [costPairs_weight_sum level program hprogram classicalInput basisInput hbasis]
      simp

theorem inputTailWeight_nonneg (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : Nat) (threshold : ℝ) :
    0 ≤ inputTailWeight metric level program classicalInput basisInput threshold := by
  unfold inputTailWeight
  apply List.sum_nonneg
  intro value hvalue
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hvalue
  split
  · exact branchWeight_nonneg program.width pair.1
  · exact le_rfl

theorem inputTailWeight_le_one (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput : Nat) (hbasis : basisInput < 2 ^ program.width)
    (threshold : ℝ) :
    inputTailWeight metric level program classicalInput basisInput threshold ≤ 1 := by
  unfold inputTailWeight
  calc
    ((costPairs level program classicalInput basisInput).map fun pair =>
        if threshold ≤ metric.value pair.2.cost then branchWeight program.width pair.1 else 0).sum ≤
        ((costPairs level program classicalInput basisInput).map fun pair =>
          branchWeight program.width pair.1).sum := by
      apply sum_map_le_sum_map
      intro pair _
      split
      · exact le_rfl
      · exact branchWeight_nonneg program.width pair.1
    _ = 1 := costPairs_weight_sum level program hprogram classicalInput basisInput hbasis

theorem threshold_mul_inputTailWeight_le_inputExpectation
    (metric : ExecutionCostMetric) (level : Nat) (program : Program)
    (classicalInput basisInput : Nat) (threshold : ℝ) :
    threshold * inputTailWeight metric level program classicalInput basisInput threshold ≤
      inputExpectation metric level program classicalInput basisInput := by
  unfold inputTailWeight inputExpectation
  rw [mul_sum_map]
  apply sum_map_le_sum_map
  intro pair _
  by_cases htail : threshold ≤ metric.value pair.2.cost
  · simp only [htail, if_true]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left htail
      (branchWeight_nonneg program.width pair.1)
  · simp only [htail, if_false, mul_zero]
    exact mul_nonneg (branchWeight_nonneg program.width pair.1) (Nat.cast_nonneg _)

variable {α : Type*} [Fintype α]

/-- Expected cost under the joint external-input and semantic-branch law. -/
def underLaw (law : FiniteLaw α) (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : α → Nat) : ℝ :=
  law.expectation fun input =>
    inputExpectation metric level program (classicalInput input) (basisInput input)

/-- Tail probability under the joint external-input and semantic-branch law. -/
def tailUnderLaw (law : FiniteLaw α) (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : α → Nat) (threshold : ℝ) : ℝ :=
  law.expectation fun input =>
    inputTailWeight metric level program (classicalInput input) (basisInput input) threshold

theorem underLaw_nonneg (law : FiniteLaw α) (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (classicalInput basisInput : α → Nat) :
    0 ≤ underLaw law metric level program classicalInput basisInput := by
  apply law.expectation_nonneg
  intro input
  exact inputExpectation_nonneg metric level program (classicalInput input) (basisInput input)

theorem underLaw_le_static (law : FiniteLaw α) (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput : α → Nat)
    (hbasis : ∀ input, basisInput input < 2 ^ program.width) :
    underLaw law metric level program classicalInput basisInput ≤
      (metric.opsRange program.ops).hi := by
  calc
    underLaw law metric level program classicalInput basisInput ≤
        law.expectation (fun _ => ((metric.opsRange program.ops).hi : ℝ)) := by
      apply law.expectation_mono
      intro input
      exact inputExpectation_le_static metric level program hprogram
        (classicalInput input) (basisInput input) (hbasis input)
    _ = (metric.opsRange program.ops).hi := law.expectation_const _

theorem underLaw_eq_of_range_point (law : FiniteLaw α) (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput : α → Nat) (value : Nat)
    (hbasis : ∀ input, basisInput input < 2 ^ program.width)
    (hrange : metric.opsRange program.ops = Range.point value) :
    underLaw law metric level program classicalInput basisInput = value := by
  unfold underLaw
  rw [show (fun input => inputExpectation metric level program
      (classicalInput input) (basisInput input)) = fun _ => (value : ℝ) by
    funext input
    exact inputExpectation_eq_of_range_point metric level program hprogram
      (classicalInput input) (basisInput input) value (hbasis input) hrange]
  exact law.expectation_const value

theorem tailUnderLaw_nonneg (law : FiniteLaw α) (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (classicalInput basisInput : α → Nat)
    (threshold : ℝ) :
    0 ≤ tailUnderLaw law metric level program classicalInput basisInput threshold := by
  apply law.expectation_nonneg
  intro input
  exact inputTailWeight_nonneg metric level program
    (classicalInput input) (basisInput input) threshold

theorem tailUnderLaw_le_one (law : FiniteLaw α) (metric : ExecutionCostMetric)
    (level : Nat) (program : Program) (hprogram : program.wellFormed level = true)
    (classicalInput basisInput : α → Nat)
    (hbasis : ∀ input, basisInput input < 2 ^ program.width) (threshold : ℝ) :
    tailUnderLaw law metric level program classicalInput basisInput threshold ≤ 1 := by
  calc
    tailUnderLaw law metric level program classicalInput basisInput threshold ≤
        law.expectation (fun _ => (1 : ℝ)) := by
      apply law.expectation_mono
      intro input
      exact inputTailWeight_le_one metric level program hprogram
        (classicalInput input) (basisInput input) (hbasis input) threshold
    _ = 1 := law.expectation_const 1

theorem threshold_mul_tailUnderLaw_le_underLaw
    (law : FiniteLaw α) (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : α → Nat) (threshold : ℝ) :
    threshold * tailUnderLaw law metric level program classicalInput basisInput threshold ≤
      underLaw law metric level program classicalInput basisInput := by
  unfold tailUnderLaw underLaw FiniteLaw.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro input _
  calc
    threshold *
        (law.mass input * inputTailWeight metric level program
          (classicalInput input) (basisInput input) threshold) =
        law.mass input *
          (threshold * inputTailWeight metric level program
            (classicalInput input) (basisInput input) threshold) := by ring
    _ ≤ law.mass input *
        inputExpectation metric level program
          (classicalInput input) (basisInput input) :=
      mul_le_mul_of_nonneg_left
        (threshold_mul_inputTailWeight_le_inputExpectation metric level program
          (classicalInput input) (basisInput input) threshold)
        (law.mass_nonneg input)

theorem tailUnderLaw_le_underLaw_div
    (law : FiniteLaw α) (metric : ExecutionCostMetric) (level : Nat)
    (program : Program) (classicalInput basisInput : α → Nat) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    tailUnderLaw law metric level program classicalInput basisInput threshold ≤
      underLaw law metric level program classicalInput basisInput / threshold := by
  apply (le_div_iff₀ hthreshold).2
  simpa [mul_comm] using threshold_mul_tailUnderLaw_le_underLaw law metric level program
    classicalInput basisInput threshold

end
end ExpectedCost
end VQBridge
