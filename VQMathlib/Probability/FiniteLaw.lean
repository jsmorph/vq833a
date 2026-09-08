import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

namespace VQMathlib.Probability

open scoped BigOperators

noncomputable section

/-- An exact real-valued probability law on a finite type. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ outcome, 0 ≤ mass outcome
  mass_sum : ∑ outcome, mass outcome = 1

namespace FiniteLaw

variable {α : Type*} [Fintype α]

@[ext]
theorem ext {left right : FiniteLaw α} (h : left.mass = right.mass) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Construct a finite law from a mass function and its two law proofs. -/
def ofMass (mass : α → ℝ) (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1) : FiniteLaw α :=
  ⟨mass, mass_nonneg, mass_sum⟩

@[simp]
theorem ofMass_mass (mass : α → ℝ)
    (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1) (outcome : α) :
    (ofMass mass mass_nonneg mass_sum).mass outcome = mass outcome := rfl

/-- Construct a real-valued finite law from exact rational masses. -/
def ofRatMass (mass : α → ℚ) (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1) : FiniteLaw α where
  mass outcome := (mass outcome : ℝ)
  mass_nonneg outcome := Rat.cast_nonneg.mpr (mass_nonneg outcome)
  mass_sum := by
    simpa only [Rat.cast_sum, Rat.cast_one] using
      congrArg (fun value : ℚ => (value : ℝ)) mass_sum

@[simp]
theorem ofRatMass_mass (mass : α → ℚ)
    (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1) (outcome : α) :
    (ofRatMass mass mass_nonneg mass_sum).mass outcome =
      (mass outcome : ℝ) := rfl

/-- The uniform law on a nonempty finite index type. -/
def uniformFin (n : Nat) [NeZero n] : FiniteLaw (Fin n) :=
  ofRatMass (fun _ => 1 / (n : ℚ))
    (fun _ => div_nonneg zero_le_one (Nat.cast_nonneg n))
    (by
      have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      simp [hn])

@[simp]
theorem uniformFin_mass (n : Nat) [NeZero n] (outcome : Fin n) :
    (uniformFin n).mass outcome = ((1 / (n : ℚ) : ℚ) : ℝ) := rfl

/-- The total mass of a Boolean event. -/
def eventWeight (law : FiniteLaw α) (event : α → Bool) : ℝ :=
  ∑ outcome, if event outcome then law.mass outcome else 0

theorem eventWeight_ofRatMass (mass : α → ℚ)
    (mass_nonneg : ∀ outcome, 0 ≤ mass outcome)
    (mass_sum : ∑ outcome, mass outcome = 1) (event : α → Bool) :
    (ofRatMass mass mass_nonneg mass_sum).eventWeight event =
      ((∑ outcome, if event outcome then mass outcome else 0 : ℚ) : ℝ) := by
  unfold eventWeight
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  cases event outcome <;> simp

/-- A Boolean event represented as a finite set. -/
def eventFinset [DecidableEq α]
    (event : α → Bool) : Finset α :=
  Finset.univ.filter fun outcome => event outcome = true

/-- A finite set represented as a Boolean event. -/
def finsetEvent [DecidableEq α] (event : Finset α) (outcome : α) : Bool :=
  decide (outcome ∈ event)

/-- The mass assigned to a finite set. -/
def finsetWeight [DecidableEq α]
    (law : FiniteLaw α) (event : Finset α) : ℝ :=
  ∑ outcome ∈ event, law.mass outcome

@[simp]
theorem mem_eventFinset [DecidableEq α] (event : α → Bool) (outcome : α) :
    outcome ∈ eventFinset event ↔ event outcome = true := by
  simp [eventFinset]

@[simp]
theorem finsetEvent_eventFinset [DecidableEq α] (event : α → Bool) :
    finsetEvent (eventFinset event) = event := by
  funext outcome
  cases h : event outcome <;> simp [finsetEvent, h]

@[simp]
theorem eventWeight_finsetEvent [DecidableEq α]
    (law : FiniteLaw α) (event : Finset α) :
    law.eventWeight (finsetEvent event) = law.finsetWeight event := by
  classical
  simp [eventWeight, finsetEvent, finsetWeight]

theorem eventWeight_eq_finsetWeight_eventFinset [DecidableEq α]
    (law : FiniteLaw α) (event : α → Bool) :
    law.eventWeight event = law.finsetWeight (eventFinset event) := by
  rw [← eventWeight_finsetEvent, finsetEvent_eventFinset]

theorem uniformFin_eventWeight (n : Nat) [NeZero n]
    (event : Fin n → Bool) :
    (uniformFin n).eventWeight event =
      (eventFinset event).card / (n : ℝ) := by
  rw [eventWeight_eq_finsetWeight_eventFinset]
  unfold finsetWeight
  simp only [uniformFin_mass, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  simp [div_eq_mul_inv]

theorem eventWeight_eq_indicator_sum (law : FiniteLaw α)
    (event : α → Bool) :
    law.eventWeight event =
      ∑ outcome, law.mass outcome * if event outcome then 1 else 0 := by
  unfold eventWeight
  apply Finset.sum_congr rfl
  intro outcome _
  cases event outcome <;> simp

@[simp]
theorem eventWeight_false (law : FiniteLaw α) :
    law.eventWeight (fun _ => false) = 0 := by
  simp [eventWeight]

@[simp]
theorem eventWeight_true (law : FiniteLaw α) :
    law.eventWeight (fun _ => true) = 1 := by
  simpa [eventWeight] using law.mass_sum

theorem eventWeight_nonneg (law : FiniteLaw α) (event : α → Bool) :
    0 ≤ law.eventWeight event := by
  unfold eventWeight
  apply Finset.sum_nonneg
  intro outcome _
  cases event outcome <;> simp [law.mass_nonneg]

theorem eventWeight_add_complement (law : FiniteLaw α)
    (event : α → Bool) :
    law.eventWeight event + law.eventWeight (fun outcome => !event outcome) = 1 := by
  rw [eventWeight, eventWeight, ← Finset.sum_add_distrib]
  calc
    (∑ outcome,
        ((if event outcome then law.mass outcome else 0) +
          if !event outcome then law.mass outcome else 0)) =
        ∑ outcome, law.mass outcome := by
      apply Finset.sum_congr rfl
      intro outcome _
      cases event outcome <;> simp
    _ = 1 := law.mass_sum

theorem eventWeight_complement (law : FiniteLaw α) (event : α → Bool) :
    law.eventWeight (fun outcome => !event outcome) =
      1 - law.eventWeight event := by
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using law.eventWeight_add_complement event

theorem eventWeight_le_one (law : FiniteLaw α) (event : α → Bool) :
    law.eventWeight event ≤ 1 := by
  have h := law.eventWeight_nonneg (fun outcome => !event outcome)
  rw [law.eventWeight_complement event] at h
  exact sub_nonneg.mp h

theorem eventWeight_mono (law : FiniteLaw α)
    {left right : α → Bool}
    (hsub : ∀ outcome, left outcome = true → right outcome = true) :
    law.eventWeight left ≤ law.eventWeight right := by
  unfold eventWeight
  apply Finset.sum_le_sum
  intro outcome _
  cases hleft : left outcome with
  | false =>
      cases right outcome <;> simp [law.mass_nonneg]
  | true =>
      have hright : right outcome = true := hsub outcome hleft
      simp [hright]

theorem eventWeight_or_le (law : FiniteLaw α)
    (left right : α → Bool) :
    law.eventWeight (fun outcome => left outcome || right outcome) ≤
      law.eventWeight left + law.eventWeight right := by
  unfold eventWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro outcome _
  cases hleft : left outcome <;> cases hright : right outcome <;>
    simp [hleft, hright, law.mass_nonneg]

/-- The image law formed by summing the masses in each fiber. -/
def pushforward {β : Type*} [Fintype β] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β) : FiniteLaw β := by
  exact
    { mass := fun target =>
        ∑ source, if f source = target then law.mass source else 0
      mass_nonneg := fun target => by
        apply Finset.sum_nonneg
        intro source _
        split <;> simp [law.mass_nonneg]
      mass_sum := by
        rw [Finset.sum_comm]
        simpa using law.mass_sum }

theorem pushforward_mass {β : Type*} [Fintype β] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β) (target : β) :
    (law.pushforward f).mass target =
      ∑ source, if f source = target then law.mass source else 0 := rfl

theorem pushforward_weighted_sum {β : Type*} [Fintype β] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β) (value : β → ℝ) :
    (∑ target, (law.pushforward f).mass target * value target) =
      ∑ source, law.mass source * value (f source) := by
  simp only [pushforward_mass]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp

theorem eventWeight_pushforward {β : Type*} [Fintype β] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β) (event : β → Bool) :
    (law.pushforward f).eventWeight event =
      law.eventWeight (fun source => event (f source)) := by
  rw [eventWeight_eq_indicator_sum, eventWeight_eq_indicator_sum,
    pushforward_weighted_sum]

@[simp]
theorem pushforward_id [DecidableEq α] (law : FiniteLaw α) :
    law.pushforward id = law := by
  apply FiniteLaw.ext
  funext target
  rw [pushforward_mass, Finset.sum_eq_single target
    (fun source _ hne => by simp [hne]) (by simp)]
  simp

/-- The empirical law of an indexed nonempty sample. -/
def empirical {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) : FiniteLaw β :=
  (uniformFin n).pushforward sample

@[simp]
theorem empirical_mass {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) (target : β) :
    (empirical sample).mass target =
      (Finset.univ.filter (fun index => sample index = target)).card / (n : ℝ) := by
  rw [empirical, pushforward_mass]
  simp only [uniformFin_mass, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem empirical_eventWeight {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) (event : β → Bool) :
    (empirical sample).eventWeight event =
      (uniformFin n).eventWeight (fun index => event (sample index)) :=
  eventWeight_pushforward (uniformFin n) sample event

theorem empirical_eventWeight_eq_card {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} [NeZero n] (sample : Fin n → β) (event : β → Bool) :
    (empirical sample).eventWeight event =
      (Finset.univ.filter fun index => event (sample index) = true).card /
        (n : ℝ) := by
  rw [empirical_eventWeight, uniformFin_eventWeight]
  rfl

/-- The independent product of a finite family of finite laws. -/
def product {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ index, Fintype (β index)]
    (laws : ∀ index, FiniteLaw (β index)) :
    FiniteLaw (∀ index, β index) where
  mass outcome := ∏ index, (laws index).mass (outcome index)
  mass_nonneg outcome := by
    exact Finset.prod_nonneg fun index _ =>
      (laws index).mass_nonneg (outcome index)
  mass_sum := by
    classical
    rw [← Fintype.prod_sum]
    simp only [(laws _).mass_sum]
    simp

@[simp]
theorem product_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*}
    [∀ index, Fintype (β index)]
    (laws : ∀ index, FiniteLaw (β index))
    (outcome : ∀ index, β index) :
    (product laws).mass outcome =
      ∏ index, (laws index).mass (outcome index) := rfl

end FiniteLaw

end

end VQMathlib.Probability
