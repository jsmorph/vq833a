import VQMathlib.Probability.FiniteLaw
import Mathlib.Data.List.OfFn

namespace VQMathlib.Probability

open scoped BigOperators

noncomputable section

namespace FiniteLaw

/-- The event that every coordinate satisfies its assigned event. -/
def allEvent {ι : Type*} [Fintype ι] {α : ι → Type*}
    (events : ∀ index, α index → Bool)
    (outcome : ∀ index, α index) : Bool :=
  decide (∀ index, events index (outcome index) = true)

theorem allEvent_eq_true_iff {ι : Type*} [Fintype ι] {α : ι → Type*}
    (events : ∀ index, α index → Bool)
    (outcome : ∀ index, α index) :
    allEvent events outcome = true ↔
      ∀ index, events index (outcome index) = true := by
  simp [allEvent]

theorem eventWeight_product_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ index, Fintype (α index)]
    (laws : ∀ index, FiniteLaw (α index))
    (events : ∀ index, α index → Bool) :
    (product laws).eventWeight (allEvent events) =
      ∏ index, (laws index).eventWeight (events index) := by
  classical
  change
    (∑ outcome, if allEvent events outcome = true then
        ∏ index, (laws index).mass (outcome index) else 0) =
      ∏ index, ∑ value,
        if events index value = true then (laws index).mass value else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hall : ∀ index, events index (outcome index) = true
  · rw [if_pos ((allEvent_eq_true_iff events outcome).2 hall)]
    apply Finset.prod_congr rfl
    intro index _
    rw [if_pos (hall index)]
  · obtain ⟨index, hindex⟩ := not_forall.mp hall
    have hnotAll : allEvent events outcome ≠ true := by
      intro htrue
      exact hall ((allEvent_eq_true_iff events outcome).1 htrue)
    rw [if_neg hnotAll]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    rw [if_neg hindex]

section Repetition

variable {α : Type*} [Fintype α]

/-- Independent, identically distributed repetition of one finite law. -/
def iid (law : FiniteLaw α) (runs : Nat) :
    FiniteLaw (Fin runs → α) :=
  product fun _ => law

@[simp]
theorem iid_mass (law : FiniteLaw α) (runs : Nat)
    (outcome : Fin runs → α) :
    (law.iid runs).mass outcome =
      ∏ index, law.mass (outcome index) := rfl

/-- The event that at least one repeated coordinate satisfies `event`. -/
def anyEvent (event : α → Bool) {runs : Nat}
    (outcome : Fin runs → α) : Bool :=
  !allEvent (fun _ value => !event value) outcome

omit [Fintype α] in
theorem anyEvent_eq_true_iff (event : α → Bool) {runs : Nat}
    (outcome : Fin runs → α) :
    anyEvent event outcome = true ↔
      ∃ index, event (outcome index) = true := by
  classical
  simp [anyEvent, allEvent]

/-- Exact success mass for independent repeated trials. -/
theorem eventWeight_anyEvent_iid (law : FiniteLaw α)
    (event : α → Bool) (runs : Nat) :
    (law.iid runs).eventWeight (anyEvent event) =
      1 - (1 - law.eventWeight event) ^ runs := by
  let failure : (Fin runs → α) → Bool :=
    allEvent (fun _ value => !event value)
  calc
    (law.iid runs).eventWeight (anyEvent event) =
        1 - (law.iid runs).eventWeight failure := by
      change
        (law.iid runs).eventWeight (fun outcome => !failure outcome) =
          1 - (law.iid runs).eventWeight failure
      exact (law.iid runs).eventWeight_complement failure
    _ = 1 - ∏ _index : Fin runs,
          law.eventWeight (fun value => !event value) := by
      dsimp [iid, failure]
      rw [eventWeight_product_all]
    _ = 1 - (1 - law.eventWeight event) ^ runs := by
      simp [law.eventWeight_complement event]

end Repetition

section FirstAccepted

variable {α β : Type*}

/-- Return the first selected output in list order. -/
def firstAcceptedOutput (select : α → Option β) : List α → Option β
  | [] => none
  | input :: inputs =>
      match select input with
      | some output => some output
      | none => firstAcceptedOutput select inputs

@[simp]
theorem firstAcceptedOutput_nil (select : α → Option β) :
    firstAcceptedOutput select [] = none := rfl

@[simp]
theorem firstAcceptedOutput_cons (select : α → Option β)
    (input : α) (inputs : List α) :
    firstAcceptedOutput select (input :: inputs) =
      match select input with
      | some output => some output
      | none => firstAcceptedOutput select inputs := rfl

theorem firstAcceptedOutput_sound (select : α → Option β)
    (good : β → Prop)
    (hselect : ∀ input output, select input = some output → good output)
    {inputs : List α} {output : β}
    (houtput : firstAcceptedOutput select inputs = some output) :
    good output := by
  induction inputs with
  | nil => simp at houtput
  | cons input inputs ih =>
      cases hselected : select input with
      | none =>
          exact ih (by simpa [firstAcceptedOutput, hselected] using houtput)
      | some selected =>
          have heq : selected = output := by
            simpa [firstAcceptedOutput, hselected] using houtput
          subst selected
          exact hselect input output hselected

/-- Apply first-accepted selection to a fixed number of runs. -/
def firstAcceptedFromRuns (select : α → Option β) {runs : Nat}
    (outcome : Fin runs → α) : Option β :=
  firstAcceptedOutput select (List.ofFn outcome)

theorem firstAcceptedFromRuns_sound (select : α → Option β)
    (good : β → Prop)
    (hselect : ∀ input output, select input = some output → good output)
    {runs : Nat} {outcome : Fin runs → α} {output : β}
    (houtput : firstAcceptedFromRuns select outcome = some output) :
    good output := by
  exact firstAcceptedOutput_sound select good hselect houtput

end FirstAccepted

end FiniteLaw

end

end VQMathlib.Probability
