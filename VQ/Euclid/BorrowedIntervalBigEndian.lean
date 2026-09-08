import VQ.Euclid.BorrowedInterval
import VQ.Euclid.IntervalBigEndianNoSign
import VQ.Reversible.BorrowedEquivalence

namespace VQ.Euclid.BorrowedIntervalBigEndian

open Reversible Interval

def firstScan (workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | top, count + 1 =>
      rightToggle (top - 1) workWidth endpointWidth ++
      BorrowedInterval.cellAt false (top - 1) workWidth endpointWidth ++
      leftToggle (top - 1) workWidth endpointWidth ++
      firstScan workWidth endpointWidth (top - 1) count

def secondScan (workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, count + 1 =>
      leftToggle j workWidth endpointWidth ++
      BorrowedInterval.cellAt true j workWidth endpointWidth ++
      rightToggle j workWidth endpointWidth ++
      secondScan workWidth endpointWidth (j + 1) count

def gates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth workWidth workWidth ++
    [.cx (carryWire workWidth endpointWidth) (signWire workWidth endpointWidth)] ++
  secondScan workWidth endpointWidth 0 workWidth

def noSignGates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth workWidth workWidth ++
    secondScan workWidth endpointWidth 0 workWidth

private theorem left_equiv (j workWidth endpointWidth : Nat) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (leftToggle j workWidth endpointWidth) (leftToggle j workWidth endpointWidth) :=
  BorrowedEquivalent.of_below (fun g hg _ hq => wire_lt_of_wellFormed
    (List.all_eq_true.mp (BorrowedInterval.endpoint_below (Or.inl rfl) (Or.inl rfl)) g hg) hq)

private theorem right_equiv (j workWidth endpointWidth : Nat) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (rightToggle j workWidth endpointWidth) (rightToggle j workWidth endpointWidth) :=
  BorrowedEquivalent.of_below (fun g hg _ hq => wire_lt_of_wellFormed
    (List.all_eq_true.mp (BorrowedInterval.endpoint_below (Or.inr rfl) (Or.inr rfl)) g hg) hq)

private theorem cell_equiv (backward : Bool) {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (if backward then umaAt j workWidth endpointWidth else majAt j workWidth endpointWidth)
      (BorrowedInterval.cellAt backward j workWidth endpointWidth) :=
  ⟨fun _ => BorrowedInterval.cellAt_clear backward hj,
    fun _ => BorrowedInterval.cellAt_preserves_borrowed backward hj⟩

theorem firstScan_equiv (workWidth endpointWidth : Nat) : ∀ count top,
    count ≤ top → top ≤ workWidth →
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (IntervalBigEndian.firstScan workWidth endpointWidth top count)
      (firstScan workWidth endpointWidth top count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro top ht hw
    exact (((right_equiv _ _ _).append (cell_equiv false (by omega))).append
      (left_equiv _ _ _)).append (ih _ (by omega) (by omega))

theorem secondScan_equiv (workWidth endpointWidth : Nat) : ∀ count j,
    j + count ≤ workWidth →
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (IntervalBigEndian.secondScan workWidth endpointWidth j count)
      (secondScan workWidth endpointWidth j count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro j hj
    exact (((left_equiv _ _ _).append (cell_equiv true (by omega))).append
      (right_equiv _ _ _)).append (ih _ (by omega))

private theorem sign_below (workWidth endpointWidth : Nat) :
    ([RGate.cx (carryWire workWidth endpointWidth) (signWire workWidth endpointWidth)]).all
      (RGate.wellFormed (cellScratchWire workWidth endpointWidth)) = true := by
  simp [RGate.wellFormed, carryWire, signWire, cellScratchWire, selectorScratchOffset]
  omega

theorem gates_equiv (workWidth endpointWidth : Nat) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (IntervalBigEndian.gates workWidth endpointWidth) (gates workWidth endpointWidth) := by
  have hs := BorrowedEquivalent.of_below (fun g hg _ hq => wire_lt_of_wellFormed
    (List.all_eq_true.mp (sign_below workWidth endpointWidth) g hg) hq)
  exact ((firstScan_equiv workWidth endpointWidth _ _ (by omega) (by omega)).append hs).append
    (secondScan_equiv workWidth endpointWidth _ _ (by omega))

theorem noSignGates_equiv (workWidth endpointWidth : Nat) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (IntervalBigEndian.noSignGates workWidth endpointWidth) (noSignGates workWidth endpointWidth) :=
  (firstScan_equiv workWidth endpointWidth _ _ (by omega) (by omega)).append
    (secondScan_equiv workWidth endpointWidth _ _ (by omega))

theorem firstScan_wellFormed (workWidth endpointWidth : Nat) : ∀ count top,
    count ≤ top → top ≤ workWidth →
    (firstScan workWidth endpointWidth top count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro top ht hw
    simp only [firstScan, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl),
      BorrowedInterval.cellAt_wellFormed false (by omega)⟩,
      endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)⟩, ih _ (by omega) (by omega)⟩

theorem secondScan_wellFormed (workWidth endpointWidth : Nat) : ∀ count j,
    j + count ≤ workWidth →
    (secondScan workWidth endpointWidth j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro j hj
    simp only [secondScan, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl),
      BorrowedInterval.cellAt_wellFormed true (by omega)⟩,
      endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl)⟩, ih _ (by omega)⟩

theorem gates_wellFormed (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨firstScan_wellFormed workWidth endpointWidth _ _ (by omega) (by omega), ?_⟩,
    secondScan_wellFormed workWidth endpointWidth _ _ (by omega)⟩
  simp [RGate.wellFormed, layout_width, carryWire, signWire, outerWire]
  omega

theorem noSignGates_wellFormed (workWidth endpointWidth : Nat) :
    (noSignGates workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  simp only [noSignGates, List.all_append, Bool.and_eq_true]
  exact ⟨firstScan_wellFormed workWidth endpointWidth _ _ (by omega) (by omega),
    secondScan_wellFormed workWidth endpointWidth _ _ (by omega)⟩

theorem gates_reverse_equiv (workWidth endpointWidth : Nat) :
    BorrowedEquivalent (cellScratchWire workWidth endpointWidth)
      (IntervalBigEndian.gates workWidth endpointWidth).reverse
      (gates workWidth endpointWidth).reverse :=
  (gates_equiv workWidth endpointWidth).reverse
    (IntervalBigEndian.circuit_wellFormed workWidth endpointWidth)
    (gates_wellFormed workWidth endpointWidth)

theorem firstScan_ccx (workWidth endpointWidth : Nat) : ∀ count top,
    (firstScan workWidth endpointWidth top count).countP RGate.isCcx =
      (IntervalBigEndian.firstScan workWidth endpointWidth top count).countP RGate.isCcx + count := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro top
    simp only [firstScan, IntervalBigEndian.firstScan, List.countP_append,
      BorrowedInterval.cellAt_ccx, ih, Bool.false_eq_true, ↓reduceIte]
    omega

theorem secondScan_ccx (workWidth endpointWidth : Nat) : ∀ count j,
    (secondScan workWidth endpointWidth j count).countP RGate.isCcx =
      (IntervalBigEndian.secondScan workWidth endpointWidth j count).countP RGate.isCcx + count := by
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro j
    simp only [secondScan, IntervalBigEndian.secondScan, List.countP_append,
      BorrowedInterval.cellAt_ccx, ih, ↓reduceIte]
    omega

theorem gates_ccx (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx =
      (IntervalBigEndian.gates workWidth endpointWidth).countP RGate.isCcx + 2 * workWidth := by
  simp only [gates, IntervalBigEndian.gates, List.countP_append, firstScan_ccx, secondScan_ccx]
  omega

theorem noSignGates_ccx (workWidth endpointWidth : Nat) :
    (noSignGates workWidth endpointWidth).countP RGate.isCcx =
      (IntervalBigEndian.noSignGates workWidth endpointWidth).countP RGate.isCcx + 2 * workWidth := by
  simp only [noSignGates, IntervalBigEndian.noSignGates, List.countP_append, firstScan_ccx, secondScan_ccx]
  omega

end VQ.Euclid.BorrowedIntervalBigEndian
