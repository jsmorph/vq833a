import VQ.Euclid.BorrowedRangeZero
import VQ.Euclid.BorrowedInterval
import VQ.Reversible.BorrowedEquivalence

namespace VQ.Euclid.BorrowedRangeScan

open Reversible RangeZero

def upperRelation (j workWidth endpointWidth : Nat) : List RGate :=
  BorrowedRangeZero.maskedNotAnd (accumulatorWire workWidth endpointWidth)
    (sourceWire j) (temporaryWire workWidth endpointWidth)
    (dirtyWire workWidth (j + 1)) (dirtyWire workWidth j)

def upperBase (j workWidth endpointWidth : Nat) : List RGate :=
  BorrowedRangeZero.maskedNotBit (accumulatorWire workWidth endpointWidth)
    (sourceWire j) (dirtyWire workWidth j)

def lowerRelation (j workWidth endpointWidth : Nat) : List RGate :=
  BorrowedRangeZero.maskedNotAnd (accumulatorWire workWidth endpointWidth)
    (sourceWire j) (temporaryWire workWidth endpointWidth)
    (dirtyWire workWidth (j - 1)) (dirtyWire workWidth j)

def upperForward (workWidth endpointWidth : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | label, j, 1 => upperBase j workWidth endpointWidth ++ endpointToggle label workWidth endpointWidth
  | label, j, count + 2 => upperRelation j workWidth endpointWidth ++
      endpointToggle label workWidth endpointWidth ++
      upperForward workWidth endpointWidth (label + 1) (j + 1) (count + 1)

def upperReverseEdges (workWidth endpointWidth : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | label, j, count + 1 => endpointToggle (label - 1) workWidth endpointWidth ++
      upperRelation (j - 1) workWidth endpointWidth ++
      upperReverseEdges workWidth endpointWidth (label - 1) (j - 1) count

def lowerForward (workWidth endpointWidth : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | label, j, 1 => upperBase j workWidth endpointWidth ++ endpointToggle label workWidth endpointWidth
  | label, j, count + 2 => lowerRelation (j + count + 1) workWidth endpointWidth ++
      endpointToggle (label + count + 1) workWidth endpointWidth ++
      lowerForward workWidth endpointWidth label j (count + 1)

def lowerReverse (workWidth endpointWidth : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | _, _, 1 => []
  | label, j, count + 2 => lowerReverse workWidth endpointWidth label j (count + 1) ++
      endpointToggle (label + count + 1) workWidth endpointWidth ++
      lowerRelation (j + count + 1) workWidth endpointWidth

def upperGates (start : Nat) : Nat → Nat → List RGate
  | 0, _ => []
  | count + 1, endpointWidth =>
      [.cx (controlWire (count + 1) endpointWidth) (accumulatorWire (count + 1) endpointWidth)] ++
      upperForward (count + 1) endpointWidth start 0 (count + 1) ++
      endpointToggle (start + count) (count + 1) endpointWidth ++
      upperReverseEdges (count + 1) endpointWidth (start + count) count count ++
      [.cx (controlWire (count + 1) endpointWidth) (accumulatorWire (count + 1) endpointWidth)]

def lowerGates (start : Nat) : Nat → Nat → List RGate
  | 0, _ => []
  | count + 1, endpointWidth =>
      [.cx (controlWire (count + 1) endpointWidth) (accumulatorWire (count + 1) endpointWidth)] ++
      lowerForward (count + 1) endpointWidth start 0 (count + 1) ++
      endpointToggle start (count + 1) endpointWidth ++
      lowerReverse (count + 1) endpointWidth start 0 (count + 1) ++
      [.cx (controlWire (count + 1) endpointWidth) (accumulatorWire (count + 1) endpointWidth)]

theorem upperRelation_equiv {j workWidth endpointWidth : Nat} (hj : j + 1 < workWidth) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperRelation j workWidth endpointWidth) (upperRelation j workWidth endpointWidth) := by
  constructor <;> intro I
  · apply BorrowedRangeZero.maskedNotAnd_clear <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega
  · apply BorrowedRangeZero.maskedNotAnd_preserves_borrowed <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega

theorem upperBase_equiv {j workWidth endpointWidth : Nat} (hj : j < workWidth) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperBase j workWidth endpointWidth) (upperBase j workWidth endpointWidth) := by
  constructor <;> intro I
  · apply BorrowedRangeZero.maskedNotBit_clear <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega
  · apply BorrowedRangeZero.maskedNotBit_preserves_borrowed <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega

theorem lowerRelation_equiv {j workWidth endpointWidth : Nat}
    (hp : 0 < j) (hj : j < workWidth) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.lowerRelation j workWidth endpointWidth) (lowerRelation j workWidth endpointWidth) := by
  constructor <;> intro I
  · apply BorrowedRangeZero.maskedNotAnd_clear <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega
  · apply BorrowedRangeZero.maskedNotAnd_preserves_borrowed <;>
      simp [sourceWire, dirtyWire, temporaryWire, accumulatorWire,
        Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset,
        Interval.outerWire] <;> omega

theorem endpoint_equiv (label workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (endpointToggle label workWidth endpointWidth) (endpointToggle label workWidth endpointWidth) := by
  apply BorrowedEquivalent.of_below
  intro g hg q hq
  exact wire_lt_of_wellFormed (List.all_eq_true.mp
    (BorrowedInterval.endpoint_below (Or.inl rfl) (Or.inl rfl)) g hg) hq

theorem toggle_equiv (workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      [.cx (controlWire workWidth endpointWidth) (accumulatorWire workWidth endpointWidth)]
      [.cx (controlWire workWidth endpointWidth) (accumulatorWire workWidth endpointWidth)] := by
  apply BorrowedEquivalent.of_below
  intro g hg q hq
  simp only [List.mem_singleton] at hg
  subst g
  simp [RGate.wires] at hq
  rcases hq with rfl | rfl <;>
    simp [controlWire, temporaryWire, accumulatorWire,
      Interval.cellScratchWire, Interval.accumulatorWire, Interval.selectorScratchOffset]
  all_goals omega

theorem upperForward_equiv (workWidth endpointWidth : Nat) : ∀ count label j,
    j + count ≤ workWidth →
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperForward workWidth endpointWidth label j count)
      (upperForward workWidth endpointWidth label j count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro label j hj
    cases count with
    | zero => exact (upperBase_equiv (by omega)).append (endpoint_equiv label workWidth endpointWidth)
    | succ count =>
      exact ((upperRelation_equiv (by omega)).append (endpoint_equiv label workWidth endpointWidth)).append
        (ih (label + 1) (j + 1) (by omega))

theorem upperReverseEdges_equiv (workWidth endpointWidth : Nat) : ∀ count label j,
    count ≤ j → j < workWidth →
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperReverseEdges workWidth endpointWidth label j count)
      (upperReverseEdges workWidth endpointWidth label j count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro label j hc hj
    exact ((endpoint_equiv (label - 1) workWidth endpointWidth).append
      (upperRelation_equiv (by omega))).append
      (ih (label - 1) (j - 1) (by omega) (by omega))

theorem lowerForward_equiv (workWidth endpointWidth : Nat) : ∀ count label j,
    j + count ≤ workWidth →
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.lowerForward workWidth endpointWidth label j count)
      (lowerForward workWidth endpointWidth label j count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro label j hj
    cases count with
    | zero => exact (upperBase_equiv (by omega)).append (endpoint_equiv label workWidth endpointWidth)
    | succ count =>
      exact ((lowerRelation_equiv (by omega) (by omega)).append
        (endpoint_equiv (label + count + 1) workWidth endpointWidth)).append
        (ih label j (by omega))

theorem lowerReverse_equiv (workWidth endpointWidth : Nat) : ∀ count label j,
    j + count ≤ workWidth →
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.lowerReverse workWidth endpointWidth label j count)
      (lowerReverse workWidth endpointWidth label j count) := by
  intro count
  induction count with
  | zero => intros; exact BorrowedEquivalent.nil _
  | succ count ih =>
    intro label j hj
    cases count with
    | zero => exact BorrowedEquivalent.nil _
    | succ count =>
      exact ((ih label j (by omega)).append
        (endpoint_equiv (label + count + 1) workWidth endpointWidth)).append
        (lowerRelation_equiv (by omega) (by omega))

theorem upperGates_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.upperGates start workWidth endpointWidth) (upperGates start workWidth endpointWidth) := by
  cases workWidth with
  | zero => exact BorrowedEquivalent.nil _
  | succ count =>
    exact ((((toggle_equiv _ _).append (upperForward_equiv _ _ _ _ _ (by omega))).append
      (endpoint_equiv _ _ _)).append (upperReverseEdges_equiv _ _ _ _ _ (by omega) (by omega))).append
      (toggle_equiv _ _)

theorem lowerGates_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (temporaryWire workWidth endpointWidth)
      (RangeZero.lowerGates start workWidth endpointWidth) (lowerGates start workWidth endpointWidth) := by
  cases workWidth with
  | zero => exact BorrowedEquivalent.nil _
  | succ count =>
    exact ((((toggle_equiv _ _).append (lowerForward_equiv _ _ _ _ _ (by omega))).append
      (endpoint_equiv _ _ _)).append (lowerReverse_equiv _ _ _ _ _ (by omega))).append
      (toggle_equiv _ _)

end VQ.Euclid.BorrowedRangeScan
