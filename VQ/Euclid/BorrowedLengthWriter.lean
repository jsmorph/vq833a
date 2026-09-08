import VQ.Euclid.BorrowedRangeScanResources
import VQ.Euclid.LengthWriter

namespace VQ.Euclid.BorrowedLengthWriter

open Reversible LengthWriter

def upperGates (start workWidth endpointWidth : Nat) : List RGate :=
  controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth
      (upperSeed start workWidth endpointWidth) ++
    upperDirtyGates start workWidth endpointWidth ++
    BorrowedRangeScan.upperGates start workWidth endpointWidth ++
    upperDirtyGates start workWidth endpointWidth ++
    BorrowedRangeScan.upperGates start workWidth endpointWidth

def lowerGates (n start workWidth endpointWidth : Nat) : List RGate :=
  controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth
      (lowerSeed n start workWidth endpointWidth) ++
    lowerDirtyGates n start workWidth endpointWidth ++
    BorrowedRangeScan.lowerGates start workWidth endpointWidth ++
    lowerDirtyGates n start workWidth endpointWidth ++
    BorrowedRangeScan.lowerGates start workWidth endpointWidth

private theorem seed_below (value workWidth endpointWidth : Nat) :
    (controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth value).all
      (RGate.wellFormed (RangeZero.temporaryWire workWidth endpointWidth)) = true := by
  apply controlledXorGates_wellFormed
  · right
    simp [controlWire, targetOffset, Interval.outerWire, Interval.rightOffset]
    omega
  · simp [controlWire, RangeZero.temporaryWire, Interval.outerWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset]
    omega
  · simp [targetOffset, RangeZero.temporaryWire, Interval.rightOffset,
      Interval.cellScratchWire, Interval.selectorScratchOffset, Interval.outerWire]
    omega

private theorem dirty_below (delta : Nat → Nat) (workWidth endpointWidth : Nat) :
    (dirtyWriteGates delta (controlWire workWidth endpointWidth)
      (dirtyOffset workWidth) (targetOffset workWidth endpointWidth)
      endpointWidth workWidth).all
      (RGate.wellFormed (RangeZero.temporaryWire workWidth endpointWidth)) = true := by
  apply dirtyWriteGates_wellFormed
  · right
    simp [controlWire, targetOffset, Interval.outerWire, Interval.rightOffset]
    omega
  · simp [dirtyOffset, targetOffset, Interval.rightOffset]; omega
  · simp [dirtyOffset, controlWire, Interval.outerWire]; omega
  · simp [controlWire, RangeZero.temporaryWire, Interval.outerWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset]
    omega
  · simp [targetOffset, RangeZero.temporaryWire, Interval.rightOffset,
      Interval.cellScratchWire, Interval.selectorScratchOffset, Interval.outerWire]
    omega

private theorem ascending_below (delta : Nat → Nat) (workWidth endpointWidth : Nat) :
    (dirtyWriteGatesAscending delta (controlWire workWidth endpointWidth)
      (dirtyOffset workWidth) (targetOffset workWidth endpointWidth)
      endpointWidth workWidth).all
      (RGate.wellFormed (RangeZero.temporaryWire workWidth endpointWidth)) = true := by
  apply dirtyWriteGatesAscending_wellFormed
  · right
    simp [controlWire, targetOffset, Interval.outerWire, Interval.rightOffset]
    omega
  · simp [dirtyOffset, targetOffset, Interval.rightOffset]; omega
  · simp [dirtyOffset, controlWire, Interval.outerWire]; omega
  · simp [controlWire, RangeZero.temporaryWire, Interval.outerWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset]
    omega
  · simp [targetOffset, RangeZero.temporaryWire, Interval.rightOffset,
      Interval.cellScratchWire, Interval.selectorScratchOffset, Interval.outerWire]
    omega

private theorem equiv_of_below {gs : List RGate} {q : Nat}
    (h : gs.all (RGate.wellFormed q) = true) : BorrowedEquivalent q gs gs :=
  BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)

theorem upperGates_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (RangeZero.temporaryWire workWidth endpointWidth)
      (LengthWriter.upperGates start workWidth endpointWidth)
      (upperGates start workWidth endpointWidth) := by
  have hs := equiv_of_below (seed_below (upperSeed start workWidth endpointWidth)
    workWidth endpointWidth)
  have hd := equiv_of_below (dirty_below (upperDelta start endpointWidth) workWidth endpointWidth)
  have hz := BorrowedRangeScan.upperGates_equiv start workWidth endpointWidth
  exact (((hs.append hd).append hz).append hd).append hz

theorem lowerGates_equiv (n start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (RangeZero.temporaryWire workWidth endpointWidth)
      (LengthWriter.lowerGates n start workWidth endpointWidth)
      (lowerGates n start workWidth endpointWidth) := by
  have hs := equiv_of_below (seed_below (lowerSeed n start workWidth endpointWidth)
    workWidth endpointWidth)
  have hd := equiv_of_below
    (ascending_below (lowerDelta n start workWidth endpointWidth) workWidth endpointWidth)
  have hz := BorrowedRangeScan.lowerGates_equiv start workWidth endpointWidth
  exact (((hs.append hd).append hz).append hd).append hz

theorem upperGates_wellFormed (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  simp only [upperGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨seedGates_wellFormed _ _ _, dirtyGates_wellFormed _ _ _⟩,
    BorrowedRangeScan.upperGates_wellFormed _ _ _⟩, dirtyGates_wellFormed _ _ _⟩,
    BorrowedRangeScan.upperGates_wellFormed _ _ _⟩

theorem lowerGates_wellFormed (n start workWidth endpointWidth : Nat) :
    (lowerGates n start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  simp only [lowerGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨seedGates_wellFormed _ _ _, dirtyGatesAscending_wellFormed _ _ _⟩,
    BorrowedRangeScan.lowerGates_wellFormed _ _ _⟩, dirtyGatesAscending_wellFormed _ _ _⟩,
    BorrowedRangeScan.lowerGates_wellFormed _ _ _⟩

theorem upperGates_reverse_equiv (start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (RangeZero.temporaryWire workWidth endpointWidth)
      (LengthWriter.upperGates start workWidth endpointWidth).reverse
      (upperGates start workWidth endpointWidth).reverse :=
  (upperGates_equiv start workWidth endpointWidth).reverse
    (LengthWriter.upperGates_wellFormed start workWidth endpointWidth)
    (upperGates_wellFormed start workWidth endpointWidth)

theorem lowerGates_reverse_equiv (n start workWidth endpointWidth : Nat) :
    BorrowedEquivalent (RangeZero.temporaryWire workWidth endpointWidth)
      (LengthWriter.lowerGates n start workWidth endpointWidth).reverse
      (lowerGates n start workWidth endpointWidth).reverse :=
  (lowerGates_equiv n start workWidth endpointWidth).reverse
    (LengthWriter.lowerGates_wellFormed n start workWidth endpointWidth)
    (lowerGates_wellFormed n start workWidth endpointWidth)

theorem upperGates_ccx (start count endpointWidth : Nat) :
    (upperGates start (count + 1) endpointWidth).countP RGate.isCcx + 6 =
      (LengthWriter.upperGates start (count + 1) endpointWidth).countP RGate.isCcx + 4 * (count + 1) := by
  simp only [upperGates, LengthWriter.upperGates, List.countP_append]
  have h := BorrowedRangeScan.upperGates_ccx start count endpointWidth
  omega

theorem lowerGates_ccx (n start count endpointWidth : Nat) :
    (lowerGates n start (count + 1) endpointWidth).countP RGate.isCcx + 6 =
      (LengthWriter.lowerGates n start (count + 1) endpointWidth).countP RGate.isCcx + 4 * (count + 1) := by
  simp only [lowerGates, LengthWriter.lowerGates, List.countP_append]
  have h := BorrowedRangeScan.lowerGates_ccx start count endpointWidth
  omega

theorem upperGates_zero (start endpointWidth : Nat) :
    upperGates start 0 endpointWidth = LengthWriter.upperGates start 0 endpointWidth := rfl

theorem lowerGates_zero (n start endpointWidth : Nat) :
    lowerGates n start 0 endpointWidth = LengthWriter.lowerGates n start 0 endpointWidth := rfl

end VQ.Euclid.BorrowedLengthWriter
