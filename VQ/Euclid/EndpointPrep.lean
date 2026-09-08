/-
Reversible preparation of the physical interval endpoints used by Algorithm 3.
-/
import VQ.Euclid.Arithmetic
import VQ.Reversible.Constant
import VQ.Reversible.ControlledConstant
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace EndpointPrep

open Reversible

def layout (width : Nat) : Layout :=
  [width, width, width, width, width, 1, 1, 1, 1]

def lenTOffset : Nat := 0
def lenQOffset (width : Nat) : Nat := width
def shiftOffset (width : Nat) : Nat := 2 * width
def leftOffset (width : Nat) : Nat := 3 * width
def rightOffset (width : Nat) : Nat := 4 * width
def controlWire (width : Nat) : Nat := 5 * width
def carryWire (width : Nat) : Nat := 5 * width + 1
def signWire (width : Nat) : Nat := 5 * width + 2
def scratchWire (width : Nat) : Nat := 5 * width + 3

def addQLeft (width : Nat) : List RGate :=
  Arithmetic.addGates width (lenQOffset width) (leftOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def addTLeft (width : Nat) : List RGate :=
  Arithmetic.addGates width lenTOffset (leftOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def subShiftRight (width : Nat) : List RGate :=
  Arithmetic.subGates width (shiftOffset width) (rightOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def addTRight (width : Nat) : List RGate :=
  Arithmetic.addGates width lenTOffset (rightOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def subTRight (width : Nat) : List RGate :=
  Arithmetic.subGates width lenTOffset (rightOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def subRPrimeRight (width : Nat) : List RGate :=
  Arithmetic.subGates width (lenQOffset width) (rightOffset width)
    (carryWire width) (signWire width) (controlWire width) (scratchWire width)

def remainderPrepare (n width : Nat) : List RGate :=
  constantXorGates 3 (leftOffset width) width ++
    constantXorGates (n + 1) (rightOffset width) width ++
    addQLeft width ++ addTLeft width ++ subShiftRight width

def remainderCleanup (n width : Nat) : List RGate :=
  (remainderPrepare n width).reverse

def swapPrepare (width : Nat) : List RGate :=
  constantXorGates 2 (leftOffset width) width ++
    addQLeft width ++ addTLeft width

def swapCleanup (width : Nat) : List RGate :=
  (swapPrepare width).reverse

def coefficientPrepare (width : Nat) : List RGate :=
  constantXorGates 1 (rightOffset width) width ++ addTRight width

def coefficientCleanup (width : Nat) : List RGate :=
  (coefficientPrepare width).reverse

def coefficientAdjustmentConstant (n : Nat) : Nat :=
  1 ^^^ n

def coefficientAdjustment (n width : Nat) : List RGate :=
  subTRight width ++
    controlledXorGates (controlWire width) (rightOffset width) width
      (coefficientAdjustmentConstant n) ++
    subRPrimeRight width ++ subShiftRight width

def coefficientAdjustmentCleanup (n width : Nat) : List RGate :=
  (coefficientAdjustment n width).reverse

def remainderLoaded (n width i : Nat) : Nat :=
  writeField
    (writeField i (leftOffset width) width (readField 3 0 width))
    (rightOffset width) width (readField (n + 1) 0 width)

def addQOut (width i : Nat) : Nat :=
  writeField
    (writeField i (leftOffset width) width
      (Arithmetic.placedAddTargetValue width (lenQOffset width)
        (leftOffset width) (controlWire width) i))
    (signWire width) 1
      (Arithmetic.placedAddSignValue width (lenQOffset width)
        (leftOffset width) (signWire width) (controlWire width) i)

def addTOut (width i : Nat) : Nat :=
  writeField
    (writeField i (leftOffset width) width
      (Arithmetic.placedAddTargetValue width lenTOffset
        (leftOffset width) (controlWire width) i))
    (signWire width) 1
      (Arithmetic.placedAddSignValue width lenTOffset
        (leftOffset width) (signWire width) (controlWire width) i)

def subShiftOut (width i : Nat) : Nat :=
  writeField
    (writeField i (rightOffset width) width
      (Arithmetic.placedSubTargetValue width (shiftOffset width)
        (rightOffset width) (controlWire width) i))
    (signWire width) 1
      (Arithmetic.placedSubSignValue width (shiftOffset width)
        (rightOffset width) (signWire width) (controlWire width) i)

def remainderOut (n width i : Nat) : Nat :=
  subShiftOut width (addTOut width (addQOut width
    (remainderLoaded n width i)))

def swapLoaded (width i : Nat) : Nat :=
  writeField i (leftOffset width) width (readField 2 0 width)

def swapOut (width i : Nat) : Nat :=
  addTOut width (addQOut width (swapLoaded width i))

def coefficientLoaded (width i : Nat) : Nat :=
  writeField i (rightOffset width) width (readField 1 0 width)

def coefficientOut (width i : Nat) : Nat :=
  writeField
    (writeField (coefficientLoaded width i) (rightOffset width) width
      (Arithmetic.placedAddTargetValue width lenTOffset
        (rightOffset width) (controlWire width) (coefficientLoaded width i)))
    (signWire width) 1
      (Arithmetic.placedAddSignValue width lenTOffset
        (rightOffset width) (signWire width) (controlWire width)
        (coefficientLoaded width i))

def subTRightOut (width i : Nat) : Nat :=
  writeField
    (writeField i (rightOffset width) width
      (Arithmetic.placedSubTargetValue width lenTOffset
        (rightOffset width) (controlWire width) i))
    (signWire width) 1
      (Arithmetic.placedSubSignValue width lenTOffset
        (rightOffset width) (signWire width) (controlWire width) i)

def coefficientXorOut (n width i : Nat) : Nat :=
  writeField i (rightOffset width) width
    (readField i (rightOffset width) width ^^^
      bitValue i (controlWire width) * coefficientAdjustmentConstant n)

def subRPrimeRightOut (width i : Nat) : Nat :=
  writeField
    (writeField i (rightOffset width) width
      (Arithmetic.placedSubTargetValue width (lenQOffset width)
        (rightOffset width) (controlWire width) i))
    (signWire width) 1
      (Arithmetic.placedSubSignValue width (lenQOffset width)
        (rightOffset width) (signWire width) (controlWire width) i)

def coefficientAdjustmentOut (n width i : Nat) : Nat :=
  subShiftOut width
    (subRPrimeRightOut width
      (coefficientXorOut n width (subTRightOut width i)))

theorem remainderOut_testBit_outside
    {n width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q)
    (hright : q < rightOffset width ∨ rightOffset width + width ≤ q)
    (hsign : q < signWire width ∨ signWire width + 1 ≤ q) :
    (remainderOut n width i).testBit q = i.testBit q := by
  simp only [remainderOut, subShiftOut, addTOut, addQOut, remainderLoaded]
  rw [testBit_writeField_outside hsign,
    testBit_writeField_outside hright,
    testBit_writeField_outside hsign,
    testBit_writeField_outside hleft,
    testBit_writeField_outside hsign,
    testBit_writeField_outside hleft,
    testBit_writeField_outside hright,
    testBit_writeField_outside hleft]

theorem remainderOut_eq_writeFields (n width i : Nat) :
    let result := remainderOut n width i
    result =
      writeField
        (writeField
          (writeField i (leftOffset width) width
            (readField result (leftOffset width) width))
          (rightOffset width) width
          (readField result (rightOffset width) width))
        (signWire width) 1 (bitValue result (signWire width)) := by
  let result := remainderOut n width i
  have hframe := eq_write_three_fields
    (i := i) (j := result)
    (o₁ := leftOffset width) (n₁ := width)
    (o₂ := rightOffset width) (n₂ := width)
    (o₃ := signWire width) (n₃ := 1)
    (by simp [leftOffset, rightOffset]; omega)
    (by simp [leftOffset, signWire]; omega)
    (by simp [rightOffset, signWire]; omega)
    (fun b hleft hright hsign => by
      exact remainderOut_testBit_outside hleft hright hsign)
  simpa [result, readField_one] using hframe

theorem swapOut_testBit_outside
    {width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q)
    (hsign : q < signWire width ∨ signWire width + 1 ≤ q) :
    (swapOut width i).testBit q = i.testBit q := by
  simp only [swapOut, swapLoaded, addTOut, addQOut]
  rw [testBit_writeField_outside hsign,
    testBit_writeField_outside hleft,
    testBit_writeField_outside hsign,
    testBit_writeField_outside hleft,
    testBit_writeField_outside hleft]

theorem swapOut_eq_writeFields (width i : Nat) :
    let result := swapOut width i
    result =
      writeField
        (writeField i (leftOffset width) width
          (readField result (leftOffset width) width))
        (signWire width) 1 (bitValue result (signWire width)) := by
  let result := swapOut width i
  have hframe := eq_write_three_fields
    (i := i) (j := result)
    (o₁ := leftOffset width) (n₁ := width)
    (o₂ := rightOffset width) (n₂ := 0)
    (o₃ := signWire width) (n₃ := 1)
    (by simp [leftOffset, rightOffset]; omega)
    (by simp [leftOffset, signWire]; omega)
    (by simp [rightOffset, signWire]; omega)
    (fun b hleft _hright hsign => by
      exact swapOut_testBit_outside hleft hsign)
  simpa [result, readField_one, writeField_zero] using hframe

def coefficientRightValue (width i : Nat) : Nat :=
  Arithmetic.placedAddTargetValue width lenTOffset
    (rightOffset width) (controlWire width) (coefficientLoaded width i)

def coefficientSignValue (width i : Nat) : Nat :=
  Arithmetic.placedAddSignValue width lenTOffset
    (rightOffset width) (signWire width) (controlWire width)
    (coefficientLoaded width i)

theorem coefficientOut_eq_writeFields (width i : Nat) :
    coefficientOut width i =
      writeField
        (writeField i (rightOffset width) width
          (coefficientRightValue width i))
        (signWire width) 1 (coefficientSignValue width i) := by
  simp [coefficientOut, coefficientRightValue, coefficientSignValue,
    coefficientLoaded, writeField_writeField]

theorem placedAddTargetValue_lt (width source target control i : Nat) :
    Arithmetic.placedAddTargetValue width source target control i < 2 ^ width := by
  unfold Arithmetic.placedAddTargetValue
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos width)
  · exact readField_lt i target width

theorem placedSubTargetValue_lt (width source target control i : Nat) :
    Arithmetic.placedSubTargetValue width source target control i < 2 ^ width := by
  unfold Arithmetic.placedSubTargetValue Adder.difference
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos width)
  · exact readField_lt i target width

theorem addQOut_left (width i : Nat) :
    readField (addQOut width i) (leftOffset width) width =
      Arithmetic.placedAddTargetValue width (lenQOffset width)
        (leftOffset width) (controlWire width) i := by
  unfold addQOut
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [leftOffset, signWire]
    omega)), readField_writeField_self]
  exact placedAddTargetValue_lt width (lenQOffset width)
    (leftOffset width) (controlWire width) i

theorem addTOut_left (width i : Nat) :
    readField (addTOut width i) (leftOffset width) width =
      Arithmetic.placedAddTargetValue width lenTOffset
        (leftOffset width) (controlWire width) i := by
  unfold addTOut
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [leftOffset, signWire]
    omega)), readField_writeField_self]
  exact placedAddTargetValue_lt width lenTOffset (leftOffset width)
    (controlWire width) i

theorem subShiftOut_right (width i : Nat) :
    readField (subShiftOut width i) (rightOffset width) width =
      Arithmetic.placedSubTargetValue width (shiftOffset width)
        (rightOffset width) (controlWire width) i := by
  unfold subShiftOut
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [rightOffset, signWire]
    omega)), readField_writeField_self]
  exact placedSubTargetValue_lt width (shiftOffset width)
    (rightOffset width) (controlWire width) i

theorem readField_addQOut_of_disjoint {width i off len : Nat}
    (hleft : leftOffset width + width ≤ off ∨ off + len ≤ leftOffset width)
    (hsign : signWire width + 1 ≤ off ∨ off + len ≤ signWire width) :
    readField (addQOut width i) off len = readField i off len := by
  unfold addQOut
  rw [readField_writeField_of_disjoint hsign,
    readField_writeField_of_disjoint hleft]

theorem readField_addTOut_of_disjoint {width i off len : Nat}
    (hleft : leftOffset width + width ≤ off ∨ off + len ≤ leftOffset width)
    (hsign : signWire width + 1 ≤ off ∨ off + len ≤ signWire width) :
    readField (addTOut width i) off len = readField i off len := by
  unfold addTOut
  rw [readField_writeField_of_disjoint hsign,
    readField_writeField_of_disjoint hleft]

theorem readField_subShiftOut_of_disjoint {width i off len : Nat}
    (hright : rightOffset width + width ≤ off ∨ off + len ≤ rightOffset width)
    (hsign : signWire width + 1 ≤ off ∨ off + len ≤ signWire width) :
    readField (subShiftOut width i) off len = readField i off len := by
  unfold subShiftOut
  rw [readField_writeField_of_disjoint hsign,
    readField_writeField_of_disjoint hright]

theorem testBit_addQOut_of_outside {width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q)
    (hsign : q < signWire width ∨ signWire width + 1 ≤ q) :
    (addQOut width i).testBit q = i.testBit q := by
  unfold addQOut
  rw [testBit_writeField_outside hsign, testBit_writeField_outside hleft]

theorem testBit_addTOut_of_outside {width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q)
    (hsign : q < signWire width ∨ signWire width + 1 ≤ q) :
    (addTOut width i).testBit q = i.testBit q := by
  unfold addTOut
  rw [testBit_writeField_outside hsign, testBit_writeField_outside hleft]

theorem remainderLoaded_left {n width i : Nat} (hthree : 3 < 2 ^ width) :
    readField (remainderLoaded n width i) (leftOffset width) width = 3 := by
  unfold remainderLoaded
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [leftOffset, rightOffset]
    omega)), readField_writeField_self (readField_lt 3 0 width)]
  simp [readField_zero, Nat.mod_eq_of_lt hthree]

theorem remainderLoaded_right {n width i : Nat} (hn : n + 1 < 2 ^ width) :
    readField (remainderLoaded n width i) (rightOffset width) width = n + 1 := by
  unfold remainderLoaded
  rw [readField_writeField_self (readField_lt (n + 1) 0 width)]
  simp [readField_zero, Nat.mod_eq_of_lt hn]

theorem readField_remainderLoaded_of_disjoint {n width i off len : Nat}
    (hleft : leftOffset width + width ≤ off ∨ off + len ≤ leftOffset width)
    (hright : rightOffset width + width ≤ off ∨ off + len ≤ rightOffset width) :
    readField (remainderLoaded n width i) off len = readField i off len := by
  unfold remainderLoaded
  rw [readField_writeField_of_disjoint hright,
    readField_writeField_of_disjoint hleft]

theorem testBit_remainderLoaded_of_outside {n width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q)
    (hright : q < rightOffset width ∨ rightOffset width + width ≤ q) :
    (remainderLoaded n width i).testBit q = i.testBit q := by
  unfold remainderLoaded
  rw [testBit_writeField_outside hright, testBit_writeField_outside hleft]

theorem swapLoaded_left {width i : Nat} (htwo : 2 < 2 ^ width) :
    readField (swapLoaded width i) (leftOffset width) width = 2 := by
  unfold swapLoaded
  rw [readField_writeField_self (readField_lt 2 0 width)]
  simp [readField_zero, Nat.mod_eq_of_lt htwo]

theorem readField_swapLoaded_of_disjoint {width i off len : Nat}
    (hleft : leftOffset width + width ≤ off ∨ off + len ≤ leftOffset width) :
    readField (swapLoaded width i) off len = readField i off len := by
  unfold swapLoaded
  rw [readField_writeField_of_disjoint hleft]

theorem testBit_swapLoaded_of_outside {width i q : Nat}
    (hleft : q < leftOffset width ∨ leftOffset width + width ≤ q) :
    (swapLoaded width i).testBit q = i.testBit q := by
  unfold swapLoaded
  rw [testBit_writeField_outside hleft]

theorem remainderOut_endpoints_mod {n width i : Nat}
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (remainderOut n width i) (leftOffset width) width =
        (readField i lenTOffset width +
          readField i (lenQOffset width) width + 3) % 2 ^ width ∧
      readField (remainderOut n width i) (rightOffset width) width =
        (n + 1 +
          (2 ^ width - readField i (shiftOffset width) width)) % 2 ^ width := by
  let i0 := remainderLoaded n width i
  let i1 := addQOut width i0
  let i2 := addTOut width i1
  have hq0 : readField i0 (lenQOffset width) width =
      readField i (lenQOffset width) width := by
    exact readField_remainderLoaded_of_disjoint
      (Or.inr (by simp [lenQOffset, leftOffset]; omega))
      (Or.inr (by simp [lenQOffset, rightOffset]; omega))
  have ht0 : readField i0 lenTOffset width = readField i lenTOffset width := by
    exact readField_remainderLoaded_of_disjoint
      (Or.inr (by simp [lenTOffset, leftOffset]; omega))
      (Or.inr (by simp [lenTOffset, rightOffset]; omega))
  have hs0 : readField i0 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    exact readField_remainderLoaded_of_disjoint
      (Or.inr (by simp [shiftOffset, leftOffset]; omega))
      (Or.inr (by simp [shiftOffset, rightOffset]; omega))
  have hc0 : i0.testBit (controlWire width) = true := by
    rw [testBit_remainderLoaded_of_outside
      (Or.inr (by simp [leftOffset, controlWire]; omega))
      (Or.inr (by simp [rightOffset, controlWire]; omega)), hcontrol]
  have hl0 : readField i0 (leftOffset width) width = 3 % 2 ^ width := by
    simp only [i0, remainderLoaded]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [leftOffset, rightOffset]
      omega)), readField_writeField_self (readField_lt 3 0 width),
      readField_zero]
  have hr0 : readField i0 (rightOffset width) width =
      (n + 1) % 2 ^ width := by
    simp only [i0, remainderLoaded]
    rw [readField_writeField_self (readField_lt (n + 1) 0 width),
      readField_zero]
  have hl1 : readField i1 (leftOffset width) width =
      (readField i (lenQOffset width) width + 3) % 2 ^ width := by
    rw [addQOut_left]
    simp only [Arithmetic.placedAddTargetValue, hc0, if_true, hq0, hl0]
    rw [Nat.add_mod_mod]
  have ht1 : readField i1 lenTOffset width = readField i lenTOffset width := by
    rw [readField_addQOut_of_disjoint
      (Or.inr (by simp [lenTOffset, leftOffset]; omega))
      (Or.inr (by simp [lenTOffset, signWire]; omega)), ht0]
  have hs1 : readField i1 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    rw [readField_addQOut_of_disjoint
      (Or.inr (by simp [shiftOffset, leftOffset]; omega))
      (Or.inr (by simp [shiftOffset, signWire]; omega)), hs0]
  have hr1 : readField i1 (rightOffset width) width =
      (n + 1) % 2 ^ width := by
    rw [readField_addQOut_of_disjoint
      (Or.inl (by simp [leftOffset, rightOffset]; omega))
      (Or.inr (by simp [rightOffset, signWire]; omega)), hr0]
  have hc1 : i1.testBit (controlWire width) = true := by
    rw [testBit_addQOut_of_outside
      (Or.inr (by simp [leftOffset, controlWire]; omega))
      (Or.inl (by simp [signWire, controlWire])), hc0]
  have hl2 : readField i2 (leftOffset width) width =
      (readField i lenTOffset width +
        readField i (lenQOffset width) width + 3) % 2 ^ width := by
    rw [addTOut_left]
    simp only [Arithmetic.placedAddTargetValue, hc1, if_true, ht1, hl1]
    rw [Nat.add_mod_mod]
    congr 1
  have hs2 : readField i2 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    rw [readField_addTOut_of_disjoint
      (Or.inr (by simp [shiftOffset, leftOffset]; omega))
      (Or.inr (by simp [shiftOffset, signWire]; omega)), hs1]
  have hr2 : readField i2 (rightOffset width) width =
      (n + 1) % 2 ^ width := by
    rw [readField_addTOut_of_disjoint
      (Or.inl (by simp [leftOffset, rightOffset]; omega))
      (Or.inr (by simp [rightOffset, signWire]; omega)), hr1]
  have hc2 : i2.testBit (controlWire width) = true := by
    rw [testBit_addTOut_of_outside
      (Or.inr (by simp [leftOffset, controlWire]; omega))
      (Or.inl (by simp [signWire, controlWire])), hc1]
  constructor
  · change readField (subShiftOut width i2) (leftOffset width) width = _
    rw [readField_subShiftOut_of_disjoint
      (Or.inr (by simp [leftOffset, rightOffset]; omega))
      (Or.inr (by simp [leftOffset, signWire]; omega)), hl2]
  · change readField (subShiftOut width i2) (rightOffset width) width = _
    rw [subShiftOut_right]
    simp only [Arithmetic.placedSubTargetValue, hc2, if_true, hs2, hr2]
    unfold Adder.difference
    rw [Nat.mod_add_mod]

theorem remainderOut_endpoints {n width i : Nat}
    (hn : n + 1 < 2 ^ width)
    (hsum : 3 + readField i (lenQOffset width) width +
      readField i lenTOffset width < 2 ^ width)
    (hshift : readField i (shiftOffset width) width ≤ n + 1)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (remainderOut n width i) (leftOffset width) width =
        3 + readField i (lenQOffset width) width +
          readField i lenTOffset width ∧
      readField (remainderOut n width i) (rightOffset width) width =
        n + 1 - readField i (shiftOffset width) width := by
  have hmod := remainderOut_endpoints_mod (n := n) hcontrol
  constructor
  · rw [hmod.1, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hmod.2]
    exact Adder.difference_eq_sub_of_le
      (readField_lt i (shiftOffset width) width) hn hshift

theorem swapOut_endpoint {width i : Nat}
    (htwo : 2 < 2 ^ width)
    (hsum : 2 + readField i (lenQOffset width) width +
      readField i lenTOffset width < 2 ^ width)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (swapOut width i) (leftOffset width) width =
      2 + readField i (lenQOffset width) width +
        readField i lenTOffset width := by
  let i0 := swapLoaded width i
  let i1 := addQOut width i0
  have hq0 : readField i0 (lenQOffset width) width =
      readField i (lenQOffset width) width := by
    exact readField_swapLoaded_of_disjoint
      (Or.inr (by simp [lenQOffset, leftOffset]; omega))
  have ht0 : readField i0 lenTOffset width = readField i lenTOffset width := by
    exact readField_swapLoaded_of_disjoint
      (Or.inr (by simp [lenTOffset, leftOffset]; omega))
  have hc0 : i0.testBit (controlWire width) = true := by
    rw [testBit_swapLoaded_of_outside
      (Or.inr (by simp [leftOffset, controlWire]; omega)), hcontrol]
  have hl0 : readField i0 (leftOffset width) width = 2 :=
    swapLoaded_left htwo
  have hl1 : readField i1 (leftOffset width) width =
      2 + readField i (lenQOffset width) width := by
    rw [addQOut_left]
    simp only [Arithmetic.placedAddTargetValue, hc0, if_true, hq0, hl0]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have ht1 : readField i1 lenTOffset width = readField i lenTOffset width := by
    rw [readField_addQOut_of_disjoint
      (Or.inr (by simp [lenTOffset, leftOffset]; omega))
      (Or.inr (by simp [lenTOffset, signWire]; omega)), ht0]
  have hc1 : i1.testBit (controlWire width) = true := by
    rw [testBit_addQOut_of_outside
      (Or.inr (by simp [leftOffset, controlWire]; omega))
      (Or.inl (by simp [signWire, controlWire])), hc0]
  change readField (addTOut width i1) (leftOffset width) width = _
  rw [addTOut_left]
  simp only [Arithmetic.placedAddTargetValue, hc1, if_true, ht1, hl1]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem coefficientLoaded_right {width i : Nat} (hone : 1 < 2 ^ width) :
    readField (coefficientLoaded width i) (rightOffset width) width = 1 := by
  unfold coefficientLoaded
  rw [readField_writeField_self (readField_lt 1 0 width)]
  simp [readField_zero, Nat.mod_eq_of_lt hone]

theorem coefficientOut_right {width i : Nat} (hone : 1 < 2 ^ width)
    (hsum : 1 + readField i lenTOffset width < 2 ^ width)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (coefficientOut width i) (rightOffset width) width =
      1 + readField i lenTOffset width := by
  let i0 := coefficientLoaded width i
  have ht0 : readField i0 lenTOffset width = readField i lenTOffset width := by
    simp only [i0, coefficientLoaded]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lenTOffset, rightOffset]
      omega))]
  have hc0 : i0.testBit (controlWire width) = true := by
    simp only [i0, coefficientLoaded]
    rw [testBit_writeField_outside (Or.inr (by
      simp [rightOffset, controlWire]
      omega)), hcontrol]
  have hr0 : readField i0 (rightOffset width) width = 1 :=
    coefficientLoaded_right hone
  unfold coefficientOut
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [rightOffset, signWire]
    omega)), readField_writeField_self
      (placedAddTargetValue_lt width lenTOffset (rightOffset width)
        (controlWire width) i0)]
  simp only [Arithmetic.placedAddTargetValue, hc0, if_true, ht0, hr0]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem layout_width (width : Nat) :
    (layout width).width = 5 * width + 4 := by
  simp [layout, Layout.width]
  omega

theorem qLeft_disjoint {width : Nat} (hwidth : 0 < width) :
    Wiring.Disjoint (Arithmetic.layout width)
      (Arithmetic.wiring (lenQOffset width) (leftOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) := by
  intro j k hj hk hne
  simp [Arithmetic.wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, lenQOffset, leftOffset,
      carryWire, signWire, controlWire, scratchWire] <;> omega

theorem tLeft_disjoint {width : Nat} (hwidth : 0 < width) :
    Wiring.Disjoint (Arithmetic.layout width)
      (Arithmetic.wiring lenTOffset (leftOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) := by
  intro j k hj hk hne
  simp [Arithmetic.wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, lenTOffset, leftOffset,
      carryWire, signWire, controlWire, scratchWire] <;> omega

theorem shiftRight_disjoint {width : Nat} (hwidth : 0 < width) :
    Wiring.Disjoint (Arithmetic.layout width)
      (Arithmetic.wiring (shiftOffset width) (rightOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) := by
  intro j k hj hk hne
  simp [Arithmetic.wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, shiftOffset, rightOffset,
      carryWire, signWire, controlWire, scratchWire] <;> omega

theorem tRight_disjoint {width : Nat} (hwidth : 0 < width) :
    Wiring.Disjoint (Arithmetic.layout width)
      (Arithmetic.wiring lenTOffset (rightOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) := by
  intro j k hj hk hne
  simp [Arithmetic.wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, lenTOffset, rightOffset,
      carryWire, signWire, controlWire, scratchWire] <;> omega

theorem rPrimeRight_disjoint {width : Nat} (hwidth : 0 < width) :
    Wiring.Disjoint (Arithmetic.layout width)
      (Arithmetic.wiring (lenQOffset width) (rightOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) := by
  intro j k hj hk hne
  simp [Arithmetic.wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, lenQOffset, rightOffset,
      carryWire, signWire, controlWire, scratchWire] <;> omega

theorem arithmeticBound (width source target : Nat) :
    source + width ≤ 5 * width + 4 →
    target + width ≤ 5 * width + 4 →
    ∀ j, j < (Arithmetic.layout width).length →
      (Arithmetic.wiring source target (carryWire width) (signWire width)
          (controlWire width) (scratchWire width)).getD j 0 +
        (Arithmetic.layout width).size j ≤ 5 * width + 4 := by
  intro hsource htarget j hj
  simp [Arithmetic.layout] at hj
  interval_cases j <;>
    simp_all [List.getD_eq_getElem?_getD, Arithmetic.wiring,
      Arithmetic.layout, Layout.size, carryWire, signWire, controlWire,
      scratchWire]

theorem addQLeft_wellFormed {width : Nat} (hwidth : 0 < width) :
    (addQLeft width).all (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.addGates_wellFormed hwidth (qLeft_disjoint hwidth)
    (arithmeticBound width (lenQOffset width) (leftOffset width)
      (by simp [lenQOffset]; omega) (by simp [leftOffset]; omega))

theorem addTLeft_wellFormed {width : Nat} (hwidth : 0 < width) :
    (addTLeft width).all (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.addGates_wellFormed hwidth (tLeft_disjoint hwidth)
    (arithmeticBound width lenTOffset (leftOffset width)
      (by simp [lenTOffset]; omega) (by simp [leftOffset]; omega))

theorem subShiftRight_wellFormed {width : Nat} (hwidth : 0 < width) :
    (subShiftRight width).all (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.subGates_wellFormed hwidth (shiftRight_disjoint hwidth)
    (arithmeticBound width (shiftOffset width) (rightOffset width)
      (by simp [shiftOffset]; omega) (by simp [rightOffset]; omega))

theorem addTRight_wellFormed {width : Nat} (hwidth : 0 < width) :
    (addTRight width).all (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.addGates_wellFormed hwidth (tRight_disjoint hwidth)
    (arithmeticBound width lenTOffset (rightOffset width)
      (by simp [lenTOffset]; omega) (by simp [rightOffset]; omega))

theorem subTRight_wellFormed {width : Nat} (hwidth : 0 < width) :
    (subTRight width).all
      (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.subGates_wellFormed hwidth (tRight_disjoint hwidth)
    (arithmeticBound width lenTOffset (rightOffset width)
      (by simp [lenTOffset]; omega) (by simp [rightOffset]; omega))

theorem subRPrimeRight_wellFormed {width : Nat} (hwidth : 0 < width) :
    (subRPrimeRight width).all
      (RGate.wellFormed (layout width).width) = true := by
  rw [layout_width]
  exact Arithmetic.subGates_wellFormed hwidth (rPrimeRight_disjoint hwidth)
    (arithmeticBound width (lenQOffset width) (rightOffset width)
      (by simp [lenQOffset]; omega) (by simp [rightOffset]; omega))

theorem remainderPrepare_wellFormed {n width : Nat} (hwidth : 0 < width) :
    (remainderPrepare n width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp only [remainderPrepare, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, addQLeft_wellFormed hwidth⟩,
    addTLeft_wellFormed hwidth⟩, subShiftRight_wellFormed hwidth⟩
  · exact constantXorGates_wellFormed (by
      rw [layout_width]
      simp [leftOffset]
      omega)
  · exact constantXorGates_wellFormed (by
      rw [layout_width]
      simp [rightOffset]
      omega)

theorem swapPrepare_wellFormed {width : Nat} (hwidth : 0 < width) :
    (swapPrepare width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp only [swapPrepare, List.all_append, Bool.and_eq_true]
  exact ⟨⟨constantXorGates_wellFormed (by
      rw [layout_width]
      simp [leftOffset]
      omega), addQLeft_wellFormed hwidth⟩,
    addTLeft_wellFormed hwidth⟩

theorem coefficientPrepare_wellFormed {width : Nat} (hwidth : 0 < width) :
    (coefficientPrepare width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp only [coefficientPrepare, List.all_append, Bool.and_eq_true]
  exact ⟨constantXorGates_wellFormed (by
      rw [layout_width]
      simp [rightOffset]
      omega), addTRight_wellFormed hwidth⟩

theorem coefficientAdjustment_wellFormed {n width : Nat}
    (hwidth : 0 < width) :
    (coefficientAdjustment n width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp only [coefficientAdjustment, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨subTRight_wellFormed hwidth, ?_⟩,
    subRPrimeRight_wellFormed hwidth⟩, subShiftRight_wellFormed hwidth⟩
  · exact controlledXorGates_wellFormed
      (by simp [controlWire, rightOffset]; omega)
      (by rw [layout_width]; simp [controlWire])
      (by rw [layout_width]; simp [rightOffset]; omega)

theorem remainderPrepare_act {n width i : Nat} (hwidth : 0 < width)
    (hleft : readField i (leftOffset width) width = 0)
    (hright : readField i (rightOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    actGates (remainderPrepare n width) i = remainderOut n width i := by
  let i0 := remainderLoaded n width i
  let i1 := addQOut width i0
  let i2 := addTOut width i1
  have hright0 : readField
      (writeField i (leftOffset width) width (readField 3 0 width))
      (rightOffset width) width = 0 := by
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [leftOffset, rightOffset]
      omega))]
    exact hright
  have hcarry0 : bitValue i0 (carryWire width) = 0 := by
    simp only [i0, remainderLoaded]
    rw [bitValue_write_out (Or.inr (by
      simp [rightOffset, carryWire]
      omega)), bitValue_write_out (Or.inr (by
      simp [leftOffset, carryWire]
      omega)), hcarry]
  have hscratch0 : i0.testBit (scratchWire width) = false := by
    simp only [i0, remainderLoaded]
    rw [testBit_writeField_outside (Or.inr (by
      simp [rightOffset, scratchWire]
      omega)), testBit_writeField_outside (Or.inr (by
      simp [leftOffset, scratchWire]
      omega)), hscratch]
  have hcarry1 : bitValue i1 (carryWire width) = 0 := by
    simp only [i1, addQOut]
    rw [bitValue_write_ne (by simp [signWire, carryWire]),
      bitValue_write_out (Or.inr (by
        simp [leftOffset, carryWire]
        omega)), hcarry0]
  have hscratch1 : i1.testBit (scratchWire width) = false := by
    simp only [i1, addQOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [signWire, scratchWire])), testBit_writeField_outside (Or.inr (by
      simp [leftOffset, scratchWire]
      omega)), hscratch0]
  have hcarry2 : bitValue i2 (carryWire width) = 0 := by
    simp only [i2, addTOut]
    rw [bitValue_write_ne (by simp [signWire, carryWire]),
      bitValue_write_out (Or.inr (by
        simp [leftOffset, carryWire]
        omega)), hcarry1]
  have hscratch2 : i2.testBit (scratchWire width) = false := by
    simp only [i2, addTOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [signWire, scratchWire])), testBit_writeField_outside (Or.inr (by
      simp [leftOffset, scratchWire]
      omega)), hscratch1]
  simp only [remainderPrepare, actGates_append]
  rw [act_constantXorGates_of_clear hleft,
    act_constantXorGates_of_clear hright0]
  change actGates (subShiftRight width)
    (actGates (addTLeft width) (actGates (addQLeft width) i0)) = _
  simp only [addQLeft, addTLeft, subShiftRight]
  rw [Arithmetic.addGates_act hwidth (qLeft_disjoint hwidth) hcarry0 hscratch0]
  change actGates
    (Arithmetic.subGates width (shiftOffset width) (rightOffset width)
      (carryWire width) (signWire width) (controlWire width)
      (scratchWire width))
    (actGates
      (Arithmetic.addGates width lenTOffset (leftOffset width)
        (carryWire width) (signWire width) (controlWire width)
        (scratchWire width)) i1) = _
  rw [Arithmetic.addGates_act hwidth (tLeft_disjoint hwidth) hcarry1 hscratch1]
  change actGates
    (Arithmetic.subGates width (shiftOffset width) (rightOffset width)
      (carryWire width) (signWire width) (controlWire width)
      (scratchWire width)) i2 = _
  rw [Arithmetic.subGates_act hwidth (shiftRight_disjoint hwidth) hcarry2 hscratch2]
  rfl

theorem swapPrepare_act {width i : Nat} (hwidth : 0 < width)
    (hleft : readField i (leftOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    actGates (swapPrepare width) i = swapOut width i := by
  let i0 := swapLoaded width i
  let i1 := addQOut width i0
  have hcarry0 : bitValue i0 (carryWire width) = 0 := by
    simp only [i0, swapLoaded]
    rw [bitValue_write_out (Or.inr (by
      simp [leftOffset, carryWire]
      omega)), hcarry]
  have hscratch0 : i0.testBit (scratchWire width) = false := by
    simp only [i0, swapLoaded]
    rw [testBit_writeField_outside (Or.inr (by
      simp [leftOffset, scratchWire]
      omega)), hscratch]
  have hcarry1 : bitValue i1 (carryWire width) = 0 := by
    simp only [i1, addQOut]
    rw [bitValue_write_ne (by simp [signWire, carryWire]),
      bitValue_write_out (Or.inr (by
        simp [leftOffset, carryWire]
        omega)), hcarry0]
  have hscratch1 : i1.testBit (scratchWire width) = false := by
    simp only [i1, addQOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [signWire, scratchWire])), testBit_writeField_outside (Or.inr (by
      simp [leftOffset, scratchWire]
      omega)), hscratch0]
  simp only [swapPrepare, actGates_append]
  rw [act_constantXorGates_of_clear hleft]
  change actGates (addTLeft width) (actGates (addQLeft width) i0) = _
  simp only [addQLeft, addTLeft]
  rw [Arithmetic.addGates_act hwidth (qLeft_disjoint hwidth) hcarry0 hscratch0]
  change actGates
    (Arithmetic.addGates width lenTOffset (leftOffset width)
      (carryWire width) (signWire width) (controlWire width)
      (scratchWire width)) i1 = _
  rw [Arithmetic.addGates_act hwidth (tLeft_disjoint hwidth) hcarry1 hscratch1]
  rfl

theorem coefficientPrepare_act {width i : Nat} (hwidth : 0 < width)
    (hright : readField i (rightOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    actGates (coefficientPrepare width) i = coefficientOut width i := by
  let i0 := coefficientLoaded width i
  have hcarry0 : bitValue i0 (carryWire width) = 0 := by
    simp only [i0, coefficientLoaded]
    rw [bitValue_write_out (Or.inr (by
      simp [rightOffset, carryWire]
      omega)), hcarry]
  have hscratch0 : i0.testBit (scratchWire width) = false := by
    simp only [i0, coefficientLoaded]
    rw [testBit_writeField_outside (Or.inr (by
      simp [rightOffset, scratchWire]
      omega)), hscratch]
  simp only [coefficientPrepare, actGates_append]
  rw [act_constantXorGates_of_clear hright]
  change actGates (addTRight width) i0 = _
  simp only [addTRight]
  rw [
    Arithmetic.addGates_act hwidth (tRight_disjoint hwidth) hcarry0 hscratch0]
  rfl

theorem coefficientAdjustment_act {n width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    actGates (coefficientAdjustment n width) i =
      coefficientAdjustmentOut n width i := by
  let i1 := subTRightOut width i
  let i2 := coefficientXorOut n width i1
  let i3 := subRPrimeRightOut width i2
  have hcarry1 : bitValue i1 (carryWire width) = 0 := by
    simp only [i1, subTRightOut]
    rw [bitValue_write_ne (by simp [signWire, carryWire]),
      bitValue_write_out (Or.inr (by simp [rightOffset, carryWire]; omega)),
      hcarry]
  have hscratch1 : i1.testBit (scratchWire width) = false := by
    simp only [i1, subTRightOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [signWire, scratchWire])),
      testBit_writeField_outside (Or.inr (by
        simp [rightOffset, scratchWire]
        omega)), hscratch]
  have hcarry2 : bitValue i2 (carryWire width) = 0 := by
    simp only [i2, coefficientXorOut]
    rw [bitValue_write_out (Or.inr (by
      simp [rightOffset, carryWire]
      omega)), hcarry1]
  have hscratch2 : i2.testBit (scratchWire width) = false := by
    simp only [i2, coefficientXorOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [rightOffset, scratchWire]
      omega)), hscratch1]
  have hcarry3 : bitValue i3 (carryWire width) = 0 := by
    simp only [i3, subRPrimeRightOut]
    rw [bitValue_write_ne (by simp [signWire, carryWire]),
      bitValue_write_out (Or.inr (by simp [rightOffset, carryWire]; omega)),
      hcarry2]
  have hscratch3 : i3.testBit (scratchWire width) = false := by
    simp only [i3, subRPrimeRightOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [signWire, scratchWire])),
      testBit_writeField_outside (Or.inr (by
        simp [rightOffset, scratchWire]
        omega)), hscratch2]
  simp only [coefficientAdjustment, actGates_append]
  rw [show actGates (subTRight width) i = i1 by
    simpa [subTRight, i1, subTRightOut] using
      Arithmetic.subGates_act hwidth (tRight_disjoint hwidth)
        hcarry hscratch]
  rw [show actGates
      (controlledXorGates (controlWire width) (rightOffset width) width
        (coefficientAdjustmentConstant n)) i1 = i2 by
    simpa [i2, coefficientXorOut] using
      controlledXorGates_act width (rightOffset width)
        (coefficientAdjustmentConstant n) i1 (by
          simp [controlWire, rightOffset]
          omega)]
  rw [show actGates (subRPrimeRight width) i2 = i3 by
    simpa [subRPrimeRight, i3, subRPrimeRightOut] using
      Arithmetic.subGates_act hwidth (rPrimeRight_disjoint hwidth)
        hcarry2 hscratch2]
  simpa [subShiftRight, subShiftOut, coefficientAdjustmentOut, i1, i2, i3] using
    Arithmetic.subGates_act hwidth (shiftRight_disjoint hwidth)
      hcarry3 hscratch3

theorem subTRightOut_of_control_zero {width i : Nat}
    (hcontrol : i.testBit (controlWire width) = false) :
    subTRightOut width i = i := by
  simp only [subTRightOut, Arithmetic.placedSubTargetValue,
    Arithmetic.placedSubSignValue, hcontrol, Bool.false_eq_true, if_false,
    writeField_read]
  rw [← readField_one, writeField_read]

theorem coefficientXorOut_of_control_zero {n width i : Nat}
    (hcontrol : i.testBit (controlWire width) = false) :
    coefficientXorOut n width i = i := by
  simp [coefficientXorOut, bitValue, hcontrol, writeField_read]

theorem subRPrimeRightOut_of_control_zero {width i : Nat}
    (hcontrol : i.testBit (controlWire width) = false) :
    subRPrimeRightOut width i = i := by
  simp only [subRPrimeRightOut, Arithmetic.placedSubTargetValue,
    Arithmetic.placedSubSignValue, hcontrol, Bool.false_eq_true, if_false,
    writeField_read]
  rw [← readField_one, writeField_read]

theorem subShiftOut_of_control_zero {width i : Nat}
    (hcontrol : i.testBit (controlWire width) = false) :
    subShiftOut width i = i := by
  simp only [subShiftOut, Arithmetic.placedSubTargetValue,
    Arithmetic.placedSubSignValue, hcontrol, Bool.false_eq_true, if_false,
    writeField_read]
  rw [← readField_one, writeField_read]

theorem coefficientAdjustmentOut_of_control_zero {n width i : Nat}
    (hcontrol : i.testBit (controlWire width) = false) :
    coefficientAdjustmentOut n width i = i := by
  rw [coefficientAdjustmentOut, subTRightOut_of_control_zero hcontrol,
    coefficientXorOut_of_control_zero hcontrol,
    subRPrimeRightOut_of_control_zero hcontrol,
    subShiftOut_of_control_zero hcontrol]

theorem coefficientAdjustment_act_of_control_zero {n width i : Nat}
    (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hcontrol : i.testBit (controlWire width) = false) :
    actGates (coefficientAdjustment n width) i = i := by
  rw [coefficientAdjustment_act hwidth hcarry hscratch,
    coefficientAdjustmentOut_of_control_zero hcontrol]

theorem coefficientAdjustment_endpoint_of_control_zero {n width i : Nat}
    (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hcontrol : i.testBit (controlWire width) = false) :
    readField (actGates (coefficientAdjustment n width) i)
      (rightOffset width) width = readField i (rightOffset width) width := by
  rw [coefficientAdjustment_act_of_control_zero hwidth hcarry hscratch
    hcontrol]

theorem coefficientAdjustment_endpoint_of_control_one
    {n width i : Nat}
    (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hcontrol : i.testBit (controlWire width) = true)
    (hn : n < 2 ^ width)
    (hright : readField i (rightOffset width) width =
      1 + readField i lenTOffset width)
    (hrPrime : readField i (lenQOffset width) width ≤ n)
    (hshift : readField i (shiftOffset width) width ≤
      n - readField i (lenQOffset width) width) :
    readField (actGates (coefficientAdjustment n width) i)
        (rightOffset width) width =
      n - readField i (lenQOffset width) width -
        readField i (shiftOffset width) width := by
  let i1 := subTRightOut width i
  let i2 := coefficientXorOut n width i1
  let i3 := subRPrimeRightOut width i2
  have hcontrol1 : i1.testBit (controlWire width) = true := by
    simp only [i1, subTRightOut]
    rw [testBit_writeField_outside (Or.inl (by
      simp [signWire, controlWire])),
      testBit_writeField_outside (Or.inr (by
        simp [rightOffset, controlWire]
        omega)), hcontrol]
  have hcontrolValue1 : bitValue i1 (controlWire width) = 1 := by
    unfold bitValue
    rw [hcontrol1]
    rfl
  have ht1 : readField i1 lenTOffset width =
      readField i lenTOffset width := by
    simp only [i1, subTRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lenTOffset, signWire]
      omega)), readField_writeField_of_disjoint (Or.inr (by
        simp [lenTOffset, rightOffset]
        omega))]
  have hrPrime1 : readField i1 (lenQOffset width) width =
      readField i (lenQOffset width) width := by
    simp only [i1, subTRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lenQOffset, signWire]
      omega)), readField_writeField_of_disjoint (Or.inr (by
        simp [lenQOffset, rightOffset]
        omega))]
  have hshift1 : readField i1 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    simp only [i1, subTRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [shiftOffset, signWire]
      omega)), readField_writeField_of_disjoint (Or.inr (by
        simp [shiftOffset, rightOffset]
        omega))]
  have hright1 : readField i1 (rightOffset width) width = 1 := by
    simp only [i1, subTRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [rightOffset, signWire]
      omega)), readField_writeField_self
      (placedSubTargetValue_lt width lenTOffset (rightOffset width)
        (controlWire width) i)]
    simp only [Arithmetic.placedSubTargetValue, hcontrol, if_true]
    rw [Adder.difference_eq_sub_of_le
      (readField_lt i lenTOffset width)
      (readField_lt i (rightOffset width) width) (by omega)]
    omega
  have hxorFit :
      readField i1 (rightOffset width) width ^^^
          bitValue i1 (controlWire width) * coefficientAdjustmentConstant n <
        2 ^ width := by
    rw [hright1, hcontrolValue1, Nat.one_mul]
    simp only [coefficientAdjustmentConstant]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    exact hn
  have hright2 : readField i2 (rightOffset width) width = n := by
    simp only [i2, coefficientXorOut]
    rw [readField_writeField_self hxorFit, hright1, hcontrolValue1,
      Nat.one_mul]
    simp only [coefficientAdjustmentConstant]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hcontrol2 : i2.testBit (controlWire width) = true := by
    simp only [i2, coefficientXorOut]
    rw [testBit_writeField_outside (Or.inr (by
      simp [rightOffset, controlWire]
      omega)), hcontrol1]
  have hrPrime2 : readField i2 (lenQOffset width) width =
      readField i (lenQOffset width) width := by
    simp only [i2, coefficientXorOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lenQOffset, rightOffset]
      omega)), hrPrime1]
  have hshift2 : readField i2 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    simp only [i2, coefficientXorOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [shiftOffset, rightOffset]
      omega)), hshift1]
  have hcontrol3 : i3.testBit (controlWire width) = true := by
    simp only [i3, subRPrimeRightOut]
    rw [testBit_writeField_outside (Or.inl (by
      simp [signWire, controlWire])),
      testBit_writeField_outside (Or.inr (by
        simp [rightOffset, controlWire]
        omega)), hcontrol2]
  have hshift3 : readField i3 (shiftOffset width) width =
      readField i (shiftOffset width) width := by
    simp only [i3, subRPrimeRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [shiftOffset, signWire]
      omega)), readField_writeField_of_disjoint (Or.inr (by
        simp [shiftOffset, rightOffset]
        omega)), hshift2]
  have hright3 : readField i3 (rightOffset width) width =
      n - readField i (lenQOffset width) width := by
    simp only [i3, subRPrimeRightOut]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [rightOffset, signWire]
      omega)), readField_writeField_self
      (placedSubTargetValue_lt width (lenQOffset width) (rightOffset width)
        (controlWire width) i2)]
    simp only [Arithmetic.placedSubTargetValue, hcontrol2, if_true,
      hrPrime2, hright2]
    rw [Adder.difference_eq_sub_of_le
      (readField_lt i (lenQOffset width) width) hn hrPrime]
  rw [coefficientAdjustment_act hwidth hcarry hscratch]
  change readField (subShiftOut width i3) (rightOffset width) width = _
  rw [subShiftOut_right]
  simp only [Arithmetic.placedSubTargetValue, hcontrol3, if_true,
    hshift3, hright3]
  rw [Adder.difference_eq_sub_of_le
    (readField_lt i (shiftOffset width) width)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn) hshift]

theorem remainderPrepare_endpoints_mod {n width i : Nat}
    (hwidth : 0 < width)
    (hleft : readField i (leftOffset width) width = 0)
    (hright : readField i (rightOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (actGates (remainderPrepare n width) i)
        (leftOffset width) width =
        (readField i lenTOffset width +
          readField i (lenQOffset width) width + 3) % 2 ^ width ∧
      readField (actGates (remainderPrepare n width) i)
        (rightOffset width) width =
        (n + 1 +
          (2 ^ width - readField i (shiftOffset width) width)) % 2 ^ width := by
  rw [remainderPrepare_act hwidth hleft hright hcarry hscratch]
  exact remainderOut_endpoints_mod hcontrol

theorem remainderPrepare_endpoints {n width i : Nat} (hwidth : 0 < width)
    (hleft : readField i (leftOffset width) width = 0)
    (hright : readField i (rightOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hn : n + 1 < 2 ^ width)
    (hsum : 3 + readField i (lenQOffset width) width +
      readField i lenTOffset width < 2 ^ width)
    (hshift : readField i (shiftOffset width) width ≤ n + 1)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (actGates (remainderPrepare n width) i)
        (leftOffset width) width =
        3 + readField i (lenQOffset width) width +
          readField i lenTOffset width ∧
      readField (actGates (remainderPrepare n width) i)
        (rightOffset width) width =
        n + 1 - readField i (shiftOffset width) width := by
  rw [remainderPrepare_act hwidth hleft hright hcarry hscratch]
  exact remainderOut_endpoints hn hsum hshift hcontrol

theorem swapPrepare_endpoint {width i : Nat} (hwidth : 0 < width)
    (hleft : readField i (leftOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (htwo : 2 < 2 ^ width)
    (hsum : 2 + readField i (lenQOffset width) width +
      readField i lenTOffset width < 2 ^ width)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (actGates (swapPrepare width) i)
      (leftOffset width) width =
        2 + readField i (lenQOffset width) width +
          readField i lenTOffset width := by
  rw [swapPrepare_act hwidth hleft hcarry hscratch]
  exact swapOut_endpoint htwo hsum hcontrol

theorem coefficientPrepare_endpoint {width i : Nat} (hwidth : 0 < width)
    (hright : readField i (rightOffset width) width = 0)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false)
    (hone : 1 < 2 ^ width)
    (hsum : 1 + readField i lenTOffset width < 2 ^ width)
    (hcontrol : i.testBit (controlWire width) = true) :
    readField (actGates (coefficientPrepare width) i)
      (rightOffset width) width = 1 + readField i lenTOffset width := by
  rw [coefficientPrepare_act hwidth hright hcarry hscratch]
  exact coefficientOut_right hone hsum hcontrol

theorem coefficientAdjustment_length (n width : Nat) :
    (coefficientAdjustment n width).length =
      30 * width + 3 +
        (controlledXorGates (controlWire width) (rightOffset width) width
          (coefficientAdjustmentConstant n)).length := by
  simp [coefficientAdjustment, subTRight, subRPrimeRight, subShiftRight,
    Arithmetic.subGates_length]
  omega

theorem coefficientAdjustment_length_le (n width : Nat) :
    (coefficientAdjustment n width).length ≤ 31 * width + 3 := by
  rw [coefficientAdjustment_length]
  have hlength := controlledXorGates_length_le (controlWire width)
    (rightOffset width) (coefficientAdjustmentConstant n) width
  omega

theorem coefficientAdjustment_ccx (n width : Nat) :
    (coefficientAdjustment n width).countP RGate.isCcx = 30 * width + 3 := by
  simp [coefficientAdjustment, subTRight, subRPrimeRight, subShiftRight,
    Arithmetic.subGates_ccx, controlledXorGates_ccx]
  omega

theorem coefficientAdjustment_cx (n width : Nat) :
    (coefficientAdjustment n width).countP RGate.isCx =
      (controlledXorGates (controlWire width) (rightOffset width) width
        (coefficientAdjustmentConstant n)).length := by
  simp [coefficientAdjustment, subTRight, subRPrimeRight, subShiftRight,
    Arithmetic.subGates_cx, controlledXorGates_cx]

theorem coefficientAdjustment_cx_le (n width : Nat) :
    (coefficientAdjustment n width).countP RGate.isCx ≤ width := by
  rw [coefficientAdjustment_cx]
  exact controlledXorGates_length_le (controlWire width)
    (rightOffset width) (coefficientAdjustmentConstant n) width

theorem remainder_cleanup_prepare {n width i : Nat} (hwidth : 0 < width) :
    actGates (remainderCleanup n width)
      (actGates (remainderPrepare n width) i) = i := by
  exact actGates_reverse (w := (layout width).width)
    (remainderPrepare_wellFormed hwidth) i

theorem swap_cleanup_prepare {width i : Nat} (hwidth : 0 < width) :
    actGates (swapCleanup width)
      (actGates (swapPrepare width) i) = i := by
  exact actGates_reverse (w := (layout width).width)
    (swapPrepare_wellFormed hwidth) i

theorem coefficient_cleanup_prepare {width i : Nat} (hwidth : 0 < width) :
    actGates (coefficientCleanup width)
      (actGates (coefficientPrepare width) i) = i := by
  exact actGates_reverse (w := (layout width).width)
    (coefficientPrepare_wellFormed hwidth) i

theorem coefficientAdjustment_cleanup_prepare {n width i : Nat}
    (hwidth : 0 < width) :
    actGates (coefficientAdjustmentCleanup n width)
      (actGates (coefficientAdjustment n width) i) = i := by
  exact actGates_reverse (w := (layout width).width)
    (coefficientAdjustment_wellFormed hwidth) i

end EndpointPrep
end Euclid
end VQ
