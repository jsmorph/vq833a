/-
Physical layout and component placement for one Algorithm 3 step.
-/
import VQ.Euclid.EndpointPrep
import VQ.Euclid.Increment
import VQ.Euclid.IntervalBigEndianNoSign
import VQ.Euclid.IntervalNoSign
import VQ.Euclid.Phase
import VQ.Euclid.PrunedSelectSwap
import VQ.Euclid.Shift
import VQ.Euclid.SwapLength
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace StepLayout

open Reversible

def selectorWidth (lengthWidth shiftWidth : Nat) : Nat :=
  max lengthWidth shiftWidth

def auxWidth (lengthWidth shiftWidth : Nat) : Nat :=
  2 * lengthWidth + selectorWidth lengthWidth shiftWidth + 12

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  VQ.Euclid.layout n lengthWidth shiftWidth (auxWidth lengthWidth shiftWidth)

def work1Offset : Nat := 0
def work2Offset (n : Nat) : Nat := workWidth n
def lenTOffset (n : Nat) : Nat := 2 * workWidth n
def lenQOffset (n lengthWidth : Nat) : Nat :=
  2 * workWidth n + lengthWidth
def lenRPrimeOffset (n lengthWidth : Nat) : Nat :=
  2 * workWidth n + 2 * lengthWidth
def shiftOffset (n lengthWidth : Nat) : Nat :=
  2 * workWidth n + 3 * lengthWidth
def phase1Wire (n lengthWidth shiftWidth : Nat) : Nat :=
  shiftOffset n lengthWidth + shiftWidth
def phase2Wire (n lengthWidth shiftWidth : Nat) : Nat :=
  phase1Wire n lengthWidth shiftWidth + 1
def iterWire (n lengthWidth shiftWidth : Nat) : Nat :=
  phase1Wire n lengthWidth shiftWidth + 2
def signWire (n lengthWidth shiftWidth : Nat) : Nat :=
  phase1Wire n lengthWidth shiftWidth + 3
def controlWire (n lengthWidth shiftWidth : Nat) : Nat :=
  phase1Wire n lengthWidth shiftWidth + 4
def auxOffset (n lengthWidth shiftWidth : Nat) : Nat :=
  phase1Wire n lengthWidth shiftWidth + 5

def leftOffset (n lengthWidth shiftWidth : Nat) : Nat :=
  auxOffset n lengthWidth shiftWidth
def rightOffset (n lengthWidth shiftWidth : Nat) : Nat :=
  auxOffset n lengthWidth shiftWidth + lengthWidth
def carryWire (n lengthWidth shiftWidth : Nat) : Nat :=
  auxOffset n lengthWidth shiftWidth + 2 * lengthWidth
def accumulatorWire (n lengthWidth shiftWidth : Nat) : Nat :=
  carryWire n lengthWidth shiftWidth + 1
def leftFlagWire (n lengthWidth shiftWidth : Nat) : Nat :=
  carryWire n lengthWidth shiftWidth + 2
def rightFlagWire (n lengthWidth shiftWidth : Nat) : Nat :=
  carryWire n lengthWidth shiftWidth + 3
def poolOffset (n lengthWidth shiftWidth : Nat) : Nat :=
  carryWire n lengthWidth shiftWidth + 4
def cellScratchWire (n lengthWidth shiftWidth : Nat) : Nat :=
  poolOffset n lengthWidth shiftWidth + selectorWidth lengthWidth shiftWidth
def zeroQWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 1
def zeroRPrimeWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 2
def zeroShiftWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 3
def conditionWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 4
def temporaryWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 5
def plusWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 6
def minusWire (n lengthWidth shiftWidth : Nat) : Nat :=
  cellScratchWire n lengthWidth shiftWidth + 7

theorem layout_width (n lengthWidth shiftWidth : Nat) :
    (layout n lengthWidth shiftWidth).width =
      auxOffset n lengthWidth shiftWidth + auxWidth lengthWidth shiftWidth := by
  simp [layout, VQ.Euclid.layout, Layout.width, auxOffset, phase1Wire,
    shiftOffset]
  omega

def intervalWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [work1Offset, work2Offset n,
    leftOffset n lengthWidth shiftWidth,
    rightOffset n lengthWidth shiftWidth,
    controlWire n lengthWidth shiftWidth,
    signWire n lengthWidth shiftWidth,
    carryWire n lengthWidth shiftWidth,
    accumulatorWire n lengthWidth shiftWidth,
    leftFlagWire n lengthWidth shiftWidth,
    rightFlagWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth,
    cellScratchWire n lengthWidth shiftWidth]

def remainderIntervalWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [work2Offset n, work1Offset,
    leftOffset n lengthWidth shiftWidth,
    rightOffset n lengthWidth shiftWidth,
    controlWire n lengthWidth shiftWidth,
    signWire n lengthWidth shiftWidth,
    carryWire n lengthWidth shiftWidth,
    accumulatorWire n lengthWidth shiftWidth,
    leftFlagWire n lengthWidth shiftWidth,
    rightFlagWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth,
    cellScratchWire n lengthWidth shiftWidth]

def ownershipWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [work1Offset, work2Offset n,
    lenTOffset n, lenRPrimeOffset n lengthWidth,
    controlWire n lengthWidth shiftWidth,
    signWire n lengthWidth shiftWidth,
    carryWire n lengthWidth shiftWidth,
    accumulatorWire n lengthWidth shiftWidth,
    leftFlagWire n lengthWidth shiftWidth,
    rightFlagWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth,
    cellScratchWire n lengthWidth shiftWidth]

def endpointWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [lenTOffset n, lenQOffset n lengthWidth,
    shiftOffset n lengthWidth,
    leftOffset n lengthWidth shiftWidth,
    rightOffset n lengthWidth shiftWidth,
    controlWire n lengthWidth shiftWidth,
    carryWire n lengthWidth shiftWidth,
    conditionWire n lengthWidth shiftWidth,
    cellScratchWire n lengthWidth shiftWidth]

def coefficientAdjustmentWiring
    (n lengthWidth shiftWidth : Nat) : Wiring :=
  [lenTOffset n, lenRPrimeOffset n lengthWidth,
    shiftOffset n lengthWidth,
    leftOffset n lengthWidth shiftWidth,
    rightOffset n lengthWidth shiftWidth,
    phase2Wire n lengthWidth shiftWidth,
    carryWire n lengthWidth shiftWidth,
    conditionWire n lengthWidth shiftWidth,
    cellScratchWire n lengthWidth shiftWidth]

def shiftWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [shiftOffset n lengthWidth,
    plusWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth,
    work2Offset n,
    minusWire n lengthWidth shiftWidth]

def quotientWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [lenQOffset n lengthWidth,
    controlWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth]

def phaseWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [phase1Wire n lengthWidth shiftWidth,
    phase2Wire n lengthWidth shiftWidth,
    signWire n lengthWidth shiftWidth,
    lenQOffset n lengthWidth,
    lenRPrimeOffset n lengthWidth,
    shiftOffset n lengthWidth,
    zeroQWire n lengthWidth shiftWidth,
    zeroRPrimeWire n lengthWidth shiftWidth,
    zeroShiftWire n lengthWidth shiftWidth,
    conditionWire n lengthWidth shiftWidth,
    temporaryWire n lengthWidth shiftWidth,
    poolOffset n lengthWidth shiftWidth]

def placed (L : Layout) (W : Wiring) (gs : List RGate) : List RGate :=
  gs.map (RGate.map (place L W))

def intervalGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Interval.layout (workWidth n) lengthWidth)
    (intervalWiring n lengthWidth shiftWidth)
    (Interval.gates (workWidth n) lengthWidth)

def intervalReverseGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (intervalGates n lengthWidth shiftWidth).reverse

def intervalNoSignGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Interval.layout (workWidth n) lengthWidth)
    (intervalWiring n lengthWidth shiftWidth)
    (Interval.noSignGates (workWidth n) lengthWidth)

def intervalNoSignReverseGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  (intervalNoSignGates n lengthWidth shiftWidth).reverse

def remainderIntervalGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Interval.layout (workWidth n) lengthWidth)
    (remainderIntervalWiring n lengthWidth shiftWidth)
    (IntervalBigEndian.gates (workWidth n) lengthWidth)

def remainderIntervalReverseGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  (remainderIntervalGates n lengthWidth shiftWidth).reverse

def remainderIntervalNoSignGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Interval.layout (workWidth n) lengthWidth)
    (remainderIntervalWiring n lengthWidth shiftWidth)
    (IntervalBigEndian.noSignGates (workWidth n) lengthWidth)

def remainderIntervalNoSignReverseGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  (remainderIntervalNoSignGates n lengthWidth shiftWidth).reverse

def selectSwapGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Interval.layout (workWidth n) lengthWidth)
    (intervalWiring n lengthWidth shiftWidth)
    (PrunedSelectSwap.gates (workWidth n) lengthWidth)

def remainderPrepareGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (EndpointPrep.layout lengthWidth)
    (endpointWiring n lengthWidth shiftWidth)
    (EndpointPrep.remainderPrepare n lengthWidth)

def remainderCleanupGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (remainderPrepareGates n lengthWidth shiftWidth).reverse

def swapPrepareGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (EndpointPrep.layout lengthWidth)
    (endpointWiring n lengthWidth shiftWidth)
    (EndpointPrep.swapPrepare lengthWidth)

def swapCleanupGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (swapPrepareGates n lengthWidth shiftWidth).reverse

def coefficientBasePrepareGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (EndpointPrep.layout lengthWidth)
    (endpointWiring n lengthWidth shiftWidth)
    (EndpointPrep.coefficientPrepare lengthWidth)

def coefficientAdjustmentGates
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (EndpointPrep.layout lengthWidth)
    (coefficientAdjustmentWiring n lengthWidth shiftWidth)
    (EndpointPrep.coefficientAdjustment n lengthWidth)

def coefficientPrepareGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  coefficientBasePrepareGates n lengthWidth shiftWidth ++
    coefficientAdjustmentGates n lengthWidth shiftWidth

def coefficientCleanupGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (coefficientPrepareGates n lengthWidth shiftWidth).reverse

def shiftGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Shift.layout (workWidth n) shiftWidth)
    (shiftWiring n lengthWidth shiftWidth)
    (Shift.gates (workWidth n) shiftWidth)

def quotientIncrementGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Increment.layout lengthWidth)
    (quotientWiring n lengthWidth shiftWidth)
    (Increment.circuit lengthWidth).gates

def quotientDecrementGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (quotientIncrementGates n lengthWidth shiftWidth).reverse

def phaseGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Phase.layout lengthWidth shiftWidth)
    (phaseWiring n lengthWidth shiftWidth)
    (Phase.gates lengthWidth shiftWidth)

def phaseSelectGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Phase.layout lengthWidth shiftWidth)
    (phaseWiring n lengthWidth shiftWidth)
    (Phase.selectGates lengthWidth shiftWidth)

def phaseUnselectGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Phase.layout lengthWidth shiftWidth)
    (phaseWiring n lengthWidth shiftWidth)
    (Phase.unselectGates lengthWidth shiftWidth)

def rPrimeZeroSelectorGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  Placed.selectorGates (encodedZero lengthWidth) lengthWidth
    (lenRPrimeOffset n lengthWidth)
    (zeroRPrimeWire n lengthWidth shiftWidth)
    (poolOffset n lengthWidth shiftWidth)

def ownershipSelectGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Phase.layout lengthWidth shiftWidth)
    (phaseWiring n lengthWidth shiftWidth)
    (Phase.ownershipSelectGates lengthWidth shiftWidth)

def ownershipUnselectGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (Phase.layout lengthWidth shiftWidth)
    (phaseWiring n lengthWidth shiftWidth)
    (Phase.ownershipUnselectGates lengthWidth shiftWidth)

def ownershipFullSwapGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (SwapLength.layout (workWidth n) lengthWidth)
    (ownershipWiring n lengthWidth shiftWidth)
    (SwapLength.fullSwap (workWidth n) lengthWidth)

def ownershipUpperGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (SwapLength.layout (workWidth n) lengthWidth)
    (ownershipWiring n lengthWidth shiftWidth)
    (SwapLength.upperBlock n (workWidth n) lengthWidth)

def ownershipLowerGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  placed (SwapLength.layout (workWidth n) lengthWidth)
    (ownershipWiring n lengthWidth shiftWidth)
    (SwapLength.lowerBlock n (workWidth n) lengthWidth)

def ownershipGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  ownershipFullSwapGates n lengthWidth shiftWidth ++
    ownershipUpperGates n lengthWidth shiftWidth ++
    ownershipLowerGates n lengthWidth shiftWidth

theorem interval_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Interval.layout (workWidth n) lengthWidth)
      (intervalWiring n lengthWidth shiftWidth) := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j k hj hk hne
  simp [intervalWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Interval.layout, Layout.size, intervalWiring, work1Offset,
      work2Offset, leftOffset, rightOffset, controlWire, signWire,
      carryWire, accumulatorWire, leftFlagWire, rightFlagWire, poolOffset,
      cellScratchWire, auxOffset, phase1Wire, shiftOffset, selectorWidth] <;>
    omega

theorem remainderInterval_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Interval.layout (workWidth n) lengthWidth)
      (remainderIntervalWiring n lengthWidth shiftWidth) := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j k hj hk hne
  simp [remainderIntervalWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Interval.layout, Layout.size, remainderIntervalWiring,
      work1Offset, work2Offset, leftOffset, rightOffset, controlWire,
      signWire, carryWire, accumulatorWire, leftFlagWire, rightFlagWire,
      poolOffset, cellScratchWire, auxOffset, phase1Wire, shiftOffset,
      selectorWidth] <;>
    omega

theorem ownership_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (SwapLength.layout (workWidth n) lengthWidth)
      (ownershipWiring n lengthWidth shiftWidth) := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j k hj hk hne
  simp [ownershipWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [SwapLength.layout, Interval.layout, Layout.size,
      ownershipWiring, work1Offset, work2Offset, lenTOffset, lenRPrimeOffset,
      controlWire, signWire, carryWire, accumulatorWire, leftFlagWire,
      rightFlagWire, poolOffset, cellScratchWire, auxOffset, phase1Wire,
      shiftOffset, selectorWidth] <;>
    omega

theorem endpoint_disjoint (n lengthWidth shiftWidth : Nat)
    (hwidths : lengthWidth ≤ shiftWidth) :
    Wiring.Disjoint (EndpointPrep.layout lengthWidth)
      (endpointWiring n lengthWidth shiftWidth) := by
  intro j k hj hk hne
  simp [endpointWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [EndpointPrep.layout, Layout.size, endpointWiring, lenTOffset,
      lenQOffset, shiftOffset, phase1Wire, conditionWire, controlWire,
      auxOffset, leftOffset, rightOffset, carryWire, poolOffset,
      cellScratchWire, selectorWidth] <;>
    omega

theorem coefficientAdjustment_disjoint (n lengthWidth shiftWidth : Nat)
    (hwidths : lengthWidth ≤ shiftWidth) :
    Wiring.Disjoint (EndpointPrep.layout lengthWidth)
      (coefficientAdjustmentWiring n lengthWidth shiftWidth) := by
  intro j k hj hk hne
  simp [coefficientAdjustmentWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [EndpointPrep.layout, Layout.size, coefficientAdjustmentWiring,
      lenTOffset, lenRPrimeOffset, shiftOffset, phase1Wire, phase2Wire,
      conditionWire, auxOffset, leftOffset, rightOffset, carryWire,
      poolOffset, cellScratchWire, selectorWidth] <;>
    omega

theorem shift_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Shift.layout (workWidth n) shiftWidth)
      (shiftWiring n lengthWidth shiftWidth) := by
  have hshift : shiftWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j k hj hk hne
  simp [shiftWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Shift.layout, Layout.size, shiftWiring, work2Offset,
      shiftOffset, phase1Wire, auxOffset, carryWire, poolOffset,
      cellScratchWire, plusWire, minusWire, selectorWidth] <;>
    omega

theorem quotient_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Increment.layout lengthWidth)
      (quotientWiring n lengthWidth shiftWidth) := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j k hj hk hne
  simp [quotientWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Increment.layout, Layout.size, quotientWiring, lenQOffset,
      controlWire, poolOffset, auxOffset, phase1Wire, shiftOffset,
      carryWire, selectorWidth] <;>
    omega

theorem phase_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Phase.layout lengthWidth shiftWidth)
      (phaseWiring n lengthWidth shiftWidth) := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  have hshift : shiftWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j k hj hk hne
  simp [phaseWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Phase.layout, Layout.size, phaseWiring, phase1Wire, phase2Wire,
      signWire, lenQOffset, lenRPrimeOffset, shiftOffset, zeroQWire,
      zeroRPrimeWire, zeroShiftWire, conditionWire, temporaryWire, poolOffset,
      cellScratchWire, auxOffset, carryWire, Phase.poolWidth, selectorWidth] <;>
    omega

theorem rPrimeZeroSelector_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Selector.layout lengthWidth)
      (Placed.selectorWiring (lenRPrimeOffset n lengthWidth)
        (zeroRPrimeWire n lengthWidth shiftWidth)
        (poolOffset n lengthWidth shiftWidth)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Selector.layout, Layout.size, Placed.selectorWiring,
      lenRPrimeOffset, zeroRPrimeWire, poolOffset, cellScratchWire,
      carryWire, auxOffset, phase1Wire, shiftOffset, selectorWidth] <;>
    omega

theorem rPrimeZeroSelector_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Selector.layout lengthWidth).length →
      (Placed.selectorWiring (lenRPrimeOffset n lengthWidth)
        (zeroRPrimeWire n lengthWidth shiftWidth)
        (poolOffset n lengthWidth shiftWidth)).getD j 0 +
          (Selector.layout lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Selector.layout, Layout.size, Placed.selectorWiring,
      layout_width, lenRPrimeOffset, zeroRPrimeWire, poolOffset,
      cellScratchWire, carryWire, auxOffset, phase1Wire, shiftOffset,
      auxWidth, selectorWidth] <;>
    omega

theorem interval_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Interval.layout (workWidth n) lengthWidth).length →
      (intervalWiring n lengthWidth shiftWidth).getD j 0 +
          (Interval.layout (workWidth n) lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j hj
  simp [Interval.layout] at hj
  interval_cases j <;>
    simp_all [Interval.layout, Layout.size, intervalWiring, layout_width,
      work1Offset, work2Offset, leftOffset, rightOffset, controlWire,
      signWire, carryWire, accumulatorWire, leftFlagWire, rightFlagWire,
      poolOffset, cellScratchWire, auxOffset, auxWidth, phase1Wire,
      shiftOffset, selectorWidth] <;>
    omega

theorem remainderInterval_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Interval.layout (workWidth n) lengthWidth).length →
      (remainderIntervalWiring n lengthWidth shiftWidth).getD j 0 +
          (Interval.layout (workWidth n) lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j hj
  simp [Interval.layout] at hj
  interval_cases j <;>
    simp_all [Interval.layout, Layout.size, remainderIntervalWiring,
      layout_width, work1Offset, work2Offset, leftOffset, rightOffset,
      controlWire, signWire, carryWire, accumulatorWire, leftFlagWire,
      rightFlagWire, poolOffset, cellScratchWire, auxOffset, auxWidth,
      phase1Wire, shiftOffset, selectorWidth] <;>
    omega

theorem ownership_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (SwapLength.layout (workWidth n) lengthWidth).length →
      (ownershipWiring n lengthWidth shiftWidth).getD j 0 +
          (SwapLength.layout (workWidth n) lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j hj
  simp [SwapLength.layout, Interval.layout] at hj
  interval_cases j <;>
    simp_all [SwapLength.layout, Interval.layout, Layout.size,
      ownershipWiring, layout_width, work1Offset, work2Offset, lenTOffset,
      lenRPrimeOffset, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, poolOffset, cellScratchWire, auxOffset,
      auxWidth, phase1Wire, shiftOffset, selectorWidth] <;>
    omega

theorem endpoint_bound (n lengthWidth shiftWidth : Nat)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (endpointWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size, endpointWiring, layout_width,
      lenTOffset, lenQOffset, shiftOffset, phase1Wire, conditionWire,
      controlWire, auxOffset, leftOffset, rightOffset, carryWire, poolOffset,
      cellScratchWire, auxWidth, selectorWidth] <;>
    omega

theorem coefficientAdjustment_bound (n lengthWidth shiftWidth : Nat)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (coefficientAdjustmentWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size, coefficientAdjustmentWiring,
      layout_width, lenTOffset, lenRPrimeOffset, shiftOffset, phase1Wire,
      phase2Wire, conditionWire, auxOffset, leftOffset, rightOffset,
      carryWire, poolOffset, cellScratchWire, auxWidth, selectorWidth] <;>
    omega

theorem shift_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Shift.layout (workWidth n) shiftWidth).length →
      (shiftWiring n lengthWidth shiftWidth).getD j 0 +
          (Shift.layout (workWidth n) shiftWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hshift : shiftWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j hj
  simp [Shift.layout] at hj
  interval_cases j <;>
    simp_all [Shift.layout, Layout.size, shiftWiring, layout_width,
      work2Offset, shiftOffset, phase1Wire, auxOffset, carryWire, poolOffset,
      cellScratchWire, plusWire, minusWire, auxWidth, selectorWidth] <;>
    omega

theorem quotient_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Increment.layout lengthWidth).length →
      (quotientWiring n lengthWidth shiftWidth).getD j 0 +
          (Increment.layout lengthWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  intro j hj
  simp [Increment.layout] at hj
  interval_cases j <;>
    simp_all [Increment.layout, Layout.size, quotientWiring, layout_width,
      lenQOffset, controlWire, poolOffset, auxOffset, phase1Wire,
      shiftOffset, carryWire, auxWidth, selectorWidth] <;>
    omega

theorem phase_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Phase.layout lengthWidth shiftWidth).length →
      (phaseWiring n lengthWidth shiftWidth).getD j 0 +
          (Phase.layout lengthWidth shiftWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hlength : lengthWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  have hshift : shiftWidth ≤ selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j hj
  simp [Phase.layout] at hj
  interval_cases j <;>
    simp_all [Phase.layout, Layout.size, phaseWiring, layout_width,
      phase1Wire, phase2Wire, signWire, lenQOffset, lenRPrimeOffset,
      shiftOffset, zeroQWire, zeroRPrimeWire, zeroShiftWire, conditionWire,
      temporaryWire, poolOffset, cellScratchWire, auxOffset, carryWire,
      auxWidth, Phase.poolWidth, selectorWidth] <;>
    omega

theorem placed_wellFormed
    {L : Layout} {W : Wiring} {gs : List RGate}
    {n lengthWidth shiftWidth : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hbound : ∀ j, j < L.length →
      W.getD j 0 + L.size j ≤ (layout n lengthWidth shiftWidth).width)
    (hwf : ∀ g ∈ gs, g.wellFormed L.width = true) :
    (placed L W gs).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  exact wellFormed_placeGates hd hlen hbound hwf

theorem placed_length (L : Layout) (W : Wiring) (gs : List RGate) :
    (placed L W gs).length = gs.length := by
  simp [placed]

theorem placed_ccx (L : Layout) (W : Wiring) (gs : List RGate) :
    (placed L W gs).countP RGate.isCcx = gs.countP RGate.isCcx := by
  rw [placed, countP_map_gates (fun g => RGate.isCcx_map _ g)]

theorem placed_cx (L : Layout) (W : Wiring) (gs : List RGate) :
    (placed L W gs).countP RGate.isCx = gs.countP RGate.isCx := by
  rw [placed, countP_map_gates (fun g => RGate.isCx_map _ g)]

theorem intervalGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (intervalGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (interval_disjoint n lengthWidth shiftWidth)
    (by simp [Interval.layout, intervalWiring])
    (interval_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Interval.circuit_wellFormed (workWidth n) lengthWidth) hg

theorem intervalReverseGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (intervalReverseGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [intervalReverseGates, intervalGates_wellFormed, List.all_reverse]

theorem intervalNoSignGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (intervalNoSignGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (interval_disjoint n lengthWidth shiftWidth)
    (by simp [Interval.layout, intervalWiring])
    (interval_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Interval.noSignCircuit_wellFormed
      (workWidth n) lengthWidth) hg

theorem intervalNoSignReverseGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (intervalNoSignReverseGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [intervalNoSignReverseGates, intervalNoSignGates_wellFormed,
    List.all_reverse]

theorem remainderIntervalGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed
    (remainderInterval_disjoint n lengthWidth shiftWidth)
    (by simp [Interval.layout, remainderIntervalWiring])
    (remainderInterval_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (IntervalBigEndian.circuit_wellFormed (workWidth n) lengthWidth) hg

theorem remainderIntervalReverseGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalReverseGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [remainderIntervalReverseGates,
    remainderIntervalGates_wellFormed, List.all_reverse]

theorem remainderIntervalNoSignGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalNoSignGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed
    (remainderInterval_disjoint n lengthWidth shiftWidth)
    (by simp [Interval.layout, remainderIntervalWiring])
    (remainderInterval_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (IntervalBigEndian.noSignCircuit_wellFormed
      (workWidth n) lengthWidth) hg

theorem remainderIntervalNoSignReverseGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalNoSignReverseGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [remainderIntervalNoSignReverseGates,
    remainderIntervalNoSignGates_wellFormed, List.all_reverse]

theorem selectSwapGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (selectSwapGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (interval_disjoint n lengthWidth shiftWidth)
    (by simp [Interval.layout, intervalWiring])
    (interval_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (PrunedSelectSwap.circuit_wellFormed (workWidth n) lengthWidth) hg

theorem remainderPrepareGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (remainderPrepareGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (endpoint_disjoint n lengthWidth shiftWidth hwidths)
    (by simp [EndpointPrep.layout, endpointWiring])
    (endpoint_bound n lengthWidth shiftWidth hwidths)
  intro g hg
  exact (List.all_eq_true.mp
    (EndpointPrep.remainderPrepare_wellFormed (n := n) hlength)) g hg

theorem remainderCleanupGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (remainderCleanupGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [remainderCleanupGates,
    remainderPrepareGates_wellFormed hlength hwidths, List.all_reverse]

theorem swapPrepareGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (swapPrepareGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (endpoint_disjoint n lengthWidth shiftWidth hwidths)
    (by simp [EndpointPrep.layout, endpointWiring])
    (endpoint_bound n lengthWidth shiftWidth hwidths)
  intro g hg
  exact (List.all_eq_true.mp
    (EndpointPrep.swapPrepare_wellFormed hlength)) g hg

theorem swapCleanupGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (swapCleanupGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [swapCleanupGates, swapPrepareGates_wellFormed hlength hwidths,
    List.all_reverse]

theorem coefficientBasePrepareGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (coefficientBasePrepareGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (endpoint_disjoint n lengthWidth shiftWidth hwidths)
    (by simp [EndpointPrep.layout, endpointWiring])
    (endpoint_bound n lengthWidth shiftWidth hwidths)
  intro g hg
  exact (List.all_eq_true.mp
    (EndpointPrep.coefficientPrepare_wellFormed hlength)) g hg

theorem coefficientAdjustmentGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (coefficientAdjustmentGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed
    (coefficientAdjustment_disjoint n lengthWidth shiftWidth hwidths)
    (by simp [EndpointPrep.layout, coefficientAdjustmentWiring])
    (coefficientAdjustment_bound n lengthWidth shiftWidth hwidths)
  intro g hg
  exact (List.all_eq_true.mp
    (EndpointPrep.coefficientAdjustment_wellFormed
      (n := n) hlength)) g hg

theorem coefficientPrepareGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (coefficientPrepareGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp only [coefficientPrepareGates, List.all_append, Bool.and_eq_true]
  exact ⟨coefficientBasePrepareGates_wellFormed hlength hwidths,
    coefficientAdjustmentGates_wellFormed hlength hwidths⟩

theorem coefficientCleanupGates_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (coefficientCleanupGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [coefficientCleanupGates,
    coefficientPrepareGates_wellFormed hlength hwidths, List.all_reverse]

theorem shiftGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (shiftGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (shift_disjoint n lengthWidth shiftWidth)
    (by simp [Shift.layout, shiftWiring])
    (shift_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Shift.circuit_wellFormed (workWidth n) shiftWidth) hg

theorem quotientIncrementGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (quotientIncrementGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (quotient_disjoint n lengthWidth shiftWidth)
    (by simp [Increment.layout, quotientWiring])
    (quotient_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem (Increment.circuit_wellFormed lengthWidth) hg

theorem quotientDecrementGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (quotientDecrementGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  simp [quotientDecrementGates, quotientIncrementGates_wellFormed,
    List.all_reverse]

theorem phaseGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (phaseGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (phase_disjoint n lengthWidth shiftWidth)
    (by simp [Phase.layout, phaseWiring])
    (phase_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Phase.circuit_wellFormed lengthWidth shiftWidth) hg

theorem phaseSelectGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (phaseSelectGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (phase_disjoint n lengthWidth shiftWidth)
    (by simp [Phase.layout, phaseWiring])
    (phase_bound n lengthWidth shiftWidth)
  intro g hg
  have h := Phase.circuit_wellFormed lengthWidth shiftWidth
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  have hselect : (Phase.selectGates lengthWidth shiftWidth).all
      (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
    simp [Phase.selectGates, h.2, h.1.2, h.1.1.2]
  exact (List.all_eq_true.mp hselect) g hg

theorem phaseUnselectGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (phaseUnselectGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (phase_disjoint n lengthWidth shiftWidth)
    (by simp [Phase.layout, phaseWiring])
    (phase_bound n lengthWidth shiftWidth)
  intro g hg
  have h := Phase.circuit_wellFormed lengthWidth shiftWidth
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  have hunselect : (Phase.unselectGates lengthWidth shiftWidth).all
      (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
    simp [Phase.unselectGates, h.2, h.1.2, h.1.1.2]
  exact (List.all_eq_true.mp hunselect) g hg

theorem rPrimeZeroSelectorGates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (rPrimeZeroSelectorGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  exact Placed.selector_wellFormed
    (rPrimeZeroSelector_disjoint n lengthWidth shiftWidth)
    (rPrimeZeroSelector_bound n lengthWidth shiftWidth)

theorem ownershipSelectGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (ownershipSelectGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (phase_disjoint n lengthWidth shiftWidth)
    (by simp [Phase.layout, phaseWiring])
    (phase_bound n lengthWidth shiftWidth)
  intro g hg
  have h := Phase.circuit_wellFormed lengthWidth shiftWidth
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  have hselect : (Phase.ownershipSelectGates lengthWidth shiftWidth).all
      (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
    simp [Phase.ownershipSelectGates, h.2, h.1.1.2]
  exact (List.all_eq_true.mp hselect) g hg

theorem ownershipUnselectGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (ownershipUnselectGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply placed_wellFormed (phase_disjoint n lengthWidth shiftWidth)
    (by simp [Phase.layout, phaseWiring])
    (phase_bound n lengthWidth shiftWidth)
  intro g hg
  have h := Phase.circuit_wellFormed lengthWidth shiftWidth
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  have hunselect :
      (Phase.ownershipUnselectGates lengthWidth shiftWidth).all
        (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
    simp [Phase.ownershipUnselectGates, h.2, h.1.1.2]
  exact (List.all_eq_true.mp hunselect) g hg

theorem ownershipGates_eq (n lengthWidth shiftWidth : Nat) :
    ownershipGates n lengthWidth shiftWidth =
      placed (SwapLength.layout (workWidth n) lengthWidth)
        (ownershipWiring n lengthWidth shiftWidth)
        (SwapLength.gates n (workWidth n) lengthWidth) := by
  simp [ownershipGates, ownershipFullSwapGates, ownershipUpperGates,
    ownershipLowerGates, placed, SwapLength.gates]

theorem ownershipGates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (ownershipGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  rw [ownershipGates_eq]
  apply placed_wellFormed (ownership_disjoint n lengthWidth shiftWidth)
    (by simp [SwapLength.layout, Interval.layout, ownershipWiring])
    (ownership_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth) hg

theorem intervalGates_length (n lengthWidth shiftWidth : Nat) :
    (intervalGates n lengthWidth shiftWidth).length =
      (Interval.gates (workWidth n) lengthWidth).length :=
  placed_length _ _ _

theorem intervalGates_ccx (n lengthWidth shiftWidth : Nat) :
    (intervalGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Interval.gates (workWidth n) lengthWidth).countP
        RGate.isCcx :=
  placed_ccx _ _ _

theorem intervalGates_cx (n lengthWidth shiftWidth : Nat) :
    (intervalGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Interval.gates (workWidth n) lengthWidth).countP
        RGate.isCx :=
  placed_cx _ _ _

theorem intervalNoSignGates_length (n lengthWidth shiftWidth : Nat) :
    (intervalNoSignGates n lengthWidth shiftWidth).length =
      (Interval.noSignGates (workWidth n) lengthWidth).length :=
  placed_length _ _ _

theorem intervalNoSignGates_ccx (n lengthWidth shiftWidth : Nat) :
    (intervalNoSignGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Interval.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCcx :=
  placed_ccx _ _ _

theorem intervalNoSignGates_cx (n lengthWidth shiftWidth : Nat) :
    (intervalNoSignGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Interval.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCx :=
  placed_cx _ _ _

theorem remainderIntervalGates_length (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalGates n lengthWidth shiftWidth).length =
      (IntervalBigEndian.gates (workWidth n) lengthWidth).length :=
  placed_length _ _ _

theorem remainderIntervalGates_ccx (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (IntervalBigEndian.gates (workWidth n) lengthWidth).countP
        RGate.isCcx :=
  placed_ccx _ _ _

theorem remainderIntervalGates_cx (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalGates n lengthWidth shiftWidth).countP RGate.isCx =
      (IntervalBigEndian.gates (workWidth n) lengthWidth).countP
        RGate.isCx :=
  placed_cx _ _ _

theorem remainderIntervalNoSignGates_length
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalNoSignGates n lengthWidth shiftWidth).length =
      (IntervalBigEndian.noSignGates (workWidth n) lengthWidth).length :=
  placed_length _ _ _

theorem remainderIntervalNoSignGates_ccx
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalNoSignGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (IntervalBigEndian.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCcx :=
  placed_ccx _ _ _

theorem remainderIntervalNoSignGates_cx
    (n lengthWidth shiftWidth : Nat) :
    (remainderIntervalNoSignGates n lengthWidth shiftWidth).countP RGate.isCx =
      (IntervalBigEndian.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCx :=
  placed_cx _ _ _

theorem selectSwapGates_length (n lengthWidth shiftWidth : Nat) :
    (selectSwapGates n lengthWidth shiftWidth).length =
      (PrunedSelectSwap.gates (workWidth n) lengthWidth).length :=
  placed_length _ _ _

theorem selectSwapGates_ccx (n lengthWidth shiftWidth : Nat) :
    (selectSwapGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (PrunedSelectSwap.gates (workWidth n) lengthWidth).countP RGate.isCcx :=
  placed_ccx _ _ _

theorem shiftGates_length (n lengthWidth shiftWidth : Nat) :
    (shiftGates n lengthWidth shiftWidth).length =
      (Shift.gates (workWidth n) shiftWidth).length :=
  placed_length _ _ _

theorem shiftGates_ccx (n lengthWidth shiftWidth : Nat) :
    (shiftGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Shift.gates (workWidth n) shiftWidth).countP RGate.isCcx :=
  placed_ccx _ _ _

theorem shiftGates_cx (n lengthWidth shiftWidth : Nat) :
    (shiftGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Shift.gates (workWidth n) shiftWidth).countP RGate.isCx :=
  placed_cx _ _ _

theorem quotientIncrementGates_length (n lengthWidth shiftWidth : Nat) :
    (quotientIncrementGates n lengthWidth shiftWidth).length =
      (Increment.circuit lengthWidth).gates.length :=
  placed_length _ _ _

theorem quotientIncrementGates_ccx (n lengthWidth shiftWidth : Nat) :
    (quotientIncrementGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Increment.circuit lengthWidth).gates.countP RGate.isCcx :=
  placed_ccx _ _ _

theorem quotientIncrementGates_cx (n lengthWidth shiftWidth : Nat) :
    (quotientIncrementGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Increment.circuit lengthWidth).gates.countP RGate.isCx :=
  placed_cx _ _ _

theorem phaseGates_length (n lengthWidth shiftWidth : Nat) :
    (phaseGates n lengthWidth shiftWidth).length =
      (Phase.gates lengthWidth shiftWidth).length :=
  placed_length _ _ _

theorem phaseGates_ccx (n lengthWidth shiftWidth : Nat) :
    (phaseGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Phase.gates lengthWidth shiftWidth).countP RGate.isCcx :=
  placed_ccx _ _ _

theorem phaseGates_cx (n lengthWidth shiftWidth : Nat) :
    (phaseGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Phase.gates lengthWidth shiftWidth).countP RGate.isCx :=
  placed_cx _ _ _

theorem rPrimeZeroSelectorGates_length
    (n lengthWidth shiftWidth : Nat) :
    (rPrimeZeroSelectorGates n lengthWidth shiftWidth).length =
      (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.length :=
  Placed.selector_length _ _ _ _ _

theorem rPrimeZeroSelectorGates_ccx
    (n lengthWidth shiftWidth : Nat) :
    (rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.countP
        RGate.isCcx :=
  Placed.selector_ccx _ _ _ _ _

theorem rPrimeZeroSelectorGates_cx
    (n lengthWidth shiftWidth : Nat) :
    (rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP RGate.isCx =
      (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.countP
        RGate.isCx :=
  Placed.selector_cx _ _ _ _ _

theorem ownershipGates_length (n lengthWidth shiftWidth : Nat) :
    (ownershipGates n lengthWidth shiftWidth).length =
      (SwapLength.gates n (workWidth n) lengthWidth).length := by
  rw [ownershipGates_eq]
  exact placed_length _ _ _

theorem ownershipGates_ccx (n lengthWidth shiftWidth : Nat) :
    (ownershipGates n lengthWidth shiftWidth).countP RGate.isCcx =
      (SwapLength.gates n (workWidth n) lengthWidth).countP RGate.isCcx := by
  rw [ownershipGates_eq]
  exact placed_ccx _ _ _

theorem ownershipGates_cx (n lengthWidth shiftWidth : Nat) :
    (ownershipGates n lengthWidth shiftWidth).countP RGate.isCx =
      (SwapLength.gates n (workWidth n) lengthWidth).countP RGate.isCx := by
  rw [ownershipGates_eq]
  exact placed_cx _ _ _

end StepLayout
end Euclid
end VQ
