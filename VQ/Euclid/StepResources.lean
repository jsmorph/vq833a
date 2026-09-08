/-
Syntax-derived resource bounds for one Euclidean step and a fixed schedule.
The one-step theorems inspect the component lists used by `Step.gates`.  The
fixed-round theorems count the identical list used by `Iteration.circuit`.
-/
import VQ.Circuit.Compose
import VQ.Euclid.Iteration

namespace VQ
namespace Euclid
namespace StepResources

open Reversible

def remainderPrepareGateBound (lengthWidth : Nat) : Nat :=
  32 * lengthWidth + 3

def swapPrepareGateBound (lengthWidth : Nat) : Nat :=
  21 * lengthWidth + 2

def coefficientAdjustmentXorLength (n lengthWidth : Nat) : Nat :=
  (controlledXorGates (EndpointPrep.controlWire lengthWidth)
    (EndpointPrep.rightOffset lengthWidth) lengthWidth
    (EndpointPrep.coefficientAdjustmentConstant n)).length

def coefficientPrepareGateBound (n lengthWidth : Nat) : Nat :=
  41 * lengthWidth + 4 + coefficientAdjustmentXorLength n lengthWidth

def remainderPrepareCcxBound (lengthWidth : Nat) : Nat :=
  30 * lengthWidth + 3

def swapPrepareCcxBound (lengthWidth : Nat) : Nat :=
  20 * lengthWidth + 2

def coefficientPrepareCcxBound (lengthWidth : Nat) : Nat :=
  40 * lengthWidth + 4

def coefficientPrepareCxBound (n lengthWidth : Nat) : Nat :=
  coefficientAdjustmentXorLength n lengthWidth

def phaseGateBound (lengthWidth shiftWidth : Nat) : Nat :=
  24 * lengthWidth + 16 * shiftWidth + 24

def phaseCcxBound (lengthWidth shiftWidth : Nat) : Nat :=
  12 * lengthWidth + 8 * shiftWidth + 4

def phaseCxBound (lengthWidth shiftWidth : Nat) : Nat :=
  24 * lengthWidth + 16 * shiftWidth + 16

/-- Upper bound on reversible gate-list length before `RGate.ccx` compilation.
`gateBound` counts each `RGate` once, while `compiledGateBound` includes the
two additional primitive gates emitted for each `RGate.ccx`. -/
def gateBound (n lengthWidth shiftWidth : Nat) : Nat :=
  let width := workWidth n
  2 * (9 * (width - 1) + 3 * Increment.lengthCost shiftWidth) +
    4 * remainderPrepareGateBound lengthWidth +
    2 * (width * (32 * lengthWidth + 23) + 1) +
    2 * (width * (32 * lengthWidth + 23)) +
    2 * swapPrepareGateBound lengthWidth +
    PrunedSelectSwap.gateBound width lengthWidth +
    2 * Increment.lengthCost lengthWidth +
    4 * coefficientPrepareGateBound n lengthWidth +
    2 * (2 * (lengthWidth - 2) + 1) +
    phaseGateBound lengthWidth shiftWidth +
    SwapLength.gateBound width lengthWidth + 73

def ccxBound (n lengthWidth shiftWidth : Nat) : Nat :=
  let width := workWidth n
  2 * (3 * (width - 1) + 3 * Increment.ccxCost shiftWidth) +
    4 * remainderPrepareCcxBound lengthWidth +
    4 * (width * (16 * lengthWidth + 11)) +
    2 * swapPrepareCcxBound lengthWidth +
    PrunedSelectSwap.ccxBound width lengthWidth +
    2 * Increment.ccxCost lengthWidth +
    4 * coefficientPrepareCcxBound lengthWidth +
    2 * (2 * (lengthWidth - 1) - 1) +
    phaseCcxBound lengthWidth shiftWidth +
    SwapLength.ccxBound width lengthWidth + 19

def cxBound (n lengthWidth shiftWidth : Nat) : Nat :=
  let width := workWidth n
  2 * (6 * (width - 1) + 3 * Increment.cxCost shiftWidth) +
    2 * (width * (32 * lengthWidth + 23) + 1) +
    2 * (width * (32 * lengthWidth + 23)) +
    PrunedSelectSwap.cxBound width lengthWidth +
    2 * Increment.cxCost lengthWidth +
    4 * coefficientPrepareCxBound n lengthWidth +
    2 * (if lengthWidth = 1 then 1 else 0) +
    phaseCxBound lengthWidth shiftWidth +
    SwapLength.gateBound width lengthWidth + 20

def compiledGateBound (n lengthWidth shiftWidth : Nat) : Nat :=
  gateBound n lengthWidth shiftWidth + 2 * ccxBound n lengthWidth shiftWidth

def compiledCliffordBound (n lengthWidth shiftWidth : Nat) : Nat :=
  gateBound n lengthWidth shiftWidth + ccxBound n lengthWidth shiftWidth

theorem remainderPrepare_length_le (n lengthWidth : Nat) :
    (EndpointPrep.remainderPrepare n lengthWidth).length ≤
      remainderPrepareGateBound lengthWidth := by
  have hthree := constantXorGates_length_le 3
    (EndpointPrep.leftOffset lengthWidth) lengthWidth
  have hn := constantXorGates_length_le (n + 1)
    (EndpointPrep.rightOffset lengthWidth) lengthWidth
  simp only [EndpointPrep.remainderPrepare, List.length_append,
    EndpointPrep.addQLeft, EndpointPrep.addTLeft,
    EndpointPrep.subShiftRight, Arithmetic.addGates_length,
    Arithmetic.subGates_length, remainderPrepareGateBound]
  omega

theorem remainderPrepare_ccx (n lengthWidth : Nat) :
    (EndpointPrep.remainderPrepare n lengthWidth).countP RGate.isCcx =
      remainderPrepareCcxBound lengthWidth := by
  simp [EndpointPrep.remainderPrepare, EndpointPrep.addQLeft,
    EndpointPrep.addTLeft, EndpointPrep.subShiftRight,
    constantXorGates_no_ccx, Arithmetic.addGates_ccx,
    Arithmetic.subGates_ccx, remainderPrepareCcxBound]
  omega

theorem remainderPrepare_cx (n lengthWidth : Nat) :
    (EndpointPrep.remainderPrepare n lengthWidth).countP RGate.isCx = 0 := by
  simp [EndpointPrep.remainderPrepare, EndpointPrep.addQLeft,
    EndpointPrep.addTLeft, EndpointPrep.subShiftRight,
    constantXorGates_no_cx, Arithmetic.addGates_cx,
    Arithmetic.subGates_cx]

theorem swapPrepare_length_le (lengthWidth : Nat) :
    (EndpointPrep.swapPrepare lengthWidth).length ≤
      swapPrepareGateBound lengthWidth := by
  have htwo := constantXorGates_length_le 2
    (EndpointPrep.leftOffset lengthWidth) lengthWidth
  simp only [EndpointPrep.swapPrepare, List.length_append,
    EndpointPrep.addQLeft, EndpointPrep.addTLeft,
    Arithmetic.addGates_length, swapPrepareGateBound]
  omega

theorem swapPrepare_ccx (lengthWidth : Nat) :
    (EndpointPrep.swapPrepare lengthWidth).countP RGate.isCcx =
      swapPrepareCcxBound lengthWidth := by
  simp [EndpointPrep.swapPrepare, EndpointPrep.addQLeft,
    EndpointPrep.addTLeft, constantXorGates_no_ccx,
    Arithmetic.addGates_ccx, swapPrepareCcxBound]
  omega

theorem swapPrepare_cx (lengthWidth : Nat) :
    (EndpointPrep.swapPrepare lengthWidth).countP RGate.isCx = 0 := by
  simp [EndpointPrep.swapPrepare, EndpointPrep.addQLeft,
    EndpointPrep.addTLeft, constantXorGates_no_cx,
    Arithmetic.addGates_cx]

theorem coefficientPrepare_length_le (n lengthWidth : Nat) :
    (EndpointPrep.coefficientPrepare lengthWidth).length +
        (EndpointPrep.coefficientAdjustment n lengthWidth).length ≤
      coefficientPrepareGateBound n lengthWidth := by
  have hone := constantXorGates_length_le 1
    (EndpointPrep.rightOffset lengthWidth) lengthWidth
  rw [EndpointPrep.coefficientAdjustment_length]
  simp only [EndpointPrep.coefficientPrepare, List.length_append,
    EndpointPrep.addTRight, Arithmetic.addGates_length,
    coefficientPrepareGateBound, coefficientAdjustmentXorLength]
  omega

theorem coefficientPrepare_ccx (n lengthWidth : Nat) :
    (EndpointPrep.coefficientPrepare lengthWidth).countP RGate.isCcx +
        (EndpointPrep.coefficientAdjustment n lengthWidth).countP
          RGate.isCcx =
      coefficientPrepareCcxBound lengthWidth := by
  rw [EndpointPrep.coefficientAdjustment_ccx]
  simp [EndpointPrep.coefficientPrepare, EndpointPrep.addTRight,
    constantXorGates_no_ccx, Arithmetic.addGates_ccx,
    coefficientPrepareCcxBound]
  omega

theorem coefficientPrepare_cx (n lengthWidth : Nat) :
    (EndpointPrep.coefficientPrepare lengthWidth).countP RGate.isCx +
        (EndpointPrep.coefficientAdjustment n lengthWidth).countP
          RGate.isCx =
      coefficientPrepareCxBound n lengthWidth := by
  rw [EndpointPrep.coefficientAdjustment_cx]
  simp [EndpointPrep.coefficientPrepare, EndpointPrep.addTRight,
    constantXorGates_no_cx, Arithmetic.addGates_cx,
    coefficientPrepareCxBound, coefficientAdjustmentXorLength]

theorem selector_length_le (value width : Nat) :
    (Selector.circuit value width).gates.length ≤ 4 * width + 1 := by
  simpa [Selector.circuit] using Selector.gates_length_le value width

theorem selector_ccx_le (value width : Nat) :
    (Selector.circuit value width).gates.countP RGate.isCcx ≤ 2 * width := by
  simpa [Selector.circuit] using Selector.gates_ccx_le value width

theorem selector_cx_le (value width : Nat) :
    (Selector.circuit value width).gates.countP RGate.isCx ≤
      4 * width + 1 := by
  exact (List.countP_le_length.trans (selector_length_le value width))

theorem rPrimeZeroSelector_length (n lengthWidth shiftWidth : Nat) :
    (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).length =
      2 * (lengthWidth - 2) + 1 := by
  rw [StepLayout.rPrimeZeroSelectorGates_length]
  simpa [Selector.circuit, encodedZero] using
    Selector.gates_allOnes_length lengthWidth

theorem rPrimeZeroSelector_ccx (n lengthWidth shiftWidth : Nat) :
    (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP
        RGate.isCcx =
      2 * (lengthWidth - 1) - 1 := by
  rw [StepLayout.rPrimeZeroSelectorGates_ccx]
  simpa [Selector.circuit, encodedZero] using
    Selector.gates_allOnes_ccx lengthWidth

theorem rPrimeZeroSelector_cx (n lengthWidth shiftWidth : Nat) :
    (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP
        RGate.isCx =
      if lengthWidth = 1 then 1 else 0 := by
  rw [StepLayout.rPrimeZeroSelectorGates_cx]
  simpa [Selector.circuit, encodedZero] using
    Selector.gates_allOnes_cx lengthWidth

theorem phaseSelect_length_le (lengthWidth shiftWidth : Nat) :
    (Phase.selectGates lengthWidth shiftWidth).length ≤
      2 * (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_length_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.selectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.length_append, Placed.selector_length]
  omega

theorem phaseSelect_ccx_le (lengthWidth shiftWidth : Nat) :
    (Phase.selectGates lengthWidth shiftWidth).countP RGate.isCcx ≤
      4 * lengthWidth + 2 * shiftWidth := by
  have hq := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_ccx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.selectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_ccx]
  omega

theorem phaseSelect_cx_le (lengthWidth shiftWidth : Nat) :
    (Phase.selectGates lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_cx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.selectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_cx]
  omega

theorem phaseUnselect_length_le (lengthWidth shiftWidth : Nat) :
    (Phase.unselectGates lengthWidth shiftWidth).length ≤
      2 * (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_length_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.unselectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.length_append, Placed.selector_length]
  omega

theorem phaseUnselect_ccx_le (lengthWidth shiftWidth : Nat) :
    (Phase.unselectGates lengthWidth shiftWidth).countP RGate.isCcx ≤
      4 * lengthWidth + 2 * shiftWidth := by
  have hq := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_ccx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.unselectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_ccx]
  omega

theorem phaseUnselect_cx_le (lengthWidth shiftWidth : Nat) :
    (Phase.unselectGates lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hr := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_cx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.unselectGates, Phase.qSelector, Phase.rPrimeSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_cx]
  omega

theorem ownershipSelect_length_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipSelectGates lengthWidth shiftWidth).length ≤
      (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_length_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipSelectGates, Phase.qSelector,
    Phase.shiftSelector, List.length_append, Placed.selector_length]
  omega

theorem ownershipSelect_ccx_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipSelectGates lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * lengthWidth + 2 * shiftWidth := by
  have hq := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_ccx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipSelectGates, Phase.qSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_ccx]
  omega

theorem ownershipSelect_cx_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipSelectGates lengthWidth shiftWidth).countP RGate.isCx ≤
      (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_cx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipSelectGates, Phase.qSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_cx]
  omega

theorem ownershipUnselect_length_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipUnselectGates lengthWidth shiftWidth).length ≤
      (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_length_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipUnselectGates, Phase.qSelector,
    Phase.shiftSelector, List.length_append, Placed.selector_length]
  omega

theorem ownershipUnselect_ccx_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipUnselectGates lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * lengthWidth + 2 * shiftWidth := by
  have hq := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_ccx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipUnselectGates, Phase.qSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_ccx]
  omega

theorem ownershipUnselect_cx_le (lengthWidth shiftWidth : Nat) :
    (Phase.ownershipUnselectGates lengthWidth shiftWidth).countP RGate.isCx ≤
      (4 * lengthWidth + 1) + (4 * shiftWidth + 1) := by
  have hq := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_cx_le (encodedZero shiftWidth) shiftWidth
  simp only [Phase.ownershipUnselectGates, Phase.qSelector,
    Phase.shiftSelector, List.countP_append, Placed.selector_cx]
  omega

theorem phaseCircuit_length_le (lengthWidth shiftWidth : Nat) :
    (Phase.circuit lengthWidth shiftWidth).gates.length ≤
      4 * (4 * lengthWidth + 1) +
        2 * (4 * shiftWidth + 1) + 14 := by
  have hl := selector_length_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_length_le (encodedZero shiftWidth) shiftWidth
  rw [Phase.circuit_length]
  omega

theorem phaseCircuit_ccx_le (lengthWidth shiftWidth : Nat) :
    (Phase.circuit lengthWidth shiftWidth).gates.countP RGate.isCcx ≤
      8 * lengthWidth + 4 * shiftWidth + 4 := by
  have hl := selector_ccx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_ccx_le (encodedZero shiftWidth) shiftWidth
  rw [Phase.circuit_ccx]
  omega

theorem phaseCircuit_cx_le (lengthWidth shiftWidth : Nat) :
    (Phase.circuit lengthWidth shiftWidth).gates.countP RGate.isCx ≤
      4 * (4 * lengthWidth + 1) +
        2 * (4 * shiftWidth + 1) + 6 := by
  have hl := selector_cx_le (encodedZero lengthWidth) lengthWidth
  have hs := selector_cx_le (encodedZero shiftWidth) shiftWidth
  rw [Phase.circuit_cx]
  omega

theorem placed_phase_length_le (n lengthWidth shiftWidth : Nat) :
    (StepLayout.phaseGates n lengthWidth shiftWidth).length +
        (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).length +
        (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).length ≤
      phaseGateBound lengthWidth shiftWidth := by
  have hc := phaseCircuit_length_le lengthWidth shiftWidth
  have hs := ownershipSelect_length_le lengthWidth shiftWidth
  have hu := ownershipUnselect_length_le lengthWidth shiftWidth
  rw [StepLayout.phaseGates_length]
  simp only [StepLayout.ownershipSelectGates,
    StepLayout.ownershipUnselectGates, StepLayout.placed_length]
  change (Phase.circuit lengthWidth shiftWidth).gates.length +
      (Phase.ownershipSelectGates lengthWidth shiftWidth).length +
      (Phase.ownershipUnselectGates lengthWidth shiftWidth).length ≤ _
  simp only [phaseGateBound]
  omega

theorem placed_phase_ccx_le (n lengthWidth shiftWidth : Nat) :
    (StepLayout.phaseGates n lengthWidth shiftWidth).countP RGate.isCcx +
        (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).countP
          RGate.isCcx +
        (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).countP
          RGate.isCcx ≤
      phaseCcxBound lengthWidth shiftWidth := by
  have hc := phaseCircuit_ccx_le lengthWidth shiftWidth
  have hs := ownershipSelect_ccx_le lengthWidth shiftWidth
  have hu := ownershipUnselect_ccx_le lengthWidth shiftWidth
  rw [StepLayout.phaseGates_ccx]
  simp only [StepLayout.ownershipSelectGates,
    StepLayout.ownershipUnselectGates, StepLayout.placed_ccx]
  change (Phase.circuit lengthWidth shiftWidth).gates.countP RGate.isCcx +
      (Phase.ownershipSelectGates lengthWidth shiftWidth).countP RGate.isCcx +
      (Phase.ownershipUnselectGates lengthWidth shiftWidth).countP
        RGate.isCcx ≤ _
  simp only [phaseCcxBound]
  omega

theorem placed_phase_cx_le (n lengthWidth shiftWidth : Nat) :
    (StepLayout.phaseGates n lengthWidth shiftWidth).countP RGate.isCx +
        (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).countP
          RGate.isCx +
        (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).countP
          RGate.isCx ≤
      phaseCxBound lengthWidth shiftWidth := by
  have hc := phaseCircuit_cx_le lengthWidth shiftWidth
  have hs := ownershipSelect_cx_le lengthWidth shiftWidth
  have hu := ownershipUnselect_cx_le lengthWidth shiftWidth
  rw [StepLayout.phaseGates_cx]
  simp only [StepLayout.ownershipSelectGates,
    StepLayout.ownershipUnselectGates, StepLayout.placed_cx]
  change (Phase.circuit lengthWidth shiftWidth).gates.countP RGate.isCx +
      (Phase.ownershipSelectGates lengthWidth shiftWidth).countP RGate.isCx +
      (Phase.ownershipUnselectGates lengthWidth shiftWidth).countP
        RGate.isCx ≤ _
  simp only [phaseCxBound]
  omega

theorem gates_length_le (n lengthWidth shiftWidth : Nat) :
    (Step.gates n lengthWidth shiftWidth).length ≤
      gateBound n lengthWidth shiftWidth := by
  rw [Step.gates_length, rPrimeZeroSelector_length]
  have hshift : (Shift.gates (workWidth n) shiftWidth).length =
      9 * (workWidth n - 1) + 3 * Increment.lengthCost shiftWidth := by
    simpa [Shift.circuit] using
      Shift.circuit_length (workWidth n) shiftWidth
  have hincrement : (Increment.circuit lengthWidth).gates.length =
      Increment.lengthCost lengthWidth :=
    Increment.circuit_length lengthWidth
  have hrprep := remainderPrepare_length_le n lengthWidth
  have hfullBigEndian :=
    IntervalBigEndian.gates_length_le (workWidth n) lengthWidth
  have hnosignBigEndian := IntervalBigEndian.noSignGates_length_le
    (workWidth n) lengthWidth
  have hfull := Interval.gates_length_le (workWidth n) lengthWidth
  have hnosign := Interval.noSignGates_length_le
    (workWidth n) lengthWidth
  have hswapPrep := swapPrepare_length_le lengthWidth
  have hselect := PrunedSelectSwap.gates_length (workWidth n) lengthWidth
  have hcoefficient := coefficientPrepare_length_le n lengthWidth
  have hphase := placed_phase_length_le n lengthWidth shiftWidth
  have hownership := SwapLength.gates_length_le n (workWidth n) lengthWidth
  simp only [StepLayout.shiftGates_length,
    StepLayout.remainderPrepareGates, StepLayout.swapPrepareGates,
    StepLayout.coefficientPrepareGates,
    StepLayout.coefficientBasePrepareGates,
    StepLayout.coefficientAdjustmentGates, StepLayout.placed_length,
    List.length_append,
    StepLayout.remainderIntervalGates_length,
    StepLayout.remainderIntervalNoSignGates_length,
    StepLayout.intervalGates_length, StepLayout.intervalNoSignGates_length,
    StepLayout.selectSwapGates_length,
    StepLayout.quotientIncrementGates_length,
    StepLayout.ownershipGates_length, gateBound]
  omega

theorem gates_ccx_le (n lengthWidth shiftWidth : Nat) :
    (Step.gates n lengthWidth shiftWidth).countP RGate.isCcx ≤
      ccxBound n lengthWidth shiftWidth := by
  rw [Step.gates_ccx, rPrimeZeroSelector_ccx]
  have hshift : (Shift.gates (workWidth n) shiftWidth).countP RGate.isCcx =
      3 * (workWidth n - 1) + 3 * Increment.ccxCost shiftWidth := by
    simpa [Shift.circuit] using
      Shift.circuit_ccx (workWidth n) shiftWidth
  have hincrement :
      (Increment.circuit lengthWidth).gates.countP RGate.isCcx =
        Increment.ccxCost lengthWidth :=
    Increment.circuit_ccx lengthWidth
  have hrprep := remainderPrepare_ccx n lengthWidth
  have hfullBigEndian :=
    IntervalBigEndian.gates_ccx_le (workWidth n) lengthWidth
  have hnosignBigEndian := IntervalBigEndian.noSignGates_ccx_le
    (workWidth n) lengthWidth
  have hfull := Interval.gates_ccx_le (workWidth n) lengthWidth
  have hnosign := Interval.noSignGates_ccx_le
    (workWidth n) lengthWidth
  have hswapPrep := swapPrepare_ccx lengthWidth
  have hselect := PrunedSelectSwap.gates_ccx (workWidth n) lengthWidth
  have hcoefficient := coefficientPrepare_ccx n lengthWidth
  have hphase := placed_phase_ccx_le n lengthWidth shiftWidth
  have hownership := SwapLength.gates_ccx_le n (workWidth n) lengthWidth
  simp only [StepLayout.shiftGates_ccx,
    StepLayout.remainderPrepareGates, StepLayout.swapPrepareGates,
    StepLayout.coefficientPrepareGates,
    StepLayout.coefficientBasePrepareGates,
    StepLayout.coefficientAdjustmentGates, StepLayout.placed_ccx,
    List.countP_append,
    StepLayout.remainderIntervalGates_ccx,
    StepLayout.remainderIntervalNoSignGates_ccx,
    StepLayout.intervalGates_ccx, StepLayout.intervalNoSignGates_ccx,
    StepLayout.selectSwapGates_ccx,
    StepLayout.quotientIncrementGates_ccx,
    StepLayout.ownershipGates_ccx, ccxBound]
  omega

theorem gates_cx_le (n lengthWidth shiftWidth : Nat) :
    (Step.gates n lengthWidth shiftWidth).countP RGate.isCx ≤
      cxBound n lengthWidth shiftWidth := by
  rw [Step.gates_cx, rPrimeZeroSelector_cx]
  have hshift : (Shift.gates (workWidth n) shiftWidth).countP RGate.isCx =
      6 * (workWidth n - 1) + 3 * Increment.cxCost shiftWidth := by
    simpa [Shift.circuit] using
      Shift.circuit_cx (workWidth n) shiftWidth
  have hincrement :
      (Increment.circuit lengthWidth).gates.countP RGate.isCx =
        Increment.cxCost lengthWidth :=
    Increment.circuit_cx lengthWidth
  have hrprep := remainderPrepare_cx n lengthWidth
  have hswapPrep := swapPrepare_cx lengthWidth
  have hfullBigEndianLength := IntervalBigEndian.gates_length_le
    (workWidth n) lengthWidth
  have hnosignBigEndianLength := IntervalBigEndian.noSignGates_length_le
    (workWidth n) lengthWidth
  have hfullBigEndian :
      (IntervalBigEndian.gates (workWidth n) lengthWidth).countP
      RGate.isCx ≤ workWidth n * (32 * lengthWidth + 23) + 1 :=
    List.countP_le_length.trans hfullBigEndianLength
  have hnosignBigEndian :
      (IntervalBigEndian.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCx ≤ workWidth n * (32 * lengthWidth + 23) :=
    List.countP_le_length.trans hnosignBigEndianLength
  have hfullLength := Interval.gates_length_le
    (workWidth n) lengthWidth
  have hnosignLength := Interval.noSignGates_length_le
    (workWidth n) lengthWidth
  have hfull : (Interval.gates (workWidth n) lengthWidth).countP
      RGate.isCx ≤ workWidth n * (32 * lengthWidth + 23) + 1 :=
    List.countP_le_length.trans hfullLength
  have hnosign :
      (Interval.noSignGates (workWidth n) lengthWidth).countP
        RGate.isCx ≤ workWidth n * (32 * lengthWidth + 23) :=
    List.countP_le_length.trans hnosignLength
  have hswap := PrunedSelectSwap.gates_cx (workWidth n) lengthWidth
  have hcoefficient := coefficientPrepare_cx n lengthWidth
  have hphase := placed_phase_cx_le n lengthWidth shiftWidth
  have hownershipLength :=
    SwapLength.gates_length_le n (workWidth n) lengthWidth
  have hownership :
      (SwapLength.gates n (workWidth n) lengthWidth).countP RGate.isCx ≤
        SwapLength.gateBound (workWidth n) lengthWidth :=
    List.countP_le_length.trans hownershipLength
  simp only [StepLayout.shiftGates_cx,
    StepLayout.remainderPrepareGates, StepLayout.swapPrepareGates,
    StepLayout.coefficientPrepareGates,
    StepLayout.coefficientBasePrepareGates,
    StepLayout.coefficientAdjustmentGates, StepLayout.placed_cx,
    List.countP_append,
    StepLayout.remainderIntervalGates_cx,
    StepLayout.remainderIntervalNoSignGates_cx,
    StepLayout.intervalGates_cx, StepLayout.intervalNoSignGates_cx,
    StepLayout.quotientIncrementGates_cx,
    StepLayout.ownershipGates_cx, cxBound]
  have hselectPlaced :
      (StepLayout.selectSwapGates n lengthWidth shiftWidth).countP RGate.isCx ≤
        PrunedSelectSwap.cxBound (workWidth n) lengthWidth := by
    rw [StepLayout.selectSwapGates, StepLayout.placed_cx]
    exact hswap.le
  omega

theorem compiledStep_toffoli_le (n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliCount
        (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      ccxBound n lengthWidth shiftWidth := by
  rw [toffoliCount_compile]
  exact gates_ccx_le n lengthWidth shiftWidth

theorem compiledStep_cnot_le (n lengthWidth shiftWidth : Nat) :
    Circuit.cnotCount
        (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      cxBound n lengthWidth shiftWidth := by
  rw [cnotCount_compile]
  exact gates_cx_le n lengthWidth shiftWidth

theorem compiledStep_gateCount_le (n lengthWidth shiftWidth : Nat) :
    Circuit.gateCount
        (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      compiledGateBound n lengthWidth shiftWidth := by
  rw [gateCount_compile]
  exact Nat.add_le_add (gates_length_le n lengthWidth shiftWidth)
    (Nat.mul_le_mul_left 2 (gates_ccx_le n lengthWidth shiftWidth))

theorem compiledStep_clifford_le (n lengthWidth shiftWidth : Nat) :
    Circuit.cliffordCount
        (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      compiledCliffordBound n lengthWidth shiftWidth := by
  rw [cliffordCount_compile]
  exact Nat.add_le_add (gates_length_le n lengthWidth shiftWidth)
    (gates_ccx_le n lengthWidth shiftWidth)

private theorem depth_le_gateCount (c : Circuit) :
    c.depth ≤ c.gateCount := by
  rw [Circuit.depth_eq_depthOf]
  simpa [Circuit.gateCount] using
    Circuit.depthOf_le_countP (fun _ => true) c

theorem compiledStep_depth_le (n lengthWidth shiftWidth : Nat) :
    Circuit.depth (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      compiledGateBound n lengthWidth shiftWidth := by
  exact (depth_le_gateCount _).trans
    (compiledStep_gateCount_le n lengthWidth shiftWidth)

theorem compiledStep_toffoliDepth_le (n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliDepth
        (compile (Step.circuit n lengthWidth shiftWidth)) ≤
      ccxBound n lengthWidth shiftWidth := by
  exact (Circuit.toffoliDepth_le_toffoliCount _).trans
    (compiledStep_toffoli_le n lengthWidth shiftWidth)

def fixedRoundGates
    (rounds n lengthWidth shiftWidth : Nat) : List RGate :=
  Iteration.gates n lengthWidth shiftWidth rounds

def fixedRoundCircuit
    (rounds n lengthWidth shiftWidth : Nat) : RCircuit :=
  Iteration.circuit n lengthWidth shiftWidth rounds

@[simp] theorem fixedRoundCircuit_width
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundCircuit rounds n lengthWidth shiftWidth).width =
      (StepLayout.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem fixedRoundCircuit_gates
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundCircuit rounds n lengthWidth shiftWidth).gates =
      fixedRoundGates rounds n lengthWidth shiftWidth := rfl

theorem fixedRoundCircuit_wellFormed
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (fixedRoundCircuit rounds n lengthWidth shiftWidth).wellFormed = true := by
  exact Iteration.circuit_wellFormed hlength hwidths

theorem fixedRoundGates_length
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).length =
      rounds * (Step.gates n lengthWidth shiftWidth).length := by
  simpa [fixedRoundGates] using
    Iteration.gates_length n lengthWidth shiftWidth rounds

theorem fixedRoundGates_ccx
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).countP RGate.isCcx =
      rounds * (Step.gates n lengthWidth shiftWidth).countP RGate.isCcx := by
  simpa [fixedRoundGates] using
    Iteration.gates_countP n lengthWidth shiftWidth rounds RGate.isCcx

theorem fixedRoundGates_cx
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).countP RGate.isCx =
      rounds * (Step.gates n lengthWidth shiftWidth).countP RGate.isCx := by
  simpa [fixedRoundGates] using
    Iteration.gates_countP n lengthWidth shiftWidth rounds RGate.isCx

theorem fixedRoundGates_length_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).length ≤
      rounds * gateBound n lengthWidth shiftWidth := by
  rw [fixedRoundGates_length]
  exact Nat.mul_le_mul_left rounds (gates_length_le n lengthWidth shiftWidth)

theorem fixedRoundGates_ccx_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).countP RGate.isCcx ≤
      rounds * ccxBound n lengthWidth shiftWidth := by
  rw [fixedRoundGates_ccx]
  exact Nat.mul_le_mul_left rounds (gates_ccx_le n lengthWidth shiftWidth)

theorem fixedRoundGates_cx_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (fixedRoundGates rounds n lengthWidth shiftWidth).countP RGate.isCx ≤
      rounds * cxBound n lengthWidth shiftWidth := by
  rw [fixedRoundGates_cx]
  exact Nat.mul_le_mul_left rounds (gates_cx_le n lengthWidth shiftWidth)

theorem compiledFixed_toffoli_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliCount
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * ccxBound n lengthWidth shiftWidth := by
  rw [toffoliCount_compile]
  exact fixedRoundGates_ccx_le rounds n lengthWidth shiftWidth

theorem compiledFixed_cnot_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.cnotCount
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * cxBound n lengthWidth shiftWidth := by
  rw [cnotCount_compile]
  exact fixedRoundGates_cx_le rounds n lengthWidth shiftWidth

theorem compiledFixed_gateCount_le
    (rounds n lengthWidth shiftWidth : Nat) :
  Circuit.gateCount
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * compiledGateBound n lengthWidth shiftWidth := by
  rw [gateCount_compile, fixedRoundCircuit_gates, fixedRoundGates_length,
    fixedRoundGates_ccx, compiledGateBound]
  have hlength := gates_length_le n lengthWidth shiftWidth
  have hccx := gates_ccx_le n lengthWidth shiftWidth
  have hstep := Nat.add_le_add hlength (Nat.mul_le_mul_left 2 hccx)
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul_left rounds hstep

theorem compiledFixed_clifford_le
    (rounds n lengthWidth shiftWidth : Nat) :
  Circuit.cliffordCount
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * compiledCliffordBound n lengthWidth shiftWidth := by
  rw [cliffordCount_compile, fixedRoundCircuit_gates,
    fixedRoundGates_length, fixedRoundGates_ccx, compiledCliffordBound]
  have hlength := gates_length_le n lengthWidth shiftWidth
  have hccx := gates_ccx_le n lengthWidth shiftWidth
  simpa [Nat.mul_add] using
    Nat.mul_le_mul_left rounds (Nat.add_le_add hlength hccx)

theorem compiledFixed_depth_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.depth
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * compiledGateBound n lengthWidth shiftWidth := by
  exact (depth_le_gateCount _).trans
    (compiledFixed_gateCount_le rounds n lengthWidth shiftWidth)

theorem compiledFixed_toffoliDepth_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliDepth
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      rounds * ccxBound n lengthWidth shiftWidth := by
  exact (Circuit.toffoliDepth_le_toffoliCount _).trans
    (compiledFixed_toffoli_le rounds n lengthWidth shiftWidth)

theorem compiledFixed_usedWires_le
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    Circuit.usedWires
        (compile (fixedRoundCircuit rounds n lengthWidth shiftWidth)) ≤
      (StepLayout.layout n lengthWidth shiftWidth).width := by
  simpa [fixedRoundCircuit] using
    usedWires_compile_le_width
      (Iteration.circuit_wellFormed
        (steps := rounds) hlength hwidths)

end StepResources
end Euclid
end VQ
