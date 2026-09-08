/-
Complete full-window gate schedule for one Algorithm 3 transition.
-/
import VQ.Euclid.StepControl
import VQ.Euclid.StepPlaced

namespace VQ
namespace Euclid
namespace Step

open Reversible

def around (compute body : List RGate) : List RGate :=
  compute ++ body ++ compute.reverse

def preShiftControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let minus := StepLayout.minusWire n lengthWidth shiftWidth
  StepControl.negativeGates p1 plus ++ [.ccx plus p2 minus]

def postShiftControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let minus := StepLayout.minusWire n lengthWidth shiftWidth
  [.cx p1 plus, .ccx plus p2 minus]

def remainderSubControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  StepControl.negativeGates
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)

def remainderFlip (n lengthWidth shiftWidth : Nat) : List RGate :=
  Phase.negativeAndGates
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.signWire n lengthWidth shiftWidth)

def remainderAddControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temp := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  [.ccx p2 sign temp] ++
    StepControl.negativeGates p1 plus ++
    Phase.negativeAndGates plus temp ctrl

def remainderGuard (n lengthWidth shiftWidth : Nat) : List RGate :=
  [.cx (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)]

def guardedRemainderSubControl
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  remainderSubControl n lengthWidth shiftWidth ++
    remainderGuard n lengthWidth shiftWidth

def guardedRemainderAddControl
    (n lengthWidth shiftWidth : Nat) : List RGate :=
  remainderAddControl n lengthWidth shiftWidth ++
    remainderGuard n lengthWidth shiftWidth

def swapControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  Phase.xorPairGates
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)

def quotientDecrementControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  Phase.negativeAndGates
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)

def quotientIncrementControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  Phase.negativeAndGates
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)

def coefficientSubControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temp := StepLayout.temporaryWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  Phase.negativeAndGates sign p2 temp ++
    Phase.negativeAndGates p1 temp ctrl

def coefficientFlip (n lengthWidth shiftWidth : Nat) : List RGate :=
  [.cx (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.signWire n lengthWidth shiftWidth)]

def coefficientAddControl (n lengthWidth shiftWidth : Nat) : List RGate :=
  [.cx (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)]

def remainderSubBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (remainderSubControl n lengthWidth shiftWidth)
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
      StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth ++
      StepLayout.remainderCleanupGates n lengthWidth shiftWidth)

def remainderAddBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (remainderAddControl n lengthWidth shiftWidth)
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
      StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth ++
      StepLayout.remainderCleanupGates n lengthWidth shiftWidth)

def guardedRemainderSubBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (guardedRemainderSubControl n lengthWidth shiftWidth)
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
      StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth ++
      StepLayout.remainderCleanupGates n lengthWidth shiftWidth)

def guardedRemainderAddBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (guardedRemainderAddControl n lengthWidth shiftWidth)
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
      StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth ++
      StepLayout.remainderCleanupGates n lengthWidth shiftWidth)

def guardedRemainderBlocks (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth)
    (guardedRemainderSubBlock n lengthWidth shiftWidth ++
      remainderFlip n lengthWidth shiftWidth ++
      guardedRemainderAddBlock n lengthWidth shiftWidth)

def swapBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (swapControl n lengthWidth shiftWidth)
    (StepLayout.swapPrepareGates n lengthWidth shiftWidth ++
      StepLayout.selectSwapGates n lengthWidth shiftWidth ++
      StepLayout.swapCleanupGates n lengthWidth shiftWidth)

def quotientDecrementBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (quotientDecrementControl n lengthWidth shiftWidth)
    (StepLayout.quotientDecrementGates n lengthWidth shiftWidth)

def quotientIncrementBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (quotientIncrementControl n lengthWidth shiftWidth)
    (StepLayout.quotientIncrementGates n lengthWidth shiftWidth)

def coefficientSubBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (coefficientSubControl n lengthWidth shiftWidth)
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
      StepLayout.intervalNoSignReverseGates n lengthWidth shiftWidth ++
      StepLayout.coefficientCleanupGates n lengthWidth shiftWidth)

def coefficientAddBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (coefficientAddControl n lengthWidth shiftWidth)
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
      StepLayout.intervalGates n lengthWidth shiftWidth ++
      StepLayout.coefficientCleanupGates n lengthWidth shiftWidth)

def ownershipBlock (n lengthWidth shiftWidth : Nat) : List RGate :=
  let zq := StepLayout.zeroQWire n lengthWidth shiftWidth
  let zs := StepLayout.zeroShiftWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  StepLayout.ownershipSelectGates n lengthWidth shiftWidth ++
    [.ccx zq zs ctrl] ++
    StepLayout.ownershipGates n lengthWidth shiftWidth ++
    [.cx ctrl (StepLayout.iterWire n lengthWidth shiftWidth)] ++
    [.ccx zq zs ctrl] ++
    StepLayout.ownershipUnselectGates n lengthWidth shiftWidth

def coefficientPrefixGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (preShiftControl n lengthWidth shiftWidth)
      (StepLayout.shiftGates n lengthWidth shiftWidth) ++
    guardedRemainderBlocks n lengthWidth shiftWidth ++
    quotientIncrementBlock n lengthWidth shiftWidth ++
    swapBlock n lengthWidth shiftWidth ++
    quotientDecrementBlock n lengthWidth shiftWidth

def gates (n lengthWidth shiftWidth : Nat) : List RGate :=
  around (preShiftControl n lengthWidth shiftWidth)
      (StepLayout.shiftGates n lengthWidth shiftWidth) ++
    guardedRemainderBlocks n lengthWidth shiftWidth ++
    quotientIncrementBlock n lengthWidth shiftWidth ++
    swapBlock n lengthWidth shiftWidth ++
    quotientDecrementBlock n lengthWidth shiftWidth ++
    coefficientSubBlock n lengthWidth shiftWidth ++
    coefficientFlip n lengthWidth shiftWidth ++
    coefficientAddBlock n lengthWidth shiftWidth ++
    around (postShiftControl n lengthWidth shiftWidth)
      (StepLayout.shiftGates n lengthWidth shiftWidth) ++
    StepLayout.phaseGates n lengthWidth shiftWidth ++
    ownershipBlock n lengthWidth shiftWidth

theorem gates_eq_coefficientPrefix_append
    (n lengthWidth shiftWidth : Nat) :
    gates n lengthWidth shiftWidth =
      coefficientPrefixGates n lengthWidth shiftWidth ++
        coefficientSubBlock n lengthWidth shiftWidth ++
        coefficientFlip n lengthWidth shiftWidth ++
        coefficientAddBlock n lengthWidth shiftWidth ++
        around (postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth) ++
        StepLayout.phaseGates n lengthWidth shiftWidth ++
        ownershipBlock n lengthWidth shiftWidth := by
  simp [gates, coefficientPrefixGates, List.append_assoc]

def circuit (n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (StepLayout.layout n lengthWidth shiftWidth).width,
    gates := gates n lengthWidth shiftWidth }

def reverseCircuit (n lengthWidth shiftWidth : Nat) : RCircuit :=
  (circuit n lengthWidth shiftWidth).reverse

private theorem controlWireFacts (n lengthWidth shiftWidth : Nat) :
    let width := (StepLayout.layout n lengthWidth shiftWidth).width
    StepLayout.phase1Wire n lengthWidth shiftWidth < width ∧
    StepLayout.phase2Wire n lengthWidth shiftWidth < width ∧
    StepLayout.iterWire n lengthWidth shiftWidth < width ∧
    StepLayout.signWire n lengthWidth shiftWidth < width ∧
    StepLayout.controlWire n lengthWidth shiftWidth < width ∧
    StepLayout.zeroQWire n lengthWidth shiftWidth < width ∧
    StepLayout.zeroShiftWire n lengthWidth shiftWidth < width ∧
    StepLayout.conditionWire n lengthWidth shiftWidth < width ∧
    StepLayout.temporaryWire n lengthWidth shiftWidth < width ∧
    StepLayout.plusWire n lengthWidth shiftWidth < width ∧
    StepLayout.minusWire n lengthWidth shiftWidth < width := by
  have hlength : lengthWidth ≤ StepLayout.selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  have hshift : shiftWidth ≤ StepLayout.selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [StepLayout.layout_width, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.iterWire, StepLayout.signWire,
      StepLayout.controlWire, StepLayout.zeroQWire,
      StepLayout.zeroShiftWire, StepLayout.conditionWire,
      StepLayout.temporaryWire, StepLayout.plusWire, StepLayout.minusWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.carryWire, StepLayout.auxOffset, StepLayout.shiftOffset,
      StepLayout.auxWidth] <;> omega

theorem controls_wellFormed (n lengthWidth shiftWidth : Nat) :
    let width := (StepLayout.layout n lengthWidth shiftWidth).width
    (preShiftControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (postShiftControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (remainderSubControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (remainderFlip n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (remainderAddControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (swapControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (quotientDecrementControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (quotientIncrementControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (coefficientSubControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (coefficientFlip n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true ∧
    (coefficientAddControl n lengthWidth shiftWidth).all
        (RGate.wellFormed width) = true := by
  let width := (StepLayout.layout n lengthWidth shiftWidth).width
  dsimp only
  simp [preShiftControl, postShiftControl, remainderSubControl,
    remainderFlip, remainderAddControl, swapControl,
    quotientDecrementControl, quotientIncrementControl,
    coefficientSubControl, coefficientFlip, coefficientAddControl,
    StepControl.negativeGates, Phase.negativeAndGates,
    Phase.xorPairGates, RGate.wellFormed, StepLayout.layout_width,
    StepLayout.phase1Wire,
    StepLayout.phase2Wire, StepLayout.signWire, StepLayout.controlWire,
    StepLayout.temporaryWire, StepLayout.plusWire, StepLayout.minusWire,
    StepLayout.cellScratchWire,
    StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
    StepLayout.shiftOffset, StepLayout.auxWidth]
  omega

theorem remainderGuard_wellFormed (n lengthWidth shiftWidth : Nat) :
    (remainderGuard n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true := by
  simp [remainderGuard, RGate.wellFormed, StepLayout.layout_width,
    StepLayout.zeroRPrimeWire, StepLayout.controlWire,
    StepLayout.cellScratchWire, StepLayout.poolOffset, StepLayout.carryWire,
    StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
    StepLayout.auxWidth, StepLayout.selectorWidth]
  omega

private theorem ownershipPrimitives_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    let width := (StepLayout.layout n lengthWidth shiftWidth).width
    RGate.wellFormed width
        (.ccx (StepLayout.zeroQWire n lengthWidth shiftWidth)
          (StepLayout.zeroShiftWire n lengthWidth shiftWidth)
          (StepLayout.controlWire n lengthWidth shiftWidth)) = true ∧
    RGate.wellFormed width
        (.cx (StepLayout.controlWire n lengthWidth shiftWidth)
          (StepLayout.iterWire n lengthWidth shiftWidth)) = true := by
  have h := controlWireFacts n lengthWidth shiftWidth
  dsimp only at h ⊢
  rcases h with ⟨hp1, hp2, hiter, hsign, hcontrol, hzq, hzs, hcondition,
    htemporary, hplus, hminus⟩
  have hqz : StepLayout.zeroQWire n lengthWidth shiftWidth ≠
      StepLayout.zeroShiftWire n lengthWidth shiftWidth := by
    simp [StepLayout.zeroQWire, StepLayout.zeroShiftWire]
  have hzc : StepLayout.zeroShiftWire n lengthWidth shiftWidth ≠
      StepLayout.controlWire n lengthWidth shiftWidth := by
    simp [StepLayout.zeroShiftWire, StepLayout.controlWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
    omega
  have hqc : StepLayout.zeroQWire n lengthWidth shiftWidth ≠
      StepLayout.controlWire n lengthWidth shiftWidth := by
    simp [StepLayout.zeroQWire, StepLayout.controlWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
    omega
  have hci : StepLayout.controlWire n lengthWidth shiftWidth ≠
      StepLayout.iterWire n lengthWidth shiftWidth := by
    simp [StepLayout.controlWire, StepLayout.iterWire]
  simp [RGate.wellFormed, hzq, hzs, hcontrol, hiter, hqz, hzc, hqc, hci]

theorem circuit_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (circuit n lengthWidth shiftWidth).wellFormed = true := by
  have hc := controls_wellFormed n lengthWidth shiftWidth
  dsimp only at hc
  rcases hc with ⟨hpre, hpost, hrsub, hrflip, hradd, hswap, hqdec, hqinc,
    htsub, htflip, htadd⟩
  have hrguard := remainderGuard_wellFormed n lengthWidth shiftWidth
  have ho := ownershipPrimitives_wellFormed n lengthWidth shiftWidth
  dsimp only at ho
  rcases ho with ⟨hoccx, hocx⟩
  simp only [circuit, RCircuit.wellFormed, gates, guardedRemainderBlocks,
    guardedRemainderSubBlock, guardedRemainderAddBlock,
    guardedRemainderSubControl,
    guardedRemainderAddControl, swapBlock, quotientDecrementBlock,
    quotientIncrementBlock, coefficientSubBlock, coefficientAddBlock,
    ownershipBlock, around, List.all_append, List.all_reverse,
    Bool.and_eq_true, hpre, hpost, hrsub, hrflip, hrguard,
    hradd, hswap, hqdec, hqinc, htsub, htflip, htadd,
    StepLayout.shiftGates_wellFormed,
    StepLayout.remainderPrepareGates_wellFormed hlength hwidths,
    StepLayout.remainderCleanupGates_wellFormed hlength hwidths,
    StepLayout.remainderIntervalReverseGates_wellFormed,
    StepLayout.remainderIntervalNoSignGates_wellFormed,
    StepLayout.swapPrepareGates_wellFormed hlength hwidths,
    StepLayout.swapCleanupGates_wellFormed hlength hwidths,
    StepLayout.selectSwapGates_wellFormed,
    StepLayout.quotientDecrementGates_wellFormed,
    StepLayout.quotientIncrementGates_wellFormed,
    StepLayout.coefficientPrepareGates_wellFormed hlength hwidths,
    StepLayout.coefficientCleanupGates_wellFormed hlength hwidths,
    StepLayout.intervalGates_wellFormed,
    StepLayout.intervalNoSignReverseGates_wellFormed,
    StepLayout.phaseGates_wellFormed,
    StepLayout.rPrimeZeroSelectorGates_wellFormed,
    StepLayout.ownershipSelectGates_wellFormed,
    StepLayout.ownershipUnselectGates_wellFormed,
    StepLayout.ownershipGates_wellFormed]
  simp [hoccx, hocx]

theorem reverseCircuit_wellFormed
    {n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (reverseCircuit n lengthWidth shiftWidth).wellFormed = true := by
  exact RCircuit.wellFormed_reverse (circuit_wellFormed hlength hwidths)

theorem gates_length (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length =
      2 * (StepLayout.shiftGates n lengthWidth shiftWidth).length +
      4 * (StepLayout.remainderPrepareGates n lengthWidth shiftWidth).length +
      (StepLayout.remainderIntervalGates n lengthWidth shiftWidth).length +
      (StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth).length +
      2 * (StepLayout.swapPrepareGates n lengthWidth shiftWidth).length +
      (StepLayout.selectSwapGates n lengthWidth shiftWidth).length +
      2 * (StepLayout.quotientIncrementGates n lengthWidth shiftWidth).length +
      4 * (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth).length +
      (StepLayout.intervalGates n lengthWidth shiftWidth).length +
      (StepLayout.intervalNoSignGates n lengthWidth shiftWidth).length +
      2 * (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).length +
      (StepLayout.phaseGates n lengthWidth shiftWidth).length +
      (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).length +
      (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).length +
      (StepLayout.ownershipGates n lengthWidth shiftWidth).length + 73 := by
  simp [gates, guardedRemainderBlocks, guardedRemainderSubBlock,
    guardedRemainderAddBlock,
    guardedRemainderSubControl, guardedRemainderAddControl, swapBlock,
    quotientDecrementBlock, quotientIncrementBlock, coefficientSubBlock,
    coefficientAddBlock, ownershipBlock, around, preShiftControl,
    postShiftControl, remainderSubControl, remainderFlip, remainderGuard,
    remainderAddControl, swapControl, quotientDecrementControl,
    quotientIncrementControl, coefficientSubControl, coefficientFlip,
    coefficientAddControl, StepControl.negativeGates,
    Phase.negativeAndGates, Phase.xorPairGates,
    StepLayout.remainderCleanupGates, StepLayout.swapCleanupGates,
    StepLayout.coefficientCleanupGates,
    StepLayout.remainderIntervalReverseGates,
    StepLayout.quotientDecrementGates, StepLayout.intervalNoSignReverseGates]
  omega

theorem gates_ccx (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCcx =
      2 * (StepLayout.shiftGates n lengthWidth shiftWidth).countP RGate.isCcx +
      4 * (StepLayout.remainderPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.remainderIntervalGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      2 * (StepLayout.swapPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.selectSwapGates n lengthWidth shiftWidth).countP RGate.isCcx +
      2 * (StepLayout.quotientIncrementGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      4 * (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.intervalGates n lengthWidth shiftWidth).countP RGate.isCcx +
      (StepLayout.intervalNoSignGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      2 * (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.phaseGates n lengthWidth shiftWidth).countP RGate.isCcx +
      (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).countP
        RGate.isCcx +
      (StepLayout.ownershipGates n lengthWidth shiftWidth).countP RGate.isCcx +
      19 := by
  simp [gates, guardedRemainderBlocks, guardedRemainderSubBlock,
    guardedRemainderAddBlock,
    guardedRemainderSubControl, guardedRemainderAddControl, swapBlock,
    quotientDecrementBlock, quotientIncrementBlock, coefficientSubBlock,
    coefficientAddBlock, ownershipBlock, around, preShiftControl,
    postShiftControl, remainderSubControl, remainderFlip, remainderGuard,
    remainderAddControl, swapControl, quotientDecrementControl,
    quotientIncrementControl, coefficientSubControl, coefficientFlip,
    coefficientAddControl, StepControl.negativeGates,
    Phase.negativeAndGates, Phase.xorPairGates,
    StepLayout.remainderCleanupGates, StepLayout.swapCleanupGates,
    StepLayout.coefficientCleanupGates,
    StepLayout.remainderIntervalReverseGates,
    StepLayout.quotientDecrementGates, StepLayout.intervalNoSignReverseGates,
    List.countP_cons, RGate.isCcx]
  omega

theorem gates_cx (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCx =
      2 * (StepLayout.shiftGates n lengthWidth shiftWidth).countP RGate.isCx +
      4 * (StepLayout.remainderPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.remainderIntervalGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      2 * (StepLayout.swapPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.selectSwapGates n lengthWidth shiftWidth).countP RGate.isCx +
      2 * (StepLayout.quotientIncrementGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      4 * (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.intervalGates n lengthWidth shiftWidth).countP RGate.isCx +
      (StepLayout.intervalNoSignGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      2 * (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.phaseGates n lengthWidth shiftWidth).countP RGate.isCx +
      (StepLayout.ownershipSelectGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth).countP
        RGate.isCx +
      (StepLayout.ownershipGates n lengthWidth shiftWidth).countP RGate.isCx +
      20 := by
  simp [gates, guardedRemainderBlocks, guardedRemainderSubBlock,
    guardedRemainderAddBlock,
    guardedRemainderSubControl, guardedRemainderAddControl, swapBlock,
    quotientDecrementBlock, quotientIncrementBlock, coefficientSubBlock,
    coefficientAddBlock, ownershipBlock, around, preShiftControl,
    postShiftControl, remainderSubControl, remainderFlip, remainderGuard,
    remainderAddControl, swapControl, quotientDecrementControl,
    quotientIncrementControl, coefficientSubControl, coefficientFlip,
    coefficientAddControl, StepControl.negativeGates,
    Phase.negativeAndGates, Phase.xorPairGates,
    StepLayout.remainderCleanupGates, StepLayout.swapCleanupGates,
    StepLayout.coefficientCleanupGates,
    StepLayout.remainderIntervalReverseGates,
    StepLayout.quotientDecrementGates, StepLayout.intervalNoSignReverseGates,
    List.countP_cons, RGate.isCx]
  omega

end Step
end Euclid
end VQ
