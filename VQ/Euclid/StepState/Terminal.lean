import VQ.Euclid.StepState.Common
import VQ.Euclid.StepState.PhaseZero

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

theorem preShiftBlock_act_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hterminal : Terminal s)
    (hnowrap : s.shift + 1 < 2 ^ shiftWidth) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  rw [preShiftBlock_act_phaseZero hterminal.2.2.2.2.1
    hterminal.2.2.2.2.2.1 hterminal.2.2.2.1 hnowrap]
  rw [step_terminal hterminal, nextCounter_eq_add_one hnowrap]

private theorem swapControl_identity_of_phase_zero
    {n lengthWidth shiftWidth I : Nat}
    (hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.swapControl n lengthWidth shiftWidth) I = I := by
  rw [StepBlocks.swapControl_act]
  simp only [Phase.xorPairOut, hclean.control, hphase1, hphase2,
    Nat.zero_add, Nat.zero_mod]
  exact writeField_zero_of_bitValue_zero hclean.control

private theorem quotientIncrementControl_identity_of_phase_zero
    {n lengthWidth shiftWidth I : Nat}
    (hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I := by
  rw [StepBlocks.quotientIncrementControl_act]
  simp only [Phase.negativeAndOut, hclean.control, hphase1, hphase2,
    if_pos, Nat.zero_add, Nat.zero_mod]
  exact writeField_zero_of_bitValue_zero hclean.control

private theorem quotientDecrementControl_identity_of_phase_zero
    {n lengthWidth shiftWidth I : Nat}
    (hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I := by
  rw [StepBlocks.quotientDecrementControl_act]
  simp only [Phase.negativeAndOut, hclean.control, hphase1, hphase2,
    if_pos, Nat.zero_add, Nat.zero_mod]
  exact writeField_zero_of_bitValue_zero hclean.control

private theorem coefficientSubControl_identity_of_phase_zero
    {n lengthWidth shiftWidth I : Nat}
    (hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I = I := by
  have htemporary : Phase.negativeAndOut
      (StepLayout.signWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.temporaryWire n lengthWidth shiftWidth) I = I := by
    simp only [Phase.negativeAndOut, hclean.temporary, hphase2, hsign,
      if_pos, Nat.zero_add, Nat.zero_mod]
    exact writeField_zero_of_bitValue_zero hclean.temporary
  rw [StepBlocks.coefficientSubControl_act]
  change Phase.negativeAndOut
      (StepLayout.phase1Wire n lengthWidth shiftWidth)
      (StepLayout.temporaryWire n lengthWidth shiftWidth)
      (StepLayout.controlWire n lengthWidth shiftWidth)
      (Phase.negativeAndOut
        (StepLayout.signWire n lengthWidth shiftWidth)
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth) I) = I
  rw [htemporary]
  simp only [Phase.negativeAndOut, hclean.control, hclean.temporary,
    hphase1, if_pos, Nat.zero_add, Nat.zero_mod]
  exact writeField_zero_of_bitValue_zero hclean.control

private def terminalSelectedEncoding
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  writeField (encoded n lengthWidth shiftWidth s)
    (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1 1

theorem rPrimeZeroSelectorGates_act_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hlength : 0 < lengthWidth) (hterminal : Terminal s) :
    actGates (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      terminalSelectedEncoding n lengthWidth shiftWidth s := by
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hpool : readField (encoded n lengthWidth shiftWidth s)
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    apply read_aux_subfield
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth]
      omega
  have hzero : bitValue (encoded n lengthWidth shiftWidth s)
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply read_aux_subfield
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth]
      omega
  rw [StepPlaced.rPrimeZeroSelectorGates_act hpool,
    read_lenRPrime_terminal hterminal, hzero]
  simp [terminalSelectedEncoding]

private theorem terminalSelected_auxCore
    {n lengthWidth shiftWidth off width : Nat} {s : State}
    (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
    (hhi : off + width ≤
      StepLayout.cellScratchWire n lengthWidth shiftWidth + 1) :
    readField (terminalSelectedEncoding n lengthWidth shiftWidth s) off width = 0 := by
  rw [terminalSelectedEncoding, readField_writeField_of_disjoint (Or.inr (by
    simp [StepLayout.zeroRPrimeWire]
    omega))]
  apply read_aux_subfield hlo
  calc
    off + width ≤ StepLayout.cellScratchWire n lengthWidth shiftWidth + 1 := hhi
    _ ≤ StepLayout.auxOffset n lengthWidth shiftWidth +
        StepLayout.auxWidth lengthWidth shiftWidth := by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth]
      omega

private theorem terminalSelected_bit_ne
    {n lengthWidth shiftWidth q : Nat} {s : State}
    (hne : q ≠ StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) :
    bitValue (terminalSelectedEncoding n lengthWidth shiftWidth s) q =
      bitValue (encoded n lengthWidth shiftWidth s) q := by
  exact bitValue_write_ne hne

private theorem terminalSelected_controlClean
    (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.ControlClean n lengthWidth shiftWidth
      (terminalSelectedEncoding n lengthWidth shiftWidth s) := by
  have h := controlClean n lengthWidth shiftWidth s
  constructor
  · rw [terminalSelected_bit_ne (by
      simp [StepLayout.controlWire, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.control
  · rw [terminalSelected_bit_ne (by
      simp [StepLayout.temporaryWire, StepLayout.zeroRPrimeWire])]
    exact h.temporary
  · rw [terminalSelected_bit_ne (by
      simp [StepLayout.plusWire, StepLayout.zeroRPrimeWire])]
    exact h.plus
  · rw [terminalSelected_bit_ne (by
      simp [StepLayout.minusWire, StepLayout.zeroRPrimeWire])]
    exact h.minus

private theorem terminalSelected_remainderScratch
    (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
      (terminalSelectedEncoding n lengthWidth shiftWidth s) := by
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  constructor
  · apply terminalSelected_auxCore (by simp [StepLayout.leftOffset])
    simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire]
    omega
  · apply terminalSelected_auxCore (by simp [StepLayout.rightOffset])
    simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire]
    omega
  · exact (terminalSelected_controlClean n lengthWidth shiftWidth s).control
  · rw [← readField_one]
    apply terminalSelected_auxCore
    · simp [StepLayout.carryWire, StepLayout.auxOffset]
    · simp [StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega
  · rw [← readField_one]
    apply terminalSelected_auxCore
    · simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega
    · simp [StepLayout.accumulatorWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega
  · rw [← readField_one]
    apply terminalSelected_auxCore
    · simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega
    · simp [StepLayout.leftFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega
  · rw [← readField_one]
    apply terminalSelected_auxCore
    · simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega
    · simp [StepLayout.rightFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega
  · apply terminalSelected_auxCore
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega
    · simp [StepLayout.cellScratchWire]
      omega
  · rw [← readField_one]
    apply terminalSelected_auxCore
    · simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega
    · omega

theorem guardedRemainderBlocks_act_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hterminal : Terminal s) :
    actGates (Step.guardedRemainderBlocks n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  let I := encoded n lengthWidth shiftWidth s
  let S := terminalSelectedEncoding n lengthWidth shiftWidth s
  have hselect : actGates
      (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth) I = S := by
    simpa [I, S] using
      rPrimeZeroSelectorGates_act_terminal hlength hterminal
  have hclean := terminalSelected_controlClean n lengthWidth shiftWidth s
  have hscratch := terminalSelected_remainderScratch n lengthWidth shiftWidth s
  have hp1 : bitValue S
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    rw [terminalSelected_bit_ne (by
      simp [StepLayout.phase1Wire, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega), read_phase1, hterminal.2.2.2.2.1]
    rfl
  have hp2 : bitValue S
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    rw [terminalSelected_bit_ne (by
      simp [StepLayout.phase2Wire, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega), read_phase2, hterminal.2.2.2.2.2.1]
    rfl
  have hsign : bitValue S
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    rw [terminalSelected_bit_ne (by
      simp [StepLayout.signWire, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega), read_sign, hterminal.2.2.2.2.2.2]
    rfl
  have hzrp : bitValue S
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1 := by
    simp [S, terminalSelectedEncoding, bitValue_write_self]
  have hsub := StepBlocks.guardedRemainderSubBlock_terminal hlength hwidths
    hscratch hclean hp1 hzrp
  have hflip := StepBlocks.remainderFlip_identity_of_phase2_zero hp2
  have hadd := StepBlocks.guardedRemainderAddBlock_terminal hlength hwidths
    hscratch hclean hp1 hp2 hsign hzrp
  apply StepBlocks.around_identity
    (StepLayout.rPrimeZeroSelectorGates_wellFormed n lengthWidth shiftWidth)
  rw [hselect]
  dsimp [S] at hsub hflip hadd ⊢
  simp only [actGates_append, hsub, hflip, hadd]

theorem coefficientPairWindow_terminal
    {n lengthWidth shiftWidth U : Nat} {s : State}
    (hfit : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hterminal : Terminal s)
    (hnowrap : s.shift + 1 < 2 ^ shiftWidth) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s)) := by
  let s' := step lengthWidth shiftWidth s
  let I := encoded n lengthWidth shiftWidth s'
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hfit
  have hterminal' : Terminal s' := by
    simpa [s'] using terminal_step hterminal
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I := by
    simpa [I] using controlClean n lengthWidth shiftWidth s'
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth I := by
    simpa [I] using encodedRemainderScratchClean
      n lengthWidth shiftWidth s'
  have hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_phase1, hterminal'.2.2.2.2.1]
    rfl
  have hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_phase2, hterminal'.2.2.2.2.2.1]
    rfl
  have hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_sign, hterminal'.2.2.2.2.2.2]
    rfl
  have hpre := preShiftBlock_act_terminal
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hterminal hnowrap
  have hrem : actGates
      (Step.guardedRemainderBlocks n lengthWidth shiftWidth) I = I := by
    simpa [I] using guardedRemainderBlocks_act_terminal
      (n := n) hlength hwidths hterminal'
  have hqincControl : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    quotientIncrementControl_identity_of_phase_zero hclean hphase1 hphase2
  have hqincScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates
          (Step.quotientIncrementControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hqincControl, StepPlaced.quotientInput_scratch]
    exact hscratch.pool
  have hqinc : actGates
      (Step.quotientIncrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientIncrementBlock_identity hqincScratch
    rw [hqincControl]
    exact hclean.control
  have hswapControl : actGates
      (Step.swapControl n lengthWidth shiftWidth) I = I :=
    swapControl_identity_of_phase_zero hclean hphase1 hphase2
  have hswapInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.swapControl n lengthWidth shiftWidth) I))) := by
    rw [hswapControl]
    exact StepPlaced.swapPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.left hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hswap : actGates
      (Step.swapBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.swapBlock_identity hlength hwidths hswapInactive
  have hqdecControl : actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I :=
    quotientDecrementControl_identity_of_phase_zero hclean hphase1 hphase2
  have hqdecScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates
          (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hqdecControl, StepPlaced.quotientInput_scratch]
    exact hscratch.pool
  have hqdec : actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientDecrementBlock_identity hqdecScratch
    rw [hqdecControl]
    exact hclean.control
  have hsubControl : actGates
      (Step.coefficientSubControl n lengthWidth shiftWidth) I = I :=
    coefficientSubControl_identity_of_phase_zero
      hclean hphase1 hphase2 hsign
  have hsubInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientSubControl n lengthWidth shiftWidth) I))) := by
    rw [hsubControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.right hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity hlength hwidths hsubInactive
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hphase1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hphase1
  have haddInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientAddControl n lengthWidth shiftWidth) I))) := by
    rw [haddControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.right hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  simp only [Step.coefficientPrefixGates, actGates_append]
  rw [hpre, show
    encoded n lengthWidth shiftWidth s' = I by rfl, hrem, hqinc, hswap,
    hqdec]
  change CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I) ∧
    CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientAddControl n lengthWidth shiftWidth)
        (actGates (Step.coefficientFlip n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubBlock n lengthWidth shiftWidth) I)))
  constructor
  · exact coefficientCallWindow_inactive hsubInactive
  · rw [hsub, hflip]
    exact coefficientCallWindow_inactive haddInactive

theorem gates_act_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hfit : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hterminal : Terminal s)
    (hnowrap : s.shift + 1 < 2 ^ shiftWidth) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  let s' := step lengthWidth shiftWidth s
  let I := encoded n lengthWidth shiftWidth s'
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hfit
  have hterminal' : Terminal s' := by
    simpa [s'] using terminal_step hterminal
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I := by
    simpa [I] using controlClean n lengthWidth shiftWidth s'
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth I := by
    simpa [I] using encodedRemainderScratchClean
      n lengthWidth shiftWidth s'
  have haux : readField I
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
    simpa [I] using read_aux n lengthWidth shiftWidth s'
  have hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_phase1, hterminal'.2.2.2.2.1]
    rfl
  have hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_phase2, hterminal'.2.2.2.2.2.1]
    rfl
  have hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    rw [read_sign, hterminal'.2.2.2.2.2.2]
    rfl
  have hpre := preShiftBlock_act_terminal
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hterminal hnowrap
  have hrem : actGates
      (Step.guardedRemainderBlocks n lengthWidth shiftWidth) I = I := by
    simpa [I] using guardedRemainderBlocks_act_terminal
      (n := n) hlength hwidths hterminal'
  have hqincControl : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    quotientIncrementControl_identity_of_phase_zero hclean hphase1 hphase2
  have hqincScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates
          (Step.quotientIncrementControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hqincControl, StepPlaced.quotientInput_scratch]
    exact hscratch.pool
  have hqinc : actGates
      (Step.quotientIncrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientIncrementBlock_identity hqincScratch
    rw [hqincControl]
    exact hclean.control
  have hswapControl : actGates
      (Step.swapControl n lengthWidth shiftWidth) I = I :=
    swapControl_identity_of_phase_zero hclean hphase1 hphase2
  have hswapInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.swapControl n lengthWidth shiftWidth) I))) := by
    rw [hswapControl]
    exact StepPlaced.swapPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.left hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hswap : actGates
      (Step.swapBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.swapBlock_identity hlength hwidths hswapInactive
  have hqdecControl : actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I :=
    quotientDecrementControl_identity_of_phase_zero hclean hphase1 hphase2
  have hqdecScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates
          (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hqdecControl, StepPlaced.quotientInput_scratch]
    exact hscratch.pool
  have hqdec : actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientDecrementBlock_identity hqdecScratch
    rw [hqdecControl]
    exact hclean.control
  have hsubControl : actGates
      (Step.coefficientSubControl n lengthWidth shiftWidth) I = I :=
    coefficientSubControl_identity_of_phase_zero
      hclean hphase1 hphase2 hsign
  have hsubInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientSubControl n lengthWidth shiftWidth) I))) := by
    rw [hsubControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.right hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity hlength hwidths hsubInactive
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hphase1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hphase1
  have haddInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientAddControl n lengthWidth shiftWidth) I))) := by
    rw [haddControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.right hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hadd : actGates
      (Step.coefficientAddBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddBlock_identity hlength hwidths haddInactive
  have hpostControl : actGates
      (Step.postShiftControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.postShiftControl_identity_of_phase1_zero_plus_zero
      hphase1 hclean.plus
  have hpostScratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hpostControl, StepPlaced.shiftInput_scratch]
    dsimp only [I]
    apply read_aux_subfield
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth,
        Nat.max_eq_right hwidths]
      omega
  have hpost : actGates
      (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
        (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I := by
    apply StepBlocks.postShiftBlock_identity hpostScratch
    · rw [hpostControl]
      exact hclean.plus
    · rw [hpostControl]
      exact hclean.minus
  have hshift : s'.shift = s.shift + 1 := by
    dsimp only [s']
    rw [step_terminal hterminal, nextCounter_eq_add_one hnowrap]
  have hshiftFit : s'.shift < 2 ^ shiftWidth := by
    rw [hshift]
    exact hnowrap
  have hshiftPositive : 0 < s'.shift := by
    rw [hshift]
    omega
  have hshiftEncoded : encodeLength shiftWidth s'.shift ≠
      encodedZero shiftWidth := by
    intro heq
    have hdecoded := decode_encodeLength hshiftFit
    rw [heq] at hdecoded
    simp [decodeLength, encodedZero] at hdecoded
    omega
  have hphase : actGates
      (StepLayout.phaseGates n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.phaseBlock_identity haux hphase1 hphase2 hsign
    dsimp only [I]
    rw [read_shift]
    exact hshiftEncoded
  have hownership : actGates
      (Step.ownershipBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.ownershipBlock_inactive hfit hclean.control haux
    right
    dsimp only [I]
    rw [read_shift]
    exact hshiftEncoded
  change actGates (Step.gates n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s) = I
  simp only [Step.gates, actGates_append]
  rw [hpre, hrem, hqinc, hswap, hqdec, hsub, hflip, hadd,
    hpost, hphase, hownership]

theorem reverseCircuit_recovers_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hfit : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hterminal : Terminal s)
    (hnowrap : s.shift + 1 < 2 ^ shiftWidth) :
    act (Step.reverseCircuit n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth s := by
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hfit
  have hforward : act (Step.circuit n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s) =
        encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s) := by
    simpa [act, Step.circuit] using gates_act_terminal
      hfit hwidths hterminal hnowrap
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
