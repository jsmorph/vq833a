import VQ.Euclid.StepState.Common

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

theorem preShiftBlock_act_phaseTwo
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  let I := encoded n lengthWidth shiftWidth s
  let C := actGates (Step.preShiftControl n lengthWidth shiftWidth) I
  have hcontrols := StepBlocks.preShiftControl_bits
    (controlClean n lengthWidth shiftWidth s)
  dsimp only at hcontrols
  rw [read_phase1, hphase1] at hcontrols
  simp only [boolValue, ↓reduceIte] at hcontrols
  have hCpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) shiftWidth = 0 := by
    have hselector : shiftWidth ≤
        StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_right _ _
    dsimp only [C, I]
    rw [preShiftControl_read]
    · apply read_aux_subfield
      · simp [StepLayout.poolOffset, StepLayout.carryWire]
        omega
      · simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth]
        omega
    · simp [StepLayout.plusWire, StepLayout.cellScratchWire]
      omega
    · simp [StepLayout.minusWire, StepLayout.cellScratchWire]
      omega
  have hscratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth C) = 0 := by
    rw [StepPlaced.shiftInput_scratch]
    exact hCpool
  apply StepBlocks.preShiftBlock_identity hscratch hcontrols.1 hcontrols.2

theorem guardedRemainderBlocks_act_phaseTwo
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.guardedRemainderBlocks n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  let I := encoded n lengthWidth shiftWidth s
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphase1 hphase2
  have hselect : actGates
      (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth) I = I := by
    simpa [I] using rPrimeZeroSelectorGates_act_live
      h.stepDomain.valid.1 hstate.2.1
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I := by
    simpa [I] using controlClean n lengthWidth shiftWidth s
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth I := by
    simpa [I] using encodedRemainderScratchClean
      n lengthWidth shiftWidth s
  have hp1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    simp [I, read_phase1, hphase1, boolValue]
  have hp2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, read_phase2, hphase2, boolValue]
  have hzrp : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
    dsimp only [I]
    apply read_aux_bit
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth]
      omega
  have hsub :=
    StepBlocks.guardedRemainderSubBlock_identity_of_phase1_one_live
      hlength hwidths hscratch hclean hp1 hzrp
  have hflip := StepBlocks.remainderFlip_identity_of_phase2_zero hp2
  have hadd :=
    StepBlocks.guardedRemainderAddBlock_identity_of_phase10_live
      hlength hwidths hscratch hclean hp1 hp2 hzrp
  apply StepBlocks.around_identity
    (StepLayout.rPrimeZeroSelectorGates_wellFormed n lengthWidth shiftWidth)
  rw [hselect]
  simp only [actGates_append, hsub, hflip, hadd]

theorem quotientIncrementBlock_act_phaseTwo
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase2 : s.phase2 = false) :
    actGates (Step.quotientIncrementBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  let I := encoded n lengthWidth shiftWidth s
  have hp2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, read_phase2, hphase2, boolValue]
  have hcontrol : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientIncrementControl_identity_of_phase2_zero hp2
  have hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates
          (Step.quotientIncrementControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hcontrol, StepPlaced.quotientInput_scratch]
    exact (encodedRemainderScratchClean
      n lengthWidth shiftWidth s).pool
  apply StepBlocks.quotientIncrementBlock_identity hscratch
  rw [hcontrol]
  exact (controlClean n lengthWidth shiftWidth s).control

theorem swapControl_act_phaseTwo
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.swapControl n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      writeField (encoded n lengthWidth shiftWidth s)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  have hclean := controlClean n lengthWidth shiftWidth s
  rw [StepBlocks.swapControl_act]
  simp [Phase.xorPairOut, hclean.control, read_phase1, read_phase2,
    hphase1, hphase2, boolValue]

theorem swapBlock_act_phaseTwoQuotientCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    let left := s.lenT + s.lenQ
    let takeBit := boolValue (s.q.testBit s.shift)
    actGates (Step.swapBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      writeField
        (writeField (encoded n lengthWidth shiftWidth s)
          StepLayout.work1Offset (workWidth n)
          (writeField (encodeWork1 n s % 2 ^ workWidth n)
            left 1 0))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 takeBit := by
  let left := s.lenT + s.lenQ
  let takeBit := boolValue (s.q.testBit s.shift)
  let E := encoded n lengthWidth shiftWidth s
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let C := actGates (Step.swapControl n lengthWidth shiftWidth) E
  let P := actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) C
  let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
  change actGates (Step.swapBlock n lengthWidth shiftWidth) E =
    writeField
      (writeField E StepLayout.work1Offset (workWidth n)
        (writeField (encodeWork1 n s % 2 ^ workWidth n) left 1 0))
      (StepLayout.signWire n lengthWidth shiftWidth) 1 takeBit
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphase1 hphase2
  have hlenQPos : 0 < s.lenQ := hstate.2.2.1
  have htPos := ReachableStepDomain.phaseTwo_t_pos
    h hphase1 hphase2
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPos
  have hleftBound : left < workWidth n := by
    have hallocation := h.stepDomain.valid.1.2.2.2.2.2.2.1
    dsimp only [left]
    omega
  have hC : C = writeField E control 1 1 := by
    simpa [C, E, control] using
      swapControl_act_phaseTwo (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) hphase1 hphase2
  have hCread (off len : Nat)
      (hout : control + 1 ≤ off ∨ off + len ≤ control) :
      readField C off len = readField E off len := by
    rw [hC]
    exact readField_writeField_of_disjoint hout
  have hCbit (q : Nat)
      (hout : control + 1 ≤ q ∨ q + 1 ≤ control) :
      bitValue C q = bitValue E q := by
    simpa [readField_one] using hCread q 1 hout
  have hClenT : readField C (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    exact (hCread _ _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans (read_lenT n lengthWidth shiftWidth s)
  have hClenQ : readField C
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
        encodeLength lengthWidth s.lenQ := by
    exact (hCread _ _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.lenQOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans (read_lenQ n lengthWidth shiftWidth s)
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth s
  have hCleft : readField C
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftOffset,
        StepLayout.auxOffset]))).trans hscratch.left
  have hCright : readField C
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightOffset,
        StepLayout.auxOffset]))).trans hscratch.right
  have hCcontrol : bitValue C control = 1 := by
    rw [hC, bitValue_write_self]
  have hCcarry : bitValue C
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.carryWire,
        StepLayout.auxOffset]))).trans hscratch.carry
  have hCaccumulator : bitValue C
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.accumulator
  have hCleftFlag : bitValue C
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.leftFlag
  have hCrightFlag : bitValue C
      (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.rightFlag
  have hCpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.pool
  have hCcellScratch : bitValue C
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.cellScratch
  have hencodedLenT : encodeLength lengthWidth s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPos),
      Nat.mod_eq_of_lt (by
        have := h.stepDomain.valid.1.2.2.1
        omega)]
  have hencodedLenQ : encodeLength lengthWidth s.lenQ = s.lenQ - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenQPos),
      Nat.mod_eq_of_lt (by
        have := h.stepDomain.valid.1.2.2.2.1
        omega)]
  have hsum : 2 +
      readField C (StepLayout.lenQOffset n lengthWidth) lengthWidth +
      readField C (StepLayout.lenTOffset n) lengthWidth <
        2 ^ lengthWidth := by
    rw [hClenQ, hClenT, hencodedLenQ, hencodedLenT]
    have hallocation := h.stepDomain.valid.1.2.2.2.2.2.2.1
    omega
  have hprepared := StepPlaced.swapPrepare_frame_of_live_frame
    hlength hwidths hCleft hCright hCcontrol hCcarry hCaccumulator
    hCleftFlag hCrightFlag hCpool hCcellScratch hsum
  dsimp only at hprepared
  rw [hClenQ, hClenT, hencodedLenQ, hencodedLenT] at hprepared
  have hleftEq : 2 + (s.lenQ - 1) + (s.lenT - 1) = left := by
    dsimp only [left]
    omega
  rw [hleftEq] at hprepared
  have hstable : Interval.Stable left 0 (workWidth n) lengthWidth input := by
    simpa [left, input, P] using hprepared.stable
  have haccumulator : bitValue input
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [input, P] using hprepared.accumulator
  have hPwork : readField P StepLayout.work1Offset (workWidth n) =
      readField E StepLayout.work1Offset (workWidth n) := by
    exact hprepared.work1.trans (hCread _ _ (Or.inr (by
      simp [control, StepLayout.work1Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)))
  have hEwork : readField E StepLayout.work1Offset (workWidth n) =
      encodeWork1 n s % 2 ^ workWidth n := by
    simpa [E] using read_work1 n lengthWidth shiftWidth s
  have hPsign : bitValue P
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    have hCsign : bitValue C
        (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
      exact (hCbit _ (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.signWire]))).trans <|
        by simp [E, read_sign,
          (ReachableStepDomain.phaseTwo_stateFacts
            h hphase1 hphase2).1, boolValue]
    exact hprepared.sign.trans hCsign
  have hworkValue : SelectSwap.workValue left (workWidth n) lengthWidth input =
      writeField (encodeWork1 n s % 2 ^ workWidth n) left 1 0 := by
    simp only [SelectSwap.workValue, if_pos hleftBound]
    rw [StepPlaced.intervalInput_source, hPwork, hEwork,
      StepPlaced.intervalInput_sign, hPsign]
  have hEtest : E.testBit (StepLayout.work1Offset + left) =
      s.q.testBit s.shift := by
    have htest := congrArg (fun z => z.testBit left) hEwork
    have hlogical := testBit_encodeWork1_currentQuotient (n := n) (s := s)
      h.stepDomain.valid.1.2.2.2.2.2.2.2.2.1 hlenQPos
    have hphysical : E.testBit (StepLayout.work1Offset + left) =
        (encodeWork1 n s).testBit left := by
      simpa [testBit_readField, hleftBound, StepLayout.work1Offset,
        Nat.testBit_mod_two_pow] using htest
    exact hphysical.trans (by simpa [left] using hlogical)
  have hPtest : P.testBit (StepLayout.work1Offset + left) =
      E.testBit (StepLayout.work1Offset + left) := by
    have htest := congrArg (fun z => z.testBit left) hPwork
    simpa [testBit_readField, hleftBound, StepLayout.work1Offset] using htest
  have hPbit : bitValue P (StepLayout.work1Offset + left) = takeBit := by
    simp [bitValue, hPtest, hEtest, takeBit, boolValue]
  have hsignValue : SelectSwap.signValue left
      (workWidth n) lengthWidth input = takeBit := by
    simp only [SelectSwap.signValue, if_pos hleftBound]
    rw [StepPlaced.intervalInput_source_bit n lengthWidth shiftWidth left P
      hleftBound]
    exact hPbit
  have hblock := StepBlocks.swapBlock_act
    (I := E) (left := left) (right := 0) hlength hwidths
    (Nat.le_of_lt hwork) hstable haccumulator
  dsimp only at hblock
  rw [hworkValue, hsignValue] at hblock
  simpa [E, C, P, input] using hblock

def phaseTwoPostSwapCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  writeField
    (writeField (encoded n lengthWidth shiftWidth s)
      StepLayout.work1Offset (workWidth n)
      (encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n))
    (StepLayout.signWire n lengthWidth shiftWidth) 1
    (boolValue (s.q.testBit s.shift))

theorem swapBlock_act_phaseTwoPostSwapCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.swapBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      phaseTwoPostSwapCheckpoint n lengthWidth shiftWidth s := by
  have hswap := swapBlock_act_phaseTwoQuotientCheckpoint
    h hwork hwidths hphase1 hphase2
  dsimp only at hswap
  rw [hswap, ReachableStepDomain.phaseTwo_work1_after_quotientRemoval
    h hwork hwidths hphase1 hphase2]
  rfl

def phaseTwoPostQuotientCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  writeField (phaseTwoPostSwapCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.lenQOffset n lengthWidth) lengthWidth
    (encodeLength lengthWidth (s.lenQ - 1))

theorem quotientDecrementBlock_act_phaseTwoPostSwapCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.quotientDecrementBlock n lengthWidth shiftWidth)
        (phaseTwoPostSwapCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s := by
  let S := phaseTwoPostSwapCheckpoint n lengthWidth shiftWidth s
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let C := actGates
    (Step.quotientDecrementControl n lengthWidth shiftWidth) S
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphase1 hphase2
  have hlenQPos : 0 < s.lenQ := hstate.2.2.1
  have hlenQFit := h.stepDomain.valid.1.2.2.2.1
  have hSread (off len : Nat)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ off ∨
        off + len ≤ StepLayout.work1Offset)
      (hsign : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ off ∨
        off + len ≤ StepLayout.signWire n lengthWidth shiftWidth) :
      readField S off len =
        readField (encoded n lengthWidth shiftWidth s) off len := by
    simp only [S, phaseTwoPostSwapCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork1]
  have hSbit (q : Nat)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ q ∨
        q + 1 ≤ StepLayout.work1Offset)
      (hsign : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q ∨
        q + 1 ≤ StepLayout.signWire n lengthWidth shiftWidth) :
      bitValue S q =
        bitValue (encoded n lengthWidth shiftWidth s) q := by
    simpa [readField_one] using hSread q 1 hwork1 hsign
  have hScontrol : bitValue S control = 0 := by
    exact (hSbit _ (Or.inl (by
      simp [StepLayout.work1Offset, control, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.signWire]))).trans
      (controlClean n lengthWidth shiftWidth s).control
  have hSp1 : bitValue S
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    exact (hSbit _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]
      omega)) (Or.inr (by
      simp [StepLayout.signWire, StepLayout.phase1Wire]))).trans <| by
      simp [read_phase1, hphase1, boolValue]
  have hSp2 : bitValue S
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    exact (hSbit _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inr (by
      simp [StepLayout.signWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire]))).trans <| by
      simp [read_phase2, hphase2, boolValue]
  have hClocal : C = writeField S control 1 1 := by
    dsimp only [C]
    rw [StepBlocks.quotientDecrementControl_act]
    simp [Phase.negativeAndOut, hScontrol, hSp1, hSp2, control]
  have hSpool : readField S
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hSread _ _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inl (by
      simp [StepLayout.signWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans (encodedRemainderScratchClean
        n lengthWidth shiftWidth s).pool
  have hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth C) = 0 := by
    rw [StepPlaced.quotientInput_scratch, hClocal,
      readField_writeField_of_disjoint (Or.inl (by
        simp [control, StepLayout.controlWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))]
    exact hSpool
  have hSlenQ : readField S
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
        encodeLength lengthWidth s.lenQ := by
    exact (hSread _ _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.lenQOffset, workWidth]
      omega)) (Or.inr (by
      simp [StepLayout.signWire, StepLayout.lenQOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans (read_lenQ n lengthWidth shiftWidth s)
  have hvalue : StepPlaced.quotientDecrementValue
      n lengthWidth shiftWidth C =
        encodeLength lengthWidth (s.lenQ - 1) := by
    simp only [StepPlaced.quotientDecrementValue]
    rw [hClocal, bitValue_write_self,
      readField_writeField_of_disjoint (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.lenQOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hSlenQ]
    exact encodeLength_pred hlenQPos hlenQFit
  have hblock := StepBlocks.quotientDecrementBlock_act
    (I := S) hscratch
  dsimp only at hblock
  rw [hvalue] at hblock
  simpa [S, C, phaseTwoPostQuotientCheckpoint] using hblock

private structure PhaseTwoPostQuotientCheckpointFrame
    (n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  controlClean : StepBlocks.ControlClean n lengthWidth shiftWidth
    (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
  scratch : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
    (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
  aux : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0
  work1 : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      StepLayout.work1Offset (workWidth n) =
    encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n
  work2 : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.work2Offset n) (workWidth n) = encodeWork2 n s
  lenT : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenTOffset n) lengthWidth =
    encodeLength lengthWidth s.lenT
  lenQ : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
    encodeLength lengthWidth (s.lenQ - 1)
  lenRPrime : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
    encodeLength lengthWidth s.lenRPrime
  shift : readField
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
    encodeLength shiftWidth s.shift
  phase1 : bitValue
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1
  phase2 : bitValue
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0
  iter : bitValue
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.iterWire n lengthWidth shiftWidth) = boolValue s.iter
  sign : bitValue
      (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.signWire n lengthWidth shiftWidth) =
    boolValue (s.q.testBit s.shift)

private theorem phaseTwoPostQuotientCheckpoint_frame
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    PhaseTwoPostQuotientCheckpointFrame n lengthWidth shiftWidth s := by
  let E := encoded n lengthWidth shiftWidth s
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let lenQOffset := StepLayout.lenQOffset n lengthWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hread (off width : Nat)
      (hlenQ : lenQOffset + lengthWidth ≤ off ∨
        off + width ≤ lenQOffset)
      (hsign : sign + 1 ≤ off ∨ off + width ≤ sign)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ off ∨
        off + width ≤ StepLayout.work1Offset) :
      readField S off width = readField E off width := by
    simp only [S, phaseTwoPostQuotientCheckpoint,
      phaseTwoPostSwapCheckpoint]
    rw [readField_writeField_of_disjoint hlenQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork1]
  have hbit (q : Nat)
      (hlenQ : lenQOffset + lengthWidth ≤ q ∨ q + 1 ≤ lenQOffset)
      (hsign : sign + 1 ≤ q ∨ q + 1 ≤ sign)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ q ∨
        q + 1 ≤ StepLayout.work1Offset) :
      bitValue S q = bitValue E q := by
    simpa [readField_one] using hread q 1 hlenQ hsign hwork1
  have hafterSign (off width : Nat) (hoff : sign + 1 ≤ off) :
      readField S off width = readField E off width := by
    apply hread
    · left
      dsimp only [lenQOffset, sign] at hoff ⊢
      simp [StepLayout.lenQOffset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset] at hoff ⊢
      omega
    · exact Or.inl hoff
    · left
      dsimp only [sign] at hoff ⊢
      simp [StepLayout.work1Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset] at hoff ⊢
      omega
  have hbitAfterSign (q : Nat) (hq : sign + 1 ≤ q) :
      bitValue S q = bitValue E q := by
    simpa [readField_one] using hafterSign q 1 hq
  have hcleanE := controlClean n lengthWidth shiftWidth s
  have hscratchE := encodedRemainderScratchClean
    n lengthWidth shiftWidth s
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth S := by
    constructor
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.controlWire])).trans
        hcleanE.control
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hcleanE.temporary
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.plusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hcleanE.plus
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.minusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hcleanE.minus
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth S := by
    constructor
    · exact (hafterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.leftOffset,
            StepLayout.auxOffset])).trans hscratchE.left
    · exact (hafterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.rightOffset,
            StepLayout.auxOffset]
          omega)).trans hscratchE.right
    · exact hclean.control
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega)).trans hscratchE.carry
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.accumulatorWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hscratchE.accumulator
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.leftFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hscratchE.leftFlag
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.rightFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hscratchE.rightFlag
    · exact (hafterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hscratchE.pool
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega)).trans hscratchE.cellScratch
  have haux : readField S
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
    exact (hafterSign _ _ (by
      simp [sign, StepLayout.signWire, StepLayout.auxOffset])).trans
      (read_aux n lengthWidth shiftWidth s)
  refine ⟨hclean, hscratch, haux, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [phaseTwoPostQuotientCheckpoint,
      phaseTwoPostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.lenQOffset, StepLayout.work1Offset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.signWire, StepLayout.work1Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)),
      readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos _))]
  · exact (hread _ _ (Or.inr (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.work2Offset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.work2Offset,
          workWidth]))).trans (read_work2 n lengthWidth shiftWidth s)
  · exact (hread _ _ (Or.inr (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.lenTOffset]))
      (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.lenTOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)) (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.lenTOffset,
          workWidth]))).trans (read_lenT n lengthWidth shiftWidth s)
  · simp only [phaseTwoPostQuotientCheckpoint]
    rw [readField_writeField_self (encodeLength_lt lengthWidth (s.lenQ - 1))]
  · exact (hread _ _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset,
          StepLayout.lenRPrimeOffset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.lenRPrimeOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)) (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.lenRPrimeOffset,
          workWidth]
        omega))).trans (read_lenRPrime n lengthWidth shiftWidth s)
  · exact (hread _ _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.shiftOffset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire]))
      (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.shiftOffset, workWidth]
        omega))).trans (read_shift n lengthWidth shiftWidth s)
  · exact (hbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire]))
      (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega))).trans (by simp [E, read_phase1, hphase1, boolValue])
  · exact (hbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.phase2Wire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase2Wire,
          StepLayout.phase1Wire])) (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.phase2Wire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))).trans (by simp [E, read_phase2, hphase2, boolValue])
  · exact (hbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.iterWire]))
      (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))).trans (read_iter n lengthWidth shiftWidth s)
  · simp only [phaseTwoPostQuotientCheckpoint,
      phaseTwoPostSwapCheckpoint]
    rw [← readField_one,
      readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.signWire, StepLayout.lenQOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), readField_writeField_self]
    exact boolValue_lt (s.q.testBit s.shift)

theorem coefficientSubControl_bits_phaseTwoPostQuotientCheckpoint
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
    let C := actGates
      (Step.coefficientSubControl n lengthWidth shiftWidth) S
    bitValue C (StepLayout.temporaryWire n lengthWidth shiftWidth) =
        boolValue (s.q.testBit s.shift) ∧
      bitValue C (StepLayout.controlWire n lengthWidth shiftWidth) =
        if s.q.testBit s.shift then 0 else 1 := by
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let C := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) S
  have hSbit (q : Nat)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ q ∨
        q + 1 ≤ StepLayout.work1Offset)
      (hsign : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q ∨
        q + 1 ≤ StepLayout.signWire n lengthWidth shiftWidth)
      (hlenQ : StepLayout.lenQOffset n lengthWidth + lengthWidth ≤ q ∨
        q + 1 ≤ StepLayout.lenQOffset n lengthWidth) :
      bitValue S q =
        bitValue (encoded n lengthWidth shiftWidth s) q := by
    simp only [S, phaseTwoPostQuotientCheckpoint,
      phaseTwoPostSwapCheckpoint]
    rw [← readField_one,
      readField_writeField_of_disjoint hlenQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork1, readField_one]
  have hSp1 : bitValue S
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    rw [hSbit]
    · simp [read_phase1, hphase1, boolValue]
    · left
      simp [StepLayout.work1Offset, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]
      omega
    · right
      simp [StepLayout.signWire, StepLayout.phase1Wire]
    · left
      simp [StepLayout.lenQOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega
  have hSp2 : bitValue S
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    rw [hSbit]
    · simp [read_phase2, hphase2, boolValue]
    · left
      simp [StepLayout.work1Offset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega
    · right
      simp [StepLayout.signWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire]
    · left
      simp [StepLayout.lenQOffset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
  have hSsign : bitValue S
      (StepLayout.signWire n lengthWidth shiftWidth) =
        boolValue (s.q.testBit s.shift) := by
    simp only [S, phaseTwoPostQuotientCheckpoint,
      phaseTwoPostSwapCheckpoint]
    rw [← readField_one,
      readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.signWire, StepLayout.lenQOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), readField_writeField_self]
    exact boolValue_lt (s.q.testBit s.shift)
  have hSclean : StepBlocks.ControlClean n lengthWidth shiftWidth S := by
    have hclean := controlClean n lengthWidth shiftWidth s
    constructor
    · exact (hSbit _ (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [StepLayout.signWire, StepLayout.controlWire])) (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hclean.control
    · exact (hSbit _ (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.temporaryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [StepLayout.signWire, StepLayout.temporaryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.temporaryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hclean.temporary
    · exact (hSbit _ (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.plusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [StepLayout.signWire, StepLayout.plusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.plusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hclean.plus
    · exact (hSbit _ (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.minusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [StepLayout.signWire, StepLayout.minusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.minusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hclean.minus
  constructor
  · rw [StepBlocks.coefficientSubControl_act]
    change bitValue
      (Phase.negativeAndOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth)
        (Phase.negativeAndOut
          (StepLayout.signWire n lengthWidth shiftWidth)
          (StepLayout.phase2Wire n lengthWidth shiftWidth)
          (StepLayout.temporaryWire n lengthWidth shiftWidth) S))
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = _
    rw [Phase.negativeAndOut_ne (by
      simp only [StepLayout.temporaryWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega),
      Phase.negativeAndOut_target, hSclean.temporary, hSp2, hSsign]
    cases s.q.testBit s.shift <;> simp [boolValue]
  · have hcontrol := StepBlocks.coefficientSubControl_bit hSclean
    dsimp only at hcontrol
    rw [hSp1, hSp2, hSsign] at hcontrol
    cases hbit : s.q.testBit s.shift
    · simpa [hbit, S, boolValue] using hcontrol
    · simpa [hbit, S, boolValue] using hcontrol

private theorem coefficientSubControl_act_phaseTwoPostQuotientCheckpoint
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
    actGates (Step.coefficientSubControl n lengthWidth shiftWidth) S =
      writeField
        (writeField S (StepLayout.temporaryWire n lengthWidth shiftWidth) 1
          (boolValue (s.q.testBit s.shift)))
        (StepLayout.controlWire n lengthWidth shiftWidth) 1
        (boolValue (!(s.q.testBit s.shift))) := by
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hframe := phaseTwoPostQuotientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hp1 : bitValue S p1 = 1 := hframe.phase1
  have hp2 : bitValue S p2 = 0 := hframe.phase2
  have htemporary : bitValue S temporary = 0 := hframe.controlClean.temporary
  have hcontrol : bitValue S control = 0 := hframe.controlClean.control
  have hsign : bitValue S sign = boolValue (s.q.testBit s.shift) :=
    hframe.sign
  dsimp only
  rw [StepBlocks.coefficientSubControl_act]
  simp only [StepBlocks.coefficientSubControlOut]
  change Phase.negativeAndOut p1 temporary control
      (Phase.negativeAndOut sign p2 temporary S) =
    writeField
      (writeField S temporary 1 (boolValue (s.q.testBit s.shift)))
      control 1 (boolValue (!(s.q.testBit s.shift)))
  cases hbit : s.q.testBit s.shift
  · have hsignZero : bitValue S sign = 0 := by
      simpa [hbit, boolValue] using hsign
    have hfirst : Phase.negativeAndOut sign p2 temporary S = S := by
      simp only [Phase.negativeAndOut, hp2, hsignZero, htemporary,
        if_pos, Nat.zero_add, Nat.zero_mod]
      exact writeField_zero_of_bitValue_zero htemporary
    rw [hfirst]
    change Phase.negativeAndOut p1 temporary control S =
      writeField (writeField S temporary 1 0) control 1 1
    rw [writeField_zero_of_bitValue_zero htemporary]
    simp [Phase.negativeAndOut, hp1, htemporary, hcontrol]
  · have hsignOne : bitValue S sign = 1 := by
      simpa [hbit, boolValue] using hsign
    let K := writeField S temporary 1 1
    have hfirst : Phase.negativeAndOut sign p2 temporary S = K := by
      simp only [Phase.negativeAndOut, hp2, hsignOne, htemporary,
        if_pos, Nat.zero_add, Nat.one_mod, K]
    have hKtemporary : bitValue K temporary = 1 := by
      simp [K, bitValue_write_self]
    have hKp1 : bitValue K p1 = 1 := by
      rw [bitValue_write_ne (by
        simp [p1, temporary, StepLayout.phase1Wire,
          StepLayout.temporaryWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.shiftOffset]
        omega)]
      exact hp1
    have hKcontrol : bitValue K control = 0 := by
      rw [bitValue_write_ne (by
        simp [control, temporary, StepLayout.controlWire,
          StepLayout.temporaryWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega)]
      exact hcontrol
    rw [hfirst]
    change Phase.negativeAndOut p1 temporary control K =
      writeField K control 1 0
    simp only [Phase.negativeAndOut, hKp1, hKtemporary, hKcontrol,
      one_ne_zero, if_false, Nat.add_zero, Nat.zero_mod]

private theorem coefficientSubBlock_phaseTwoSelected_result
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hselected : s.q.testBit s.shift = true) :
    StepPlaced.IntervalInactive (workWidth n) lengthWidth
        (StepPlaced.intervalInput n lengthWidth shiftWidth
          (actGates
            (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
            (actGates (Step.coefficientSubControl n lengthWidth shiftWidth)
              (phaseTwoPostQuotientCheckpoint
                n lengthWidth shiftWidth s)))) ∧
      actGates (Step.coefficientSubBlock n lengthWidth shiftWidth)
          (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
        phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s := by
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let C := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) S
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hframe := phaseTwoPostQuotientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hC : C = writeField (writeField S temporary 1 1) control 1 0 := by
    simpa [C, S, temporary, control, hselected, boolValue] using
      coefficientSubControl_act_phaseTwoPostQuotientCheckpoint
        (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
        hphase1 hphase2
  have hCread (off width : Nat)
      (hcontrol : control + 1 ≤ off ∨ off + width ≤ control)
      (htemporary : temporary + 1 ≤ off ∨
        off + width ≤ temporary) :
      readField C off width = readField S off width := by
    rw [hC, readField_writeField_of_disjoint hcontrol,
      readField_writeField_of_disjoint htemporary]
  have hCbit (q : Nat)
      (hcontrol : control + 1 ≤ q ∨ q + 1 ≤ control)
      (htemporary : temporary + 1 ≤ q ∨ q + 1 ≤ temporary) :
      bitValue C q = bitValue S q := by
    simpa [readField_one] using hCread q 1 hcontrol htemporary
  have hright : readField C
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightOffset,
        StepLayout.auxOffset])) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.rightOffset,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hframe.scratch.right
  have hcontrol : bitValue C control = 0 := by
    rw [hC, bitValue_write_self]
  have hcarry : bitValue C
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.carryWire,
        StepLayout.auxOffset])) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.carryWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hframe.scratch.carry
  have haccumulator : bitValue C
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire,
        StepLayout.accumulatorWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega))).trans hframe.scratch.accumulator
  have hleftFlag : bitValue C
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.leftFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hframe.scratch.leftFlag
  have hrightFlag : bitValue C
      (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.rightFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hframe.scratch.rightFlag
  have hpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.poolOffset,
        StepLayout.cellScratchWire, StepLayout.selectorWidth,
        Nat.max_eq_right hwidths]
      omega))).trans hframe.scratch.pool
  have hcellScratch : bitValue C
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)) (Or.inr (by
      simp [temporary, StepLayout.temporaryWire,
        StepLayout.cellScratchWire]))).trans hframe.scratch.cellScratch
  have hinactive := StepPlaced.coefficientPrepare_inactive_of_physical_scratch
    hlength hwidths hright hcontrol hcarry haccumulator hleftFlag
    hrightFlag hpool hcellScratch
  exact ⟨by simpa [C, S] using hinactive,
    StepBlocks.coefficientSubBlock_identity hlength hwidths hinactive⟩

private theorem coefficientSubBlock_identity_phaseTwoSelected
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hselected : s.q.testBit s.shift = true) :
    actGates (Step.coefficientSubBlock n lengthWidth shiftWidth)
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s := by
  exact (coefficientSubBlock_phaseTwoSelected_result
    hwork hwidths hphase1 hphase2 hselected).2

private theorem coefficientPrepare_frame_of_controlled_scratch
    {n lengthWidth shiftWidth I J lenT : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hI : I = writeField J
      (StepLayout.controlWire n lengthWidth shiftWidth) 1 1)
    (hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth J)
    (hphase2 : bitValue J
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hlenTread : readField J (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth lenT)
    (hlenTPos : 0 < lenT) (hlenTFit : lenT < 2 ^ lengthWidth) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    StepPlaced.CoefficientPreparedFrame
      n lengthWidth shiftWidth I P 0 lenT := by
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hread (off width : Nat)
      (hout : control + 1 ≤ off ∨ off + width ≤ control) :
      readField I off width = readField J off width := by
    rw [hI, readField_writeField_of_disjoint hout]
  have hbit (q : Nat)
      (hout : control + 1 ≤ q ∨ q + 1 ≤ control) :
      bitValue I q = bitValue J q := by
    simpa [readField_one] using hread q 1 hout
  have hlenTI : readField I (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth lenT := by
    exact (hread _ _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans hlenTread
  have hrightValue : lenT =
      1 + readField I (StepLayout.lenTOffset n) lengthWidth := by
    rw [hlenTI]
    have hpredFit : lenT - 1 < 2 ^ lengthWidth :=
      (Nat.sub_le lenT 1).trans_lt hlenTFit
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPos),
      Nat.mod_eq_of_lt hpredFit]
    omega
  apply StepPlaced.coefficientPrepare_frame_of_live_frame
    hlength hwidths
  · exact (hread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftOffset,
        StepLayout.auxOffset]))).trans hscratch.left
  · exact (hread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightOffset,
        StepLayout.auxOffset]))).trans hscratch.right
  · exact hrightValue
  · rw [hI, bitValue_write_self]
  · exact (hbit _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]))).trans hphase2
  · exact (hbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.carryWire,
        StepLayout.auxOffset]))).trans hscratch.carry
  · exact (hbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.accumulator
  · exact (hbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.leftFlag
  · exact (hbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.rightFlag
  · exact (hread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hscratch.pool
  · exact (hbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega))).trans hscratch.cellScratch
  · exact hlenTFit

theorem coefficientFlip_act_phaseTwoSelectedBit
    {n lengthWidth shiftWidth I : Nat} {selected : Bool}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hsign : bitValue I (StepLayout.signWire n lengthWidth shiftWidth) =
      boolValue selected) :
    actGates (Step.coefficientFlip n lengthWidth shiftWidth) I =
      writeField I (StepLayout.signWire n lengthWidth shiftWidth) 1
        (boolValue (!selected)) := by
  rw [StepBlocks.coefficientFlip_act, hphase1, hsign]
  cases selected <;> rfl

theorem coefficientAddControl_act_phaseTwo
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I =
      writeField I (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  rw [StepBlocks.coefficientAddControl_act, hphase1, hcontrol]

def phaseTwoPostCoefficientCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  let tPrime := if s.q.testBit s.shift then
    s.tPrime + shifted s.t s.shift else s.tPrime
  writeField
    (writeField (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.work2Offset n) (workWidth n)
      (encodeWork2 n { s with tPrime := tPrime }))
    (StepLayout.signWire n lengthWidth shiftWidth) 1 0

private theorem coefficientBlocks_phaseTwoSelected_result
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hselected : s.q.testBit s.shift = true)
    (hU : s.lenT + 1 ≤ U) :
    CoefficientPairWindow n lengthWidth shiftWidth U
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) ∧
      actGates
          (Step.coefficientSubBlock n lengthWidth shiftWidth ++
            Step.coefficientFlip n lengthWidth shiftWidth ++
            Step.coefficientAddBlock n lengthWidth shiftWidth)
          (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
        phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
  let width := s.lenT + 1
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let F := actGates (Step.coefficientFlip n lengthWidth shiftWidth) S
  let C := actGates
    (Step.coefficientAddControl n lengthWidth shiftWidth) F
  let P := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C
  let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, _hlenRPrime, hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphase1 hphase2
  have htPos := ReachableStepDomain.phaseTwo_t_pos
    h hphase1 hphase2
  have hframe := phaseTwoPostQuotientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hsubResult := coefficientSubBlock_phaseTwoSelected_result
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hwork hwidths hphase1 hphase2 hselected
  have hsubInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientSubControl n lengthWidth shiftWidth) S))) := by
    simpa [S] using hsubResult.1
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) S = S := by
    simpa [S] using hsubResult.2
  have hF : F = writeField S sign 1 0 := by
    have hflip := coefficientFlip_act_phaseTwoSelectedBit
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      hframe.phase1 hframe.sign
    simpa [F, sign, hselected, boolValue] using hflip
  have hscratchF : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth F := by
    rw [hF]
    exact remainderScratchClean_write_sign hframe.scratch
  have hp2F : bitValue F
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    rw [hF, bitValue_write_ne (by
      simp [sign, StepLayout.signWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire])]
    exact hframe.phase2
  have hp1F : bitValue F
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    rw [hF, bitValue_write_ne (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire])]
    exact hframe.phase1
  have hcontrolF : bitValue F control = 0 := by
    simpa [control] using hscratchF.control
  have hC : C = writeField F control 1 1 := by
    simpa [C, control] using
      coefficientAddControl_act_phaseTwo hp1F hcontrolF
  have hlenTF : readField F (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [hF, readField_writeField_of_disjoint (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
    exact hframe.lenT
  have hprepared := coefficientPrepare_frame_of_controlled_scratch
    (I := C) (J := F) (lenT := s.lenT) hlength hwidths hC hscratchF
    hp2F hlenTF (by rw [hlenT]; exact bitLength_pos htPos) hlenTFit
  dsimp only at hprepared
  change StepPlaced.CoefficientPreparedFrame
    n lengthWidth shiftWidth C P 0 s.lenT at hprepared
  have hfit : width ≤ workWidth n := by
    have hwindow := ReachableStepDomain.phaseTwo_coefficientWindow
      h hphase1 hphase2
    dsimp only [width]
    omega
  have hCread (off fieldWidth : Nat)
      (hcontrolOut : control + 1 ≤ off ∨
        off + fieldWidth ≤ control)
      (hsignOut : sign + 1 ≤ off ∨ off + fieldWidth ≤ sign) :
      readField C off fieldWidth = readField S off fieldWidth := by
    rw [hC, readField_writeField_of_disjoint hcontrolOut, hF,
      readField_writeField_of_disjoint hsignOut]
  have hwork1Slice : readField
      (encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n)
      0 width = s.t := by
    have htStep : (step lengthWidth shiftWidth s).t <
        2 ^ (step lengthWidth shiftWidth s).lenT := by
      simpa [step, hphase1, hphase2] using ht
    have hraw := readField_encodeWork1_coefficient
      (n := n) (s := step lengthWidth shiftWidth s) htStep
    have hdvd : 2 ^ width ∣ 2 ^ workWidth n :=
      Nat.pow_dvd_pow 2 hfit
    simpa [width, step, hphase1, hphase2, readField,
      Nat.mod_mod_of_dvd _ hdvd] using hraw
  have hsource : readField input Interval.sourceOffset width = s.t := by
    calc
      readField input Interval.sourceOffset width =
          readField input (Interval.sourceOffset + 0) width := by simp
      _ = readField P (StepLayout.work1Offset + 0) width :=
        StepPlaced.intervalInput_source_sub
          n lengthWidth shiftWidth 0 width P (by simpa using hfit)
      _ = readField
          (readField P StepLayout.work1Offset (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := P) (D := StepLayout.work1Offset) (W := workWidth n)
          (off := 0) (len := width) (by simpa using hfit)
      _ = readField
          (readField C StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hprepared.work1]
      _ = readField
          (readField S StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hCread _ _ (Or.inr (by
          simp [control, StepLayout.controlWire, StepLayout.work1Offset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inr (by
          simp [sign, StepLayout.signWire, StepLayout.work1Offset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      _ = s.t := by rw [hframe.work1, hwork1Slice]
  have htargetFull : readField input
      (Interval.targetOffset (workWidth n)) (workWidth n) =
        encodeWork2 n s := by
    rw [StepPlaced.intervalInput_target, hprepared.work2,
      hCread _ _ (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)), hframe.work2]
  have htarget : readField input
      (Interval.targetOffset (workWidth n)) width =
        s.tPrime >>> s.shift := by
    calc
      readField input (Interval.targetOffset (workWidth n)) width =
          readField (readField input
            (Interval.targetOffset (workWidth n)) (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := input) (D := Interval.targetOffset (workWidth n))
          (W := workWidth n) (off := 0) (len := width)
          (by simpa using hfit)
      _ = readField (encodeWork2 n s) 0 width := by rw [htargetFull]
      _ = s.tPrime >>> s.shift := by
        exact ReachableStepDomain.phaseTwo_work2Coefficient
          h hphase1 hphase2
  have hsignInput : bitValue input
      (Interval.signWire (workWidth n) lengthWidth) = 0 := by
    rw [StepPlaced.intervalInput_sign, hprepared.sign]
    have hsignC : bitValue C sign = 0 := by
      rw [hC, bitValue_write_ne (by
        simp [control, sign, StepLayout.controlWire, StepLayout.signWire]),
        hF, bitValue_write_self]
    simpa [sign] using hsignC
  have hbounds := ReachableStepDomain.phaseTwo_coefficientOperandBounds
    h hphase1 hphase2
  have htargetValue : StepPlaced.coefficientIntervalAddTargetValue
      0 s.lenT (workWidth n) lengthWidth input =
        writeField (encodeWork2 n s) 0 width
          (s.tPrime >>> s.shift + s.t) := by
    simp only [StepPlaced.coefficientIntervalAddTargetValue]
    change writeField (readField input
        (Interval.targetOffset (workWidth n)) (workWidth n)) 0 width
      ((readField input (Interval.targetOffset (workWidth n)) width +
        readField input Interval.sourceOffset width) % 2 ^ width) = _
    rw [htargetFull, htarget, hsource,
      Nat.mod_eq_of_lt hbounds.2]
  have hsignValue : StepPlaced.coefficientIntervalAddSignValue
      0 s.lenT (workWidth n) lengthWidth input = 0 := by
    simp only [StepPlaced.coefficientIntervalAddSignValue]
    change (bitValue input
        (Interval.signWire (workWidth n) lengthWidth) +
      (readField input (Interval.targetOffset (workWidth n)) width +
        readField input Interval.sourceOffset width) / 2 ^ width) % 2 = 0
    rw [hsignInput, htarget, hsource, Nat.div_eq_of_lt hbounds.2]
  have hblock := StepBlocks.coefficientAddBlock_act
    (I := F) (left := 0) (right := s.lenT)
    hlength hwidths (Nat.le_of_lt hwork) (Nat.zero_le _)
    (by
      have := ReachableStepDomain.phaseTwo_coefficientWindow
        h hphase1 hphase2
      omega)
    hprepared.stable hprepared.accumulator hprepared.carry
  dsimp only at hblock
  rw [htargetValue, hsignValue,
    ReachableStepDomain.phaseTwo_work2_after_coefficientAddition
      h hphase1 hphase2] at hblock
  let leftFin : Fin U := ⟨0, by omega⟩
  let rightFin : Fin U := ⟨s.lenT, by omega⟩
  have hsubWindow : CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) S) :=
    coefficientCallWindow_inactive hsubInactive
  have haddWindow : CoefficientCallWindow n lengthWidth shiftWidth U C := by
    apply coefficientCallWindow_active
      (left := leftFin) (right := rightFin)
    · simp [leftFin, rightFin]
    · simpa [leftFin, rightFin] using hprepared
  have hpair : CoefficientPairWindow n lengthWidth shiftWidth U S := by
    change CoefficientCallWindow n lengthWidth shiftWidth U
        (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) S) ∧
      CoefficientCallWindow n lengthWidth shiftWidth U
        (actGates (Step.coefficientAddControl n lengthWidth shiftWidth)
          (actGates (Step.coefficientFlip n lengthWidth shiftWidth)
            (actGates
              (Step.coefficientSubBlock n lengthWidth shiftWidth) S)))
    refine ⟨hsubWindow, ?_⟩
    rw [hsub]
    simpa [F, C] using haddWindow
  have haction : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth ++
        Step.coefficientFlip n lengthWidth shiftWidth ++
        Step.coefficientAddBlock n lengthWidth shiftWidth) S =
      phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
    simp only [actGates_append, hsub]
    rw [show actGates (Step.coefficientFlip n lengthWidth shiftWidth) S = F
      by rfl, hblock]
    simp only [phaseTwoPostCoefficientCheckpoint, hselected, if_pos]
    rw [hF, writeField_comm (by
      left
      simp [StepLayout.signWire, StepLayout.work2Offset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega), writeField_writeField]
    exact writeField_comm (i := S) (o₁ := sign) (n₁ := 1)
      (o₂ := StepLayout.work2Offset n) (n₂ := workWidth n) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
  exact ⟨by simpa [S] using hpair, by simpa [S] using haction⟩

private theorem coefficientBlocks_act_phaseTwoSelected
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hselected : s.q.testBit s.shift = true) :
    actGates
        (Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth)
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
  apply (coefficientBlocks_phaseTwoSelected_result h hwork hwidths
    hphase1 hphase2 hselected (U := workWidth n) ?_).2
  have hwindow := ReachableStepDomain.phaseTwo_coefficientWindow
    h hphase1 hphase2
  omega

private theorem coefficientBlocks_phaseTwoUnselected_result
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hunselected : s.q.testBit s.shift = false)
    (hU : s.lenT + 1 ≤ U) :
    CoefficientPairWindow n lengthWidth shiftWidth U
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) ∧
      actGates
          (Step.coefficientSubBlock n lengthWidth shiftWidth ++
            Step.coefficientFlip n lengthWidth shiftWidth ++
            Step.coefficientAddBlock n lengthWidth shiftWidth)
          (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
        phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
  let width := s.lenT + 1
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let Csub := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) S
  let Psub := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) Csub
  let inputSub := StepPlaced.intervalInput n lengthWidth shiftWidth Psub
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, _hlenRPrime, hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have htPos := ReachableStepDomain.phaseTwo_t_pos
    h hphase1 hphase2
  have hframe := phaseTwoPostQuotientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hfit : width ≤ workWidth n := by
    have hwindow := ReachableStepDomain.phaseTwo_coefficientWindow
      h hphase1 hphase2
    dsimp only [width]
    omega
  have hright : s.lenT < workWidth n := by
    dsimp only [width] at hfit
    omega
  have hCsub : Csub = writeField S control 1 1 := by
    have hcontrolState :=
      coefficientSubControl_act_phaseTwoPostQuotientCheckpoint
        (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
        hphase1 hphase2
    dsimp only at hcontrolState
    simp [hunselected, boolValue] at hcontrolState
    have htemporary := hframe.controlClean.temporary
    rw [writeField_zero_of_bitValue_zero htemporary] at hcontrolState
    simpa [Csub, control] using hcontrolState
  have hpreparedSub := coefficientPrepare_frame_of_controlled_scratch
    (I := Csub) (J := S) (lenT := s.lenT) hlength hwidths hCsub
    hframe.scratch hframe.phase2 hframe.lenT
    (by rw [hlenT]; exact bitLength_pos htPos) hlenTFit
  dsimp only at hpreparedSub
  change StepPlaced.CoefficientPreparedFrame
    n lengthWidth shiftWidth Csub Psub 0 s.lenT at hpreparedSub
  have hCsubRead (off fieldWidth : Nat)
      (hout : control + 1 ≤ off ∨ off + fieldWidth ≤ control) :
      readField Csub off fieldWidth = readField S off fieldWidth := by
    rw [hCsub, readField_writeField_of_disjoint hout]
  have hwork1Slice : readField
      (encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n)
      0 width = s.t := by
    have htStep : (step lengthWidth shiftWidth s).t <
        2 ^ (step lengthWidth shiftWidth s).lenT := by
      simpa [step, hphase1, hphase2] using ht
    have hraw := readField_encodeWork1_coefficient
      (n := n) (s := step lengthWidth shiftWidth s) htStep
    have hdvd : 2 ^ width ∣ 2 ^ workWidth n :=
      Nat.pow_dvd_pow 2 hfit
    simpa [width, step, hphase1, hphase2, readField,
      Nat.mod_mod_of_dvd _ hdvd] using hraw
  have hsourceSub : readField inputSub Interval.sourceOffset width = s.t := by
    calc
      readField inputSub Interval.sourceOffset width =
          readField inputSub (Interval.sourceOffset + 0) width := by simp
      _ = readField Psub (StepLayout.work1Offset + 0) width :=
        StepPlaced.intervalInput_source_sub
          n lengthWidth shiftWidth 0 width Psub (by simpa using hfit)
      _ = readField
          (readField Psub StepLayout.work1Offset (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := Psub) (D := StepLayout.work1Offset) (W := workWidth n)
          (off := 0) (len := width) (by simpa using hfit)
      _ = readField
          (readField Csub StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hpreparedSub.work1]
      _ = readField
          (readField S StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hCsubRead _ _ (Or.inr (by
          simp [control, StepLayout.controlWire, StepLayout.work1Offset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      _ = s.t := by rw [hframe.work1, hwork1Slice]
  have htargetSubFull : readField inputSub
      (Interval.targetOffset (workWidth n)) (workWidth n) =
        encodeWork2 n s := by
    rw [StepPlaced.intervalInput_target, hpreparedSub.work2,
      hCsubRead _ _ (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)), hframe.work2]
  have htargetSub : readField inputSub
      (Interval.targetOffset (workWidth n)) width =
        s.tPrime >>> s.shift := by
    calc
      readField inputSub (Interval.targetOffset (workWidth n)) width =
          readField (readField inputSub
            (Interval.targetOffset (workWidth n)) (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := inputSub) (D := Interval.targetOffset (workWidth n))
          (W := workWidth n) (off := 0) (len := width)
          (by simpa using hfit)
      _ = readField (encodeWork2 n s) 0 width := by rw [htargetSubFull]
      _ = s.tPrime >>> s.shift := by
        exact ReachableStepDomain.phaseTwo_work2Coefficient
          h hphase1 hphase2
  let difference := Adder.difference width s.t (s.tPrime >>> s.shift)
  let subWork2 := writeField (encodeWork2 n s) 0 width difference
  have hsubValue : StepPlaced.coefficientIntervalSubTargetValue
      0 s.lenT (workWidth n) lengthWidth inputSub = subWork2 := by
    simp only [StepPlaced.coefficientIntervalSubTargetValue]
    change writeField (readField inputSub
        (Interval.targetOffset (workWidth n)) (workWidth n)) 0 width
      (Adder.difference width
        (readField inputSub Interval.sourceOffset width)
        (readField inputSub (Interval.targetOffset (workWidth n)) width)) = _
    rw [htargetSubFull, hsourceSub, htargetSub]
  let B := writeField S (StepLayout.work2Offset n) (workWidth n) subWork2
  have hsubBlock : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) S = B := by
    have hblock := StepBlocks.coefficientSubBlock_act
      (I := S) (left := 0) (right := s.lenT)
      hlength hwidths (Nat.le_of_lt hwork) (Nat.zero_le _) hright
      hpreparedSub.stable hpreparedSub.accumulator hpreparedSub.carry
    dsimp only at hblock
    rw [hsubValue] at hblock
    simpa [B] using hblock
  let F := actGates (Step.coefficientFlip n lengthWidth shiftWidth) B
  have hBphase1 : bitValue B
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    simp only [B]
    rw [bitValue_write_out (Or.inr (by
      simp [StepLayout.work2Offset, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]
      omega))]
    exact hframe.phase1
  have hBphase2 : bitValue B
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    simp only [B]
    rw [bitValue_write_out (Or.inr (by
      simp [StepLayout.work2Offset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))]
    exact hframe.phase2
  have hBsign : bitValue B sign = 0 := by
    simp only [B]
    rw [bitValue_write_out (Or.inr (by
      simp [sign, StepLayout.work2Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))]
    simpa [sign, hunselected, boolValue] using hframe.sign
  have hF : F = writeField B sign 1 1 := by
    have hflip := coefficientFlip_act_phaseTwoSelectedBit
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (selected := false) hBphase1 (by simpa [boolValue] using hBsign)
    simpa [F, sign, boolValue] using hflip
  have hscratchB : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth B := by
    exact remainderScratchClean_write_work2 hframe.scratch
  have hscratchF : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth F := by
    rw [hF]
    exact remainderScratchClean_write_sign hscratchB
  have hp2F : bitValue F
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    rw [hF, bitValue_write_ne (by
      simp [sign, StepLayout.signWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire])]
    exact hBphase2
  let Cadd := actGates
    (Step.coefficientAddControl n lengthWidth shiftWidth) F
  let Padd := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) Cadd
  let inputAdd := StepPlaced.intervalInput n lengthWidth shiftWidth Padd
  have hp1F : bitValue F
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    rw [hF, bitValue_write_ne (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire])]
    exact hBphase1
  have hcontrolF : bitValue F control = 0 := by
    simpa [control] using hscratchF.control
  have hCadd : Cadd = writeField F control 1 1 := by
    simpa [Cadd, control] using
      coefficientAddControl_act_phaseTwo hp1F hcontrolF
  have hlenTF : readField F (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [hF, readField_writeField_of_disjoint (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.lenTOffset, workWidth,
        two_mul]))]
    exact hframe.lenT
  have hpreparedAdd := coefficientPrepare_frame_of_controlled_scratch
    (I := Cadd) (J := F) (lenT := s.lenT) hlength hwidths hCadd
    hscratchF hp2F hlenTF (by rw [hlenT]; exact bitLength_pos htPos)
    hlenTFit
  dsimp only at hpreparedAdd
  change StepPlaced.CoefficientPreparedFrame
    n lengthWidth shiftWidth Cadd Padd 0 s.lenT at hpreparedAdd
  have hdifferenceLt : difference < 2 ^ width := by
    simp only [difference, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hwork2BaseLt : encodeWork2 n s < 2 ^ workWidth n := by
    simpa [encodeWork2] using
      rotatePositionsLeft_lt (workWidth n) s.shift (encodeWork2Raw n s)
  have hsubWork2Lt : subWork2 < 2 ^ workWidth n := by
    exact writeField_lt (by simpa using hfit) hwork2BaseLt
  have hCaddRead (off fieldWidth : Nat)
      (hcontrolOut : control + 1 ≤ off ∨
        off + fieldWidth ≤ control)
      (hsignOut : sign + 1 ≤ off ∨ off + fieldWidth ≤ sign)
      (hwork2Out : StepLayout.work2Offset n + workWidth n ≤ off ∨
        off + fieldWidth ≤ StepLayout.work2Offset n) :
      readField Cadd off fieldWidth = readField S off fieldWidth := by
    rw [hCadd, readField_writeField_of_disjoint hcontrolOut, hF,
      readField_writeField_of_disjoint hsignOut]
    simp only [B]
    rw [readField_writeField_of_disjoint hwork2Out]
  have hsourceAdd : readField inputAdd Interval.sourceOffset width = s.t := by
    calc
      readField inputAdd Interval.sourceOffset width =
          readField inputAdd (Interval.sourceOffset + 0) width := by simp
      _ = readField Padd (StepLayout.work1Offset + 0) width :=
        StepPlaced.intervalInput_source_sub
          n lengthWidth shiftWidth 0 width Padd (by simpa using hfit)
      _ = readField
          (readField Padd StepLayout.work1Offset (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := Padd) (D := StepLayout.work1Offset) (W := workWidth n)
          (off := 0) (len := width) (by simpa using hfit)
      _ = readField
          (readField Cadd StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hpreparedAdd.work1]
      _ = readField
          (readField S StepLayout.work1Offset (workWidth n)) 0 width := by
        rw [hCaddRead _ _ (Or.inr (by
          simp [control, StepLayout.controlWire, StepLayout.work1Offset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inr (by
          simp [sign, StepLayout.signWire, StepLayout.work1Offset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inr (by simp [StepLayout.work1Offset,
          StepLayout.work2Offset, workWidth]))]
      _ = s.t := by rw [hframe.work1, hwork1Slice]
  have htargetAddFull : readField inputAdd
      (Interval.targetOffset (workWidth n)) (workWidth n) = subWork2 := by
    rw [StepPlaced.intervalInput_target, hpreparedAdd.work2, hCadd,
      readField_writeField_of_disjoint (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)), hF, readField_writeField_of_disjoint (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))]
    simp only [B]
    rw [readField_writeField_self hsubWork2Lt]
  have htargetAdd : readField inputAdd
      (Interval.targetOffset (workWidth n)) width = difference := by
    calc
      readField inputAdd (Interval.targetOffset (workWidth n)) width =
          readField (readField inputAdd
            (Interval.targetOffset (workWidth n)) (workWidth n)) 0 width := by
        symm
        simpa using readField_readField
          (i := inputAdd) (D := Interval.targetOffset (workWidth n))
          (W := workWidth n) (off := 0) (len := width)
          (by simpa using hfit)
      _ = readField subWork2 0 width := by rw [htargetAddFull]
      _ = difference := by
        exact readField_writeField_self hdifferenceLt
  have hsignAdd : bitValue inputAdd
      (Interval.signWire (workWidth n) lengthWidth) = 1 := by
    rw [StepPlaced.intervalInput_sign, hpreparedAdd.sign]
    have hsignCadd : bitValue Cadd sign = 1 := by
      rw [hCadd, bitValue_write_ne (by
        simp [control, sign, StepLayout.controlWire, StepLayout.signWire]),
        hF, bitValue_write_self]
    simpa [sign] using hsignCadd
  have hbounds := ReachableStepDomain.phaseTwo_coefficientOperandBounds
    h hphase1 hphase2
  have htWidth : s.t < 2 ^ width := by
    dsimp only [width]
    exact ht.trans (Nat.pow_lt_pow_right (by omega) (by omega))
  have huWidth : s.tPrime >>> s.shift < 2 ^ width :=
    hbounds.1.trans htWidth
  have htargetValue : StepPlaced.coefficientIntervalAddTargetValue
      0 s.lenT (workWidth n) lengthWidth inputAdd = encodeWork2 n s := by
    apply StepPlaced.coefficientIntervalAddTargetValue_difference
      (base := encodeWork2 n s) (a := s.t) (b := s.tPrime >>> s.shift)
    · simpa using hfit
    · simpa [subWork2, difference] using htargetAddFull
    · simpa using hsourceAdd
    · exact ReachableStepDomain.phaseTwo_work2Coefficient
        h hphase1 hphase2
    · exact htWidth
    · exact huWidth
  have hsignValue : StepPlaced.coefficientIntervalAddSignValue
      0 s.lenT (workWidth n) lengthWidth inputAdd = 0 := by
    apply StepPlaced.coefficientIntervalAddSignValue_difference
      (base := encodeWork2 n s) (a := s.t) (b := s.tPrime >>> s.shift)
    · simpa using hfit
    · simpa [subWork2, difference] using htargetAddFull
    · simpa using hsourceAdd
    · exact htWidth
    · exact huWidth
    · exact hsignAdd
    · exact hbounds.1
  have haddBlock : actGates
      (Step.coefficientAddBlock n lengthWidth shiftWidth) F =
        writeField
          (writeField F (StepLayout.work2Offset n) (workWidth n)
            (encodeWork2 n s)) sign 1 0 := by
    have hblock := StepBlocks.coefficientAddBlock_act
      (I := F) (left := 0) (right := s.lenT)
      hlength hwidths (Nat.le_of_lt hwork) (Nat.zero_le _) hright
      hpreparedAdd.stable hpreparedAdd.accumulator hpreparedAdd.carry
    dsimp only at hblock
    rw [htargetValue, hsignValue] at hblock
    simpa [sign] using hblock
  have hwork2Sign : StepLayout.work2Offset n + workWidth n ≤ sign := by
    simp [sign, StepLayout.signWire, StepLayout.work2Offset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega
  have hnormalize :
      writeField
          (writeField
            (writeField B sign 1 1)
            (StepLayout.work2Offset n) (workWidth n) (encodeWork2 n s))
          sign 1 0 =
        writeField
          (writeField B (StepLayout.work2Offset n) (workWidth n)
            (encodeWork2 n s))
          sign 1 0 := by
    rw [writeField_comm (i := B) (o₁ := sign) (n₁ := 1)
      (o₂ := StepLayout.work2Offset n) (n₂ := workWidth n)
      (Or.inr hwork2Sign), writeField_writeField]
  let leftFin : Fin U := ⟨0, by omega⟩
  let rightFin : Fin U := ⟨s.lenT, by omega⟩
  have hsubWindow : CoefficientCallWindow n lengthWidth shiftWidth U Csub := by
    apply coefficientCallWindow_active
      (left := leftFin) (right := rightFin)
    · simp [leftFin, rightFin]
    · simpa [leftFin, rightFin] using hpreparedSub
  have haddWindow : CoefficientCallWindow n lengthWidth shiftWidth U Cadd := by
    apply coefficientCallWindow_active
      (left := leftFin) (right := rightFin)
    · simp [leftFin, rightFin]
    · simpa [leftFin, rightFin] using hpreparedAdd
  have hpair : CoefficientPairWindow n lengthWidth shiftWidth U S := by
    change CoefficientCallWindow n lengthWidth shiftWidth U Csub ∧
      CoefficientCallWindow n lengthWidth shiftWidth U
        (actGates (Step.coefficientAddControl n lengthWidth shiftWidth)
          (actGates (Step.coefficientFlip n lengthWidth shiftWidth)
            (actGates
              (Step.coefficientSubBlock n lengthWidth shiftWidth) S)))
    refine ⟨hsubWindow, ?_⟩
    rw [hsubBlock]
    simpa [F, Cadd] using haddWindow
  have haction : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth ++
        Step.coefficientFlip n lengthWidth shiftWidth ++
        Step.coefficientAddBlock n lengthWidth shiftWidth) S =
      phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
    simp only [actGates_append, hsubBlock]
    rw [show actGates (Step.coefficientFlip n lengthWidth shiftWidth) B = F
      by rfl, haddBlock]
    simp only [phaseTwoPostCoefficientCheckpoint]
    simp [hunselected]
    rw [hF, hnormalize]
    simp only [B]
    rw [writeField_writeField]
  exact ⟨by simpa [S] using hpair, by simpa [S] using haction⟩

private theorem coefficientBlocks_act_phaseTwoUnselected
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hunselected : s.q.testBit s.shift = false) :
    actGates
        (Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth)
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
  apply (coefficientBlocks_phaseTwoUnselected_result h hwork hwidths
    hphase1 hphase2 hunselected (U := workWidth n) ?_).2
  have hwindow := ReachableStepDomain.phaseTwo_coefficientWindow
    h hphase1 hphase2
  omega

theorem coefficientBlocks_act_phaseTwoPostCoefficientCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates
        (Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth)
        (phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s := by
  cases hselected : s.q.testBit s.shift
  · exact coefficientBlocks_act_phaseTwoUnselected
      h hwork hwidths hphase1 hphase2 hselected
  · exact coefficientBlocks_act_phaseTwoSelected
      h hwork hwidths hphase1 hphase2 hselected

private structure PhaseTwoPostCoefficientCheckpointFrame
    (n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  controlClean : StepBlocks.ControlClean n lengthWidth shiftWidth
    (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
  aux : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0
  work1 : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      StepLayout.work1Offset (workWidth n) =
    encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n
  work2 : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.work2Offset n) (workWidth n) =
    encodeWork2 n { s with
      tPrime := if s.q.testBit s.shift then
        s.tPrime + shifted s.t s.shift else s.tPrime }
  lenT : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenTOffset n) lengthWidth =
    encodeLength lengthWidth s.lenT
  lenQ : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
    encodeLength lengthWidth (s.lenQ - 1)
  lenRPrime : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
    encodeLength lengthWidth s.lenRPrime
  shift : readField
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
    encodeLength shiftWidth s.shift
  phase1 : bitValue
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1
  phase2 : bitValue
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0
  iter : bitValue
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.iterWire n lengthWidth shiftWidth) = boolValue s.iter
  sign : bitValue
      (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.signWire n lengthWidth shiftWidth) = 0

private theorem phaseTwoPostCoefficientCheckpoint_frame
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    PhaseTwoPostCoefficientCheckpointFrame n lengthWidth shiftWidth s := by
  let S := phaseTwoPostQuotientCheckpoint n lengthWidth shiftWidth s
  let P := phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let work2 := StepLayout.work2Offset n
  let sC : State := { s with
    tPrime := if s.q.testBit s.shift then
      s.tPrime + shifted s.t s.shift else s.tPrime }
  have hframe := phaseTwoPostQuotientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hread (off width : Nat)
      (hwork2 : work2 + workWidth n ≤ off ∨
        off + width ≤ work2)
      (hsign : sign + 1 ≤ off ∨ off + width ≤ sign) :
      readField P off width = readField S off width := by
    simp only [P, phaseTwoPostCoefficientCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork2]
  have hbit (q : Nat)
      (hwork2 : work2 + workWidth n ≤ q ∨ q + 1 ≤ work2)
      (hsign : sign + 1 ≤ q ∨ q + 1 ≤ sign) :
      bitValue P q = bitValue S q := by
    simpa [readField_one] using hread q 1 hwork2 hsign
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth P := by
    constructor
    · exact (hbit _ (Or.inl (by
          simp [work2, StepLayout.work2Offset, StepLayout.controlWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.controlWire]))).trans
        hframe.controlClean.control
    · exact (hbit _ (Or.inl (by
          simp [work2, StepLayout.work2Offset, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans hframe.controlClean.temporary
    · exact (hbit _ (Or.inl (by
          simp [work2, StepLayout.work2Offset, StepLayout.plusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.plusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans hframe.controlClean.plus
    · exact (hbit _ (Or.inl (by
          simp [work2, StepLayout.work2Offset, StepLayout.minusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega)) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.minusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans hframe.controlClean.minus
  refine ⟨hclean, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hread _ _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inl (by
        simp [sign, StepLayout.signWire, StepLayout.auxOffset]))).trans
      hframe.aux
  · exact (hread _ _ (Or.inr (by
        simp [work2, StepLayout.work2Offset, StepLayout.work1Offset]))
      (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work1Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))).trans hframe.work1
  · simp only [phaseTwoPostCoefficientCheckpoint]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.signWire, StepLayout.work2Offset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)), readField_writeField_self]
    simpa [sC] using
      (show encodeWork2 n sC < 2 ^ workWidth n by
        simpa [encodeWork2] using
          rotatePositionsLeft_lt (workWidth n) sC.shift
            (encodeWork2Raw n sC))
  · exact (hread _ _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.lenTOffset,
          workWidth, two_mul])) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.lenTOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.lenT
  · exact (hread _ _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.lenQOffset,
          workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.lenQOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.lenQ
  · exact (hread _ _ (Or.inl (by
        simp [work2, StepLayout.work2Offset,
          StepLayout.lenRPrimeOffset, workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.lenRPrimeOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.lenRPrime
  · exact (hread _ _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.shiftOffset,
          workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire]))).trans
      hframe.shift
  · exact (hbit _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire]))).trans
      hframe.phase1
  · exact (hbit _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.phase2Wire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase2Wire,
          StepLayout.phase1Wire]))).trans hframe.phase2
  · exact (hbit _ (Or.inl (by
        simp [work2, StepLayout.work2Offset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.iterWire]))).trans
      hframe.iter
  · simp only [phaseTwoPostCoefficientCheckpoint]
    rw [bitValue_write_self]

private def phaseTwoPostShiftPhysicalCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  let sC : State := { s with
    tPrime := if s.q.testBit s.shift then
      s.tPrime + shifted s.t s.shift else s.tPrime }
  writeField
    (writeField (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth
      (encodeLength shiftWidth (s.shift + 1)))
    (StepLayout.work2Offset n) (workWidth n)
    (encodeWork2 n { sC with shift := s.shift + 1 })

private theorem postShiftBlock_act_phaseTwoPhysicalCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostShiftPhysicalCheckpoint n lengthWidth shiftWidth s := by
  let P := phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s
  let C := actGates (Step.postShiftControl n lengthWidth shiftWidth) P
  let J := StepPlaced.shiftInput n lengthWidth shiftWidth C
  let result := Shift.out (workWidth n) shiftWidth J
  let sC : State := { s with
    tPrime := if s.q.testBit s.shift then
      s.tPrime + shifted s.t s.shift else s.tPrime }
  have hframe := phaseTwoPostCoefficientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hcontrols := StepBlocks.postShiftControl_bits hframe.controlClean
  dsimp only at hcontrols
  rw [hframe.phase1, hframe.phase2] at hcontrols
  norm_num at hcontrols
  have hplus : bitValue J (Shift.plusWire shiftWidth) = 1 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_plus]
    exact hcontrols.1
  have hminus : bitValue J
      (Shift.minusWire (workWidth n) shiftWidth) = 0 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_minus]
    exact hcontrols.2
  have hCshift : readField C
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
        encodeLength shiftWidth s.shift := by
    dsimp only [C]
    rw [postShiftControl_read, hframe.shift]
    · simp [StepLayout.plusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
    · simp [StepLayout.minusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
  have hCwork : readField C (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n sC := by
    dsimp only [C]
    rw [postShiftControl_read]
    · simpa [sC] using hframe.work2
    · simp [StepLayout.plusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset,
        StepLayout.work2Offset, workWidth]
      omega
    · simp [StepLayout.minusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset,
        StepLayout.work2Offset, workWidth]
      omega
  have hCpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) shiftWidth = 0 := by
    have hselector : shiftWidth ≤
        StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_right _ _
    dsimp only [C]
    rw [postShiftControl_read]
    · apply readField_sub_zero
        (show StepLayout.auxOffset n lengthWidth shiftWidth ≤
          StepLayout.poolOffset n lengthWidth shiftWidth by
          simp [StepLayout.poolOffset, StepLayout.carryWire]
          omega)
        (show StepLayout.poolOffset n lengthWidth shiftWidth + shiftWidth ≤
          StepLayout.auxOffset n lengthWidth shiftWidth +
            StepLayout.auxWidth lengthWidth shiftWidth by
          simp [StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxWidth, StepLayout.selectorWidth]
          omega)
        hframe.aux
    · simp [StepLayout.plusWire, StepLayout.cellScratchWire]
      omega
    · simp [StepLayout.minusWire, StepLayout.cellScratchWire]
      omega
  have hscratch : Shift.scratch shiftWidth J = 0 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_scratch]
    exact hCpool
  have hposition : Shift.position shiftWidth J =
      encodeLength shiftWidth s.shift := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_position]
    exact hCshift
  have hworkPhysical : Shift.work (workWidth n) shiftWidth J =
      encodeWork2 n sC := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_work]
    exact hCwork
  have hnowrap : s.shift + 1 < 2 ^ shiftWidth :=
    StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2
  have hout := Shift.out_increment hplus hminus
  have hresultPosition : Shift.position shiftWidth result =
      encodeLength shiftWidth (s.shift + 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_succ hnowrap]
  have hresultWork : Shift.work (workWidth n) shiftWidth result =
      encodeWork2 n { sC with shift := s.shift + 1 } := by
    dsimp only [result]
    rw [hout.2, hworkPhysical]
    simp [sC, encodeWork2, encodeWork2Raw, rotatePositionsLeft_succ]
  rw [StepBlocks.postShiftBlock_act hscratch,
    hresultPosition, hresultWork]
  rfl

def phaseTwoPostShiftCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  encoded n lengthWidth shiftWidth
    { step lengthWidth shiftWidth s with
      phase2 := false
      sign := false }

private theorem phaseTwoPostShiftPhysicalCheckpoint_eq_checkpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    phaseTwoPostShiftPhysicalCheckpoint n lengthWidth shiftWidth s =
      phaseTwoPostShiftCheckpoint n lengthWidth shiftWidth s := by
  let L := StepLayout.layout n lengthWidth shiftWidth
  let P := phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s
  let X := phaseTwoPostShiftPhysicalCheckpoint n lengthWidth shiftWidth s
  let sC : State := { s with
    tPrime := if s.q.testBit s.shift then
      s.tPrime + shifted s.t s.shift else s.tPrime }
  let s10 : State := { step lengthWidth shiftWidth s with
    phase2 := false
    sign := false }
  have hframe := phaseTwoPostCoefficientCheckpoint_frame
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1 hphase2
  have hstep := ReachableStepDomain.phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  have hreadP (off width : Nat)
      (hshift : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ off ∨
        off + width ≤ StepLayout.shiftOffset n lengthWidth)
      (hwork2 : StepLayout.work2Offset n + workWidth n ≤ off ∨
        off + width ≤ StepLayout.work2Offset n) :
      readField X off width = readField P off width := by
    simp only [X, phaseTwoPostShiftPhysicalCheckpoint]
    rw [readField_writeField_of_disjoint hwork2,
      readField_writeField_of_disjoint hshift]
  have hbitP (q : Nat)
      (hshift : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ q ∨
        q + 1 ≤ StepLayout.shiftOffset n lengthWidth)
      (hwork2 : StepLayout.work2Offset n + workWidth n ≤ q ∨
        q + 1 ≤ StepLayout.work2Offset n) :
      bitValue X q = bitValue P q := by
    simpa [readField_one] using hreadP q 1 hshift hwork2
  have hXwork1 : readField X StepLayout.work1Offset (workWidth n) =
      encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n := by
    exact (hreadP _ _ (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.work2Offset]))).trans
      hframe.work1
  have hXwork2 : readField X (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n { sC with shift := s.shift + 1 } := by
    simp only [X, phaseTwoPostShiftPhysicalCheckpoint]
    rw [readField_writeField_self]
    simpa using
      (show encodeWork2 n { sC with shift := s.shift + 1 } <
          2 ^ workWidth n by
        simpa [encodeWork2] using rotatePositionsLeft_lt
          (workWidth n) (s.shift + 1)
          (encodeWork2Raw n { sC with shift := s.shift + 1 }))
  have hXlenT : readField X (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    exact (hreadP _ _ (Or.inr (by
      simp [StepLayout.lenTOffset, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inl (by
      simp [StepLayout.lenTOffset, StepLayout.work2Offset, workWidth,
        two_mul]))).trans hframe.lenT
  have hXlenQ : readField X
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth (s.lenQ - 1) := by
    exact (hreadP _ _ (Or.inr (by
      simp [StepLayout.lenQOffset, StepLayout.shiftOffset, workWidth]
      omega)) (Or.inl (by
      simp [StepLayout.lenQOffset, StepLayout.work2Offset, workWidth]
      omega))).trans hframe.lenQ
  have hXlenRPrime : readField X
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
    exact (hreadP _ _ (Or.inr (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.shiftOffset,
        workWidth, two_mul, three_mul]
      omega)) (Or.inl (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.work2Offset, workWidth]
      omega))).trans hframe.lenRPrime
  have hXshift : readField X
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      encodeLength shiftWidth (s.shift + 1) := by
    simp only [X, phaseTwoPostShiftPhysicalCheckpoint]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.shiftOffset, StepLayout.work2Offset, workWidth]
      omega)), readField_writeField_self]
    exact encodeLength_lt shiftWidth (s.shift + 1)
  have hXp1 : bitValue X
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    exact (hbitP _ (Or.inl (by
      simp [StepLayout.phase1Wire, StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.phase1Wire, StepLayout.work2Offset,
        StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.phase1
  have hXp2 : bitValue X
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    exact (hbitP _ (Or.inl (by
      simp [StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.phase2
  have hXiter : bitValue X
      (StepLayout.iterWire n lengthWidth shiftWidth) = boolValue s.iter := by
    exact (hbitP _ (Or.inl (by
      simp [StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.iter
  have hXsign : bitValue X
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    exact (hbitP _ (Or.inl (by
      simp [StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.sign
  have hXcontrol : bitValue X
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    exact (hbitP _ (Or.inl (by
      simp [StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.controlClean.control
  have hXaux : readField X
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
    exact (hreadP _ _ (Or.inl (by
      simp [StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset])) (Or.inl (by
      simp [StepLayout.auxOffset, StepLayout.work2Offset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))).trans hframe.aux
  have hwork1Bound : StepLayout.work1Offset + workWidth n ≤ L.width := by
    simp [L, StepLayout.layout_width, StepLayout.work1Offset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  have hwork2Bound : StepLayout.work2Offset n + workWidth n ≤ L.width := by
    simp [L, StepLayout.layout_width, StepLayout.work2Offset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  have hlenQBound : StepLayout.lenQOffset n lengthWidth + lengthWidth ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.lenQOffset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
    omega
  have hshiftBound : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.shiftOffset,
      StepLayout.auxOffset, StepLayout.phase1Wire]
    omega
  have hsignBound : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.signWire,
      StepLayout.auxOffset]
    omega
  have hPlt : P < 2 ^ L.width := by
    simp only [P, phaseTwoPostCoefficientCheckpoint,
      phaseTwoPostQuotientCheckpoint, phaseTwoPostSwapCheckpoint]
    exact writeField_lt hsignBound
      (writeField_lt hwork2Bound
        (writeField_lt hlenQBound
          (writeField_lt hsignBound
            (writeField_lt hwork1Bound
              (encoded_lt n lengthWidth shiftWidth s)))))
  have hXlt : X < 2 ^ L.width := by
    simp only [X, phaseTwoPostShiftPhysicalCheckpoint]
    exact writeField_lt hwork2Bound (writeField_lt hshiftBound hPlt)
  apply Layout.ext hXlt (encoded_lt n lengthWidth shiftWidth s10)
  intro j hj
  have hj' : j < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hj
  interval_cases j
  · change readField X StepLayout.work1Offset (workWidth n) =
      readField (encoded n lengthWidth shiftWidth s10)
        StepLayout.work1Offset (workWidth n)
    rw [hXwork1, read_work1]
    simp [s10, encodeWork1]
  · change readField X (StepLayout.work2Offset n) (workWidth n) =
      readField (encoded n lengthWidth shiftWidth s10)
        (StepLayout.work2Offset n) (workWidth n)
    rw [hXwork2, read_work2]
    simp [s10, sC, hstep, encodeWork2, encodeWork2Raw]
  · have hvalue : encodeLength lengthWidth s.lenT =
        encodeLength lengthWidth s10.lenT := by simp [s10, hstep]
    have heq := hXlenT.trans <| hvalue.trans
      (read_lenT n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenTOffset, two_mul,
      Nat.add_assoc] using heq
  · have hvalue : encodeLength lengthWidth (s.lenQ - 1) =
        encodeLength lengthWidth s10.lenQ := by simp [s10, hstep]
    have heq := hXlenQ.trans <| hvalue.trans
      (read_lenQ n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenQOffset, two_mul,
      Nat.add_assoc] using heq
  · have hvalue : encodeLength lengthWidth s.lenRPrime =
        encodeLength lengthWidth s10.lenRPrime := by simp [s10, hstep]
    have heq := hXlenRPrime.trans <| hvalue.trans
      (read_lenRPrime n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenRPrimeOffset, two_mul,
      Nat.add_assoc] using heq
  · have hvalue : encodeLength shiftWidth (s.shift + 1) =
        encodeLength shiftWidth s10.shift := by simp [s10, hstep]
    have heq := hXshift.trans <| hvalue.trans
      (read_shift n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.shiftOffset, two_mul,
      three_mul, Nat.add_assoc] using heq
  · have hvalue : 1 = boolValue s10.phase1 := by
      simp [s10, hstep, hphase1, boolValue]
    have heq := hXp1.trans <| hvalue.trans
      (read_phase1 n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase1Wire,
      StepLayout.shiftOffset, readField_one, two_mul, three_mul,
      Nat.add_assoc] using heq
  · have hvalue : 0 = boolValue s10.phase2 := by
      simp [s10, boolValue]
    have heq := hXp2.trans <| hvalue.trans
      (read_phase2 n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase2Wire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have hvalue : boolValue s.iter = boolValue s10.iter := by
      simp [s10, hstep]
    have heq := hXiter.trans <| hvalue.trans
      (read_iter n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have hvalue : 0 = boolValue s10.sign := by simp [s10, boolValue]
    have heq := hXsign.trans <| hvalue.trans
      (read_sign n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.signWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have heq := hXcontrol.trans
      (read_control n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.controlWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have heq := hXaux.trans
      (read_aux n lengthWidth shiftWidth s10).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, two_mul, three_mul,
      Nat.add_assoc] using heq

theorem postShiftBlock_act_phaseTwoPostShiftCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (phaseTwoPostCoefficientCheckpoint n lengthWidth shiftWidth s) =
      phaseTwoPostShiftCheckpoint n lengthWidth shiftWidth s := by
  rw [postShiftBlock_act_phaseTwoPhysicalCheckpoint
    h hwork hwidths hphase1 hphase2]
  exact phaseTwoPostShiftPhysicalCheckpoint_eq_checkpoint
    h hwork hwidths hphase1 hphase2

theorem phaseGates_act_phaseTwoPostShiftCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
        (phaseTwoPostShiftCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  let s' := step lengthWidth shiftWidth s
  let s10 : State := { s' with phase2 := false, sign := false }
  have hstep := ReachableStepDomain.phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  have hpacked := ReachableStepDomain.phaseTwo_packed_after_step
    h hwork hwidths hphase1 hphase2
  have hstate := ReachableStepDomain.phaseTwo_stateFacts h hphase1 hphase2
  change actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s10) =
    encoded n lengthWidth shiftWidth s'
  have hlenQFit : s'.lenQ < 2 ^ lengthWidth := hpacked.2.2.2.1
  have hlenRPrimeFit : s'.lenRPrime < 2 ^ lengthWidth :=
    hpacked.2.2.2.2.1
  have hshiftFit : s'.shift < 2 ^ shiftWidth :=
    hpacked.2.2.2.2.2.1
  have hlenRPrimePos : 0 < s'.lenRPrime := by
    have hrPrimePos : 0 < s'.rPrime := by
      simpa [s', hstep] using hstate.2.1
    rw [hpacked.2.1]
    exact bitLength_pos hrPrimePos
  have hshiftPos : 0 < s'.shift := by
    simp [s', hstep]
  have hlenRPrimePhysical : readField
      (encoded n lengthWidth shiftWidth s10)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth := by
    rw [read_lenRPrime]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hlenRPrimeFit).mp (by
      simpa [s10] using hzero)
    omega
  have hshiftPhysical : readField
      (encoded n lengthWidth shiftWidth s10)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
      encodedZero shiftWidth := by
    rw [read_shift]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hshiftFit).mp (by
      simpa [s10] using hzero)
    omega
  have hphaseAct := StepBlocks.phaseBlock_act_phase10
    (I := encoded n lengthWidth shiftWidth s10)
    (read_aux n lengthWidth shiftWidth s10)
    (by simp [read_phase1, s10, s', hstep, hphase1, boolValue])
    (by simp [read_phase2, s10, boolValue])
    (by simp [read_sign, s10, boolValue])
    hlenRPrimePhysical hshiftPhysical
  dsimp only at hphaseAct
  let zeroQ := Phase.selectorValue lengthWidth
    (StepLayout.lenQOffset n lengthWidth)
    (encoded n lengthWidth shiftWidth s10)
  have hlenQPredFit : s.lenQ - 1 < 2 ^ lengthWidth := by
    simpa [s', hstep] using hlenQFit
  have hlenRPrimeOriginalPos : 0 < s.lenRPrime := by
    simpa [s', hstep] using hlenRPrimePos
  have hzeroQ : zeroQ = boolValue s'.phase2 := by
    simp [zeroQ, Phase.selectorValue, read_lenQ, s10,
      encodeLength_eq_encodedZero_iff hlenQPredFit, s', hstep,
      hlenRPrimeOriginalPos, boolValue]
  rw [hphaseAct, ← show zeroQ = Phase.selectorValue lengthWidth
      (StepLayout.lenQOffset n lengthWidth)
      (encoded n lengthWidth shiftWidth s10) by rfl,
    hzeroQ]
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth s10
    s'.phase1 s'.phase2 s'.sign
  dsimp only at hwrite
  simpa [Layout.write, StepLayout.layout, VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.phase1Wire,
    StepLayout.phase2Wire, StepLayout.signWire, StepLayout.shiftOffset,
    s10, s', hstep, hphase1, boolValue, two_mul, three_mul,
    Nat.add_assoc] using hwrite

theorem ownershipBlock_inactive_phaseTwoStep
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hstep := ReachableStepDomain.phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  have hshiftFit : s.shift + 1 < 2 ^ shiftWidth :=
    StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2
  apply StepBlocks.ownershipBlock_inactive hwork
    (read_control n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s))
    (read_aux n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s))
  right
  rw [read_shift]
  intro hzero
  have hdecoded := (encodeLength_eq_encodedZero_iff (by
    rw [hstep]
    exact hshiftFit)).mp hzero
  rw [hstep] at hdecoded
  simp at hdecoded

theorem coefficientPairWindow_phaseTwo
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hU : s.lenT + 1 ≤ U) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s)) := by
  have hpre := preShiftBlock_act_phaseTwo
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1
  have hrem := guardedRemainderBlocks_act_phaseTwo
    h hwork hwidths hphase1 hphase2
  have hqinc := quotientIncrementBlock_act_phaseTwo
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase2
  have hswap := swapBlock_act_phaseTwoPostSwapCheckpoint
    h hwork hwidths hphase1 hphase2
  have hqdec := quotientDecrementBlock_act_phaseTwoPostSwapCheckpoint
    h hphase1 hphase2
  simp only [Step.coefficientPrefixGates, actGates_append]
  rw [hpre, hrem, hqinc,
    hswap, hqdec]
  cases hselected : s.q.testBit s.shift
  · exact (coefficientBlocks_phaseTwoUnselected_result
      h hwork hwidths hphase1 hphase2 hselected hU).1
  · exact (coefficientBlocks_phaseTwoSelected_result
      h hwork hwidths hphase1 hphase2 hselected hU).1

theorem gates_act_phaseTwo
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hpre := preShiftBlock_act_phaseTwo
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1
  have hrem := guardedRemainderBlocks_act_phaseTwo
    h hwork hwidths hphase1 hphase2
  have hqinc := quotientIncrementBlock_act_phaseTwo
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase2
  have hswap := swapBlock_act_phaseTwoPostSwapCheckpoint
    h hwork hwidths hphase1 hphase2
  have hqdec := quotientDecrementBlock_act_phaseTwoPostSwapCheckpoint
    h hphase1 hphase2
  have hcoefficient :=
    coefficientBlocks_act_phaseTwoPostCoefficientCheckpoint
      h hwork hwidths hphase1 hphase2
  simp only [actGates_append] at hcoefficient
  have hpost := postShiftBlock_act_phaseTwoPostShiftCheckpoint
    h hwork hwidths hphase1 hphase2
  have hphase := phaseGates_act_phaseTwoPostShiftCheckpoint
    h hwork hwidths hphase1 hphase2
  have hownership := ownershipBlock_inactive_phaseTwoStep
    h hwork hwidths hphase1 hphase2
  simp only [Step.gates, actGates_append]
  rw [hpre, hrem, hqinc, hswap, hqdec, hcoefficient, hpost,
    hphase, hownership]

theorem reverseCircuit_recovers_phaseTwo
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    act (Step.reverseCircuit n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth s := by
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hforward : act (Step.circuit n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s) =
        encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s) := by
    simpa [act, Step.circuit] using gates_act_phaseTwo
      h hwork hwidths hphase1 hphase2
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
