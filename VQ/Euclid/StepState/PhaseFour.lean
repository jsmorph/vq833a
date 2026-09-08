import VQ.Euclid.StepState.Common
import VQ.Euclid.StepState.PhaseTwo
import VQ.Euclid.StepState.Ownership

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

theorem phaseFourPrefix_act
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
            (StepLayout.shiftGates n lengthWidth shiftWidth) ++
          Step.guardedRemainderBlocks n lengthWidth shiftWidth ++
          Step.quotientIncrementBlock n lengthWidth shiftWidth ++
          Step.swapBlock n lengthWidth shiftWidth ++
          Step.quotientDecrementBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  let I := encoded n lengthWidth shiftWidth s
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
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
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    simp [I, read_phase2, hphase2, boolValue]
  have hpre := preShiftBlock_act_phaseTwo
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hphase1
  have hselect : actGates
      (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth) I = I := by
    simpa [I] using rPrimeZeroSelectorGates_act_live
      h.stepDomain.valid.1 hstate.1
  have hzrp : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
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
  have hflip := StepBlocks.remainderFlip_identity_of_phase1_one hp1
  have hadd :=
    StepBlocks.guardedRemainderAddBlock_identity_of_phase1_one_live
      hlength hwidths hscratch hclean hp1 hzrp
  have hrem : actGates
      (Step.guardedRemainderBlocks n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.around_identity
      (StepLayout.rPrimeZeroSelectorGates_wellFormed
        n lengthWidth shiftWidth)
    rw [hselect]
    simp only [actGates_append, hsub, hflip, hadd]
  have hqincControl : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientIncrementControl_identity_of_phase1_one hp1
  have hqinc : actGates
      (Step.quotientIncrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientIncrementBlock_identity
    · rw [hqincControl, StepPlaced.quotientInput_scratch]
      exact hscratch.pool
    · rw [hqincControl]
      exact hclean.control
  have hswapControl : actGates
      (Step.swapControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.swapControl_identity_of_equal_phases (hp1.trans hp2.symm)
  have hswap : actGates
      (Step.swapBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.swapBlock_identity hlength hwidths
    rw [hswapControl]
    exact StepPlaced.swapPrepare_inactive_of_physical_scratch
      hlength hwidths hscratch.left hscratch.control hscratch.carry
      hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
      hscratch.pool hscratch.cellScratch
  have hqdecControl : actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientDecrementControl_identity_of_phase2_one hp2
  have hqdec : actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientDecrementBlock_identity
    · rw [hqdecControl, StepPlaced.quotientInput_scratch]
      exact hscratch.pool
    · rw [hqdecControl]
      exact hclean.control
  simp only [actGates_append]
  rw [hpre, hrem, hqinc, hswap, hqdec]

private theorem coefficientPrepare_frame_phaseFour_of_controlled_scratch
    {p n lengthWidth shiftWidth I J : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hI : I = writeField J
      (StepLayout.controlWire n lengthWidth shiftWidth) 1 1)
    (hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth J)
    (hphase2J : bitValue J
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1)
    (hlenT : readField J (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT)
    (hlenRPrime : readField J
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime)
    (hshift : readField J
      (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.shift) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    StepPlaced.CoefficientPreparedFrame
      n lengthWidth shiftWidth I P 0
        (workWidth n - s.lenRPrime - s.shift - 1) := by
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  have htPos := h.positiveLiveCoefficient hstate.1
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPos
  have hlenRPrimePos : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hlenTFit : s.lenT < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.1
  have hlenRPrimeFit : s.lenRPrime < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.2.2.1
  have hshiftFit : s.shift < 2 ^ lengthWidth := hstate.2.2.2.2.1.trans hwork
  have hlenTPredFit : s.lenT - 1 < 2 ^ lengthWidth := by
    have : s.lenT - 1 < s.lenT := by omega
    exact this.trans hlenTFit
  have hlenRPrimePredFit : s.lenRPrime - 1 < 2 ^ lengthWidth := by
    have : s.lenRPrime - 1 < s.lenRPrime := by omega
    exact this.trans hlenRPrimeFit
  have hlenTEncoded : encodeLength lengthWidth s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPos),
      Nat.mod_eq_of_lt hlenTPredFit]
  have hlenRPrimeEncoded : encodeLength lengthWidth s.lenRPrime =
      s.lenRPrime - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenRPrimePos),
      Nat.mod_eq_of_lt hlenRPrimePredFit]
  have hshiftEncoded : encodeLength lengthWidth s.shift = s.shift - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hstate.2.2.2.1),
      Nat.mod_eq_of_lt (by omega)]
  have hreadI (off width : Nat)
      (hout : StepLayout.controlWire n lengthWidth shiftWidth + 1 ≤ off ∨
        off + width ≤
          StepLayout.controlWire n lengthWidth shiftWidth) :
      readField I off width = readField J off width := by
    rw [hI, readField_writeField_of_disjoint hout]
  have hbitI (q : Nat)
      (hne : q ≠ StepLayout.controlWire n lengthWidth shiftWidth) :
      bitValue I q = bitValue J q := by
    rw [hI, bitValue_write_ne hne]
  apply StepPlaced.coefficientPrepare_frame_phase11
      (I := I) (left := 0) (lenRPrime := s.lenRPrime)
      (shift := s.shift) hlength hwidths
  · rw [hreadI _ _ (Or.inl (by
        simp [StepLayout.leftOffset, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire]))]
    exact hscratch.left
  · rw [hreadI _ _ (Or.inl (by
        simp [StepLayout.rightOffset, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire]))]
    exact hscratch.right
  · rw [hreadI _ _ (Or.inr (by
        simp [StepLayout.lenTOffset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hlenT, hlenTEncoded]
    have hone : 1 + (s.lenT - 1) = s.lenT := by omega
    rw [hone]
    exact hlenTFit
  · rw [hreadI _ _ (Or.inr (by
        simp [StepLayout.lenRPrimeOffset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hlenRPrime, hlenRPrimeEncoded]
  · rw [hreadI _ _ (Or.inr (by
        simp [StepLayout.shiftOffset, StepLayout.controlWire,
          StepLayout.phase1Wire]
        omega)), hshift, hshiftEncoded]
  · rw [hI, bitValue_write_self]
  · rw [hbitI _ (by
        simp [StepLayout.phase2Wire, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset])]
    exact hphase2J
  · rw [hbitI _ (by
        simp [StepLayout.carryWire, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire]
        omega)]
    exact hscratch.carry
  · rw [hbitI _ (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire]
        omega)]
    exact hscratch.accumulator
  · rw [hbitI _ (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire]
        omega)]
    exact hscratch.leftFlag
  · rw [hbitI _ (by
        simp [StepLayout.rightFlagWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire]
        omega)]
    exact hscratch.rightFlag
  · rw [hreadI _ _ (Or.inl (by
        simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire]
        omega))]
    exact hscratch.pool
  · rw [hbitI _ (by
        simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire]
        omega)]
    exact hscratch.cellScratch
  · have hn : n < workWidth n := by simp [workWidth]
    exact hn.trans hwork
  · exact hlenRPrimePos
  · exact hstate.2.2.2.1
  · have hsum := StepDomain.phaseFour_stored_length_sum
      h.stepDomain hphase1 hphase2
    omega
  · have hfit := ReachableStepDomain.phaseFour_coefficientIntervalFit
      h hphase1 hphase2
    simp only [workWidth] at hfit ⊢
    omega
  · have hright : workWidth n - s.lenRPrime - s.shift - 1 <
        workWidth n := by
      have hfit := ReachableStepDomain.phaseFour_coefficientIntervalFit
        h hphase1 hphase2
      omega
    exact hright.trans hwork

private theorem coefficientBlocks_phaseFour_result
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hU : workWidth n - s.lenRPrime - s.shift ≤ U) :
    CoefficientPairWindow n lengthWidth shiftWidth U
        (encoded n lengthWidth shiftWidth s) ∧
      actGates
          (Step.coefficientSubBlock n lengthWidth shiftWidth ++
            Step.coefficientFlip n lengthWidth shiftWidth ++
            Step.coefficientAddBlock n lengthWidth shiftWidth)
          (encoded n lengthWidth shiftWidth s) =
        writeField (encoded n lengthWidth shiftWidth s)
          (StepLayout.signWire n lengthWidth shiftWidth) 1 1 := by
  let width := workWidth n - s.lenRPrime - s.shift
  let right := width - 1
  let S := encoded n lengthWidth shiftWidth s
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
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  have hinterval := ReachableStepDomain.phaseFour_coefficientIntervalFit
    h hphase1 hphase2
  have hwidthPos : 0 < width := by
    dsimp only [width]
    omega
  have hfit : width ≤ workWidth n := by
    dsimp only [width]
    omega
  have hrightWidth : right + 1 = width := by
    dsimp only [right]
    omega
  have hright : right < workWidth n := by omega
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth S := by
    simpa [S] using encodedRemainderScratchClean
      n lengthWidth shiftWidth s
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth S := by
    simpa [S] using controlClean n lengthWidth shiftWidth s
  have hp1 : bitValue S
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
    simp [S, read_phase1, hphase1, boolValue]
  have hp2 : bitValue S
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    simp [S, read_phase2, hphase2, boolValue]
  have hCsub : Csub = writeField S control 1 1 := by
    simpa [Csub, control] using
      StepBlocks.coefficientSubControl_act_phase11 hclean hp1 hp2
  have hshiftFit : s.shift < 2 ^ lengthWidth :=
    hstate.2.2.2.2.1.trans hwork
  have hpreparedSub :=
    coefficientPrepare_frame_phaseFour_of_controlled_scratch
      (I := Csub) (J := S) h hwork hwidths hphase1 hphase2 hCsub
      hscratch hp2 (read_lenT n lengthWidth shiftWidth s)
      (read_lenRPrime n lengthWidth shiftWidth s)
      (read_shift_narrow hwidths hshiftFit)
  dsimp only at hpreparedSub
  change StepPlaced.CoefficientPreparedFrame
    n lengthWidth shiftWidth Csub Psub 0 right at hpreparedSub
  have hCsubRead (off fieldWidth : Nat)
      (hout : control + 1 ≤ off ∨ off + fieldWidth ≤ control) :
      readField Csub off fieldWidth = readField S off fieldWidth := by
    rw [hCsub, readField_writeField_of_disjoint hout]
  have hwork1Slice : readField
      (encodeWork1 n s % 2 ^ workWidth n) 0 width = s.t := by
    have hdvd : 2 ^ width ∣ 2 ^ workWidth n :=
      Nat.pow_dvd_pow 2 hfit
    simpa [readField, Nat.mod_mod_of_dvd _ hdvd] using
      ReachableStepDomain.phaseFour_work1Coefficient
        h hphase1 hphase2
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
      _ = s.t := by rw [read_work1, hwork1Slice]
  have htargetSubFull : readField inputSub
      (Interval.targetOffset (workWidth n)) (workWidth n) =
        encodeWork2 n s := by
    rw [StepPlaced.intervalInput_target, hpreparedSub.work2,
      hCsubRead _ _ (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.work2Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)), read_work2]
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
        exact ReachableStepDomain.phaseFour_work2Coefficient
          h hphase1 hphase2
  let difference := Adder.difference width s.t (s.tPrime >>> s.shift)
  let subWork2 := writeField (encodeWork2 n s) 0 width difference
  have hsubValue : StepPlaced.coefficientIntervalSubTargetValue
      0 right (workWidth n) lengthWidth inputSub = subWork2 := by
    simp only [StepPlaced.coefficientIntervalSubTargetValue,
      Nat.sub_zero]
    rw [hrightWidth]
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
      (I := S) (left := 0) (right := right)
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
    exact hp1
  have hBphase2 : bitValue B
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    simp only [B]
    rw [bitValue_write_out (Or.inr (by
      simp [StepLayout.work2Offset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))]
    exact hp2
  have hBsign : bitValue B sign = boolValue s.sign := by
    simp only [B]
    rw [bitValue_write_out (Or.inr (by
      simp [sign, StepLayout.work2Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))]
    simpa [S, sign] using read_sign n lengthWidth shiftWidth s
  have hF : F = writeField B sign 1 (boolValue (!s.sign)) := by
    have hflip := coefficientFlip_act_phaseTwoSelectedBit
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (selected := s.sign) hBphase1 hBsign
    simpa [F, sign] using hflip
  have hscratchB : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth B :=
    remainderScratchClean_write_work2 hscratch
  have hscratchF : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth F := by
    rw [hF]
    exact remainderScratchClean_write_sign hscratchB
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
  have hp2F : bitValue F
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    rw [hF, bitValue_write_ne (by
      simp [sign, StepLayout.signWire, StepLayout.phase2Wire,
        StepLayout.phase1Wire])]
    exact hBphase2
  have hcontrolF : bitValue F control = 0 := by
    simpa [control] using hscratchF.control
  have hCadd : Cadd = writeField F control 1 1 := by
    simpa [Cadd, control] using
      coefficientAddControl_act_phaseTwo hp1F hcontrolF
  have hreadF (off fieldWidth : Nat)
      (hsignOut : sign + 1 ≤ off ∨ off + fieldWidth ≤ sign)
      (hwork2Out : StepLayout.work2Offset n + workWidth n ≤ off ∨
        off + fieldWidth ≤ StepLayout.work2Offset n) :
      readField F off fieldWidth = readField S off fieldWidth := by
    rw [hF, readField_writeField_of_disjoint hsignOut]
    simp only [B]
    rw [readField_writeField_of_disjoint hwork2Out]
  have hlenTF : readField F (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [hreadF _ _ (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.lenTOffset, workWidth,
        two_mul])), read_lenT]
  have hlenRPrimeF : readField F
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
        encodeLength lengthWidth s.lenRPrime := by
    rw [hreadF _ _ (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.lenRPrimeOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.lenRPrimeOffset, workWidth,
        two_mul])), read_lenRPrime]
  have hshiftF : readField F
      (StepLayout.shiftOffset n lengthWidth) lengthWidth =
        encodeLength lengthWidth s.shift := by
    rw [hreadF _ _ (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.shiftOffset,
        StepLayout.phase1Wire]
      omega)) (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.shiftOffset, workWidth,
        two_mul])), read_shift_narrow hwidths hshiftFit]
  have hpreparedAdd :=
    coefficientPrepare_frame_phaseFour_of_controlled_scratch
      (I := Cadd) (J := F) h hwork hwidths hphase1 hphase2 hCadd
      hscratchF hp2F hlenTF hlenRPrimeF hshiftF
  dsimp only at hpreparedAdd
  change StepPlaced.CoefficientPreparedFrame
    n lengthWidth shiftWidth Cadd Padd 0 right at hpreparedAdd
  have hCaddRead (off fieldWidth : Nat)
      (hcontrolOut : control + 1 ≤ off ∨ off + fieldWidth ≤ control)
      (hsignOut : sign + 1 ≤ off ∨ off + fieldWidth ≤ sign)
      (hwork2Out : StepLayout.work2Offset n + workWidth n ≤ off ∨
        off + fieldWidth ≤ StepLayout.work2Offset n) :
      readField Cadd off fieldWidth = readField S off fieldWidth := by
    rw [hCadd, readField_writeField_of_disjoint hcontrolOut,
      hreadF _ _ hsignOut hwork2Out]
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
      _ = s.t := by rw [read_work1, hwork1Slice]
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
    exact readField_writeField_self (by
      exact writeField_lt (by simpa using hfit)
        (by simpa [encodeWork2] using
          rotatePositionsLeft_lt (workWidth n) s.shift (encodeWork2Raw n s)))
  have hdifferenceLt : difference < 2 ^ width := by
    simp only [difference, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
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
      _ = difference := readField_writeField_self hdifferenceLt
  have hsignAdd : bitValue inputAdd
      (Interval.signWire (workWidth n) lengthWidth) =
        boolValue (!s.sign) := by
    rw [StepPlaced.intervalInput_sign, hpreparedAdd.sign]
    have hsignCadd : bitValue Cadd sign = boolValue (!s.sign) := by
      rw [hCadd, bitValue_write_ne (by
        simp [control, sign, StepLayout.controlWire, StepLayout.signWire]),
        hF, bitValue_write_self]
      cases s.sign <;> rfl
    simpa [sign] using hsignCadd
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have htWidth : s.t < 2 ^ width := by
    have hlenTWidth : s.lenT < width := by
      dsimp only [width]
      omega
    exact ht.trans (Nat.pow_lt_pow_right (by omega) hlenTWidth)
  have huWidth : s.tPrime >>> s.shift < 2 ^ width := by
    rw [← ReachableStepDomain.phaseFour_work2Coefficient
      h hphase1 hphase2]
    simpa only [width] using readField_lt (encodeWork2 n s) 0
      (workWidth n - s.lenRPrime - s.shift)
  have htargetValue : StepPlaced.coefficientIntervalAddTargetValue
      0 right (workWidth n) lengthWidth inputAdd = encodeWork2 n s := by
    apply StepPlaced.coefficientIntervalAddTargetValue_difference
      (base := encodeWork2 n s) (a := s.t) (b := s.tPrime >>> s.shift)
    · simpa [hrightWidth] using hfit
    · simpa [subWork2, difference, hrightWidth] using htargetAddFull
    · simpa [hrightWidth] using hsourceAdd
    · simpa [hrightWidth] using
        ReachableStepDomain.phaseFour_work2Coefficient h hphase1 hphase2
    · simpa [hrightWidth] using htWidth
    · simpa [hrightWidth] using huWidth
  have hsignBorrow : boolValue s.sign =
      Adder.borrow s.t (s.tPrime >>> s.shift) := by
    have hcompare : (s.tPrime >>> s.shift < s.t) ↔
        (s.tPrime < shifted s.t s.shift) := by
      have hle := shifted_le_iff_le_shiftRight s.t s.tPrime s.shift
      omega
    rw [hstate.2.2.2.2.2.2]
    by_cases hlt : s.tPrime >>> s.shift < s.t
    · rw [Adder.borrow, if_pos hlt]
      simp [hcompare.mp hlt, boolValue]
    · rw [Adder.borrow, if_neg hlt]
      have hnot : ¬s.tPrime < shifted s.t s.shift := by
        exact fun hlt' => hlt (hcompare.mpr hlt')
      simp [hnot, boolValue]
  have hsignValue : StepPlaced.coefficientIntervalAddSignValue
      0 right (workWidth n) lengthWidth inputAdd = 1 := by
    rw [StepPlaced.coefficientIntervalAddSignValue_of_difference
      (base := encodeWork2 n s) (a := s.t)
      (b := s.tPrime >>> s.shift)
      (by simpa [hrightWidth] using hfit)
      (by simpa [subWork2, difference, hrightWidth] using htargetAddFull)
      (by simpa [hrightWidth] using hsourceAdd)
      (by simpa [hrightWidth] using htWidth)
      (by simpa [hrightWidth] using huWidth),
      hsignAdd, ← hsignBorrow]
    cases s.sign <;> rfl
  have haddBlock : actGates
      (Step.coefficientAddBlock n lengthWidth shiftWidth) F =
        writeField
          (writeField F (StepLayout.work2Offset n) (workWidth n)
            (encodeWork2 n s)) sign 1 1 := by
    have hblock := StepBlocks.coefficientAddBlock_act
      (I := F) (left := 0) (right := right)
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
            (writeField B sign 1 (boolValue (!s.sign)))
            (StepLayout.work2Offset n) (workWidth n) (encodeWork2 n s))
          sign 1 1 =
        writeField
          (writeField B (StepLayout.work2Offset n) (workWidth n)
            (encodeWork2 n s))
          sign 1 1 := by
    rw [writeField_comm (i := B) (o₁ := sign) (n₁ := 1)
      (o₂ := StepLayout.work2Offset n) (n₂ := workWidth n)
      (Or.inr hwork2Sign), writeField_writeField]
  have hrightU : right < U := by
    dsimp only [right, width]
    omega
  let leftFin : Fin U := ⟨0, by omega⟩
  let rightFin : Fin U := ⟨right, hrightU⟩
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
      writeField S sign 1 1 := by
    simp only [actGates_append, hsubBlock]
    rw [show actGates (Step.coefficientFlip n lengthWidth shiftWidth) B = F
      by rfl, haddBlock, hF, hnormalize]
    simp only [B]
    rw [writeField_writeField, ← read_work2 n lengthWidth shiftWidth s,
      writeField_read]
  exact ⟨by simpa [S] using hpair, by simpa [S, sign] using haction⟩

private theorem coefficientBlocks_act_phaseFour
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    actGates
        (Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      writeField (encoded n lengthWidth shiftWidth s)
        (StepLayout.signWire n lengthWidth shiftWidth) 1 1 := by
  exact (coefficientBlocks_phaseFour_result h hwork hwidths
    hphase1 hphase2 (U := workWidth n) (by omega)).2

theorem coefficientPairWindow_phaseFour
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hU : workWidth n - s.lenRPrime - s.shift ≤ U) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s)) := by
  rw [show actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s) =
        encoded n lengthWidth shiftWidth s by
    simpa [Step.coefficientPrefixGates] using
      phaseFourPrefix_act h hwork hwidths hphase1 hphase2]
  exact (coefficientBlocks_phaseFour_result h hwork hwidths
    hphase1 hphase2 hU).1

private theorem encoded_write_sign_true
    (n lengthWidth shiftWidth : Nat) (s : State) :
    writeField (encoded n lengthWidth shiftWidth s)
        (StepLayout.signWire n lengthWidth shiftWidth) 1 1 =
      encoded n lengthWidth shiftWidth { s with sign := true } := by
  let L := StepLayout.layout n lengthWidth shiftWidth
  have hp1Read : L.read (encoded n lengthWidth shiftWidth s) 6 =
      boolValue s.phase1 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size,
      Nat.mod_eq_of_lt (boolValue_lt s.phase1)] using
      read_encoded n lengthWidth shiftWidth s 6
  have hp2Read : L.read (encoded n lengthWidth shiftWidth s) 7 =
      boolValue s.phase2 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size,
      Nat.mod_eq_of_lt (boolValue_lt s.phase2)] using
      read_encoded n lengthWidth shiftWidth s 7
  have hp1Write : L.write (encoded n lengthWidth shiftWidth s) 6
      (boolValue s.phase1) = encoded n lengthWidth shiftWidth s := by
    rw [← hp1Read]
    exact L.write_read _ _
  have hp2Write : L.write (encoded n lengthWidth shiftWidth s) 7
      (boolValue s.phase2) = encoded n lengthWidth shiftWidth s := by
    rw [← hp2Read]
    exact L.write_read _ _
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth s
    s.phase1 s.phase2 true
  dsimp only at hwrite
  rw [hp1Write, hp2Write] at hwrite
  simpa [L, Layout.write, StepLayout.layout, VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.signWire,
    StepLayout.phase1Wire, StepLayout.shiftOffset, boolValue,
    two_mul, three_mul, Nat.add_assoc] using hwrite

private theorem postShiftBlock_act_phaseFourEncoded
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hlenQ : s.lenQ = 0) (hshiftPos : 0 < s.shift)
    (hshiftFit : s.shift < 2 ^ shiftWidth) :
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth { s with shift := s.shift - 1 } := by
  let I := encoded n lengthWidth shiftWidth s
  let C := actGates (Step.postShiftControl n lengthWidth shiftWidth) I
  let J := StepPlaced.shiftInput n lengthWidth shiftWidth C
  let result := Shift.out (workWidth n) shiftWidth J
  have hcontrols := StepBlocks.postShiftControl_bits
    (controlClean n lengthWidth shiftWidth s)
  dsimp only at hcontrols
  rw [read_phase1, hphase1, read_phase2, hphase2] at hcontrols
  norm_num [boolValue] at hcontrols
  have hplus : bitValue J (Shift.plusWire shiftWidth) = 1 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_plus]
    exact hcontrols.1
  have hminus : bitValue J
      (Shift.minusWire (workWidth n) shiftWidth) = 1 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_minus]
    exact hcontrols.2
  have hCshift : readField C
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
        encodeLength shiftWidth s.shift := by
    dsimp only [C, I]
    rw [postShiftControl_read, read_shift]
    · simp [StepLayout.plusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
    · simp [StepLayout.minusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
  have hCwork : readField C (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n s := by
    dsimp only [C, I]
    rw [postShiftControl_read, read_work2]
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
    dsimp only [C, I]
    rw [postShiftControl_read]
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
  have hscratch : Shift.scratch shiftWidth J = 0 := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_scratch]
    exact hCpool
  have hposition : Shift.position shiftWidth J =
      encodeLength shiftWidth s.shift := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_position]
    exact hCshift
  have hwork : Shift.work (workWidth n) shiftWidth J =
      encodeWork2 n s := by
    dsimp only [J]
    rw [StepPlaced.shiftInput_work]
    exact hCwork
  have hout := Shift.out_decrement hplus hminus
  have hresultPosition : Shift.position shiftWidth result =
      encodeLength shiftWidth (s.shift - 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_pred hshiftPos hshiftFit]
  have hresultWork : Shift.work (workWidth n) shiftWidth result =
      encodeWork2 n { s with shift := s.shift - 1 } := by
    dsimp only [result]
    rw [hout.2, hwork]
    change rotateLeftValue (workWidth n)
        (rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s)) =
      rotatePositionsLeft (workWidth n) (s.shift - 1)
        (encodeWork2Raw n s)
    have hshift : s.shift - 1 + 1 = s.shift := by omega
    calc
      rotateLeftValue (workWidth n)
          (rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s)) =
          rotateLeftValue (workWidth n)
            (rotatePositionsLeft (workWidth n) (s.shift - 1 + 1)
              (encodeWork2Raw n s)) := by rw [hshift]
      _ = rotatePositionsLeft (workWidth n) (s.shift - 1)
          (encodeWork2Raw n s) :=
        rotatePositionsLeft_pred (workWidth n) (s.shift - 1)
          (encodeWork2Raw n s)
  rw [StepBlocks.postShiftBlock_act hscratch,
    hresultPosition, hresultWork]
  dsimp only [I]
  simpa [encodeWork2, encodeWork2Raw, Layout.write, StepLayout.layout,
    VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.shiftOffset,
    StepLayout.work2Offset, two_mul, three_mul, Nat.add_assoc] using
    (encoded_write_shift_work2_of_lenQ_zero n lengthWidth shiftWidth
      (s.shift - 1) s hlenQ)

def phaseFourPostShiftCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  encoded n lengthWidth shiftWidth
    { s with shift := s.shift - 1, sign := true }

theorem postShiftBlock_act_phaseFourPostShiftCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (writeField (encoded n lengthWidth shiftWidth s)
          (StepLayout.signWire n lengthWidth shiftWidth) 1 1) =
      phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s := by
  let s11 : State := { s with sign := true }
  have hencoded : writeField (encoded n lengthWidth shiftWidth s)
      (StepLayout.signWire n lengthWidth shiftWidth) 1 1 =
        encoded n lengthWidth shiftWidth s11 := by
    simpa [s11] using encoded_write_sign_true n lengthWidth shiftWidth s
  rw [hencoded]
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  have hpost := postShiftBlock_act_phaseFourEncoded
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (s := s11) (by simpa [s11] using hphase1)
    (by simpa [s11] using hphase2) (by simpa [s11] using hstate.2.2.1)
    (by simpa [s11] using hstate.2.2.2.1)
    (by simpa [s11] using h.stepDomain.valid.1.2.2.2.2.2.1)
  simpa [phaseFourPostShiftCheckpoint, s11] using hpost

private theorem phaseBlock_act_phaseFourPostShiftCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    let I := phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s
    let zeroShift := Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth) I
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1
            ((1 + zeroShift) % 2))
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          ((1 + zeroShift) % 2))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 0 := by
  dsimp only
  let s11 : State := { s with shift := s.shift - 1, sign := true }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  have hlenRPrimeFit : s.lenRPrime < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.2.2.1
  have hlenRPrimePhysical : readField
      (encoded n lengthWidth shiftWidth s11)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
        encodedZero lengthWidth := by
    rw [read_lenRPrime]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hlenRPrimeFit).mp (by
      simpa [s11] using hzero)
    have hlenRPrimePos : 0 < s.lenRPrime := by
      rw [h.stepDomain.valid.1.2.1]
      exact bitLength_pos hstate.1
    omega
  have hphaseAct := StepBlocks.phaseBlock_act_phase11
    (I := encoded n lengthWidth shiftWidth s11)
    (read_aux n lengthWidth shiftWidth s11)
    (by simp [read_phase1, s11, hphase1, boolValue])
    (by simp [read_phase2, s11, hphase2, boolValue])
    (by simp [read_sign, s11, boolValue])
    (by simp [read_lenQ, s11, hstate.2.2.1, encodeLength])
    hlenRPrimePhysical
  simpa [phaseFourPostShiftCheckpoint, s11] using hphaseAct

theorem phaseGates_act_phaseFourDecrementCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
        (phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        { s with shift := s.shift - 1, sign := false } := by
  let s11 : State := { s with shift := s.shift - 1, sign := true }
  have hphase := phaseBlock_act_phaseFourPostShiftCheckpoint
    h hphase1 hphase2
  dsimp only at hphase
  have hshiftPredFit : s.shift - 1 < 2 ^ shiftWidth := by
    have hfit := h.stepDomain.valid.1.2.2.2.2.2.1
    omega
  have hzeroShift : Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth)
      (phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s) = 0 := by
    simp [Phase.selectorValue, phaseFourPostShiftCheckpoint, read_shift,
      encodeLength_eq_encodedZero_iff hshiftPredFit, hdecrement]
  rw [hphase, hzeroShift]
  norm_num
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth s11
    true true false
  dsimp only at hwrite
  simpa [phaseFourPostShiftCheckpoint, s11, Layout.write,
    StepLayout.layout, VQ.Euclid.layout, Layout.offset, Layout.size,
    StepLayout.phase1Wire, StepLayout.phase2Wire, StepLayout.signWire,
    StepLayout.shiftOffset, hphase1, hphase2, boolValue, two_mul,
    three_mul, Nat.add_assoc] using hwrite

theorem phaseGates_act_phaseFourSwapCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
        (phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        { s with
          shift := 0
          phase1 := false
          phase2 := false
          sign := false } := by
  let s11 : State := { s with shift := s.shift - 1, sign := true }
  have hphase := phaseBlock_act_phaseFourPostShiftCheckpoint
    h hphase1 hphase2
  dsimp only at hphase
  have hzeroShift : Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth)
      (phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s) = 1 := by
    simp [Phase.selectorValue, phaseFourPostShiftCheckpoint, read_shift,
      hswap, encodeLength]
  rw [hphase, hzeroShift]
  norm_num
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth s11
    false false false
  dsimp only at hwrite
  simpa [phaseFourPostShiftCheckpoint, s11, hswap, Layout.write,
    StepLayout.layout, VQ.Euclid.layout, Layout.offset, Layout.size,
    StepLayout.phase1Wire, StepLayout.phase2Wire, StepLayout.signWire,
    StepLayout.shiftOffset, boolValue, two_mul, three_mul,
    Nat.add_assoc] using hwrite

theorem ownershipBlock_inactive_phaseFourDecrement
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hdecrement : s.shift - 1 ≠ 0) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          { s with shift := s.shift - 1, sign := false }) =
      encoded n lengthWidth shiftWidth
        { s with shift := s.shift - 1, sign := false } := by
  let s11 : State := { s with shift := s.shift - 1, sign := false }
  apply StepBlocks.ownershipBlock_inactive hwork
    (read_control n lengthWidth shiftWidth s11)
    (read_aux n lengthWidth shiftWidth s11)
  right
  rw [read_shift]
  intro hzero
  have hshiftFit : s.shift - 1 < 2 ^ shiftWidth := by
    have hfit := h.stepDomain.valid.1.2.2.2.2.2.1
    omega
  have hdecoded := (encodeLength_eq_encodedZero_iff hshiftFit).mp (by
    simpa [s11] using hzero)
  exact hdecrement hdecoded

private theorem ownershipBlock_act_phaseFourSwapPhysical
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    let s00 : State := { s with
      shift := 0
      phase1 := false
      phase2 := false
      sign := false }
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s00) =
      StepBlocks.ownershipCleanedState n lengthWidth shiftWidth
        (StepBlocks.ownershipPostState n lengthWidth shiftWidth
          (encoded n lengthWidth shiftWidth s00)
          (encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
            s.tPrime s.rPrime)
          (encodeSplit (workWidth n) (s.lenT + 1) s.t s.r)
          (encodeLength lengthWidth (bitLength s.tPrime))
          (encodeLength lengthWidth (bitLength s.r))) := by
  dsimp only
  let s00 : State := { s with
    shift := 0
    phase1 := false
    phase2 := false
    sign := false }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  apply ownershipBlock_act_active h.stepDomain hphase1 hphase2 hwork
    (read_control n lengthWidth shiftWidth s00)
    (read_aux n lengthWidth shiftWidth s00)
  · simp [read_lenQ, s00, hstate.2.2.1, encodeLength]
  · simp [read_shift, s00, encodeLength]
  · rw [read_work1, Nat.mod_eq_of_lt (encodeWork1_lt
      (by simpa [s00] using ht) (by simpa [s00, hstate.2.2.1] using
        hallocation))]
    have hzero : reverseBits 0 s.q = 0 := by
      have hlt := reverseBits_lt 0 s.q
      omega
    simp [s00, hstate.2.2.1, encodeWork1, encodeSplit, hzero]
  · rw [read_work2]
    have hraw : encodeWork2Raw n s =
        encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
          s.tPrime s.rPrime := by
      simp [encodeWork2Raw, encodeSplit, Nat.sub_sub_self
        _hwork2Allocation]
    have hrawLt : encodeWork2Raw n s < 2 ^ workWidth n := by
      rw [hraw]
      exact encodeSplit_lt (Nat.sub_le _ _)
        _htPrimeFit
    change rotatePositionsLeft (workWidth n) 0 (encodeWork2Raw n s00) = _
    rw [show encodeWork2Raw n s00 = encodeWork2Raw n s by rfl]
    simpa [rotatePositionsLeft, Nat.mod_eq_of_lt hrawLt] using hraw
  · simpa [s00] using read_lenT n lengthWidth shiftWidth s00
  · simpa [s00] using read_lenRPrime n lengthWidth shiftWidth s00

theorem phaseFour_swap_work1Encoding
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime =
      encodeWork1 n (step lengthWidth shiftWidth s) := by
  have hstep := ReachableStepDomain.phaseFour_swap_step_eq
    h hphase1 hphase2 hswap
  have hcore := StepDomain.phaseFour_length_core
    h.stepDomain hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, hlenRPrime, _ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, hrPrime⟩
  have hfirst : bitLength s.tPrime + 1 ≤
      workWidth n - s.lenRPrime := by
    simp only [workWidth]
    omega
  have hright : s.rPrime <
      2 ^ (workWidth n - (workWidth n - s.lenRPrime)) := by
    have heq : workWidth n - (workWidth n - s.lenRPrime) =
        s.lenRPrime := by omega
    simpa only [heq] using hrPrime
  have hsplit := encodeSplit_eq_of_split_le
    (left := s.tPrime) (right := s.rPrime)
    hfirst (Nat.sub_le _ _) hright
  rw [hstep]
  have hzero : reverseBits 0 0 = 0 := by
    have hlt := reverseBits_lt 0 0
    omega
  simpa [encodeWork1, encodeSplit, hzero] using hsplit.symm

theorem phaseFour_swap_work2Encoding
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    encodeSplit (workWidth n) (s.lenT + 1) s.t s.r =
      encodeWork2 n (step lengthWidth shiftWidth s) := by
  have hstep := ReachableStepDomain.phaseFour_swap_step_eq
    h hphase1 hphase2 hswap
  have hcore := StepDomain.phaseFour_length_core
    h.stepDomain hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hfirst : s.lenT + 1 ≤ workWidth n - bitLength s.r := by
    simp only [workWidth]
    omega
  have hsecond : workWidth n - bitLength s.r ≤ workWidth n :=
    Nat.sub_le _ _
  have hright : s.r <
      2 ^ (workWidth n - (workWidth n - bitLength s.r)) := by
    have hlen : bitLength s.r ≤ workWidth n := by
      simp only [workWidth]
      omega
    have heq : workWidth n - (workWidth n - bitLength s.r) =
        bitLength s.r := by omega
    simpa only [heq] using lt_two_pow_bitLength s.r
  have hsplit := encodeSplit_eq_of_split_le
    (left := s.t) (right := s.r) hfirst hsecond hright
  have htSecond : s.t < 2 ^ (workWidth n - bitLength s.r) := by
    exact ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hsplitLt : encodeSplit (workWidth n)
      (workWidth n - bitLength s.r) s.t s.r < 2 ^ workWidth n :=
    encodeSplit_lt hsecond htSecond
  have hwidthSub :
      workWidth n - (workWidth n - bitLength s.r) = bitLength s.r := by
    omega
  have hrawLt :
      s.t ||| reverseBits (bitLength s.r) s.r <<<
          (workWidth n - bitLength s.r) <
        2 ^ workWidth n := by
    simpa [encodeSplit, hwidthSub] using hsplitLt
  rw [hstep]
  simpa [encodeWork2, encodeWork2Raw, rotatePositionsLeft, encodeSplit,
    hwidthSub, Nat.mod_eq_of_lt hrawLt] using hsplit

private theorem ownershipBlock_act_phaseFourSwap
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    let s00 : State := { s with
      shift := 0
      phase1 := false
      phase2 := false
      sign := false }
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s00) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  dsimp only
  let s00 : State := { s with
    shift := 0
    phase1 := false
    phase2 := false
    sign := false }
  let s' := step lengthWidth shiftWidth s
  let I := encoded n lengthWidth shiftWidth s00
  let w1 := encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
    s.tPrime s.rPrime
  let w2 := encodeSplit (workWidth n) (s.lenT + 1) s.t s.r
  let newLenT := encodeLength lengthWidth (bitLength s.tPrime)
  let newLenRPrime := encodeLength lengthWidth (bitLength s.r)
  let newIter :=
    (bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) + 1) % 2
  let X := writeField
    (StepBlocks.ownershipBodyState n lengthWidth shiftWidth I
      w1 w2 newLenT newLenRPrime)
    (StepLayout.iterWire n lengthWidth shiftWidth) 1 newIter
  let L := StepLayout.layout n lengthWidth shiftWidth
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphase1 hphase2
  have hstep := ReachableStepDomain.phaseFour_swap_step_eq
    h hphase1 hphase2 hswap
  rw [ownershipBlock_act_phaseFourSwapPhysical h hwork hphase1 hphase2]
  have hIcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    simpa [I] using read_control n lengthWidth shiftWidth s00
  have hIaux : readField I
      (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
    simpa [I] using read_aux n lengthWidth shiftWidth s00
  have hIlenQ : readField I
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth := by
    simpa [I, s00, hstate.2.2.1, encodeLength] using
      read_lenQ n lengthWidth shiftWidth s00
  have hIshift : readField I
      (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      encodedZero shiftWidth := by
    simpa [I, s00, encodeLength] using
      read_shift n lengthWidth shiftWidth s00
  rw [StepBlocks.ownershipCleanedPostState_eq_result
    (I := I) (w1 := w1) (w2 := w2)
    (newLenT := newLenT) (newLenRPrime := newLenRPrime)
    hIcontrol hIaux hIlenQ hIshift]
  change X = encoded n lengthWidth shiftWidth s'
  have hXform : X =
      L.write
        (L.write
          (L.write
            (L.write
              (L.write I 0 w1)
              1 w2)
            2 newLenT)
          4 newLenRPrime)
        8 newIter := by
    simp [X, L, StepBlocks.ownershipBodyState, Layout.write,
      StepLayout.layout, VQ.Euclid.layout, Layout.offset, Layout.size,
      StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.lenTOffset, StepLayout.lenRPrimeOffset,
      StepLayout.iterWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      two_mul, three_mul, Nat.add_assoc]
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, htPrimeFit, _hrPrimeFit⟩
  have hw1Fit : w1 < 2 ^ L.size 0 := by
    change encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
      s.tPrime s.rPrime < 2 ^ workWidth n
    exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit
  have hw2Fit : w2 < 2 ^ L.size 1 := by
    change encodeSplit (workWidth n) (s.lenT + 1) s.t s.r <
      2 ^ workWidth n
    apply encodeSplit_lt
    · omega
    · exact ht.trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right s.lenT 1))
  have hnewLenTFit : newLenT < 2 ^ L.size 2 := by
    change encodeLength lengthWidth (bitLength s.tPrime) <
      2 ^ lengthWidth
    exact encodeLength_lt _ _
  have hnewLenRPrimeFit : newLenRPrime < 2 ^ L.size 4 := by
    change encodeLength lengthWidth (bitLength s.r) < 2 ^ lengthWidth
    exact encodeLength_lt _ _
  have hnewIterFit : newIter < 2 ^ L.size 8 := by
    change
      (bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) + 1) % 2 < 2
    exact Nat.mod_lt _ (by omega)
  have hXlt : X < 2 ^ L.width := by
    rw [hXform]
    exact Layout.write_lt
      (Layout.write_lt
        (Layout.write_lt
          (Layout.write_lt
            (Layout.write_lt (encoded_lt n lengthWidth shiftWidth s00)))))
  apply Layout.ext hXlt (encoded_lt n lengthWidth shiftWidth s')
  intro j hj
  have hj' : j < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hj
  interval_cases j
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_self hw1Fit]
    change w1 = readField (encoded n lengthWidth shiftWidth s')
      StepLayout.work1Offset (workWidth n)
    rw [read_work1,
      ← phaseFour_swap_work1Encoding h hphase1 hphase2 hswap]
    exact (Nat.mod_eq_of_lt (by
      simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size] using
        hw1Fit)).symm
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_self hw2Fit]
    change w2 = readField (encoded n lengthWidth shiftWidth s')
      (StepLayout.work2Offset n) (workWidth n)
    rw [read_work2]
    exact phaseFour_swap_work2Encoding h hphase1 hphase2 hswap
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_self hnewLenTFit]
    have heq : newLenT =
        readField (encoded n lengthWidth shiftWidth s')
          (StepLayout.lenTOffset n) lengthWidth := by
      rw [read_lenT]
      simp [newLenT, s', hstep]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenTOffset, two_mul,
      Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth =
          readField (encoded n lengthWidth shiftWidth s')
            (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_lenQ, read_lenQ]
      simp [s00, s', hstep, hstate.2.2.1]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenQOffset, two_mul,
      Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_self hnewLenRPrimeFit]
    have heq : newLenRPrime =
        readField (encoded n lengthWidth shiftWidth s')
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth := by
      rw [read_lenRPrime]
      simp [newLenRPrime, s', hstep]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenRPrimeOffset, two_mul,
      Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth =
          readField (encoded n lengthWidth shiftWidth s')
            (StepLayout.shiftOffset n lengthWidth) shiftWidth := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_shift, read_shift]
      simp [s00, s', hstep]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.shiftOffset, two_mul,
      three_mul, Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) =
          bitValue (encoded n lengthWidth shiftWidth s')
            (StepLayout.phase1Wire n lengthWidth shiftWidth) := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_phase1, read_phase1]
      simp [s00, s', hstep, boolValue]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase1Wire,
      StepLayout.shiftOffset, readField_one, two_mul, three_mul,
      Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) =
          bitValue (encoded n lengthWidth shiftWidth s')
            (StepLayout.phase2Wire n lengthWidth shiftWidth) := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_phase2, read_phase2]
      simp [s00, s', hstep, boolValue]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase2Wire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_self hnewIterFit]
    have heq : newIter =
        bitValue (encoded n lengthWidth shiftWidth s')
          (StepLayout.iterWire n lengthWidth shiftWidth) := by
      rw [read_iter]
      simp only [newIter]
      rw [show bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) =
          boolValue s.iter by
        simpa [I, s00] using read_iter n lengthWidth shiftWidth s00]
      cases hiter : s.iter <;> simp [s', hstep, boolValue, hiter]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        bitValue I (StepLayout.signWire n lengthWidth shiftWidth) =
          bitValue (encoded n lengthWidth shiftWidth s')
            (StepLayout.signWire n lengthWidth shiftWidth) := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_sign, read_sign]
      simp [s00, s', hstep, boolValue]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.signWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) =
          bitValue (encoded n lengthWidth shiftWidth s')
            (StepLayout.controlWire n lengthWidth shiftWidth) := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_control, read_control]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.controlWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    have heq :
        readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
            (StepLayout.auxWidth lengthWidth shiftWidth) =
          readField (encoded n lengthWidth shiftWidth s')
            (StepLayout.auxOffset n lengthWidth shiftWidth)
            (StepLayout.auxWidth lengthWidth shiftWidth) := by
      rw [show I = encoded n lengthWidth shiftWidth s00 by rfl,
        read_aux, read_aux]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, two_mul, three_mul,
      Nat.add_assoc] using heq

theorem phaseOwnershipBlocks_act_phaseFour
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    actGates
        (StepLayout.phaseGates n lengthWidth shiftWidth ++
          Step.ownershipBlock n lengthWidth shiftWidth)
        (phaseFourPostShiftCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth s) := by
  simp only [actGates_append]
  by_cases hswap : s.shift - 1 = 0
  · rw [phaseGates_act_phaseFourSwapCheckpoint
      h hphase1 hphase2 hswap,
      ownershipBlock_act_phaseFourSwap
        h hwork hphase1 hphase2 hswap]
  · rw [phaseGates_act_phaseFourDecrementCheckpoint
      h hphase1 hphase2 hswap,
      ownershipBlock_inactive_phaseFourDecrement
        h hwork hswap,
      ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]

theorem gates_act_phaseFour
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth s) := by
  have hprefix := phaseFourPrefix_act
    h hwork hwidths hphase1 hphase2
  have hcoefficient := coefficientBlocks_act_phaseFour
    h hwork hwidths hphase1 hphase2
  have hpost := postShiftBlock_act_phaseFourPostShiftCheckpoint
    h hphase1 hphase2
  have hphaseOwnership := phaseOwnershipBlocks_act_phaseFour
    h hwork hphase1 hphase2
  simp only [actGates_append] at hprefix hcoefficient hphaseOwnership
  simp only [Step.gates, actGates_append]
  rw [hprefix, hcoefficient, hpost, hphaseOwnership]

theorem reverseCircuit_recovers_phaseFour
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    act (Step.reverseCircuit n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s)) =
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
    simpa [act, Step.circuit] using gates_act_phaseFour
      h hwork hwidths hphase1 hphase2
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
