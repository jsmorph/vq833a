import VQ.Euclid.StepState.Common

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

theorem preShiftBlock_act_phaseZero
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hlenQ : s.lenQ = 0)
    (hnowrap : s.shift + 1 < 2 ^ shiftWidth) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        { s with shift := s.shift + 1 } := by
  let I := encoded n lengthWidth shiftWidth s
  let C := actGates (Step.preShiftControl n lengthWidth shiftWidth) I
  let J := StepPlaced.shiftInput n lengthWidth shiftWidth C
  let result := Shift.out (workWidth n) shiftWidth J
  have hcontrols := StepBlocks.preShiftControl_bits
    (controlClean n lengthWidth shiftWidth s)
  dsimp only at hcontrols
  rw [read_phase1, hphase1, read_phase2, hphase2] at hcontrols
  simp only [boolValue, Bool.false_eq_true, ↓reduceIte] at hcontrols
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
    dsimp only [C, I]
    rw [preShiftControl_read, read_shift]
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
    rw [preShiftControl_read, read_work2]
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
  have hout := Shift.out_increment hplus hminus
  have hresultPosition : Shift.position shiftWidth result =
      encodeLength shiftWidth (s.shift + 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_succ hnowrap]
  have hresultWork : Shift.work (workWidth n) shiftWidth result =
      rotatePositionsLeft (workWidth n) (s.shift + 1)
        (encodeWork2Raw n s) := by
    dsimp only [result]
    rw [hout.2, hwork, encodeWork2,
      rotatePositionsLeft_succ]
  rw [StepBlocks.preShiftBlock_act hscratch,
    hresultPosition, hresultWork]
  dsimp only [I]
  simpa [Layout.write, StepLayout.layout, VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.shiftOffset,
    StepLayout.work2Offset, two_mul, three_mul, Nat.add_assoc] using
    (encoded_write_shift_work2_of_lenQ_zero n lengthWidth shiftWidth
      (s.shift + 1) s hlenQ)

theorem preShiftBlock_act_reachable_phaseZero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        { s with shift := s.shift + 1 } := by
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  exact preShiftBlock_act_phaseZero hphase1 hphase2 hready.2.2.1
    (StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2)

theorem guardedRemainderSubControl_act_encoded_phase1_zero
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = false) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      writeField (encoded n lengthWidth shiftWidth s)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  have hzero : bitValue (encoded n lengthWidth shiftWidth s)
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
    apply read_aux_bit
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth]
      omega
  have hclean := controlClean n lengthWidth shiftWidth s
  rw [StepBlocks.guardedRemainderSubControl_act_live hzero,
    StepBlocks.remainderSubControl_act]
  simp [StepControl.negativeOut, hclean.control, read_phase1, hphase1,
    boolValue]

theorem phaseZero_remainderLeftEndpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    (encodeLength lengthWidth s.lenT +
        encodeLength lengthWidth s.lenQ + 3) % 2 ^ lengthWidth =
      s.lenT + 1 := by
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos
      (ReachableStepDomain.phaseZero_t_pos h hphase1 hrPrime)
  have hlenTFit : s.lenT < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.1
  have hsum : s.lenT + 1 < 2 ^ lengthWidth := by
    have hallocation := h.stepDomain.valid.1.2.2.2.2.2.2.1
    omega
  have hencodeT : encodeLength lengthWidth s.lenT = s.lenT - 1 := by
    simp [encodeLength, Nat.ne_of_gt hlenTPos,
      Nat.mod_eq_of_lt (show s.lenT - 1 < 2 ^ lengthWidth by omega)]
  have hencodeQ : encodeLength lengthWidth s.lenQ =
      2 ^ lengthWidth - 1 := by
    simp [encodeLength, encodedZero, hlive.2.1]
  rw [hencodeT, hencodeQ]
  have heq : s.lenT - 1 + (2 ^ lengthWidth - 1) + 3 =
      s.lenT + 1 + 2 ^ lengthWidth := by
    have hpow := Nat.two_pow_pos lengthWidth
    omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsum]

theorem phaseZero_remainderRightEndpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    (n + 1 +
        (2 ^ lengthWidth - encodeLength lengthWidth (s.shift + 1))) %
        2 ^ lengthWidth =
      n + 1 - s.shift := by
  have hlength := ReachableStepDomain.phaseZero_length_shift_le
    h hphase1 hphase2 hrPrime
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hnextWindow := ReachableStepDomain.phaseZero_nextWindow
    h hphase1 hphase2 hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ lengthWidth := by
    omega
  have hencode : encodeLength lengthWidth (s.shift + 1) = s.shift := by
    simp [encodeLength,
      Nat.mod_eq_of_lt (show s.shift < 2 ^ lengthWidth by omega)]
  rw [hencode]
  have heq : n + 1 + (2 ^ lengthWidth - s.shift) =
      2 ^ lengthWidth + (n + 1 - s.shift) := by
    have hpow := Nat.two_pow_pos lengthWidth
    have htPos := ReachableStepDomain.phaseZero_t_pos h hphase1 hrPrime
    have hlenTPos : 0 < s.lenT := by
      rw [h.stepDomain.valid.1.1]
      exact bitLength_pos htPos
    omega
  have hrightFit : n + 1 - s.shift < 2 ^ lengthWidth := by
    omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hrightFit]

theorem phaseZero_remainderPrepare_stable
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let s0 : State := { s with shift := s.shift + 1 }
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s0)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    Interval.Stable (s.lenT + 1) (n + 1 - s.shift)
        (workWidth n) lengthWidth input ∧
      bitValue input
          (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
        bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
  dsimp only
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hnextWindow := ReachableStepDomain.phaseZero_nextWindow
    h hphase1 hphase2 hrPrime
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hshiftFit : s.shift + 1 < 2 ^ lengthWidth := by omega
  let s0 : State := { s with shift := s.shift + 1 }
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth s0
  have hframe := StepBlocks.remainderPrepare_frame_of_controlled_clean
    hlength hwidths hscratch
  dsimp only at hframe
  have hstable := hframe.stable
  dsimp [s0] at hstable
  rw [read_lenT, read_lenQ, read_shift_narrow hwidths hshiftFit,
    phaseZero_remainderLeftEndpoint h hwork hphase1 hphase2 hrPrime,
    phaseZero_remainderRightEndpoint h hwork hphase1 hphase2 hrPrime]
      at hstable
  rw [guardedRemainderSubControl_act_encoded_phase1_zero
    (s := s0) (by simp [s0, hphase1])]
  simpa [s0] using ⟨hstable, hframe.accumulator, hframe.carry⟩

theorem phaseZero_remainderOperands
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    let s0 : State := { s with shift := k }
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s0)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    readField input (Interval.sourceOffset + left) width =
        readField (encodeWork2 n s0) left width ∧
      reverseBits width
          (readField input (Interval.sourceOffset + left) width) =
        s.rPrime ∧
      readField input (Interval.targetOffset (workWidth n) + left) width =
        readField (encodeWork1 n s0) left width ∧
      reverseBits width
          (readField input
            (Interval.targetOffset (workWidth n) + left) width) =
        s.r >>> k ∧
      readField input (Interval.targetOffset (workWidth n)) (workWidth n) =
        encodeWork1 n s0 % 2 ^ workWidth n ∧
      bitValue input (Interval.signWire (workWidth n) lengthWidth) = 0 := by
  dsimp only
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hnextWindow := ReachableStepDomain.phaseZero_nextWindow
    h hphase1 hphase2 hrPrime
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have htPrimeLt := h.earlyCoefficientOrder hphase1 hrPrime
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, hlenRPrime, _hlenTFit, _hlenQFit, hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, htFit, _hqShift,
      _hlenQValue, hrFit, _htPrimeFit, hrPrimeFit⟩
  have hlenRPrimePos : 0 < s.lenRPrime := by
    rw [hlenRPrime]
    exact bitLength_pos hrPrime
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp at hlenRPrimeFit
    omega
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := n + 1 - s.shift
  let width := right - left + 1
  let s0 : State := { s with shift := k }
  have hbound : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    simp only [workWidth]
    omega
  have hwidthEq : width = workWidth n - k - left := by
    dsimp [width, right, k, left]
    simp only [workWidth]
    omega
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth s0
  have hframe := StepBlocks.remainderPrepare_frame_of_controlled_clean
    hlength hwidths hscratch
  dsimp only at hframe
  let prepared := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
    (writeField (encoded n lengthWidth shiftWidth s0)
      (StepLayout.controlWire n lengthWidth shiftWidth) 1 1)
  have hpreparedWork1 : readField prepared StepLayout.work1Offset
      (workWidth n) = encodeWork1 n s0 % 2 ^ workWidth n := by
    calc
      readField prepared StepLayout.work1Offset (workWidth n) =
          readField (encoded n lengthWidth shiftWidth s0)
            StepLayout.work1Offset (workWidth n) := by
        simpa [prepared] using hframe.work1
      _ = encodeWork1 n s0 % 2 ^ workWidth n :=
        read_work1 n lengthWidth shiftWidth s0
  have hpreparedWork2 : readField prepared (StepLayout.work2Offset n)
      (workWidth n) = encodeWork2 n s0 := by
    calc
      readField prepared (StepLayout.work2Offset n) (workWidth n) =
          readField (encoded n lengthWidth shiftWidth s0)
            (StepLayout.work2Offset n) (workWidth n) := by
        simpa [prepared] using hframe.work2
      _ = encodeWork2 n s0 := read_work2 n lengthWidth shiftWidth s0
  have hpreparedSign : bitValue prepared
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    calc
      bitValue prepared (StepLayout.signWire n lengthWidth shiftWidth) =
          bitValue (encoded n lengthWidth shiftWidth s0)
            (StepLayout.signWire n lengthWidth shiftWidth) := by
        simpa [prepared] using hframe.sign
      _ = boolValue s0.sign := read_sign n lengthWidth shiftWidth s0
      _ = 0 := by simp [s0, hready.1, boolValue]
  let input := StepPlaced.remainderIntervalInput
    n lengthWidth shiftWidth prepared
  have hsourceSlice :
      readField input (Interval.sourceOffset + left) width =
        readField (encodeWork2 n s0) left width := by
    calc
      readField input (Interval.sourceOffset + left) width =
          readField prepared (StepLayout.work2Offset n + left) width := by
        simpa [input] using
          StepPlaced.remainderIntervalInput_source_sub
            n lengthWidth shiftWidth left width prepared hbound
      _ = readField
          (readField prepared (StepLayout.work2Offset n) (workWidth n))
          left width := by
        symm
        exact readField_readField hbound
      _ = readField (encodeWork2 n s0) left width := by
        rw [hpreparedWork2]
  have htPrimeBound : s.tPrime < 2 ^ (left + k) := by
    have htPower : s.tPrime < 2 ^ s.lenT := htPrimeLt.trans htFit
    exact htPower.trans_le (Nat.pow_le_pow_right (by omega) (by
      dsimp [left, k]
      omega))
  have hrPrimeCover : s.lenRPrime ≤ width := by
    dsimp [left, width, right, k]
    simp only [workWidth] at hnextWindow
    omega
  have hsourceTop : left + k + width = workWidth n := by
    dsimp [left, width, right, k]
    simp only [workWidth]
    omega
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) =
      s.rPrime := by
    rw [hsourceSlice]
    simpa [s0] using reverseBits_readField_encodeWork2_top
      (n := n) (s := s0) (off := left) (len := width)
      htPrimeBound hrPrimeFit hrPrimeCover hsourceTop
  have htargetSlice :
      readField input (Interval.targetOffset (workWidth n) + left) width =
        readField (encodeWork1 n s0) left width := by
    calc
      readField input (Interval.targetOffset (workWidth n) + left) width =
          readField prepared (StepLayout.work1Offset + left) width := by
        simpa [input] using
          StepPlaced.remainderIntervalInput_target_sub
            n lengthWidth shiftWidth left width prepared hbound
      _ = readField
          (readField prepared StepLayout.work1Offset (workWidth n))
          left width := by
        symm
        exact readField_readField hbound
      _ = readField (encodeWork1 n s0 % 2 ^ workWidth n) left width := by
        rw [hpreparedWork1]
      _ = readField (encodeWork1 n s0) left width := by
        apply Nat.eq_of_testBit_eq
        intro b
        rw [testBit_readField, testBit_readField]
        by_cases hb : b < width
        · simp [hb, Nat.testBit_mod_two_pow,
            show left + b < workWidth n by omega]
        · simp [hb]
  have htargetWindow : s0.lenT + 1 + s0.lenQ + k ≤ workWidth n := by
    dsimp [s0, k]
    rw [hlive.2.1]
    omega
  have htargetValue : reverseBits width
      (readField input
        (Interval.targetOffset (workWidth n) + left) width) =
      s.r >>> k := by
    rw [htargetSlice]
    rw [hwidthEq]
    have hdecode := reverseBits_readField_encodeWork1_remainder_discard
      (n := n) (s := s0) (discard := k)
      htargetWindow htFit hrFit
    dsimp only at hdecode
    simpa [s0, left, k, hlive.2.1] using hdecode
  have htarget : readField input
      (Interval.targetOffset (workWidth n)) (workWidth n) =
      encodeWork1 n s0 % 2 ^ workWidth n := by
    calc
      readField input (Interval.targetOffset (workWidth n)) (workWidth n) =
          readField prepared StepLayout.work1Offset (workWidth n) := by
        simpa [input] using StepPlaced.remainderIntervalInput_target
          n lengthWidth shiftWidth prepared
      _ = encodeWork1 n s0 % 2 ^ workWidth n := hpreparedWork1
  have hsignValue : bitValue input
      (Interval.signWire (workWidth n) lengthWidth) = 0 := by
    exact (by simpa [input] using
      (StepPlaced.remainderIntervalInput_sign
        n lengthWidth shiftWidth prepared).trans hpreparedSign)
  rw [guardedRemainderSubControl_act_encoded_phase1_zero
    (s := s0) (by simp [s0, hphase1])]
  simpa [left, right, width, s0, prepared, input, k] using
    ⟨hsourceSlice, hsourceValue, htargetSlice, htargetValue, htarget,
      hsignValue⟩

theorem phaseZero_remainderOperandBounds
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    s.rPrime < 2 ^ width ∧ s.r >>> k < 2 ^ width := by
  dsimp only
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hnextWindow := ReachableStepDomain.phaseZero_nextWindow
    h hphase1 hphase2 hrPrime
  have hlength := ReachableStepDomain.phaseZero_length_shift_le
    h hphase1 hphase2 hrPrime
  rcases h.stepDomain.valid.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hrFit, _, hrPrimeFit⟩
  have hrPrimeCover : s.lenRPrime ≤
      (n + 1 - s.shift) - (s.lenT + 1) + 1 := by
    simp only [workWidth] at hnextWindow
    omega
  constructor
  · exact hrPrimeFit.trans_le
      (Nat.pow_le_pow_right (by omega) hrPrimeCover)
  · rw [Nat.shiftRight_eq_div_pow,
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (s.shift + 1))]
    have hpow :
        2 ^ ((n + 1 - s.shift) - (s.lenT + 1) + 1) *
            2 ^ (s.shift + 1) =
          2 ^ (workWidth n - (s.lenT + 1 + s.lenQ)) := by
      rw [← pow_add]
      congr 1
      rw [hlive.2.1]
      simp only [workWidth]
      omega
    rw [hpow]
    exact hrFit

theorem phaseZero_remainderPreparedSubValues
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    let s0 : State := { s with shift := k }
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s0)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    StepPlaced.intervalSubTargetValue left right (workWidth n) lengthWidth
        input =
      writeField (encodeWork1 n s0 % 2 ^ workWidth n) left width
        (reverseBits width
          (Adder.difference width s.rPrime (s.r >>> k))) ∧
      StepPlaced.intervalSubSignValue left right (workWidth n) lengthWidth
          input =
        Adder.borrow s.rPrime (s.r >>> k) := by
  dsimp only
  have hoperands := phaseZero_remainderOperands
    h hwidths hphase1 hphase2 hrPrime
  dsimp only at hoperands
  rcases hoperands with ⟨_, hsource, _, htarget, hfull, hsign⟩
  constructor
  · simp only [StepPlaced.intervalSubTargetValue]
    rw [hfull, hsource, htarget]
  · simp only [StepPlaced.intervalSubSignValue]
    rw [hsign, hsource, htarget]
    by_cases hborrow : s.r >>> (s.shift + 1) < s.rPrime
    · simp [Adder.borrow, hborrow]
    · simp [Adder.borrow, hborrow]

theorem phaseZero_remainderDecodedSubValues
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    Adder.difference width s.rPrime targetWord = subWord ∧
      Adder.borrow s.rPrime targetWord = subSign := by
  dsimp only
  have hbounds := phaseZero_remainderOperandBounds
    h hphase1 hphase2 hrPrime
  dsimp only at hbounds
  have htake : shifted s.rPrime (s.shift + 1) ≤ s.r ↔
      s.rPrime ≤ s.r >>> (s.shift + 1) :=
    shifted_le_iff_le_shiftRight s.rPrime s.r (s.shift + 1)
  constructor
  · rw [Adder.difference_eq_if hbounds.1 hbounds.2]
    by_cases htakeValue : shifted s.rPrime (s.shift + 1) ≤ s.r
    · rw [if_pos (htake.mp htakeValue), if_pos htakeValue]
    · have hnotLe : ¬ s.rPrime ≤ s.r >>> (s.shift + 1) := by
        exact fun hle => htakeValue (htake.mpr hle)
      rw [if_neg hnotLe, if_neg htakeValue]
  · simp only [Adder.borrow]
    by_cases htakeValue : shifted s.rPrime (s.shift + 1) ≤ s.r
    · have hle := htake.mp htakeValue
      have hnotLt : ¬ s.r >>> (s.shift + 1) < s.rPrime :=
        Nat.not_lt_of_ge hle
      rw [if_neg hnotLt, if_pos htakeValue]
    · have hnotLe : ¬ s.rPrime ≤ s.r >>> (s.shift + 1) := by
        exact fun hle => htakeValue (htake.mpr hle)
      have hlt : s.r >>> (s.shift + 1) < s.rPrime :=
        Nat.lt_of_not_ge hnotLe
      rw [if_pos hlt, if_neg htakeValue]

theorem guardedRemainderSubBlock_act_phaseZero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let s0 : State := { s with shift := k }
    let I := encoded n lengthWidth shiftWidth s0
    actGates (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work1Offset + left) width
          (reverseBits width subWord))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 subSign := by
  dsimp only
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hfit : s.lenT + 1 +
      ((n + 1 - s.shift) - (s.lenT + 1) + 1) ≤ workWidth n := by
    simp only [workWidth]
    omega
  have hstable := phaseZero_remainderPrepare_stable
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hstable
  have hprepared := phaseZero_remainderPreparedSubValues
    h hwidths hphase1 hphase2 hrPrime
  dsimp only at hprepared
  have hdecoded := phaseZero_remainderDecodedSubValues
    h hphase1 hphase2 hrPrime
  dsimp only at hdecoded
  have hblock := StepBlocks.guardedRemainderSubBlock_act
    (I := encoded n lengthWidth shiftWidth
      { s with shift := s.shift + 1 })
    (left := s.lenT + 1) (right := n + 1 - s.shift)
    hlength hwidths (Nat.le_of_lt hwork) hendpoint.1 hendpoint.2
    hstable.1 hstable.2.1 hstable.2.2
  dsimp only at hblock
  rw [hprepared.1, hprepared.2, hdecoded.1, hdecoded.2] at hblock
  rw [← read_work1 n lengthWidth shiftWidth
    { s with shift := s.shift + 1 }] at hblock
  rw [← writeField_subfield hfit] at hblock
  exact hblock

theorem guardedRemainderAddControl_act_phaseZeroPostSub
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let s0 : State := { s with shift := k }
    let I := encoded n lengthWidth shiftWidth s0
    let B := writeField I (StepLayout.work1Offset + left) width
      (reverseBits width subWord)
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
    F = writeField B (StepLayout.signWire n lengthWidth shiftWidth) 1
        subSign ∧
      C = writeField
        (writeField F (StepLayout.plusWire n lengthWidth shiftWidth) 1 1)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := n + 1 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let s0 : State := { s with shift := k }
  let I := encoded n lengthWidth shiftWidth s0
  let B := writeField I (StepLayout.work1Offset + left) width
    (reverseBits width subWord)
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let C := actGates
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let minus := StepLayout.minusWire n lengthWidth shiftWidth
  let zeroRPrime := StepLayout.zeroRPrimeWire n lengthWidth shiftWidth
  change F = writeField B sign 1 subSign ∧
    C = writeField (writeField F plus 1 1) control 1 1
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hbound : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    simp only [workWidth]
    omega
  have hS : S = writeField B sign 1 subSign := by
    exact guardedRemainderSubBlock_act_phaseZero
      h hwork hwidths hphase1 hphase2 hrPrime
  have hBbit (q : Nat) (hq : workWidth n ≤ q) :
      bitValue B q = bitValue I q := by
    apply bitValue_write_out
    right
    simpa [B, StepLayout.work1Offset] using hbound.trans hq
  have hSbit (q : Nat) (hqs : q ≠ sign) (hq : workWidth n ≤ q) :
      bitValue S q = bitValue I q := by
    rw [hS, bitValue_write_ne hqs]
    exact hBbit q hq
  have hp2S : bitValue S p2 = 0 := by
    rw [hSbit p2 (by
      simp [p2, sign, StepLayout.phase2Wire, StepLayout.signWire]) (by
      simp [p2, StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simpa [I, p2, s0, hphase2, boolValue] using
      read_phase2 n lengthWidth shiftWidth s0
  have hF : F = writeField B sign 1 subSign := by
    change actGates (Step.remainderFlip n lengthWidth shiftWidth) S = _
    rw [StepBlocks.remainderFlip_identity_of_phase2_zero hp2S, hS]
  have hFbit (q : Nat) (hqs : q ≠ sign) (hq : workWidth n ≤ q) :
      bitValue F q = bitValue I q := by
    rw [hF, bitValue_write_ne hqs]
    exact hBbit q hq
  have hp1F : bitValue F p1 = 0 := by
    rw [hFbit p1 (by
      simp [p1, sign, StepLayout.signWire]) (by
      simp [p1, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simpa [I, p1, s0, hphase1, boolValue] using
      read_phase1 n lengthWidth shiftWidth s0
  have hp2F : bitValue F p2 = 0 := by
    rw [hFbit p2 (by
      simp [p2, sign, StepLayout.phase2Wire, StepLayout.signWire]) (by
      simp [p2, StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simpa [I, p2, s0, hphase2, boolValue] using
      read_phase2 n lengthWidth shiftWidth s0
  have hcleanI := controlClean n lengthWidth shiftWidth s0
  have hcleanF : StepBlocks.ControlClean n lengthWidth shiftWidth F := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hFbit control (by
        simp [control, sign, StepLayout.controlWire, StepLayout.signWire]) (by
        simp [control, StepLayout.controlWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega)]
      simpa [I, control] using hcleanI.control
    · rw [hFbit temporary (by
        simp [temporary, sign, StepLayout.temporaryWire,
          StepLayout.signWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [temporary, StepLayout.temporaryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
      simpa [I, temporary] using hcleanI.temporary
    · rw [hFbit plus (by
        simp [plus, sign, StepLayout.plusWire, StepLayout.signWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [plus, StepLayout.plusWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
      simpa [I, plus] using hcleanI.plus
    · rw [hFbit minus (by
        simp [minus, sign, StepLayout.minusWire, StepLayout.signWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [minus, StepLayout.minusWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
      simpa [I, minus] using hcleanI.minus
  have hzeroRPrimeF : bitValue F zeroRPrime = 0 := by
    rw [hFbit zeroRPrime (by
      simp [zeroRPrime, sign, StepLayout.zeroRPrimeWire,
        StepLayout.signWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega) (by
      simp [zeroRPrime, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    apply read_aux_bit
    · simp [zeroRPrime, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire]
      omega
    · simp [zeroRPrime, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth]
      omega
  have hC : C = writeField (writeField F plus 1 1) control 1 1 := by
    exact StepBlocks.guardedRemainderAddControl_act_phase00
      hcleanF hp1F hp2F hzeroRPrimeF
  exact ⟨hF, hC⟩

private theorem phaseZero_remainderAddControl_scratchExceptControl
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let s0 : State := { s with shift := k }
    let I := encoded n lengthWidth shiftWidth s0
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
    readField C (StepLayout.leftOffset n lengthWidth shiftWidth)
        lengthWidth = 0 ∧
      readField C (StepLayout.rightOffset n lengthWidth shiftWidth)
        lengthWidth = 0 ∧
      bitValue C (StepLayout.carryWire n lengthWidth shiftWidth) = 0 ∧
      bitValue C
          (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 ∧
      bitValue C (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 ∧
      bitValue C
          (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 ∧
      readField C (StepLayout.poolOffset n lengthWidth shiftWidth)
          lengthWidth = 0 ∧
      bitValue C
          (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := n + 1 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let s0 : State := { s with shift := k }
  let I := encoded n lengthWidth shiftWidth s0
  let B := writeField I (StepLayout.work1Offset + left) width
    (reverseBits width subWord)
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let C := actGates
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  change readField C (StepLayout.leftOffset n lengthWidth shiftWidth)
        lengthWidth = 0 ∧
    readField C (StepLayout.rightOffset n lengthWidth shiftWidth)
        lengthWidth = 0 ∧
    bitValue C (StepLayout.carryWire n lengthWidth shiftWidth) = 0 ∧
    bitValue C (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 ∧
    bitValue C (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 ∧
    bitValue C (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 ∧
    readField C (StepLayout.poolOffset n lengthWidth shiftWidth)
        lengthWidth = 0 ∧
    bitValue C (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hfit : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    simp only [workWidth]
    omega
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hpost := guardedRemainderAddControl_act_phaseZeroPostSub
    h hwork hwidths hphase1 hphase2 hrPrime
  have hF : F = writeField B sign 1 subSign := hpost.1
  have hFaux (off len : Nat)
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off) :
      readField F off len = readField I off len := by
    rw [hF, readField_writeField_of_disjoint (Or.inl (by
      simp [sign, StepLayout.signWire, StepLayout.auxOffset] at hlo ⊢
      omega))]
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp only [StepLayout.work1Offset]
      have haux : workWidth n ≤
          StepLayout.auxOffset n lengthWidth shiftWidth := by
        simp [StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega
      omega))]
  have hCaux (off len : Nat)
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
      (hhi : off + len ≤
        StepLayout.cellScratchWire n lengthWidth shiftWidth + 1) :
      readField C off len = readField I off len := by
    calc
      readField C off len = readField F off len := by
        simpa [C] using
          StepBlocks.guardedRemainderAddControl_preserves_auxCore
            (I := F) hlo hhi
      _ = readField I off len := hFaux off len hlo
  have hCauxBit (q : Nat)
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ q)
      (hhi : q + 1 ≤
        StepLayout.cellScratchWire n lengthWidth shiftWidth + 1) :
      bitValue C q = bitValue I q := by
    simpa [readField_one] using hCaux q 1 hlo hhi
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth s0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hCaux _ _ (by simp [StepLayout.leftOffset]) (by
      simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega)).trans hscratch.left
  · exact (hCaux _ _ (by simp [StepLayout.rightOffset]) (by
      simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega)).trans hscratch.right
  · exact (hCauxBit _ (by
      simp [StepLayout.carryWire, StepLayout.auxOffset]) (by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)).trans hscratch.carry
  · exact (hCauxBit _ (by
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.accumulatorWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega)).trans hscratch.accumulator
  · exact (hCauxBit _ (by
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.leftFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega)).trans hscratch.leftFlag
  · exact (hCauxBit _ (by
      simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.rightFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega)).trans hscratch.rightFlag
  · exact (hCaux _ _ (by
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.cellScratchWire]
      omega)).trans hscratch.pool
  · exact (hCauxBit _ (by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega) (by omega)).trans hscratch.cellScratch

theorem phaseZero_remainderPreparedAdd
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    let s0 : State := { s with shift := k }
    let I := encoded n lengthWidth shiftWidth s0
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    Interval.Stable left right (workWidth n) lengthWidth input ∧
      bitValue input
          (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
        bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 ∧
          StepPlaced.intervalAddTargetValue left right (workWidth n)
              lengthWidth input =
            encodeWork1 n s0 % 2 ^ workWidth n := by
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := n + 1 - s.shift
  let width := right - left + 1
  let targetWord := s.r >>> k
  let x := Adder.difference width s.rPrime targetWord
  let base := encodeWork1 n { s with shift := k } % 2 ^ workWidth n
  let s0 : State := { s with shift := k }
  let I := encoded n lengthWidth shiftWidth s0
  let B := writeField I (StepLayout.work1Offset + left) width
    (reverseBits width x)
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let C := actGates
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
  let P := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
  let input := StepPlaced.remainderIntervalInput
    n lengthWidth shiftWidth P
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  change Interval.Stable left right (workWidth n) lengthWidth input ∧
    bitValue input
        (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
      bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 ∧
        StepPlaced.intervalAddTargetValue left right (workWidth n)
            lengthWidth input = base
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hfit : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    simp only [workWidth]
    omega
  have hbounds := phaseZero_remainderOperandBounds
    h hphase1 hphase2 hrPrime
  dsimp only at hbounds
  have hdecoded := phaseZero_remainderDecodedSubValues
    h hphase1 hphase2 hrPrime
  dsimp only at hdecoded
  have hpost := guardedRemainderAddControl_act_phaseZeroPostSub
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hpost
  rw [← hdecoded.1] at hpost
  have hF : F = writeField B sign 1
      (if shifted s.rPrime k ≤ s.r then 0 else 1) := by
    simpa [F, B, S, I, sign, x, targetWord, width, left, right, k]
      using hpost.1
  have hC : C = writeField (writeField F plus 1 1) control 1 1 := by
    simpa [C, F, S, I, control, plus, sign, x, targetWord,
      width, left, right, k] using hpost.2
  have hscratchC := phaseZero_remainderAddControl_scratchExceptControl
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hscratchC
  rcases hscratchC with
    ⟨hleftC, hrightC, hcarryC, haccumulatorC,
      hleftFlagC, hrightFlagC, hpoolC, hcellScratchC⟩
  have hcontrolC : bitValue C control = 1 := by
    rw [hC, bitValue_write_self]
  have hframe := StepBlocks.remainderPrepare_frame_of_live_frame
    (I := C) hlength hwidths hleftC hrightC hcontrolC hcarryC
      haccumulatorC hleftFlagC hrightFlagC hpoolC hcellScratchC
  dsimp only at hframe
  change StepBlocks.RemainderPreparedFrame
    n lengthWidth shiftWidth C P at hframe
  have hCfield (off len : Nat) (hlo : workWidth n ≤ off)
      (hhi : off + len ≤ sign) :
      readField C off len = readField I off len := by
    rw [hC,
      readField_writeField_of_disjoint (Or.inr (hhi.trans (by
        simp [control, sign, StepLayout.controlWire, StepLayout.signWire]))),
      readField_writeField_of_disjoint (Or.inr (hhi.trans (by
        simp [plus, sign, StepLayout.plusWire, StepLayout.signWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))), hF,
      readField_writeField_of_disjoint (Or.inr hhi)]
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp only [StepLayout.work1Offset]
      omega))]
  have hshiftFit : s.shift + 1 < 2 ^ lengthWidth := by
    omega
  have hlenTC : readField C (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [hCfield _ _ (by
      simp [StepLayout.lenTOffset, workWidth]) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.lenTOffset]
      omega)]
    exact read_lenT n lengthWidth shiftWidth s0
  have hlenQC : readField C
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenQ := by
    rw [hCfield _ _ (by
      simp [StepLayout.lenQOffset, workWidth]
      omega) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.lenQOffset]
      omega)]
    exact read_lenQ n lengthWidth shiftWidth s0
  have hshiftC : readField C
      (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth (s.shift + 1) := by
    rw [hCfield _ _ (by
      simp [StepLayout.shiftOffset]
      omega) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire]
      omega)]
    exact read_shift_narrow hwidths hshiftFit
  have hstable := hframe.stable
  rw [hlenTC, hlenQC, hshiftC,
    phaseZero_remainderLeftEndpoint h hwork hphase1 hphase2 hrPrime,
    phaseZero_remainderRightEndpoint h hwork hphase1 hphase2 hrPrime]
      at hstable
  have hwork2C : readField C (StepLayout.work2Offset n) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
    exact hCfield _ _ (by simp [StepLayout.work2Offset]) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.work2Offset]
      omega)
  have hwork2P : readField P (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n s0 := by
    rw [hframe.work2, hwork2C]
    exact read_work2 n lengthWidth shiftWidth s0
  have hwork1C : readField C StepLayout.work1Offset (workWidth n) =
      readField B StepLayout.work1Offset (workWidth n) := by
    rw [hC,
      readField_writeField_of_disjoint (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.work1Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [plus, StepLayout.plusWire, StepLayout.work1Offset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hF,
      readField_writeField_of_disjoint (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work1Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))]
  have hbase : readField I StepLayout.work1Offset (workWidth n) = base := by
    simpa [I, base, s0, k] using
      read_work1 n lengthWidth shiftWidth s0
  have hbaseBound : base < 2 ^ workWidth n := by
    exact Nat.mod_lt _ (Nat.two_pow_pos (workWidth n))
  have hupdatedBound : writeField base left width (reverseBits width x) <
      2 ^ workWidth n := writeField_lt hfit hbaseBound
  have hwork1B : readField B StepLayout.work1Offset (workWidth n) =
      writeField base left width (reverseBits width x) := by
    simp only [B]
    rw [writeField_subfield hfit, readField_writeField,
      hbase, Nat.mod_eq_of_lt hupdatedBound]
  have hwork1P : readField P StepLayout.work1Offset (workWidth n) =
      writeField base left width (reverseBits width x) := by
    rw [hframe.work1, hwork1C, hwork1B]
  have hsourceSlice : readField input (Interval.sourceOffset + left) width =
      readField (encodeWork2 n s0) left width := by
    calc
      readField input (Interval.sourceOffset + left) width =
          readField P (StepLayout.work2Offset n + left) width := by
        simpa [input] using
          StepPlaced.remainderIntervalInput_source_sub
            n lengthWidth shiftWidth left width P hfit
      _ = readField
          (readField P (StepLayout.work2Offset n) (workWidth n))
          left width := by
        symm
        exact readField_readField hfit
      _ = readField (encodeWork2 n s0) left width := by rw [hwork2P]
  have hoperands := phaseZero_remainderOperands
    h hwidths hphase1 hphase2 hrPrime
  dsimp only at hoperands
  rcases hoperands with
    ⟨holdSourceSlice, holdSource, holdTargetSlice, holdTarget, _, _⟩
  rw [holdSourceSlice] at holdSource
  rw [holdTargetSlice] at holdTarget
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) = s.rPrime := by
    rw [hsourceSlice]
    exact holdSource
  have htargetFull : readField input
      (Interval.targetOffset (workWidth n)) (workWidth n) =
      writeField base left width (reverseBits width x) := by
    calc
      readField input (Interval.targetOffset (workWidth n)) (workWidth n) =
          readField P StepLayout.work1Offset (workWidth n) := by
        simpa [input] using StepPlaced.remainderIntervalInput_target
          n lengthWidth shiftWidth P
      _ = writeField base left width (reverseBits width x) := hwork1P
  have hbaseSlice : readField base left width =
      readField (encodeWork1 n s0) left width := by
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [base, s0]
    rw [testBit_readField, testBit_readField]
    by_cases hb : b < width
    · simp [hb, Nat.testBit_mod_two_pow,
        show left + b < workWidth n by omega]
    · simp [hb]
  have horiginal : reverseBits width (readField base left width) =
      targetWord := by
    rw [hbaseSlice]
    exact holdTarget
  have htargetValueRestored :
      StepPlaced.intervalAddTargetValue left right (workWidth n)
          lengthWidth input = base := by
    simpa only [x, width] using
      StepPlaced.intervalAddTargetValue_difference
        (endpointWidth := lengthWidth) hfit htargetFull hsourceValue
          horiginal hbounds.1 hbounds.2
  exact ⟨hstable, hframe.accumulator, hframe.carry,
    htargetValueRestored⟩

theorem guardedRemainderAddBlock_act_phaseZeroPostSub
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let take := shifted s.rPrime k ≤ s.r
    let subSign := if take then 0 else 1
    let s0 : State := { s with shift := k }
    let I := encoded n lengthWidth shiftWidth s0
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) F =
      writeField I (StepLayout.signWire n lengthWidth shiftWidth) 1
        subSign := by
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := n + 1 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let s0 : State := { s with shift := k }
  let I := encoded n lengthWidth shiftWidth s0
  let B := writeField I (StepLayout.work1Offset + left) width
    (reverseBits width subWord)
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let base := encodeWork1 n s0 % 2 ^ workWidth n
  change actGates
      (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) F =
    writeField I sign 1 subSign
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphase1 hphase2 hrPrime
  dsimp only at hendpoint
  have hfit : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    simp only [workWidth]
    omega
  have hprepared := phaseZero_remainderPreparedAdd
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hprepared
  have hblock := StepBlocks.guardedRemainderAddBlock_act
    (I := F) (left := left) (right := right)
    hlength hwidths (Nat.le_of_lt hwork) hendpoint.1 hendpoint.2
    hprepared.1 hprepared.2.1 hprepared.2.2.1
  dsimp only at hblock
  rw [hprepared.2.2.2] at hblock
  have hpost := guardedRemainderAddControl_act_phaseZeroPostSub
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hpost
  have hF : F = writeField B sign 1 subSign := by
    simpa [F, B, S, I, sign, subWord, take, targetWord,
      width, left, right, k] using hpost.1
  have hbase : readField I StepLayout.work1Offset (workWidth n) = base := by
    simpa [I, base] using read_work1 n lengthWidth shiftWidth s0
  have hrestore :
      writeField F StepLayout.work1Offset (workWidth n) base =
        writeField I sign 1 subSign := by
    rw [hF, writeField_comm (by
      right
      simp [sign, StepLayout.work1Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simp only [B]
    rw [writeField_subfield hfit, writeField_writeField,
      ← hbase, writeField_read]
  exact hblock.trans hrestore

def phaseZeroRemainderCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  let k := s.shift + 1
  let take := shifted s.rPrime k ≤ s.r
  let subSign := if take then 0 else 1
  writeField
    (encoded n lengthWidth shiftWidth { s with shift := k })
    (StepLayout.signWire n lengthWidth shiftWidth) 1 subSign

def phaseZeroBorrowState (s : State) : State :=
  { s with
    shift := s.shift + 1
    sign := decide (s.r < shifted s.rPrime (s.shift + 1)) }

theorem guardedRemainderBlocks_act_phaseZeroCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    actGates (Step.guardedRemainderBlocks n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          { s with shift := s.shift + 1 }) =
      phaseZeroRemainderCheckpoint n lengthWidth shiftWidth s := by
  let k := s.shift + 1
  let take := shifted s.rPrime k ≤ s.r
  let subSign := if take then 0 else 1
  let s0 : State := { s with shift := k }
  let I := encoded n lengthWidth shiftWidth s0
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let selector :=
    StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth
  let body := Step.guardedRemainderSubBlock n lengthWidth shiftWidth ++
    Step.remainderFlip n lengthWidth shiftWidth ++
    Step.guardedRemainderAddBlock n lengthWidth shiftWidth
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  have hrem := guardedRemainderAddBlock_act_phaseZeroPostSub
    h hwork hwidths hphase1 hphase2 hrPrime
  dsimp only at hrem
  have hbody : actGates body I = writeField I sign 1 subSign := by
    simpa [body, actGates_append, F, S, I, s0, sign, subSign, take, k]
      using hrem
  have hpackedStep := ReachableStepDomain.phaseZero_packed_after_step
    h hwork hwidths hphase1 hphase2
  rw [ReachableStepDomain.phaseZero_step_eq
    h hwork hwidths hphase1 hphase2] at hpackedStep
  have hpackedS0 : Packed n lengthWidth shiftWidth s0 := by
    simpa [s0, k, Packed] using hpackedStep
  have hselect : actGates selector I = I := by
    have hselectorWidth : lengthWidth ≤
        StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
    have hpool : readField I
        (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
      dsimp [I]
      apply read_aux_subfield
      · simp [StepLayout.poolOffset, StepLayout.carryWire]
        omega
      · simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth]
        omega
    have hzero : bitValue I
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
      dsimp [I]
      apply read_aux_bit
      · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire]
        omega
      · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth]
        omega
    have hliveLen : readField I
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
          encodedZero lengthWidth % 2 ^ lengthWidth := by
      simpa [I] using read_lenRPrime_live hpackedS0 hrPrime
    dsimp [selector]
    rw [StepPlaced.rPrimeZeroSelectorGates_act hpool, if_neg hliveLen]
    exact write_of_bitValue (by simp [hzero])
  have hbodySelected : actGates body (actGates selector I) =
      writeField (actGates selector I) sign 1 subSign := by
    rw [hselect]
    exact hbody
  have hout := StepBlocks.around_write
    (compute := selector) (body := body) (I := I)
    (StepLayout.rPrimeZeroSelectorGates_wellFormed
      n lengthWidth shiftWidth)
    (StepBlocks.rPrimeZeroSelectorGates_avoids_sign
      n lengthWidth shiftWidth)
    hbodySelected
  simpa [Step.guardedRemainderBlocks, selector, body, I, sign,
    phaseZeroRemainderCheckpoint, s0, k, take, subSign] using hout

theorem phaseZeroRemainderCheckpoint_eq_encoded
    (n lengthWidth shiftWidth : Nat) (s : State) :
    phaseZeroRemainderCheckpoint n lengthWidth shiftWidth s =
      encoded n lengthWidth shiftWidth (phaseZeroBorrowState s) := by
  let k := s.shift + 1
  let borrow := decide (s.r < shifted s.rPrime k)
  let s0 : State := { s with shift := k }
  let E := encoded n lengthWidth shiftWidth s0
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hborrow : (if shifted s.rPrime k ≤ s.r then 0 else 1) =
      boolValue borrow := by
    by_cases htake : shifted s.rPrime k ≤ s.r
    · have hnlt : ¬ s.r < shifted s.rPrime k := Nat.not_lt_of_ge htake
      simp [borrow, htake, hnlt, boolValue]
    · have hlt : s.r < shifted s.rPrime k := Nat.lt_of_not_ge htake
      simp [borrow, htake, hlt, boolValue]
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth
    s0 s.phase1 s.phase2 borrow
  dsimp only at hwrite
  have hwrite' : writeField
      (writeField (writeField E p1 1 (boolValue s.phase1))
        p2 1 (boolValue s.phase2)) sign 1 (boolValue borrow) =
      encoded n lengthWidth shiftWidth
        { s0 with
          phase1 := s.phase1
          phase2 := s.phase2
          sign := borrow } := by
    simpa [E, p1, p2, sign, Layout.write, StepLayout.layout,
      VQ.Euclid.layout,
      Layout.offset, Layout.size, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.signWire, StepLayout.shiftOffset,
      two_mul, three_mul, Nat.add_assoc] using hwrite
  have hp1 : writeField E p1 1 (boolValue s.phase1) = E := by
    rw [show boolValue s.phase1 = bitValue E p1 by
      simpa [E, p1, s0] using
        (read_phase1 n lengthWidth shiftWidth s0).symm]
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt E p1))
  have hp2 : writeField E p2 1 (boolValue s.phase2) = E := by
    rw [show boolValue s.phase2 = bitValue E p2 by
      simpa [E, p2, s0] using
        (read_phase2 n lengthWidth shiftWidth s0).symm]
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt E p2))
  rw [hp1, hp2] at hwrite'
  simpa [phaseZeroRemainderCheckpoint, phaseZeroBorrowState, k, borrow,
    s0, E, sign,
    Layout.offset, Layout.size, StepLayout.phase1Wire,
    StepLayout.phase2Wire, StepLayout.signWire, StepLayout.shiftOffset,
    hborrow] using hwrite'

private theorem coefficientSubCallWindow_of_phase1_zero
    {n lengthWidth shiftWidth U I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hclean : StepBlocks.ControlClean n lengthWidth shiftWidth I)
    (hscratch : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0) :
    CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I) := by
  let C := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) I
  have hpreserveAux (off len : Nat)
      (hlo : StepLayout.controlWire n lengthWidth shiftWidth + 1 ≤ off)
      (hhi : off + len ≤
        StepLayout.temporaryWire n lengthWidth shiftWidth) :
      readField C off len = readField I off len := by
    dsimp only [C]
    apply readField_actGates_of_outside
    intro g hg q hq
    have hq' : q ∈
        (Step.coefficientSubControl n lengthWidth shiftWidth).flatMap
          RGate.wires := by
      rw [List.mem_flatMap]
      exact ⟨g, hg, hq⟩
    simp [Step.coefficientSubControl, Phase.negativeAndGates,
      RGate.wires] at hq'
    have hqCases :
        q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
          q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
          q = StepLayout.signWire n lengthWidth shiftWidth ∨
          q = StepLayout.controlWire n lengthWidth shiftWidth ∨
          q = StepLayout.temporaryWire n lengthWidth shiftWidth := by
      aesop
    rcases hqCases with
        rfl | rfl | rfl | rfl | rfl <;>
      simp [StepLayout.phase2Wire, StepLayout.signWire,
        StepLayout.controlWire, StepLayout.temporaryWire] at hlo hhi ⊢ <;>
      omega
  have hcontrol : bitValue C
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    have hbit := StepBlocks.coefficientSubControl_bit hclean
    dsimp only at hbit
    rw [hphase1] at hbit
    simp only [ite_self] at hbit
    simpa [C] using hbit
  have hscratchC : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth C := by
    have hselector : lengthWidth ≤
        StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
    constructor
    · rw [hpreserveAux
        (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.leftOffset, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.leftOffset, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)]
      exact hscratch.left
    · rw [hpreserveAux
        (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.rightOffset, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.rightOffset, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)]
      exact hscratch.right
    · exact hcontrol
    · rw [← readField_one, hpreserveAux
        (StepLayout.carryWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.carryWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.carry
    · rw [← readField_one, hpreserveAux
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.accumulatorWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.accumulatorWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.accumulator
    · rw [← readField_one, hpreserveAux
        (StepLayout.leftFlagWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.leftFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.leftFlagWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.leftFlag
    · rw [← readField_one, hpreserveAux
        (StepLayout.rightFlagWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.rightFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.rightFlagWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.rightFlag
    · rw [hpreserveAux
        (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.temporaryWire, StepLayout.cellScratchWire]
          omega)]
      exact hscratch.pool
    · rw [← readField_one, hpreserveAux
        (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.controlWire]
          omega) (by
          simp [StepLayout.temporaryWire]), readField_one]
      exact hscratch.cellScratch
  apply coefficientCallWindow_inactive
  exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
    hlength hwidths hscratchC.right hscratchC.control hscratchC.carry
    hscratchC.accumulator hscratchC.leftFlag hscratchC.rightFlag
    hscratchC.pool hscratchC.cellScratch

theorem coefficientPairWindow_phaseZero
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s)) := by
  let sB := phaseZeroBorrowState s
  let I := encoded n lengthWidth shiftWidth sB
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hclean := controlClean n lengthWidth shiftWidth sB
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth sB
  have hp1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, sB, phaseZeroBorrowState, read_phase1, hphase1, boolValue]
  have hp2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, sB, phaseZeroBorrowState, read_phase2, hphase2, boolValue]
  have hpre := preShiftBlock_act_reachable_phaseZero
    h hwork hwidths hphase1 hphase2
  have hrem := guardedRemainderBlocks_act_phaseZeroCheckpoint
    h hwork hwidths hphase1 hphase2 hrPrime
  have hqincControl : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientIncrementControl_identity_of_phase2_zero hp2
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
    StepBlocks.swapControl_identity_of_equal_phases (hp1.trans hp2.symm)
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
    StepBlocks.quotientDecrementControl_identity_of_phase1_zero hp1
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
  have hsubWindow := coefficientSubCallWindow_of_phase1_zero
    (U := U) hlength hwidths hclean hscratch hp1
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity_of_phase1_zero
      hlength hwidths hclean hscratch hp1
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hp1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hp1
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
  rw [hpre, hrem,
    phaseZeroRemainderCheckpoint_eq_encoded, show
      encoded n lengthWidth shiftWidth sB = I by rfl, hqinc, hswap, hqdec]
  change CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I) ∧
    CoefficientCallWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientAddControl n lengthWidth shiftWidth)
        (actGates (Step.coefficientFlip n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubBlock n lengthWidth shiftWidth) I)))
  constructor
  · exact hsubWindow
  · rw [hsub, hflip]
    exact coefficientCallWindow_inactive haddInactive

theorem phaseZeroInactiveSuffix_act
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false) :
    actGates
        (Step.quotientIncrementBlock n lengthWidth shiftWidth ++
          Step.swapBlock n lengthWidth shiftWidth ++
          Step.quotientDecrementBlock n lengthWidth shiftWidth ++
          Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth ++
          Step.around (Step.postShiftControl n lengthWidth shiftWidth)
            (StepLayout.shiftGates n lengthWidth shiftWidth))
        (phaseZeroRemainderCheckpoint n lengthWidth shiftWidth s) =
      phaseZeroRemainderCheckpoint n lengthWidth shiftWidth s := by
  let sB := phaseZeroBorrowState s
  let I := encoded n lengthWidth shiftWidth sB
  rw [phaseZeroRemainderCheckpoint_eq_encoded]
  change actGates
      (Step.quotientIncrementBlock n lengthWidth shiftWidth ++
        Step.swapBlock n lengthWidth shiftWidth ++
        Step.quotientDecrementBlock n lengthWidth shiftWidth ++
        Step.coefficientSubBlock n lengthWidth shiftWidth ++
        Step.coefficientFlip n lengthWidth shiftWidth ++
        Step.coefficientAddBlock n lengthWidth shiftWidth ++
        Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hclean := controlClean n lengthWidth shiftWidth sB
  have hscratch := encodedRemainderScratchClean
    n lengthWidth shiftWidth sB
  have haux := read_aux n lengthWidth shiftWidth sB
  have hp1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, sB, phaseZeroBorrowState, read_phase1, hphase1, boolValue]
  have hp2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    simp [I, sB, phaseZeroBorrowState, read_phase2, hphase2, boolValue]
  have hqincControl : actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientIncrementControl_identity_of_phase2_zero hp2
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
    StepBlocks.swapControl_identity_of_equal_phases (hp1.trans hp2.symm)
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
    StepBlocks.quotientDecrementControl_identity_of_phase1_zero hp1
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
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity_of_phase1_zero
      hlength hwidths hclean hscratch hp1
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hp1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hp1
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
      hp1 hclean.plus
  have hpostScratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)) = 0 := by
    rw [hpostControl, StepPlaced.shiftInput_scratch]
    apply readField_sub_zero
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
      haux
  have hpost : actGates
      (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
        (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I := by
    apply StepBlocks.postShiftBlock_identity hpostScratch
    · rw [hpostControl]
      exact hclean.plus
    · rw [hpostControl]
      exact hclean.minus
  simp only [actGates_append]
  rw [hqinc, hswap, hqdec, hsub, hflip, hadd, hpost]

theorem phaseGates_act_phaseZeroCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
        (phaseZeroRemainderCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth s) := by
  let borrow := decide
    (s.r < shifted s.rPrime (s.shift + 1))
  let sB := phaseZeroBorrowState s
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ shiftWidth :=
    StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2
  rw [phaseZeroRemainderCheckpoint_eq_encoded]
  change actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth sB) =
    encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s)
  have hlenQPhysical : readField (encoded n lengthWidth shiftWidth sB)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth := by
    rw [read_lenQ]
    simp [sB, phaseZeroBorrowState, hlive.2.1, encodeLength, encodedZero]
  have hlenRPrimePhysical : readField
      (encoded n lengthWidth shiftWidth sB)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth := by
    rw [read_lenRPrime]
    intro hzero
    have hfit : sB.lenRPrime < 2 ^ lengthWidth := by
      simpa [sB, phaseZeroBorrowState] using
        h.stepDomain.valid.1.2.2.2.2.1
    have hdecoded := (encodeLength_eq_encodedZero_iff hfit).mp hzero
    have hlenPos : 0 < s.lenRPrime := by
      rw [h.stepDomain.valid.1.2.1]
      exact bitLength_pos hrPrime
    have hlenPosB : 0 < sB.lenRPrime := by
      simpa [sB, phaseZeroBorrowState] using hlenPos
    omega
  have hshiftPhysical : readField (encoded n lengthWidth shiftWidth sB)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
      encodedZero shiftWidth := by
    rw [read_shift]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hshiftFit).mp hzero
    simp at hdecoded
  have hphaseAct := StepBlocks.phaseBlock_act_phase00
    (I := encoded n lengthWidth shiftWidth sB)
    (read_aux n lengthWidth shiftWidth sB)
    (by simp [read_phase1, sB, phaseZeroBorrowState, hphase1, boolValue])
    (by simp [read_phase2, sB, phaseZeroBorrowState, hphase2, boolValue])
    hlenQPhysical hlenRPrimePhysical hshiftPhysical
  rw [hphaseAct, read_sign]
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth sB
    false borrow false
  dsimp only at hwrite
  simpa [Layout.write, StepLayout.layout, VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.phase1Wire,
    StepLayout.phase2Wire, StepLayout.signWire, StepLayout.shiftOffset,
    sB, borrow, phaseZeroBorrowState,
    ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2,
    hphase1, boolValue, two_mul, three_mul, Nat.add_assoc] using hwrite

theorem ownershipBlock_inactive_phaseZeroStep
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hstep := ReachableStepDomain.phaseZero_step_eq
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

theorem gates_act_phaseZero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hpre := preShiftBlock_act_reachable_phaseZero
    h hwork hwidths hphase1 hphase2
  have hrem := guardedRemainderBlocks_act_phaseZeroCheckpoint
    h hwork hwidths hphase1 hphase2 hrPrime
  have hsuffix := phaseZeroInactiveSuffix_act
    h hwork hwidths hphase1 hphase2
  simp only [actGates_append] at hsuffix
  have hphase := phaseGates_act_phaseZeroCheckpoint
    h hwork hwidths hphase1 hphase2 hrPrime
  have hownership := ownershipBlock_inactive_phaseZeroStep
    h hwork hwidths hphase1 hphase2
  simp only [Step.gates, actGates_append]
  rw [hpre, hrem, hsuffix, hphase, hownership]

theorem reverseCircuit_recovers_phaseZero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
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
    simpa [act, Step.circuit] using gates_act_phaseZero
      h hwork hwidths hphase1 hphase2 hrPrime
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
