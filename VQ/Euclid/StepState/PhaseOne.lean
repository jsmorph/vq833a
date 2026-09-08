import VQ.Euclid.StepState.Common

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

def phaseOnePreShiftCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  writeField
    (writeField (encoded n lengthWidth shiftWidth s)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth
      (encodeLength shiftWidth (s.shift - 1)))
    (StepLayout.work2Offset n) (workWidth n)
    (encodeWork2 n { s with shift := s.shift - 1 })

private theorem phaseOnePreShiftCheckpoint_read
    {n lengthWidth shiftWidth off width : Nat} {s : State}
    (hwork2 : StepLayout.work2Offset n + workWidth n ≤ off ∨
      off + width ≤ StepLayout.work2Offset n)
    (hshift : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ off ∨
      off + width ≤ StepLayout.shiftOffset n lengthWidth) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) off width =
      readField (encoded n lengthWidth shiftWidth s) off width := by
  rw [phaseOnePreShiftCheckpoint,
    readField_writeField_of_disjoint hwork2,
    readField_writeField_of_disjoint hshift]

private theorem phaseOnePreShiftCheckpoint_bit
    {n lengthWidth shiftWidth q : Nat} {s : State}
    (hwork2 : StepLayout.work2Offset n + workWidth n ≤ q ∨
      q + 1 ≤ StepLayout.work2Offset n)
    (hshift : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ q ∨
      q + 1 ≤ StepLayout.shiftOffset n lengthWidth) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) q =
      bitValue (encoded n lengthWidth shiftWidth s) q := by
  rw [← readField_one, ← readField_one,
    phaseOnePreShiftCheckpoint_read hwork2 hshift]

private theorem phaseOnePreShiftCheckpoint_read_after_shift
    {n lengthWidth shiftWidth off width : Nat} {s : State}
    (hoff : StepLayout.phase1Wire n lengthWidth shiftWidth ≤ off) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) off width =
      readField (encoded n lengthWidth shiftWidth s) off width := by
  apply phaseOnePreShiftCheckpoint_read
  · left
    calc
      StepLayout.work2Offset n + workWidth n ≤
          StepLayout.phase1Wire n lengthWidth shiftWidth := by
        simp [StepLayout.work2Offset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega
      _ ≤ off := hoff
  · left
    simpa [StepLayout.phase1Wire] using hoff

private theorem phaseOnePreShiftCheckpoint_bit_after_shift
    {n lengthWidth shiftWidth q : Nat} {s : State}
    (hq : StepLayout.phase1Wire n lengthWidth shiftWidth ≤ q) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) q =
      bitValue (encoded n lengthWidth shiftWidth s) q := by
  rw [← readField_one, ← readField_one,
    phaseOnePreShiftCheckpoint_read_after_shift hq]

theorem preShiftBlock_act_phaseOne
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hshiftPos : 0 < s.shift) (hshiftFit : s.shift < 2 ^ shiftWidth) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s := by
  change actGates
      (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
        (StepLayout.shiftGates n lengthWidth shiftWidth))
      (encoded n lengthWidth shiftWidth s) =
    writeField
      (writeField (encoded n lengthWidth shiftWidth s)
        (StepLayout.shiftOffset n lengthWidth) shiftWidth
        (encodeLength shiftWidth (s.shift - 1)))
      (StepLayout.work2Offset n) (workWidth n)
      (encodeWork2 n { s with shift := s.shift - 1 })
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
      (Shift.minusWire (workWidth n) shiftWidth) = 1 := by
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
  rw [StepBlocks.preShiftBlock_act hscratch,
    hresultPosition, hresultWork]

theorem preShiftBlock_act_reachable_phaseOne
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth))
        (encoded n lengthWidth shiftWidth s) =
      phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s := by
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  exact preShiftBlock_act_phaseOne hphase1 hphase2 hstate.2.1
    h.stepDomain.valid.1.2.2.2.2.2.1

theorem phaseOnePreShiftCheckpoint_work1
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        StepLayout.work1Offset (workWidth n) =
      encodeWork1 n s % 2 ^ workWidth n := by
  rw [phaseOnePreShiftCheckpoint_read, read_work1]
  · right
    simp [StepLayout.work1Offset, StepLayout.work2Offset]
  · right
    simp [StepLayout.work1Offset, StepLayout.shiftOffset]
    omega

theorem phaseOnePreShiftCheckpoint_work2
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n { s with shift := s.shift - 1 } := by
  have hfit : encodeWork2 n { s with shift := s.shift - 1 } <
      2 ^ workWidth n := by
    simpa [encodeWork2] using rotatePositionsLeft_lt
      (workWidth n) (s.shift - 1)
      (encodeWork2Raw n { s with shift := s.shift - 1 })
  rw [phaseOnePreShiftCheckpoint, readField_writeField,
    Nat.mod_eq_of_lt hfit]

theorem phaseOnePreShiftCheckpoint_phase1
    (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.phase1Wire n lengthWidth shiftWidth) =
      boolValue s.phase1 := by
  rw [phaseOnePreShiftCheckpoint_bit_after_shift (Nat.le_refl _),
    read_phase1]

theorem phaseOnePreShiftCheckpoint_phase2
    (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.phase2Wire n lengthWidth shiftWidth) =
      boolValue s.phase2 := by
  rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.phase2Wire]),
    read_phase2]

theorem phaseOnePreShiftCheckpoint_sign
    (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.signWire n lengthWidth shiftWidth) =
      boolValue s.sign := by
  rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.signWire]),
    read_sign]

theorem phaseOnePreShiftCheckpoint_lenT
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
  rw [phaseOnePreShiftCheckpoint_read, read_lenT]
  · left
    simp [StepLayout.work2Offset, StepLayout.lenTOffset]
    omega
  · right
    simp [StepLayout.lenTOffset, StepLayout.shiftOffset]
    omega

theorem phaseOnePreShiftCheckpoint_lenQ
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenQ := by
  rw [phaseOnePreShiftCheckpoint_read, read_lenQ]
  · left
    simp [StepLayout.work2Offset, StepLayout.lenQOffset]
    omega
  · right
    simp [StepLayout.lenQOffset, StepLayout.shiftOffset]
    omega

theorem phaseOnePreShiftCheckpoint_shift
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hwidths : lengthWidth ≤ shiftWidth)
    (hfit : s.shift - 1 < 2 ^ lengthWidth) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth (s.shift - 1) := by
  rw [phaseOnePreShiftCheckpoint,
    readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.shiftOffset]
      omega)),
    readField_writeField_narrow hwidths,
    encodeLength_mod_of_le hwidths hfit]

theorem phaseOnePreShiftCheckpoint_lenRPrime
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
  rw [phaseOnePreShiftCheckpoint_read, read_lenRPrime]
  · left
    simp [StepLayout.work2Offset, StepLayout.lenRPrimeOffset]
    omega
  · right
    simp [StepLayout.lenRPrimeOffset, StepLayout.shiftOffset]
    omega

theorem phaseOnePreShiftCheckpoint_aux
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.auxOffset n lengthWidth shiftWidth)
        (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
  rw [phaseOnePreShiftCheckpoint_read_after_shift (by
      simp [StepLayout.auxOffset]),
    read_aux]

theorem phaseOnePreShiftCheckpoint_controlClean
    (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.ControlClean n lengthWidth shiftWidth
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) := by
  have h := controlClean n lengthWidth shiftWidth s
  constructor
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.controlWire])]
    exact h.control
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.temporary
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.plusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.plus
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.minusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.minus

theorem phaseOnePreShiftCheckpoint_remainderScratchClean
    (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) := by
  have h := encodedRemainderScratchClean n lengthWidth shiftWidth s
  constructor
  · rw [phaseOnePreShiftCheckpoint_read_after_shift (by
      simp [StepLayout.leftOffset, StepLayout.auxOffset])]
    exact h.left
  · rw [phaseOnePreShiftCheckpoint_read_after_shift (by
      simp [StepLayout.rightOffset, StepLayout.auxOffset]
      omega)]
    exact h.right
  · exact (phaseOnePreShiftCheckpoint_controlClean
      n lengthWidth shiftWidth s).control
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.carry
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    exact h.accumulator
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    exact h.leftFlag
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    exact h.rightFlag
  · rw [phaseOnePreShiftCheckpoint_read_after_shift (by
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    exact h.pool
  · rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact h.cellScratch

theorem phaseOnePreShiftCheckpoint_zeroRPrime
    (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
  rw [phaseOnePreShiftCheckpoint_bit_after_shift (by
      simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
  apply read_aux_bit
  · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
    omega
  · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth,
      StepLayout.auxOffset, StepLayout.selectorWidth]
    omega

theorem rPrimeZeroSelectorGates_act_phaseOneCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth)
        (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) =
      phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s := by
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hscratch := phaseOnePreShiftCheckpoint_remainderScratchClean
    n lengthWidth shiftWidth s
  have hlen : readField
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth % 2 ^ lengthWidth := by
    have hlive := read_lenRPrime_live h.stepDomain.valid.1 hstate.1
    rw [read_lenRPrime] at hlive
    rw [phaseOnePreShiftCheckpoint_lenRPrime]
    exact hlive
  rw [StepPlaced.rPrimeZeroSelectorGates_act hscratch.pool, if_neg hlen]
  exact write_of_bitValue (by
    simp [phaseOnePreShiftCheckpoint_zeroRPrime])

theorem guardedRemainderSubControl_act_phaseOneCheckpoint
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hphase1 : s.phase1 = false) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
        (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) =
      writeField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  have hzero := phaseOnePreShiftCheckpoint_zeroRPrime n lengthWidth shiftWidth s
  have hclean := phaseOnePreShiftCheckpoint_controlClean
    n lengthWidth shiftWidth s
  have hp1 : bitValue (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    rw [phaseOnePreShiftCheckpoint_phase1, hphase1]
    rfl
  rw [StepBlocks.guardedRemainderSubControl_act_live hzero,
    StepBlocks.remainderSubControl_act]
  simp [StepControl.negativeOut, hclean.control, hp1]

theorem phaseOne_remainderLeftEndpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    (encodeLength lengthWidth s.lenT +
        encodeLength lengthWidth s.lenQ + 3) % 2 ^ lengthWidth =
      s.lenT + 1 + s.lenQ := by
  have htOrder := ReachableStepDomain.phaseOne_tPrime_lt_t
    h hphase1 hphase2
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos (by omega)
  have hlenTFit : s.lenT < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.1
  have hlenQFit : s.lenQ < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.2.1
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hsum : s.lenT + 1 + s.lenQ < 2 ^ lengthWidth := by omega
  have hencodeT : encodeLength lengthWidth s.lenT = s.lenT - 1 := by
    simp [encodeLength, Nat.ne_of_gt hlenTPos,
      Nat.mod_eq_of_lt (show s.lenT - 1 < 2 ^ lengthWidth by omega)]
  by_cases hlenQZero : s.lenQ = 0
  · have hencodeQ : encodeLength lengthWidth s.lenQ =
        2 ^ lengthWidth - 1 := by
      simp [encodeLength, encodedZero, hlenQZero]
    rw [hencodeT, hencodeQ, hlenQZero]
    have heq : s.lenT - 1 + (2 ^ lengthWidth - 1) + 3 =
        s.lenT + 1 + 2 ^ lengthWidth := by
      have hpow := Nat.two_pow_pos lengthWidth
      omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega
  · have hlenQPos : 0 < s.lenQ := Nat.pos_of_ne_zero hlenQZero
    have hencodeQ : encodeLength lengthWidth s.lenQ = s.lenQ - 1 := by
      simp [encodeLength, hlenQZero,
        Nat.mod_eq_of_lt (show s.lenQ - 1 < 2 ^ lengthWidth by omega)]
    rw [hencodeT, hencodeQ]
    have heq : s.lenT - 1 + (s.lenQ - 1) + 3 =
        s.lenT + 1 + s.lenQ := by omega
    rw [heq, Nat.mod_eq_of_lt hsum]

theorem phaseOne_remainderRightEndpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    (n + 1 +
        (2 ^ lengthWidth - encodeLength lengthWidth (s.shift - 1))) %
        2 ^ lengthWidth =
      workWidth n - s.shift := by
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hshiftPos : 0 < s.shift := hstate.2.1
  have hshiftWork : s.shift < workWidth n := hstate.2.2
  have hright : workWidth n - s.shift < 2 ^ lengthWidth := by omega
  by_cases hshiftOne : s.shift = 1
  · have hencode : encodeLength lengthWidth (s.shift - 1) =
        2 ^ lengthWidth - 1 := by
      simp [encodeLength, encodedZero, hshiftOne]
    rw [hencode]
    have heq : n + 1 + (2 ^ lengthWidth - (2 ^ lengthWidth - 1)) =
        n + 2 := by
      have hpow := Nat.two_pow_pos lengthWidth
      omega
    have hvalue : n + 2 < 2 ^ lengthWidth := by
      simp [workWidth] at hwork
      omega
    rw [heq, Nat.mod_eq_of_lt hvalue]
    simp [workWidth, hshiftOne]
  · have hpredPos : 0 < s.shift - 1 := by omega
    have hencode : encodeLength lengthWidth (s.shift - 1) =
        s.shift - 2 := by
      simp [encodeLength, Nat.ne_of_gt hpredPos,
        Nat.mod_eq_of_lt
          (show s.shift - 1 - 1 < 2 ^ lengthWidth by omega)]
      omega
    rw [hencode]
    have heq : n + 1 + (2 ^ lengthWidth - (s.shift - 2)) =
        2 ^ lengthWidth + (workWidth n - s.shift) := by
      simp [workWidth] at hshiftWork ⊢
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hright]

theorem phaseOne_remainderPrepare_stable
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    Interval.Stable (s.lenT + 1 + s.lenQ) (workWidth n - s.shift)
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
  let checkpoint := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  have hscratch := phaseOnePreShiftCheckpoint_remainderScratchClean
    n lengthWidth shiftWidth s
  have hshiftFit : s.shift - 1 < 2 ^ lengthWidth := by
    have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
    omega
  have hframe := StepBlocks.remainderPrepare_frame_of_controlled_clean
    hlength hwidths hscratch
  dsimp only at hframe
  have hstable := hframe.stable
  rw [phaseOnePreShiftCheckpoint_lenT,
    phaseOnePreShiftCheckpoint_lenQ,
    phaseOnePreShiftCheckpoint_shift hwidths hshiftFit,
    phaseOne_remainderLeftEndpoint h hwork hphase1 hphase2,
    phaseOne_remainderRightEndpoint h hwork hphase1 hphase2] at hstable
  rw [guardedRemainderSubControl_act_phaseOneCheckpoint hphase1]
  simpa [checkpoint] using ⟨hstable, hframe.accumulator, hframe.carry⟩

theorem phaseOne_remainderOperands
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    readField input (Interval.sourceOffset + left) width =
        readField (encodeWork2 n { s with shift := s.shift - 1 })
          left width ∧
      reverseBits width
          (readField input (Interval.sourceOffset + left) width) =
        s.rPrime ∧
      readField input (Interval.targetOffset (workWidth n) + left) width =
        readField (encodeWork1 n s) left width ∧
      reverseBits width
          (readField input
            (Interval.targetOffset (workWidth n) + left) width) =
        s.r >>> (s.shift - 1) ∧
      readField input (Interval.targetOffset (workWidth n)) (workWidth n) =
        encodeWork1 n s % 2 ^ workWidth n ∧
      bitValue input (Interval.signWire (workWidth n) lengthWidth) = 0 := by
  dsimp only
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hlenRPrimePos : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hlenRPrimeFit : s.lenRPrime < 2 ^ lengthWidth :=
    h.stepDomain.valid.1.2.2.2.2.1
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp at hlenRPrimeFit
    omega
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have htPrimeLt := ReachableStepDomain.phaseOne_tPrime_lt_t
    h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, htFit, _hqShift,
      _hlenQValue, hrFit, _htPrimeFit, hrPrimeFit⟩
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hsign : s.sign = false := hready.1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  have hbound : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    omega
  let checkpoint := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  have hscratch := phaseOnePreShiftCheckpoint_remainderScratchClean
    n lengthWidth shiftWidth s
  have hframe := StepBlocks.remainderPrepare_frame_of_controlled_clean
    hlength hwidths hscratch
  dsimp only at hframe
  let prepared := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
    (writeField checkpoint
      (StepLayout.controlWire n lengthWidth shiftWidth) 1 1)
  have hpreparedWork1 : readField prepared StepLayout.work1Offset
      (workWidth n) = encodeWork1 n s % 2 ^ workWidth n := by
    calc
      readField prepared StepLayout.work1Offset (workWidth n) =
          readField checkpoint StepLayout.work1Offset (workWidth n) := by
            simpa [prepared, checkpoint] using hframe.work1
      _ = encodeWork1 n s % 2 ^ workWidth n := by
            simpa [checkpoint] using phaseOnePreShiftCheckpoint_work1
              n lengthWidth shiftWidth s
  have hpreparedWork2 : readField prepared (StepLayout.work2Offset n)
      (workWidth n) =
        encodeWork2 n { s with shift := s.shift - 1 } := by
    calc
      readField prepared (StepLayout.work2Offset n) (workWidth n) =
          readField checkpoint (StepLayout.work2Offset n) (workWidth n) := by
            simpa [prepared, checkpoint] using hframe.work2
      _ = encodeWork2 n { s with shift := s.shift - 1 } := by
            simpa [checkpoint] using phaseOnePreShiftCheckpoint_work2
              n lengthWidth shiftWidth s
  have hpreparedSign : bitValue prepared
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    calc
      bitValue prepared (StepLayout.signWire n lengthWidth shiftWidth) =
          bitValue checkpoint
            (StepLayout.signWire n lengthWidth shiftWidth) := by
              simpa [prepared, checkpoint] using hframe.sign
      _ = boolValue s.sign := by
            simpa [checkpoint] using phaseOnePreShiftCheckpoint_sign
              n lengthWidth shiftWidth s
      _ = 0 := by simp [hsign, boolValue]
  let input := StepPlaced.remainderIntervalInput
    n lengthWidth shiftWidth prepared
  have hsourceSlice :
      readField input (Interval.sourceOffset + left) width =
        readField (encodeWork2 n { s with shift := s.shift - 1 })
          left width := by
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
      _ = readField (encodeWork2 n { s with shift := s.shift - 1 })
          left width := by rw [hpreparedWork2]
  have htPrimeBound : s.tPrime < 2 ^ (left + (s.shift - 1)) := by
    have htPower : s.tPrime < 2 ^ s.lenT := htPrimeLt.trans htFit
    exact htPower.trans_le (Nat.pow_le_pow_right (by omega) (by
      dsimp [left]
      omega))
  have hrPrimeCover : s.lenRPrime ≤ width := by
    dsimp [left, width, right]
    omega
  have hsourceTop : left + (s.shift - 1) + width = workWidth n := by
    dsimp [left, width, right]
    omega
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) =
      s.rPrime := by
    rw [hsourceSlice]
    simpa using reverseBits_readField_encodeWork2_top
      (n := n) (s := { s with shift := s.shift - 1 })
      (off := left) (len := width) htPrimeBound hrPrimeFit hrPrimeCover
      hsourceTop
  have htargetSlice :
      readField input (Interval.targetOffset (workWidth n) + left) width =
        readField (encodeWork1 n s) left width := by
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
      _ = readField (encodeWork1 n s % 2 ^ workWidth n) left width := by
            rw [hpreparedWork1]
      _ = readField (encodeWork1 n s) left width := by
            apply Nat.eq_of_testBit_eq
            intro b
            rw [testBit_readField, testBit_readField]
            by_cases hb : b < width
            · simp [hb, Nat.testBit_mod_two_pow, show left + b < workWidth n by
                omega]
            · simp [hb]
  have htargetValue : reverseBits width
      (readField input (Interval.targetOffset (workWidth n) + left) width) =
      s.r >>> (s.shift - 1) := by
    rw [htargetSlice]
    simpa [left, width, right] using
      reverseBits_readField_encodeWork1_remainder
        (n := n) (s := s) hstate.2.1 (by omega) htFit hrFit
  have htarget : readField input
      (Interval.targetOffset (workWidth n)) (workWidth n) =
      encodeWork1 n s % 2 ^ workWidth n := by
    calc
      readField input (Interval.targetOffset (workWidth n)) (workWidth n) =
          readField prepared StepLayout.work1Offset (workWidth n) := by
            simpa [input] using StepPlaced.remainderIntervalInput_target
              n lengthWidth shiftWidth prepared
      _ = encodeWork1 n s % 2 ^ workWidth n := hpreparedWork1
  have hsignValue : bitValue input
      (Interval.signWire (workWidth n) lengthWidth) = 0 := by
    exact (by simpa [input] using
      (StepPlaced.remainderIntervalInput_sign
        n lengthWidth shiftWidth prepared).trans hpreparedSign)
  rw [guardedRemainderSubControl_act_phaseOneCheckpoint hphase1]
  simpa [left, right, width, checkpoint, prepared, input] using
    ⟨hsourceSlice, hsourceValue, htargetSlice, htargetValue, htarget,
      hsignValue⟩

theorem phaseOne_remainderOperandBounds
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    s.rPrime < 2 ^ width ∧ s.r >>> k < 2 ^ width := by
  dsimp only
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hrFit, _, hrPrimeFit⟩
  have hrPrimeCover : s.lenRPrime ≤
      workWidth n - s.shift - (s.lenT + 1 + s.lenQ) + 1 := by
    omega
  constructor
  · exact hrPrimeFit.trans_le
      (Nat.pow_le_pow_right (by omega) hrPrimeCover)
  · rw [Nat.shiftRight_eq_div_pow,
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (s.shift - 1))]
    have hpow :
        2 ^ (workWidth n - s.shift - (s.lenT + 1 + s.lenQ) + 1) *
            2 ^ (s.shift - 1) =
          2 ^ (workWidth n - (s.lenT + 1 + s.lenQ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    exact hrFit

theorem phaseOne_remainderPreparedSubValues
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth)
      (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    StepPlaced.intervalSubTargetValue left right (workWidth n) lengthWidth
        input =
      writeField (encodeWork1 n s % 2 ^ workWidth n) left width
        (reverseBits width
          (Adder.difference width s.rPrime (s.r >>> (s.shift - 1)))) ∧
      StepPlaced.intervalSubSignValue left right (workWidth n) lengthWidth
          input =
        Adder.borrow s.rPrime (s.r >>> (s.shift - 1)) := by
  dsimp only
  have hoperands := phaseOne_remainderOperands
    h hwidths hphase1 hphase2
  dsimp only at hoperands
  rcases hoperands with ⟨_, hsource, _, htarget, hfull, hsign⟩
  constructor
  · simp only [StepPlaced.intervalSubTargetValue]
    rw [hfull, hsource, htarget]
  · simp only [StepPlaced.intervalSubSignValue]
    rw [hsign, hsource, htarget]
    by_cases hborrow : s.r >>> (s.shift - 1) < s.rPrime
    · simp [Adder.borrow, hborrow]
    · simp [Adder.borrow, hborrow]

theorem phaseOne_remainderDecodedSubValues
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    Adder.difference width s.rPrime targetWord = subWord ∧
      Adder.borrow s.rPrime targetWord = subSign := by
  dsimp only
  have hbounds := phaseOne_remainderOperandBounds h hphase1 hphase2
  dsimp only at hbounds
  have htake : shifted s.rPrime (s.shift - 1) ≤ s.r ↔
      s.rPrime ≤ s.r >>> (s.shift - 1) :=
    shifted_le_iff_le_shiftRight s.rPrime s.r (s.shift - 1)
  constructor
  · rw [Adder.difference_eq_if hbounds.1 hbounds.2]
    by_cases htakeValue : shifted s.rPrime (s.shift - 1) ≤ s.r
    · rw [if_pos (htake.mp htakeValue), if_pos htakeValue]
    · have hnotLe : ¬ s.rPrime ≤ s.r >>> (s.shift - 1) := by
        exact fun hle => htakeValue (htake.mpr hle)
      rw [if_neg hnotLe, if_neg htakeValue]
  · simp only [Adder.borrow]
    by_cases htakeValue : shifted s.rPrime (s.shift - 1) ≤ s.r
    · have hle := htake.mp htakeValue
      have hnotLt : ¬ s.r >>> (s.shift - 1) < s.rPrime :=
        Nat.not_lt_of_ge hle
      rw [if_neg hnotLt, if_pos htakeValue]
    · have hnotLe : ¬ s.rPrime ≤ s.r >>> (s.shift - 1) := by
        exact fun hle => htakeValue (htake.mpr hle)
      have hlt : s.r >>> (s.shift - 1) < s.rPrime :=
        Nat.lt_of_not_ge hnotLe
      rw [if_pos hlt, if_neg htakeValue]

theorem guardedRemainderSubBlock_act_phaseOneCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hLR : s.lenT + 1 + s.lenQ ≤ workWidth n - s.shift := by
    omega
  have hR : workWidth n - s.shift < workWidth n := by
    omega
  have hfit : s.lenT + 1 + s.lenQ +
      (workWidth n - s.shift - (s.lenT + 1 + s.lenQ) + 1) ≤
        workWidth n := by
    omega
  have hstable := phaseOne_remainderPrepare_stable
    h hwork hwidths hphase1 hphase2
  dsimp only at hstable
  have hprepared := phaseOne_remainderPreparedSubValues
    h hwidths hphase1 hphase2
  dsimp only at hprepared
  have hdecoded := phaseOne_remainderDecodedSubValues h hphase1 hphase2
  dsimp only at hdecoded
  have hblock := StepBlocks.guardedRemainderSubBlock_act
    (I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
    (left := s.lenT + 1 + s.lenQ)
    (right := workWidth n - s.shift)
    hlength hwidths (Nat.le_of_lt hwork) hLR hR
    hstable.1 hstable.2.1 hstable.2.2
  dsimp only at hblock
  rw [hprepared.1, hprepared.2, hdecoded.1, hdecoded.2] at hblock
  rw [← phaseOnePreShiftCheckpoint_work1
    n lengthWidth shiftWidth s] at hblock
  rw [← writeField_subfield hfit] at hblock
  exact hblock

theorem guardedRemainderAddControl_act_phaseOnePostSub
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let postSign := if take then 1 else 0
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
    let B := writeField I (StepLayout.work1Offset + left) width
      (reverseBits width subWord)
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
    F = writeField B (StepLayout.signWire n lengthWidth shiftWidth) 1
        postSign ∧
      C = writeField
        (writeField
          (writeField F
            (StepLayout.temporaryWire n lengthWidth shiftWidth) 1 postSign)
          (StepLayout.plusWire n lengthWidth shiftWidth) 1 1)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 subSign := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let postSign := if take then 1 else 0
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
  let zeroRPrime := StepLayout.zeroRPrimeWire n lengthWidth shiftWidth
  change F = writeField B sign 1 postSign ∧
    C = writeField (writeField (writeField F temporary 1 postSign)
      plus 1 1) control 1 subSign
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hleftRight : left ≤ right := by
    dsimp [left, right]
    omega
  have hright : right < workWidth n := by
    dsimp [right]
    omega
  have hbound : left + width ≤ workWidth n := by
    dsimp [width]
    omega
  have hS : S = writeField B sign 1 subSign := by
    exact guardedRemainderSubBlock_act_phaseOneCheckpoint
      h hwork hwidths hphase1 hphase2
  have hBbit (q : Nat) (hq : workWidth n ≤ q) :
      bitValue B q = bitValue I q := by
    apply bitValue_write_out
    right
    dsimp [B, left]
    simp only [StepLayout.work1Offset]
    omega
  have hSbit (q : Nat) (hqs : q ≠ sign) (hq : workWidth n ≤ q) :
      bitValue S q = bitValue I q := by
    rw [hS, bitValue_write_ne hqs]
    exact hBbit q hq
  have hp1S : bitValue S p1 = 0 := by
    rw [hSbit p1 (by
      simp [p1, sign, StepLayout.signWire]) (by
      simp [p1, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simp [I, p1, phaseOnePreShiftCheckpoint_phase1, hphase1, boolValue]
  have hp2S : bitValue S p2 = 1 := by
    rw [hSbit p2 (by
      simp [p2, sign, StepLayout.phase2Wire, StepLayout.signWire]) (by
      simp [p2, StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simp [I, p2, phaseOnePreShiftCheckpoint_phase2, hphase2, boolValue]
  have hsignS : bitValue S sign = subSign := by
    rw [hS, bitValue_write_self]
    by_cases htake : take <;> simp [subSign, htake]
  have hF : F = writeField B sign 1 postSign := by
    change actGates (Step.remainderFlip n lengthWidth shiftWidth) S = _
    rw [StepBlocks.remainderFlip_act, Phase.negativeAndOut,
      hp1S, hp2S, hsignS, if_pos rfl, hS, writeField_writeField]
    by_cases htake : take <;> simp [subSign, postSign, htake]
  have hFbit (q : Nat) (hqs : q ≠ sign) (hq : workWidth n ≤ q) :
      bitValue F q = bitValue I q := by
    rw [hF, bitValue_write_ne hqs]
    exact hBbit q hq
  have hp1F : bitValue F p1 = 0 := by
    rw [hFbit p1 (by
      simp [p1, sign, StepLayout.signWire]) (by
      simp [p1, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simp [I, p1, phaseOnePreShiftCheckpoint_phase1, hphase1, boolValue]
  have hp2F : bitValue F p2 = 1 := by
    rw [hFbit p2 (by
      simp [p2, sign, StepLayout.phase2Wire, StepLayout.signWire]) (by
      simp [p2, StepLayout.phase2Wire, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simp [I, p2, phaseOnePreShiftCheckpoint_phase2, hphase2, boolValue]
  have hsignF : bitValue F sign = postSign := by
    rw [hF, bitValue_write_self]
    by_cases htake : take <;> simp [postSign, htake]
  have hcleanI := phaseOnePreShiftCheckpoint_controlClean
    n lengthWidth shiftWidth s
  have hcontrolF : bitValue F control = 0 := by
    rw [hFbit control (by
      simp [control, sign, StepLayout.controlWire, StepLayout.signWire]) (by
      simp [control, StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simpa [I, control] using hcleanI.control
  have htemporaryF : bitValue F temporary = 0 := by
    rw [hFbit temporary (by
      simp [temporary, sign, StepLayout.temporaryWire,
        StepLayout.signWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega) (by
      simp [temporary, StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simpa [I, temporary] using hcleanI.temporary
  have hplusF : bitValue F plus = 0 := by
    rw [hFbit plus (by
      simp [plus, sign, StepLayout.plusWire, StepLayout.signWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega) (by
      simp [plus, StepLayout.plusWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)]
    simpa [I, plus] using hcleanI.plus
  have hzeroRPrimeF : bitValue F zeroRPrime = 0 := by
    rw [hFbit zeroRPrime (by
      simp [zeroRPrime, sign, StepLayout.zeroRPrimeWire,
        StepLayout.signWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega) (by
      simp [zeroRPrime, StepLayout.zeroRPrimeWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    simpa [I, zeroRPrime] using
      phaseOnePreShiftCheckpoint_zeroRPrime n lengthWidth shiftWidth s
  let K := Phase.ccxOut p2 sign temporary F
  have hK : K = writeField F temporary 1 postSign := by
    simp only [K, Phase.ccxOut]
    rw [htemporaryF, hp2F, hsignF]
    by_cases htake : take <;> simp [postSign, htake]
  have hp1K : bitValue K p1 = 0 := by
    rw [hK, bitValue_write_ne (by
      simp [p1, temporary, StepLayout.temporaryWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]
    exact hp1F
  have hplusK : bitValue K plus = 0 := by
    rw [hK, bitValue_write_ne (by
      simp [plus, temporary, StepLayout.plusWire,
        StepLayout.temporaryWire])]
    exact hplusF
  let L := StepControl.negativeOut p1 plus K
  have hL : L = writeField K plus 1 1 := by
    simp [L, StepControl.negativeOut, hp1K, hplusK]
  have hcontrolL : bitValue L control = 0 := by
    rw [hL, bitValue_write_ne (by
      simp [control, plus, StepLayout.controlWire, StepLayout.plusWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega),
      hK, bitValue_write_ne (by
        simp [control, temporary, StepLayout.controlWire,
          StepLayout.temporaryWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
    exact hcontrolF
  have htemporaryL : bitValue L temporary = postSign := by
    rw [hL, bitValue_write_ne (by
      simp [temporary, plus, StepLayout.temporaryWire,
        StepLayout.plusWire]), hK, bitValue_write_self]
    by_cases htake : take <;> simp [postSign, htake]
  have hplusL : bitValue L plus = 1 := by
    rw [hL, bitValue_write_self]
  have hlast : Phase.negativeAndOut plus temporary control L =
      writeField L control 1 subSign := by
    simp only [Phase.negativeAndOut]
    rw [hcontrolL, htemporaryL, hplusL]
    by_cases htake : take <;> simp [postSign, subSign, htake]
  have hC : C = writeField
      (writeField (writeField F temporary 1 postSign) plus 1 1)
      control 1 subSign := by
    change actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F = _
    rw [StepBlocks.guardedRemainderAddControl_act_live hzeroRPrimeF,
      StepBlocks.remainderAddControl_act,
      StepBlocks.remainderAddControlOut]
    change Phase.negativeAndOut plus temporary control L = _
    rw [hlast, hL, hK]
  exact ⟨hF, hC⟩

private theorem phaseOne_remainderAddControl_scratchExceptControl
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let postSign := if take then 1 else 0
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hleftRight : left ≤ right := by
    dsimp [left, right]
    omega
  have hright : right < workWidth n := by
    dsimp [right]
    omega
  have hfit : left + width ≤ workWidth n := by
    dsimp [width]
    omega
  have hpost := guardedRemainderAddControl_act_phaseOnePostSub
    h hwork hwidths hphase1 hphase2
  have hF : F = writeField B sign 1 postSign := by
    exact hpost.1
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
  have hscratch := phaseOnePreShiftCheckpoint_remainderScratchClean
    n lengthWidth shiftWidth s
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
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

theorem phaseOne_remainderPreparedAdd_reject
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hreject : ¬ shifted s.rPrime (s.shift - 1) ≤ s.r) :
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
            encodeWork1 n s % 2 ^ workWidth n ∧
          bitValue input
              (Interval.signWire (workWidth n) lengthWidth) = 0 := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let targetWord := s.r >>> k
  let x := Adder.difference width s.rPrime targetWord
  let base := encodeWork1 n s % 2 ^ workWidth n
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
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
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  change Interval.Stable left right (workWidth n) lengthWidth input ∧
    bitValue input
        (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
      bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 ∧
        StepPlaced.intervalAddTargetValue left right (workWidth n)
            lengthWidth input = base ∧
        bitValue input (Interval.signWire (workWidth n) lengthWidth) = 0
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hleftRight : left ≤ right := by
    dsimp [left, right]
    omega
  have hright : right < workWidth n := by
    dsimp [right]
    omega
  have hfit : left + width ≤ workWidth n := by
    dsimp [width]
    omega
  have hbounds := phaseOne_remainderOperandBounds h hphase1 hphase2
  dsimp only at hbounds
  have hdecoded := phaseOne_remainderDecodedSubValues h hphase1 hphase2
  dsimp only at hdecoded
  have hxword : x = targetWord + (2 ^ width - s.rPrime) := by
    simpa [x, targetWord, width, k, hreject] using hdecoded.1
  have hpost := guardedRemainderAddControl_act_phaseOnePostSub
    h hwork hwidths hphase1 hphase2
  dsimp only at hpost
  simp only [if_neg hreject] at hpost
  rw [← hxword] at hpost
  have hF : F = writeField B sign 1 0 := by
    simpa [F, B, S, I, sign, x, targetWord, width, left, right, k]
      using hpost.1
  have hC : C = writeField
      (writeField (writeField F temporary 1 0) plus 1 1)
      control 1 1 := by
    simpa [C, F, S, I, control, temporary, plus, sign, x, targetWord,
      width, left, right, k] using hpost.2
  have hscratchC := phaseOne_remainderAddControl_scratchExceptControl
    h hwork hwidths hphase1 hphase2
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
        omega))),
      readField_writeField_of_disjoint (Or.inr (hhi.trans (by
        simp [temporary, sign, StepLayout.temporaryWire,
          StepLayout.signWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))), hF,
      readField_writeField_of_disjoint (Or.inr hhi)]
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp only [StepLayout.work1Offset]
      omega))]
  have hshiftFit : s.shift - 1 < 2 ^ lengthWidth := by omega
  have hlenTC : readField C (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [hCfield _ _ (by
      simp [StepLayout.lenTOffset, workWidth]) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.lenTOffset]
      omega)]
    exact phaseOnePreShiftCheckpoint_lenT n lengthWidth shiftWidth s
  have hlenQC : readField C
      (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenQ := by
    rw [hCfield _ _ (by
      simp [StepLayout.lenQOffset, workWidth]
      omega) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.lenQOffset]
      omega)]
    exact phaseOnePreShiftCheckpoint_lenQ n lengthWidth shiftWidth s
  have hshiftC : readField C
      (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth (s.shift - 1) := by
    rw [hCfield _ _ (by
      simp [StepLayout.shiftOffset]
      omega) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire]
      omega)]
    exact phaseOnePreShiftCheckpoint_shift hwidths hshiftFit
  have hstable := hframe.stable
  rw [hlenTC, hlenQC, hshiftC,
    phaseOne_remainderLeftEndpoint h hwork hphase1 hphase2,
    phaseOne_remainderRightEndpoint h hwork hphase1 hphase2] at hstable
  have hwork2C : readField C (StepLayout.work2Offset n) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
    exact hCfield _ _ (by simp [StepLayout.work2Offset]) (by
      simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.work2Offset]
      omega)
  have hwork2P : readField P (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n { s with shift := s.shift - 1 } := by
    rw [hframe.work2, hwork2C]
    exact phaseOnePreShiftCheckpoint_work2 n lengthWidth shiftWidth s
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
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [temporary, StepLayout.temporaryWire, StepLayout.work1Offset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hF,
      readField_writeField_of_disjoint (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.work1Offset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))]
  have hbase : readField I StepLayout.work1Offset (workWidth n) = base := by
    simpa [I, base] using
      phaseOnePreShiftCheckpoint_work1 n lengthWidth shiftWidth s
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
      readField (encodeWork2 n { s with shift := s.shift - 1 })
        left width := by
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
      _ = readField (encodeWork2 n { s with shift := s.shift - 1 })
          left width := by rw [hwork2P]
  have hoperands := phaseOne_remainderOperands
    h hwidths hphase1 hphase2
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
      readField (encodeWork1 n s) left width := by
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [base]
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
  have hsignC : bitValue C sign = 0 := by
    rw [hC,
      bitValue_write_ne (by
        simp [sign, control, StepLayout.signWire, StepLayout.controlWire]),
      bitValue_write_ne (by
        simp [sign, plus, StepLayout.signWire, StepLayout.plusWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega),
      bitValue_write_ne (by
        simp [sign, temporary, StepLayout.signWire,
          StepLayout.temporaryWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega), hF, bitValue_write_self]
  have hsignInput : bitValue input
      (Interval.signWire (workWidth n) lengthWidth) = 0 := by
    calc
      bitValue input (Interval.signWire (workWidth n) lengthWidth) =
          bitValue P sign := by
            simpa [input, sign] using StepPlaced.remainderIntervalInput_sign
              n lengthWidth shiftWidth P
      _ = bitValue C sign := by simpa [sign] using hframe.sign
      _ = 0 := hsignC
  exact ⟨hstable, hframe.accumulator, hframe.carry,
    htargetValueRestored, hsignInput⟩

theorem phaseOne_remainderPreparedAdd_take
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (htake : shifted s.rPrime (s.shift - 1) ≤ s.r) :
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput
        n lengthWidth shiftWidth P) := by
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let C := actGates
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth) F
  let P := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  change StepPlaced.IntervalInactive (workWidth n) lengthWidth
    (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth P)
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hpost := guardedRemainderAddControl_act_phaseOnePostSub
    h hwork hwidths hphase1 hphase2
  dsimp only at hpost
  simp only [if_pos htake] at hpost
  have hC : C = writeField
      (writeField (writeField F temporary 1 1) plus 1 1)
      control 1 0 := by
    simpa [C, F, S, I, control, temporary, plus] using hpost.2
  have hcontrolC : bitValue C control = 0 := by
    rw [hC, bitValue_write_self]
  have hscratchC := phaseOne_remainderAddControl_scratchExceptControl
    h hwork hwidths hphase1 hphase2
  dsimp only at hscratchC
  rcases hscratchC with
    ⟨hleftC, hrightC, hcarryC, haccumulatorC,
      hleftFlagC, hrightFlagC, hpoolC, hcellScratchC⟩
  exact StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths hleftC hrightC hcontrolC hcarryC
      haccumulatorC hleftFlagC hrightFlagC hpoolC hcellScratchC

theorem guardedRemainderAddBlock_act_phaseOnePostSub
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let take := shifted s.rPrime (s.shift - 1) ≤ s.r
    let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
    let S := actGates
      (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
    let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) F =
      if take then F else I := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let base := encodeWork1 n s % 2 ^ workWidth n
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  let B := writeField I (StepLayout.work1Offset + left) width
    (reverseBits width subWord)
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  change actGates
    (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) F =
      if take then F else I
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hR : right < workWidth n := by
    dsimp [right]
    omega
  have hfit : left + width ≤ workWidth n := by
    dsimp [width]
    omega
  by_cases htake : take
  · rw [if_pos htake]
    have hp := phaseOne_remainderPreparedAdd_take
      h hwork hwidths hphase1 hphase2 htake
    dsimp only at hp
    exact StepBlocks.guardedRemainderAddBlock_identity
      hlength hwidths hp
  · rw [if_neg htake]
    have hp := phaseOne_remainderPreparedAdd_reject
      h hwork hwidths hphase1 hphase2 htake
    dsimp only at hp
    have hblock := StepBlocks.guardedRemainderAddBlock_act
      (I := F) (left := left) (right := right)
      hlength hwidths (Nat.le_of_lt hwork) hLR hR
      hp.1 hp.2.1 hp.2.2.1
    dsimp only at hblock
    rw [hp.2.2.2.1] at hblock
    have hpost := guardedRemainderAddControl_act_phaseOnePostSub
      h hwork hwidths hphase1 hphase2
    dsimp only at hpost
    have hF : F = writeField B sign 1 0 := by
      simpa [F, B, S, I, sign, subWord, take, targetWord,
        width, left, right, k, htake] using hpost.1
    have hbase : readField I StepLayout.work1Offset (workWidth n) = base := by
      simpa [I, base] using
        phaseOnePreShiftCheckpoint_work1 n lengthWidth shiftWidth s
    have hready := h.stepDomain.valid.2
    simp [PhaseReady, hphase1, hphase2] at hready
    have hsignI : bitValue I sign = 0 := by
      simpa [I, sign, hready.1, boolValue] using
        phaseOnePreShiftCheckpoint_sign n lengthWidth shiftWidth s
    have hrestore :
        writeField F StepLayout.work1Offset (workWidth n) base = I := by
      rw [hF, writeField_comm (by
        right
        simp [sign, StepLayout.work1Offset, StepLayout.signWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
      simp only [B]
      rw [writeField_subfield hfit, writeField_writeField,
        ← hbase, writeField_read,
        ← hsignI, ← readField_one, writeField_read]
    exact hblock.trans hrestore

def phaseOneRemainderCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let resultWord := if take then targetWord - s.rPrime else targetWord
  let takeBit := if take then 1 else 0
  writeField
    (writeField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.work1Offset + left) width
      (reverseBits width resultWord))
    (StepLayout.signWire n lengthWidth shiftWidth) 1 takeBit

theorem phaseOneRemainderCheckpoint_work1
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
    readField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
        StepLayout.work1Offset (workWidth n) =
      writeField (encodeWork1 n s % 2 ^ workWidth n)
        left width (reverseBits width resultWord) := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hfit : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    omega
  have hupdatedBound : writeField
      (readField I StepLayout.work1Offset (workWidth n))
      left width (reverseBits width resultWord) < 2 ^ workWidth n :=
    writeField_lt hfit
      (readField_lt I StepLayout.work1Offset (workWidth n))
  change readField
      (writeField
        (writeField I (StepLayout.work1Offset + left) width
          (reverseBits width resultWord))
        sign 1 (if take then 1 else 0))
      StepLayout.work1Offset (workWidth n) = _
  rw [readField_writeField_of_disjoint (Or.inr (by
      simp [sign, StepLayout.signWire, StepLayout.work1Offset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)),
    writeField_subfield hfit, readField_writeField,
    Nat.mod_eq_of_lt hupdatedBound,
    phaseOnePreShiftCheckpoint_work1]

theorem guardedRemainderBlocks_act_phaseOneCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (Step.guardedRemainderBlocks n lengthWidth shiftWidth)
        (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s) =
      phaseOneRemainderCheckpoint n lengthWidth shiftWidth s := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let resultWord := if take then targetWord - s.rPrime else targetWord
  let takeBit := if take then 1 else 0
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  let off := StepLayout.work1Offset + left
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let selector :=
    StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth
  let body := Step.guardedRemainderSubBlock n lengthWidth shiftWidth ++
    Step.remainderFlip n lengthWidth shiftWidth ++
    Step.guardedRemainderAddBlock n lengthWidth shiftWidth
  let S := actGates
    (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I
  let F := actGates (Step.remainderFlip n lengthWidth shiftWidth) S
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hfit : left + width ≤ workWidth n := by
    dsimp [width, right]
    omega
  have hrem := guardedRemainderAddBlock_act_phaseOnePostSub
    h hwork hwidths hphase1 hphase2
  dsimp only at hrem
  have hpost := guardedRemainderAddControl_act_phaseOnePostSub
    h hwork hwidths hphase1 hphase2
  dsimp only at hpost
  let base := encodeWork1 n s % 2 ^ workWidth n
  have hbase : readField I StepLayout.work1Offset (workWidth n) = base := by
    simpa [I, base] using
      phaseOnePreShiftCheckpoint_work1 n lengthWidth shiftWidth s
  have hISlice : readField I off width = readField base left width := by
    calc
      readField I off width =
          readField
            (readField I StepLayout.work1Offset (workWidth n)) left width := by
            symm
            simpa [off] using readField_readField (i := I)
              (D := StepLayout.work1Offset) (W := workWidth n)
              (off := left) (len := width) hfit
      _ = readField base left width := by rw [hbase]
  have hbaseSlice : readField base left width =
      readField (encodeWork1 n s) left width := by
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [base]
    rw [testBit_readField, testBit_readField]
    by_cases hb : b < width
    · simp [hb, Nat.testBit_mod_two_pow,
        show left + b < workWidth n by omega]
    · simp [hb]
  have hoperands := phaseOne_remainderOperands
    h hwidths hphase1 hphase2
  dsimp only at hoperands
  rcases hoperands with
    ⟨_, _, htargetSlice, htargetValue, _, _⟩
  rw [htargetSlice] at htargetValue
  change reverseBits width
      (readField (encodeWork1 n s) left width) = targetWord at htargetValue
  have htargetPhysical :
      readField I off width = reverseBits width targetWord := by
    rw [hISlice, hbaseSlice, ← htargetValue]
    exact (reverseBits_involutive
      (readField_lt (encodeWork1 n s) left width)).symm
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hsignI : bitValue I sign = 0 := by
    simpa [I, sign, hready.1, boolValue] using
      phaseOnePreShiftCheckpoint_sign n lengthWidth shiftWidth s
  have hcanonical :
      (if take then F else I) =
        writeField
          (writeField I off width (reverseBits width resultWord))
          sign 1 takeBit := by
    by_cases htake : take
    · rw [if_pos htake]
      have hF : F = writeField
          (writeField I off width
            (reverseBits width (targetWord - s.rPrime)))
          sign 1 1 := by
        simpa [F, S, I, off, sign, take, targetWord, width,
          left, right, k, htake] using hpost.1
      simpa [resultWord, takeBit, htake] using hF
    · rw [if_neg htake]
      simp only [resultWord, takeBit, if_neg htake]
      symm
      rw [← htargetPhysical, writeField_read,
        ← hsignI, ← readField_one, writeField_read]
  have hbody : actGates body I =
      writeField
        (writeField I off width (reverseBits width resultWord))
        sign 1 takeBit := by
    simpa only [body, actGates_append] using hrem.trans hcanonical
  have hselect : actGates selector I = I := by
    simpa [selector, I] using
      rPrimeZeroSelectorGates_act_phaseOneCheckpoint h hphase1 hphase2
  have hbodySelected : actGates body (actGates selector I) =
      writeField
        (writeField (actGates selector I) off width
          (reverseBits width resultWord))
        sign 1 takeBit := by
    rw [hselect]
    exact hbody
  have havoidOff : ∀ g ∈ selector, ∀ q ∈ g.wires,
      q < off ∨ off + width ≤ q := by
    intro g hg q hq
    rcases StepBlocks.rPrimeZeroSelectorGates_avoids_work1
        n lengthWidth shiftWidth g hg q hq with hlo | hhi
    · exact Or.inl (by dsimp [off]; omega)
    · exact Or.inr (by dsimp [off]; omega)
  have hout := StepBlocks.around_write_two
    (compute := selector) (body := body) (I := I)
    (StepLayout.rPrimeZeroSelectorGates_wellFormed
      n lengthWidth shiftWidth)
    havoidOff
    (StepBlocks.rPrimeZeroSelectorGates_avoids_sign
      n lengthWidth shiftWidth)
    hbodySelected
  simpa [Step.guardedRemainderBlocks, selector, body, I, off, sign,
    phaseOneRemainderCheckpoint, k, left, right, width, take,
    targetWord, resultWord, takeBit] using hout

private structure PhaseOneRemainderCheckpointFrame
    (n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  controlClean : StepBlocks.ControlClean n lengthWidth shiftWidth
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
  scratch : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
  aux : readField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.auxOffset n lengthWidth shiftWidth)
    (StepLayout.auxWidth lengthWidth shiftWidth) = 0
  lenT : readField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.lenTOffset n) lengthWidth = encodeLength lengthWidth s.lenT
  lenQ : readField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenQ
  phase1 : bitValue
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
  phase2 : bitValue
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1
  sign : bitValue
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.signWire n lengthWidth shiftWidth) =
      if shifted s.rPrime (s.shift - 1) ≤ s.r then 1 else 0

private theorem phaseOneRemainderCheckpoint_frame
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    PhaseOneRemainderCheckpointFrame n lengthWidth shiftWidth s := by
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let I := phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hfit : left + width ≤ workWidth n := by
    dsimp [width, right]
    omega
  have hread (fieldOff fieldWidth : Nat)
      (hlo : workWidth n ≤ fieldOff)
      (hsign : sign + 1 ≤ fieldOff ∨ fieldOff + fieldWidth ≤ sign) :
      readField R fieldOff fieldWidth = readField I fieldOff fieldWidth := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp only [StepLayout.work1Offset]
        omega))]
  have hbit (q : Nat) (hlo : workWidth n ≤ q)
      (hsign : sign + 1 ≤ q ∨ q + 1 ≤ sign) :
      bitValue R q = bitValue I q := by
    simpa [readField_one] using hread q 1 hlo hsign
  have hcleanI := phaseOnePreShiftCheckpoint_controlClean
    n lengthWidth shiftWidth s
  have hcleanR : StepBlocks.ControlClean n lengthWidth shiftWidth R := by
    constructor
    · exact (hbit _ (by
          simp [StepLayout.controlWire, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.controlWire]))).trans
        hcleanI.control
    · exact (hbit _ (by
          simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hcleanI.temporary
    · exact (hbit _ (by
          simp [StepLayout.plusWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.plusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hcleanI.plus
    · exact (hbit _ (by
          simp [StepLayout.minusWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.minusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hcleanI.minus
  have hscratchI := phaseOnePreShiftCheckpoint_remainderScratchClean
    n lengthWidth shiftWidth s
  have hscratchR :
      StepBlocks.RemainderScratchClean n lengthWidth shiftWidth R := by
    constructor
    · exact (hread _ _ (by
          simp [StepLayout.leftOffset, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.leftOffset,
            StepLayout.auxOffset]))).trans
        hscratchI.left
    · exact (hread _ _ (by
          simp [StepLayout.rightOffset, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.rightOffset,
            StepLayout.auxOffset]
          omega))).trans
        hscratchI.right
    · exact hcleanR.control
    · exact (hbit _ (by
          simp [StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega))).trans
        hscratchI.carry
    · exact (hbit _ (by
          simp [StepLayout.accumulatorWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.accumulatorWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hscratchI.accumulator
    · exact (hbit _ (by
          simp [StepLayout.leftFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.leftFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hscratchI.leftFlag
    · exact (hbit _ (by
          simp [StepLayout.rightFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.rightFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hscratchI.rightFlag
    · exact (hread _ _ (by
          simp [StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega))).trans
        hscratchI.pool
    · exact (hbit _ (by
          simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega) (Or.inl (by
          simp [sign, StepLayout.signWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega))).trans
        hscratchI.cellScratch
  refine ⟨hcleanR, hscratchR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hread _ _ (by
        simp [StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega) (Or.inl (by
        simp [sign, StepLayout.signWire, StepLayout.auxOffset]))).trans
      (phaseOnePreShiftCheckpoint_aux n lengthWidth shiftWidth s)
  · exact (hread _ _ (by
        simp [StepLayout.lenTOffset, workWidth]) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.lenTOffset]
        omega))).trans
      (phaseOnePreShiftCheckpoint_lenT n lengthWidth shiftWidth s)
  · exact (hread _ _ (by
        simp [StepLayout.lenQOffset, workWidth]
        omega) (Or.inr (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.lenQOffset]
        omega))).trans
      (phaseOnePreShiftCheckpoint_lenQ n lengthWidth shiftWidth s)
  · calc
      bitValue R (StepLayout.phase1Wire n lengthWidth shiftWidth) =
          bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) :=
        hbit _ (by
          simp [StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega) (Or.inr (by
          simp [sign, StepLayout.signWire]))
      _ = 0 := by
        simp [I, phaseOnePreShiftCheckpoint_phase1, hphase1, boolValue]
  · calc
      bitValue R (StepLayout.phase2Wire n lengthWidth shiftWidth) =
          bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) :=
        hbit _ (by
          simp [StepLayout.phase2Wire, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega) (Or.inr (by
          simp [sign, StepLayout.signWire, StepLayout.phase2Wire]))
      _ = 1 := by
        simp [I, phaseOnePreShiftCheckpoint_phase2, hphase2, boolValue]
  · simp only [phaseOneRemainderCheckpoint, bitValue_write_self]
    split <;> simp

theorem quotientIncrementControl_act_phaseOneRemainderCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (Step.quotientIncrementControl n lengthWidth shiftWidth)
        (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s) =
      writeField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  have hframe := phaseOneRemainderCheckpoint_frame
    h hphase1 hphase2
  rw [StepBlocks.quotientIncrementControl_act]
  simp [Phase.negativeAndOut, hframe.controlClean.control,
    hframe.phase1, hframe.phase2]

theorem quotientIncrementBlock_act_phaseOneRemainderCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (Step.quotientIncrementBlock n lengthWidth shiftWidth)
        (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s) =
      writeField (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth
        (encodeLength lengthWidth (s.lenQ + 1)) := by
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let C := actGates
    (Step.quotientIncrementControl n lengthWidth shiftWidth) R
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hframe := phaseOneRemainderCheckpoint_frame
    h hphase1 hphase2
  have hC : C = writeField R control 1 1 := by
    simpa [C, R, control] using
      quotientIncrementControl_act_phaseOneRemainderCheckpoint
        h hphase1 hphase2
  have hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth C) = 0 := by
    rw [StepPlaced.quotientInput_scratch, hC,
      readField_writeField_of_disjoint (Or.inl (by
        simp [control, StepLayout.controlWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))]
    exact hframe.scratch.pool
  have hvalue : StepPlaced.quotientIncrementValue
      n lengthWidth shiftWidth C =
        encodeLength lengthWidth (s.lenQ + 1) := by
    simp only [StepPlaced.quotientIncrementValue]
    rw [hC, bitValue_write_self,
      readField_writeField_of_disjoint (Or.inr (by
        simp [control, StepLayout.controlWire, StepLayout.lenQOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)), hframe.lenQ]
    simpa using encodeLength_succ
      (ReachableStepDomain.phaseOne_lenQ_noWrap
        h hwork hphase1 hphase2)
  have hblock := StepBlocks.quotientIncrementBlock_act
    (I := R) hscratch
  dsimp only at hblock
  rw [hvalue] at hblock
  simpa [R, C] using hblock

def phaseOnePostSwapCheckpoint
    (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  let Q := writeField
    (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.lenQOffset n lengthWidth) lengthWidth
    (encodeLength lengthWidth (s.lenQ + 1))
  writeField
    (writeField Q StepLayout.work1Offset (workWidth n)
      (encodeWork1 n (step lengthWidth shiftWidth s) % 2 ^ workWidth n))
    (StepLayout.signWire n lengthWidth shiftWidth) 1 0

theorem swapControl_act_phaseOneQuotientCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let Q := writeField
      (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth
      (encodeLength lengthWidth (s.lenQ + 1))
    actGates (Step.swapControl n lengthWidth shiftWidth) Q =
      writeField Q (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  dsimp only
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let Q := writeField R (StepLayout.lenQOffset n lengthWidth) lengthWidth
    (encodeLength lengthWidth (s.lenQ + 1))
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hframe := phaseOneRemainderCheckpoint_frame h hphase1 hphase2
  have hQbit (q : Nat)
      (hout : StepLayout.lenQOffset n lengthWidth + lengthWidth ≤ q) :
      bitValue Q q = bitValue R q := by
    simp only [Q]
    exact bitValue_write_out (Or.inr hout)
  have hcontrol : bitValue Q control = 0 := by
    exact (hQbit _ (by
      simp [control, StepLayout.controlWire, StepLayout.lenQOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)).trans hframe.controlClean.control
  have hphase1Q : bitValue Q
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    exact (hQbit _ (by
      simp [StepLayout.lenQOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)).trans hframe.phase1
  have hphase2Q : bitValue Q
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    exact (hQbit _ (by
      simp [StepLayout.lenQOffset, StepLayout.phase2Wire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)).trans hframe.phase2
  change actGates (Step.swapControl n lengthWidth shiftWidth) Q =
    writeField Q control 1 1
  have hcontrol' : bitValue Q
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    simpa [control] using hcontrol
  rw [StepBlocks.swapControl_act]
  simp [Phase.xorPairOut, hcontrol', hphase1Q, hphase2Q, control]

theorem swapBlock_act_phaseOneQuotientCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let left := s.lenT + 1 + s.lenQ
    let takeBit :=
      if shifted s.rPrime (s.shift - 1) ≤ s.r then 1 else 0
    let Q := writeField
      (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth
      (encodeLength lengthWidth (s.lenQ + 1))
    actGates (Step.swapBlock n lengthWidth shiftWidth) Q =
      writeField
        (writeField Q StepLayout.work1Offset (workWidth n)
          (writeField
            (readField Q StepLayout.work1Offset (workWidth n))
            left 1 takeBit))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 0 := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let takeBit := if take then 1 else 0
  let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let lenQOffset := StepLayout.lenQOffset n lengthWidth
  let Q := writeField R lenQOffset lengthWidth
    (encodeLength lengthWidth (s.lenQ + 1))
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  let C := actGates (Step.swapControl n lengthWidth shiftWidth) Q
  let P := actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) C
  let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
  change actGates (Step.swapBlock n lengthWidth shiftWidth) Q =
    writeField
      (writeField Q StepLayout.work1Offset (workWidth n)
        (writeField (readField Q StepLayout.work1Offset (workWidth n))
          left 1 takeBit))
      (StepLayout.signWire n lengthWidth shiftWidth) 1 0
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hframe := phaseOneRemainderCheckpoint_frame h hphase1 hphase2
  have hleftBound : left < workWidth n := by
    dsimp [left]
    omega
  have hwidthPos : 0 < width := by
    have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
      h hphase1 hphase2
    dsimp only at hbounds
    dsimp [width, right, left]
    omega
  have hQread (off len : Nat)
      (hout : lenQOffset + lengthWidth ≤ off ∨ off + len ≤ lenQOffset) :
      readField Q off len = readField R off len := by
    simp only [Q]
    exact readField_writeField_of_disjoint hout
  have hQbit (q : Nat)
      (hout : lenQOffset + lengthWidth ≤ q ∨ q + 1 ≤ lenQOffset) :
      bitValue Q q = bitValue R q := by
    simpa [readField_one] using hQread q 1 hout
  have hC : C = writeField Q control 1 1 := by
    simpa [C, Q, R, lenQOffset, control] using
      swapControl_act_phaseOneQuotientCheckpoint h hphase1 hphase2
  have hCread (off len : Nat)
      (hout : control + 1 ≤ off ∨ off + len ≤ control) :
      readField C off len = readField Q off len := by
    rw [hC]
    exact readField_writeField_of_disjoint hout
  have hCbit (q : Nat)
      (hout : control + 1 ≤ q ∨ q + 1 ≤ control) :
      bitValue C q = bitValue Q q := by
    simpa [readField_one] using hCread q 1 hout
  have hClenT : readField C (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    exact (hCread _ _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans <| (hQread _ _ (Or.inr (by
        simp [lenQOffset, StepLayout.lenQOffset,
          StepLayout.lenTOffset]))).trans hframe.lenT
  have hClenQ : readField C lenQOffset lengthWidth =
      encodeLength lengthWidth (s.lenQ + 1) := by
    rw [hCread _ _ (Or.inr (by
      simp [control, lenQOffset, StepLayout.controlWire,
        StepLayout.lenQOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega))]
    simp only [Q]
    rw [readField_writeField,
      Nat.mod_eq_of_lt (encodeLength_lt _ _)]
  have hCleft : readField C
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftOffset,
        StepLayout.auxOffset]))).trans <| (hQread _ _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.leftOffset,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega))).trans hframe.scratch.left
  have hCright : readField C
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightOffset,
        StepLayout.auxOffset]))).trans <| (hQread _ _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.rightOffset,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega))).trans hframe.scratch.right
  have hCcontrol : bitValue C control = 1 := by
    rw [hC, bitValue_write_self]
  have hCcarry : bitValue C
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.carryWire,
        StepLayout.auxOffset]))).trans <| (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega))).trans hframe.scratch.carry
  have hCaccumulator : bitValue C
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans <| (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset,
          StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega))).trans hframe.scratch.accumulator
  have hCleftFlag : bitValue C
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans <| (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.leftFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.scratch.leftFlag
  have hCrightFlag : bitValue C
      (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans <| (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.rightFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.scratch.rightFlag
  have hCpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    exact (hCread _ _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans <| (hQread _ _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.scratch.pool
  have hCcellScratch : bitValue C
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    exact (hCbit _ (Or.inl (by
      simp [control, StepLayout.controlWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans <| (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans hframe.scratch.cellScratch
  have htPos : 0 < s.t := h.positiveLiveCoefficient hstate.1
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPos
  have hencodedLenT : encodeLength lengthWidth s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPos),
      Nat.mod_eq_of_lt (by
        have := h.stepDomain.valid.1.2.2.1
        omega)]
  have hencodedLenQ : encodeLength lengthWidth (s.lenQ + 1) = s.lenQ := by
    rw [encodeLength, if_neg (by omega), Nat.add_sub_cancel,
      Nat.mod_eq_of_lt h.stepDomain.valid.1.2.2.2.1]
  have hsum : 2 + readField C lenQOffset lengthWidth +
      readField C (StepLayout.lenTOffset n) lengthWidth < 2 ^ lengthWidth := by
    rw [hClenQ, hClenT, hencodedLenQ, hencodedLenT]
    omega
  have hprepared := StepPlaced.swapPrepare_frame_of_live_frame
    hlength hwidths hCleft hCright hCcontrol hCcarry hCaccumulator
    hCleftFlag hCrightFlag hCpool hCcellScratch hsum
  dsimp only at hprepared
  rw [hClenQ, hClenT, hencodedLenQ, hencodedLenT] at hprepared
  have hleftEq : 2 + s.lenQ + (s.lenT - 1) = left := by
    dsimp [left]
    omega
  rw [hleftEq] at hprepared
  have hstable : Interval.Stable left 0 (workWidth n) lengthWidth input := by
    simpa [left, input, P] using hprepared.stable
  have haccumulator : bitValue input
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [input, P] using hprepared.accumulator
  have hPwork : readField P StepLayout.work1Offset (workWidth n) =
      readField C StepLayout.work1Offset (workWidth n) := by
    simpa [P] using hprepared.work1
  have hCwork : readField C StepLayout.work1Offset (workWidth n) =
      readField Q StepLayout.work1Offset (workWidth n) := by
    exact hCread _ _ (Or.inr (by
      simp [control, StepLayout.work1Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))
  have hPsign : bitValue P
      (StepLayout.signWire n lengthWidth shiftWidth) =
        bitValue C (StepLayout.signWire n lengthWidth shiftWidth) := by
    simpa [P] using hprepared.sign
  have hCsign : bitValue C
      (StepLayout.signWire n lengthWidth shiftWidth) = takeBit := by
    exact (hCbit _ (Or.inr (by
      simp [control, StepLayout.controlWire, StepLayout.signWire]))).trans <|
      (hQbit _ (Or.inl (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.signWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega))).trans <| by simpa [R, takeBit, take, k] using hframe.sign
  have hworkValue : SelectSwap.workValue left (workWidth n) lengthWidth input =
      writeField (readField Q StepLayout.work1Offset (workWidth n))
        left 1 takeBit := by
    simp only [SelectSwap.workValue, if_pos hleftBound]
    rw [StepPlaced.intervalInput_source, hPwork, hCwork,
      StepPlaced.intervalInput_sign, hPsign, hCsign]
  have hnewRFit :
      (if take then s.r - shifted s.rPrime k else s.r) <
        2 ^ (workWidth n - (left + 1)) := by
    simpa [take, k, left, Nat.add_assoc] using
      ReachableStepDomain.phaseOne_remainderFit_after_step h hphase1 hphase2
  have hresultEq : resultWord =
      (if take then s.r - shifted s.rPrime k else s.r) >>> k := by
    by_cases htake : take
    · simpa [resultWord, take, htake] using
        (sub_shifted_shiftRight htake).symm
    · simp [resultWord, take, htake]
  have hresultFit : resultWord < 2 ^ (width - 1) := by
    rw [hresultEq, Nat.shiftRight_eq_div_pow,
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
    have hpow : 2 ^ (width - 1) * 2 ^ k =
        2 ^ (workWidth n - (left + 1)) := by
      rw [← pow_add]
      congr 1
      dsimp [width, right, k, left]
      omega
    rw [hpow]
    exact hnewRFit
  have hresultFirst : (reverseBits width resultWord).testBit 0 = false := by
    rw [testBit_reverseBits]
    have hbit : resultWord.testBit (width - 1) = false :=
      Nat.testBit_lt_two_pow hresultFit
    simp [hwidthPos, hbit]
  have hRbit : bitValue R (StepLayout.work1Offset + left) = 0 := by
    have htest : R.testBit (StepLayout.work1Offset + left) = false := by
      simp only [R, phaseOneRemainderCheckpoint]
      rw [testBit_writeField_outside (Or.inl (by
          simp [StepLayout.signWire, StepLayout.phase1Wire,
            StepLayout.shiftOffset, StepLayout.work1Offset]
          omega)),
        testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
      exact hresultFirst
    simp [bitValue, htest]
  have hPbit : bitValue P (StepLayout.work1Offset + left) = 0 := by
    have hPQwork : readField P StepLayout.work1Offset (workWidth n) =
        readField Q StepLayout.work1Offset (workWidth n) :=
      hPwork.trans hCwork
    have hPQtest : P.testBit (StepLayout.work1Offset + left) =
        Q.testBit (StepLayout.work1Offset + left) := by
      have htest := congrArg (fun z => z.testBit left) hPQwork
      simpa [testBit_readField, hleftBound, StepLayout.work1Offset] using htest
    have hfromP : bitValue P (StepLayout.work1Offset + left) =
        bitValue Q (StepLayout.work1Offset + left) := by
      simp [bitValue, hPQtest]
    refine hfromP.trans <| (hQbit _ (Or.inr (by
        simp [lenQOffset, StepLayout.lenQOffset, StepLayout.work1Offset]
        omega))).trans hRbit
  have hsignValue : SelectSwap.signValue left (workWidth n) lengthWidth input =
      0 := by
    simp only [SelectSwap.signValue, if_pos hleftBound]
    rw [StepPlaced.intervalInput_source_bit n lengthWidth shiftWidth left P
      hleftBound]
    exact hPbit
  have hblock := StepBlocks.swapBlock_act
    (I := Q) (left := left) (right := 0) hlength hwidths
    (Nat.le_of_lt hwork) hstable haccumulator
  dsimp only at hblock
  rw [hworkValue, hsignValue] at hblock
  simpa [Q, C, P, input] using hblock

theorem swapBlock_act_phaseOnePostSwapCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let Q := writeField
      (phaseOneRemainderCheckpoint n lengthWidth shiftWidth s)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth
      (encodeLength lengthWidth (s.lenQ + 1))
    actGates (Step.swapBlock n lengthWidth shiftWidth) Q =
      phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let Q := writeField R (StepLayout.lenQOffset n lengthWidth) lengthWidth
    (encodeLength lengthWidth (s.lenQ + 1))
  have hswap := swapBlock_act_phaseOneQuotientCheckpoint
    h hwork hwidths hphase1 hphase2
  dsimp only at hswap
  have hRwork : readField R StepLayout.work1Offset (workWidth n) =
      writeField (encodeWork1 n s % 2 ^ workWidth n)
        left width (reverseBits width resultWord) := by
    simpa [R, k, left, right, width, take, resultWord] using
      phaseOneRemainderCheckpoint_work1 h hphase1 hphase2
  have hQwork : readField Q StepLayout.work1Offset (workWidth n) =
      writeField (encodeWork1 n s % 2 ^ workWidth n)
        left width (reverseBits width resultWord) := by
    simp only [Q]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.lenQOffset, StepLayout.work1Offset]
      omega))]
    exact hRwork
  have hsemantic :=
    ReachableStepDomain.phaseOne_work1_after_quotientInsertion
      h hwork hphase1 hphase2
  dsimp only at hsemantic
  rw [hswap, hQwork, hsemantic]
  rfl

private structure PhaseOnePostSwapCheckpointFrame
    (n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  controlClean : StepBlocks.ControlClean n lengthWidth shiftWidth
    (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
  scratch : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
    (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
  aux : readField (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.auxOffset n lengthWidth shiftWidth)
    (StepLayout.auxWidth lengthWidth shiftWidth) = 0
  phase1 : bitValue (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
  phase2 : bitValue (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1
  sign : bitValue (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s)
    (StepLayout.signWire n lengthWidth shiftWidth) = 0

private theorem phaseOnePostSwapCheckpoint_frame
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    PhaseOnePostSwapCheckpointFrame n lengthWidth shiftWidth s := by
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  let P := phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s
  let lenQOffset := StepLayout.lenQOffset n lengthWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hframe := phaseOneRemainderCheckpoint_frame h hphase1 hphase2
  have hread (off fieldWidth : Nat)
      (hlenQ : lenQOffset + lengthWidth ≤ off ∨
        off + fieldWidth ≤ lenQOffset)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ off ∨
        off + fieldWidth ≤ StepLayout.work1Offset)
      (hsign : sign + 1 ≤ off ∨ off + fieldWidth ≤ sign) :
      readField P off fieldWidth = readField R off fieldWidth := by
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork1,
      readField_writeField_of_disjoint hlenQ]
  have hbit (q : Nat)
      (hlenQ : lenQOffset + lengthWidth ≤ q ∨ q + 1 ≤ lenQOffset)
      (hwork1 : StepLayout.work1Offset + workWidth n ≤ q ∨
        q + 1 ≤ StepLayout.work1Offset)
      (hsign : sign + 1 ≤ q ∨ q + 1 ≤ sign) :
      bitValue P q = bitValue R q := by
    simpa [readField_one] using hread q 1 hlenQ hwork1 hsign
  have hreadAfterSign (off fieldWidth : Nat) (hoff : sign + 1 ≤ off) :
      readField P off fieldWidth = readField R off fieldWidth := by
    apply hread
    · left
      dsimp only [lenQOffset, sign] at hoff ⊢
      simp [StepLayout.lenQOffset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset] at hoff ⊢
      omega
    · left
      dsimp only [sign] at hoff ⊢
      simp [StepLayout.work1Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset] at hoff ⊢
      omega
    · exact Or.inl hoff
  have hbitAfterSign (q : Nat) (hq : sign + 1 ≤ q) :
      bitValue P q = bitValue R q := by
    simpa [readField_one] using hreadAfterSign q 1 hq
  have hclean : StepBlocks.ControlClean n lengthWidth shiftWidth P := by
    constructor
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.controlWire])).trans
        hframe.controlClean.control
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.controlClean.temporary
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.plusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.controlClean.plus
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.minusWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.controlClean.minus
  have hscratch : StepBlocks.RemainderScratchClean
      n lengthWidth shiftWidth P := by
    constructor
    · exact (hreadAfterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.leftOffset,
            StepLayout.auxOffset])).trans hframe.scratch.left
    · exact (hreadAfterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.rightOffset,
            StepLayout.auxOffset]
          omega)).trans hframe.scratch.right
    · exact hclean.control
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega)).trans hframe.scratch.carry
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.accumulatorWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.scratch.accumulator
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.leftFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.scratch.leftFlag
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.rightFlagWire,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.scratch.rightFlag
    · exact (hreadAfterSign _ _ (by
          simp [sign, StepLayout.signWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)).trans hframe.scratch.pool
    · exact (hbitAfterSign _ (by
          simp [sign, StepLayout.signWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega)).trans hframe.scratch.cellScratch
  have haux : readField P (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
    exact (hreadAfterSign _ _ (by
      simp [sign, StepLayout.signWire, StepLayout.auxOffset])).trans hframe.aux
  have hp1 : bitValue P
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 := by
    exact (hbit _ (Or.inl (by
          simp [lenQOffset, StepLayout.lenQOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega)) (Or.inl (by
          simp [StepLayout.work1Offset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega)) (Or.inr (by
          simp [sign, StepLayout.signWire]))).trans hframe.phase1
  have hp2 : bitValue P
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    exact (hbit _ (Or.inl (by
          simp [lenQOffset, StepLayout.lenQOffset,
            StepLayout.phase2Wire, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega)) (Or.inl (by
          simp [StepLayout.work1Offset, StepLayout.phase2Wire,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega)) (Or.inr (by
          simp [sign, StepLayout.signWire, StepLayout.phase2Wire]))).trans
      hframe.phase2
  have hsignZero : bitValue P
      (StepLayout.signWire n lengthWidth shiftWidth) = 0 := by
    simp [P, phaseOnePostSwapCheckpoint, bitValue_write_self]
  exact ⟨hclean, hscratch, haux, hp1, hp2, hsignZero⟩

private theorem phaseOnePostSwapCheckpoint_lt
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s <
      2 ^ (StepLayout.layout n lengthWidth shiftWidth).width := by
  let L := StepLayout.layout n lengthWidth shiftWidth
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let width := right - left + 1
  let R := phaseOneRemainderCheckpoint n lengthWidth shiftWidth s
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hsubFit : left + width ≤ workWidth n := by
    dsimp [left, width, right]
    omega
  have hshiftBound : StepLayout.shiftOffset n lengthWidth + shiftWidth ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.auxOffset,
      StepLayout.phase1Wire]
    omega
  have hwork2Bound : StepLayout.work2Offset n + workWidth n ≤ L.width := by
    simp [L, StepLayout.layout_width, StepLayout.work2Offset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
    omega
  have hsubBound : StepLayout.work1Offset + left + width ≤ L.width := by
    have hworkBound : workWidth n ≤ L.width := by
      simp [L, StepLayout.layout_width, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega
    simp only [StepLayout.work1Offset, Nat.zero_add]
    omega
  have hsignBound : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.signWire,
      StepLayout.auxOffset]
    omega
  have hlenQBound : StepLayout.lenQOffset n lengthWidth + lengthWidth ≤
      L.width := by
    simp [L, StepLayout.layout_width, StepLayout.lenQOffset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
    omega
  have hwork1Bound : StepLayout.work1Offset + workWidth n ≤ L.width := by
    simp [L, StepLayout.layout_width, StepLayout.work1Offset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  have hpre : phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s <
      2 ^ L.width := by
    simp only [phaseOnePreShiftCheckpoint]
    exact writeField_lt hwork2Bound
      (writeField_lt hshiftBound (encoded_lt n lengthWidth shiftWidth s))
  have hR : R < 2 ^ L.width := by
    simp only [R, phaseOneRemainderCheckpoint]
    exact writeField_lt hsignBound (writeField_lt hsubBound hpre)
  have hQ : writeField R (StepLayout.lenQOffset n lengthWidth) lengthWidth
      (encodeLength lengthWidth (s.lenQ + 1)) < 2 ^ L.width :=
    writeField_lt hlenQBound hR
  simpa only [L, phaseOnePostSwapCheckpoint, R] using
    writeField_lt hsignBound (writeField_lt hwork1Bound hQ)

theorem phaseOnePostSwapCheckpoint_eq_encoded_phase01
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s =
      encoded n lengthWidth shiftWidth
        { step lengthWidth shiftWidth s with
          phase1 := false
          phase2 := true } := by
  let L := StepLayout.layout n lengthWidth shiftWidth
  let s' := step lengthWidth shiftWidth s
  let s01 : State := { s' with phase1 := false, phase2 := true }
  let P := phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth n - s.shift
  let remWidth := right - left + 1
  have hwindow := ReachableStepDomain.phaseOne_window h hphase1 hphase2
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  have hsubFit : left + remWidth ≤ workWidth n := by
    dsimp [left, remWidth, right]
    omega
  have hframe : PhaseOnePostSwapCheckpointFrame n lengthWidth shiftWidth s :=
    phaseOnePostSwapCheckpoint_frame h hphase1 hphase2
  have hreadPre (off fieldWidth : Nat)
      (hoff : workWidth n ≤ off)
      (hlenQ : StepLayout.lenQOffset n lengthWidth + lengthWidth ≤ off ∨
        off + fieldWidth ≤ StepLayout.lenQOffset n lengthWidth)
      (hsign : StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ off ∨
        off + fieldWidth ≤
          StepLayout.signWire n lengthWidth shiftWidth) :
      readField P off fieldWidth =
        readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
          off fieldWidth := by
    simp only [P, phaseOnePostSwapCheckpoint, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simpa [StepLayout.work1Offset] using hoff)),
      readField_writeField_of_disjoint hlenQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp only [StepLayout.work1Offset, Nat.zero_add]
        dsimp [left, remWidth, right] at hsubFit
        omega))]
  have hPwork1 : readField P StepLayout.work1Offset (workWidth n) =
      encodeWork1 n s' % 2 ^ workWidth n := by
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)), readField_writeField, Nat.mod_mod]
  have hPwork2 : readField P (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n s' := by
    calc
      readField P (StepLayout.work2Offset n) (workWidth n) =
          readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
            (StepLayout.work2Offset n) (workWidth n) :=
        hreadPre _ _ (by simp [StepLayout.work2Offset]) (Or.inr (by
          simp [StepLayout.work2Offset, StepLayout.lenQOffset]
          omega)) (Or.inr (by
          simp [StepLayout.work2Offset, StepLayout.signWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega))
      _ = encodeWork2 n { s with shift := s.shift - 1 } :=
        phaseOnePreShiftCheckpoint_work2 n lengthWidth shiftWidth s
      _ = encodeWork2 n s' := by
        simp [s', hstep, encodeWork2, encodeWork2Raw]
  have hPlenT : readField P (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s'.lenT := by
    calc
      readField P (StepLayout.lenTOffset n) lengthWidth =
          readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
            (StepLayout.lenTOffset n) lengthWidth :=
        hreadPre _ _ (by
          simp [StepLayout.lenTOffset, workWidth]) (Or.inr (by
          simp [StepLayout.lenTOffset, StepLayout.lenQOffset])) (Or.inr (by
          simp [StepLayout.lenTOffset, StepLayout.signWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega))
      _ = encodeLength lengthWidth s.lenT :=
        phaseOnePreShiftCheckpoint_lenT n lengthWidth shiftWidth s
      _ = encodeLength lengthWidth s'.lenT := by simp [s', hstep]
  have hPlenQ : readField P (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s'.lenQ := by
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.lenQOffset, StepLayout.signWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)), readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.lenQOffset]
      omega)), readField_writeField,
      Nat.mod_eq_of_lt (encodeLength_lt lengthWidth (s.lenQ + 1))]
    simp [s', hstep]
  have hPlenRPrime : readField P
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s'.lenRPrime := by
    calc
      readField P (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
          readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
            (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth :=
        hreadPre _ _ (by
          simp [StepLayout.lenRPrimeOffset, workWidth]
          omega) (Or.inl (by
          simp [StepLayout.lenQOffset, StepLayout.lenRPrimeOffset]
          omega))
          (Or.inr (by
          simp [StepLayout.lenRPrimeOffset, StepLayout.signWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega))
      _ = encodeLength lengthWidth s.lenRPrime :=
        phaseOnePreShiftCheckpoint_lenRPrime n lengthWidth shiftWidth s
      _ = encodeLength lengthWidth s'.lenRPrime := by simp [s', hstep]
  have hPshift : readField P (StepLayout.shiftOffset n lengthWidth)
      shiftWidth = encodeLength shiftWidth s'.shift := by
    calc
      readField P (StepLayout.shiftOffset n lengthWidth) shiftWidth =
          readField (phaseOnePreShiftCheckpoint n lengthWidth shiftWidth s)
            (StepLayout.shiftOffset n lengthWidth) shiftWidth :=
        hreadPre _ _ (by
          simp [StepLayout.shiftOffset, workWidth]
          omega) (Or.inl (by
          simp [StepLayout.lenQOffset, StepLayout.shiftOffset]
          omega)) (Or.inr (by
          simp [StepLayout.signWire, StepLayout.phase1Wire,
            StepLayout.shiftOffset]))
      _ = encodeLength shiftWidth (s.shift - 1) := by
        rw [phaseOnePreShiftCheckpoint,
          readField_writeField_of_disjoint (Or.inl (by
            simp [StepLayout.work2Offset, StepLayout.shiftOffset]
            omega)), readField_writeField,
          Nat.mod_eq_of_lt (encodeLength_lt shiftWidth (s.shift - 1))]
      _ = encodeLength shiftWidth s'.shift := by simp [s', hstep]
  have hPiter : bitValue P
      (StepLayout.iterWire n lengthWidth shiftWidth) = boolValue s'.iter := by
    rw [← readField_one,
      hreadPre _ 1 (by
        simp [StepLayout.iterWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega) (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)) (Or.inr (by
        simp [StepLayout.signWire, StepLayout.iterWire])), readField_one,
      phaseOnePreShiftCheckpoint_bit_after_shift (by
        simp [StepLayout.iterWire]), read_iter]
    simp [s', hstep]
  have hPsign : bitValue P
      (StepLayout.signWire n lengthWidth shiftWidth) = boolValue s'.sign := by
    rw [show bitValue P (StepLayout.signWire n lengthWidth shiftWidth) = 0 by
      simpa [P] using hframe.sign]
    simp [s', hstep, boolValue]
  have hPlt : P < 2 ^ L.width := by
    simpa [P, L] using
      phaseOnePostSwapCheckpoint_lt h hphase1 hphase2
  apply Layout.ext hPlt (encoded_lt n lengthWidth shiftWidth s01)
  intro j hj
  have hj' : j < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hj
  interval_cases j
  · change readField P StepLayout.work1Offset (workWidth n) =
      readField (encoded n lengthWidth shiftWidth s01)
        StepLayout.work1Offset (workWidth n)
    rw [hPwork1, read_work1]
    simp [s01, encodeWork1]
  · change readField P (StepLayout.work2Offset n) (workWidth n) =
      readField (encoded n lengthWidth shiftWidth s01)
        (StepLayout.work2Offset n) (workWidth n)
    rw [hPwork2, read_work2]
    simp [s01, encodeWork2, encodeWork2Raw]
  · have heq := hPlenT.trans
        (read_lenT n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenTOffset, two_mul,
      Nat.add_assoc] using heq
  · have heq := hPlenQ.trans
        (read_lenQ n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenQOffset, two_mul,
      Nat.add_assoc] using heq
  · have heq := hPlenRPrime.trans
        (read_lenRPrime n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenRPrimeOffset, two_mul,
      Nat.add_assoc] using heq
  · have heq := hPshift.trans
        (read_shift n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.shiftOffset, two_mul,
      three_mul, Nat.add_assoc] using heq
  · have heq : bitValue P
        (StepLayout.phase1Wire n lengthWidth shiftWidth) =
        bitValue (encoded n lengthWidth shiftWidth s01)
          (StepLayout.phase1Wire n lengthWidth shiftWidth) := by
      rw [show bitValue P
          (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0 by
        simpa [P] using hframe.phase1, read_phase1]
      simp [s01, boolValue]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase1Wire,
      StepLayout.shiftOffset, readField_one, two_mul, three_mul,
      Nat.add_assoc] using heq
  · have heq : bitValue P
        (StepLayout.phase2Wire n lengthWidth shiftWidth) =
        bitValue (encoded n lengthWidth shiftWidth s01)
          (StepLayout.phase2Wire n lengthWidth shiftWidth) := by
      rw [show bitValue P
          (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 by
        simpa [P] using hframe.phase2, read_phase2]
      simp [s01, boolValue]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.phase2Wire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have heq := hPiter.trans
        (read_iter n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc, s01] using heq
  · have heq := hPsign.trans
        (read_sign n lengthWidth shiftWidth s01).symm
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.signWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc, s01] using heq
  · have heq : bitValue P
        (StepLayout.controlWire n lengthWidth shiftWidth) =
        bitValue (encoded n lengthWidth shiftWidth s01)
          (StepLayout.controlWire n lengthWidth shiftWidth) := by
      rw [show bitValue P
          (StepLayout.controlWire n lengthWidth shiftWidth) = 0 by
        simpa [P] using hframe.controlClean.control, read_control]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.controlWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, readField_one,
      two_mul, three_mul, Nat.add_assoc] using heq
  · have heq : readField P
        (StepLayout.auxOffset n lengthWidth shiftWidth)
        (StepLayout.auxWidth lengthWidth shiftWidth) =
        readField (encoded n lengthWidth shiftWidth s01)
          (StepLayout.auxOffset n lengthWidth shiftWidth)
          (StepLayout.auxWidth lengthWidth shiftWidth) := by
      rw [show readField P
          (StepLayout.auxOffset n lengthWidth shiftWidth)
          (StepLayout.auxWidth lengthWidth shiftWidth) = 0 by
        simpa [P] using hframe.aux, read_aux]
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, two_mul,
      three_mul, Nat.add_assoc] using heq

private theorem coefficientPairWindow_phaseOnePostSwapCheckpoint
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s) := by
  let I := phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s
  have hframe := phaseOnePostSwapCheckpoint_frame h hphase1 hphase2
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hsubControl : actGates
      (Step.coefficientSubControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubControl_identity_of_phase01
      hframe.phase1 hframe.phase2
  have hsubInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientSubControl n lengthWidth shiftWidth) I))) := by
    rw [hsubControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hframe.scratch.right hframe.scratch.control
      hframe.scratch.carry hframe.scratch.accumulator
      hframe.scratch.leftFlag hframe.scratch.rightFlag hframe.scratch.pool
      hframe.scratch.cellScratch
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity hlength hwidths hsubInactive
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hframe.phase1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hframe.phase1
  have haddInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientAddControl n lengthWidth shiftWidth) I))) := by
    rw [haddControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hframe.scratch.right hframe.scratch.control
      hframe.scratch.carry hframe.scratch.accumulator
      hframe.scratch.leftFlag hframe.scratch.rightFlag hframe.scratch.pool
      hframe.scratch.cellScratch
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

theorem coefficientPairWindow_phaseOne
    {p n lengthWidth shiftWidth U : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    CoefficientPairWindow n lengthWidth shiftWidth U
      (actGates (Step.coefficientPrefixGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s)) := by
  let I := phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s
  have hframe := phaseOnePostSwapCheckpoint_frame h hphase1 hphase2
  have hpre := preShiftBlock_act_reachable_phaseOne
    h hphase1 hphase2
  have hrem := guardedRemainderBlocks_act_phaseOneCheckpoint
    h hwork hwidths hphase1 hphase2
  have hqinc := quotientIncrementBlock_act_phaseOneRemainderCheckpoint
    h hwork hphase1 hphase2
  have hswap := swapBlock_act_phaseOnePostSwapCheckpoint
    h hwork hwidths hphase1 hphase2
  have hqdecControl : actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientDecrementControl_identity_of_phase2_one hframe.phase2
  have hqdecScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) =
        0 := by
    rw [hqdecControl, StepPlaced.quotientInput_scratch]
    exact hframe.scratch.pool
  have hqdec : actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientDecrementBlock_identity hqdecScratch
    rw [hqdecControl]
    exact hframe.controlClean.control
  simp only [Step.coefficientPrefixGates, actGates_append]
  rw [hpre, hrem, hqinc,
    hswap, show phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s = I
      by rfl, hqdec]
  exact coefficientPairWindow_phaseOnePostSwapCheckpoint
    h hwork hwidths hphase1 hphase2

theorem phaseOnePostSwapInactiveSuffix_act
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates
        (Step.quotientDecrementBlock n lengthWidth shiftWidth ++
          Step.coefficientSubBlock n lengthWidth shiftWidth ++
          Step.coefficientFlip n lengthWidth shiftWidth ++
          Step.coefficientAddBlock n lengthWidth shiftWidth ++
          Step.around (Step.postShiftControl n lengthWidth shiftWidth)
            (StepLayout.shiftGates n lengthWidth shiftWidth))
        (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s) =
      phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s := by
  let I := phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s
  have hframe := phaseOnePostSwapCheckpoint_frame h hphase1 hphase2
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos (h.positiveLiveCoefficient hstate.1)
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    have hlenTFit := h.stepDomain.valid.1.2.2.1
    simp at hlenTFit
    omega
  have hqdecControl : actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.quotientDecrementControl_identity_of_phase2_one hframe.phase2
  have hqdecScratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) =
        0 := by
    rw [hqdecControl, StepPlaced.quotientInput_scratch]
    exact hframe.scratch.pool
  have hqdec : actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
    apply StepBlocks.quotientDecrementBlock_identity hqdecScratch
    rw [hqdecControl]
    exact hframe.controlClean.control
  have hsubControl : actGates
      (Step.coefficientSubControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubControl_identity_of_phase01
      hframe.phase1 hframe.phase2
  have hsubInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientSubControl n lengthWidth shiftWidth) I))) := by
    rw [hsubControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hframe.scratch.right hframe.scratch.control
      hframe.scratch.carry hframe.scratch.accumulator
      hframe.scratch.leftFlag hframe.scratch.rightFlag hframe.scratch.pool
      hframe.scratch.cellScratch
  have hsub : actGates
      (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientSubBlock_identity hlength hwidths hsubInactive
  have hflip : actGates
      (Step.coefficientFlip n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientFlip_identity_of_phase1_zero hframe.phase1
  have haddControl : actGates
      (Step.coefficientAddControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddControl_identity_of_phase1_zero hframe.phase1
  have haddInactive : StepPlaced.IntervalInactive
      (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.coefficientAddControl n lengthWidth shiftWidth) I))) := by
    rw [haddControl]
    exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
      hlength hwidths hframe.scratch.right hframe.scratch.control
      hframe.scratch.carry hframe.scratch.accumulator
      hframe.scratch.leftFlag hframe.scratch.rightFlag hframe.scratch.pool
      hframe.scratch.cellScratch
  have hadd : actGates
      (Step.coefficientAddBlock n lengthWidth shiftWidth) I = I :=
    StepBlocks.coefficientAddBlock_identity hlength hwidths haddInactive
  have hpostControl : actGates
      (Step.postShiftControl n lengthWidth shiftWidth) I = I :=
    StepBlocks.postShiftControl_identity_of_phase1_zero_plus_zero
      hframe.phase1 hframe.controlClean.plus
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
      hframe.aux
  have hpost : actGates
      (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
        (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I := by
    apply StepBlocks.postShiftBlock_identity hpostScratch
    · rw [hpostControl]
      exact hframe.controlClean.plus
    · rw [hpostControl]
      exact hframe.controlClean.minus
  change actGates
      (Step.quotientDecrementBlock n lengthWidth shiftWidth ++
        Step.coefficientSubBlock n lengthWidth shiftWidth ++
        Step.coefficientFlip n lengthWidth shiftWidth ++
        Step.coefficientAddBlock n lengthWidth shiftWidth ++
        Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I
  simp only [actGates_append]
  rw [hqdec, hsub, hflip, hadd, hpost]

theorem phaseGates_act_phaseOnePostSwapCheckpoint
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
        (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  let s' := step lengthWidth shiftWidth s
  let s01 : State := { s' with phase1 := false, phase2 := true }
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  have hpacked := ReachableStepDomain.phaseOne_packed_after_step
    h hwork hphase1 hphase2
  have hstate := ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2
  have hcheckpoint := phaseOnePostSwapCheckpoint_eq_encoded_phase01
    h hwork hphase1 hphase2
  change actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
      (phaseOnePostSwapCheckpoint n lengthWidth shiftWidth s) =
    encoded n lengthWidth shiftWidth s'
  rw [hcheckpoint]
  change actGates (StepLayout.phaseGates n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s01) =
    encoded n lengthWidth shiftWidth s'
  have hlenQFit : s'.lenQ < 2 ^ lengthWidth := hpacked.2.2.2.1
  have hlenRPrimeFit : s'.lenRPrime < 2 ^ lengthWidth :=
    hpacked.2.2.2.2.1
  have hshiftFit : s'.shift < 2 ^ shiftWidth :=
    hpacked.2.2.2.2.2.1
  have hlenQPos : 0 < s'.lenQ := by
    simp [s', hstep]
  have hrPrimePos : 0 < s'.rPrime := by
    simpa [s', hstep] using hstate.1
  have hlenRPrimePos : 0 < s'.lenRPrime := by
    have hbitLengthPos := bitLength_pos hrPrimePos
    rw [hpacked.2.1]
    exact hbitLengthPos
  have hlenQPhysical : readField (encoded n lengthWidth shiftWidth s01)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth := by
    rw [read_lenQ]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hlenQFit).mp (by
      simpa [s01] using hzero)
    omega
  have hlenRPrimePhysical :
      readField (encoded n lengthWidth shiftWidth s01)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
        encodedZero lengthWidth := by
    rw [read_lenRPrime]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff hlenRPrimeFit).mp (by
      simpa [s01] using hzero)
    omega
  have hphaseAct := StepBlocks.phaseBlock_act_phase01
    (I := encoded n lengthWidth shiftWidth s01)
    (read_aux n lengthWidth shiftWidth s01)
    (by simp [read_phase1, s01, boolValue])
    (by simp [read_phase2, s01, boolValue])
    (by simp [read_sign, s01, s', hstep, boolValue])
    hlenQPhysical hlenRPrimePhysical
  dsimp only at hphaseAct
  let zeroShift := Phase.selectorValue shiftWidth
    (StepLayout.shiftOffset n lengthWidth)
    (encoded n lengthWidth shiftWidth s01)
  have hsPhase1 : s'.phase1 = decide (s'.shift = 0) := by
    simp [s', hstep]
  have hsPhase2 : s'.phase2 = decide (s'.shift ≠ 0) := by
    simp [s', hstep]
  have hzeroShift : zeroShift = boolValue s'.phase1 := by
    simp [zeroShift, Phase.selectorValue, read_shift, s01,
      encodeLength_eq_encodedZero_iff hshiftFit, hsPhase1, boolValue]
  have hphase2Value : (1 + zeroShift) % 2 = boolValue s'.phase2 := by
    rw [hzeroShift]
    by_cases hz : s'.shift = 0 <;>
      simp [hsPhase1, hsPhase2, hz, boolValue]
  rw [hphaseAct, ← show zeroShift = Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth)
      (encoded n lengthWidth shiftWidth s01) by rfl,
    hphase2Value, hzeroShift]
  have hwrite := encoded_write_phase_sign n lengthWidth shiftWidth s01
    s'.phase1 s'.phase2 false
  dsimp only at hwrite
  simpa [Layout.write, StepLayout.layout, VQ.Euclid.layout,
    Layout.offset, Layout.size, StepLayout.phase1Wire,
    StepLayout.phase2Wire, StepLayout.signWire, StepLayout.shiftOffset,
    two_mul, three_mul, Nat.add_assoc, s01, s', hstep, boolValue] using hwrite

theorem ownershipBlock_inactive_phaseOneStep
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  apply StepBlocks.ownershipBlock_inactive hwork
    (read_control n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s))
    (read_aux n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s))
  left
  rw [read_lenQ]
  intro hzero
  rw [hstep] at hzero
  have hlenQZero :=
    (encodeLength_eq_encodedZero_iff
      (ReachableStepDomain.phaseOne_lenQ_noWrap
        h hwork hphase1 hphase2)).mp hzero
  omega

theorem gates_act_phaseOne
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth (step lengthWidth shiftWidth s) := by
  have hpre := preShiftBlock_act_reachable_phaseOne
    h hphase1 hphase2
  have hrem := guardedRemainderBlocks_act_phaseOneCheckpoint
    h hwork hwidths hphase1 hphase2
  have hqinc := quotientIncrementBlock_act_phaseOneRemainderCheckpoint
    h hwork hphase1 hphase2
  have hswap := swapBlock_act_phaseOnePostSwapCheckpoint
    h hwork hwidths hphase1 hphase2
  have hsuffix := phaseOnePostSwapInactiveSuffix_act
    h hwidths hphase1 hphase2
  simp only [actGates_append] at hsuffix
  have hphase := phaseGates_act_phaseOnePostSwapCheckpoint
    h hwork hphase1 hphase2
  have hownership := ownershipBlock_inactive_phaseOneStep
    h hwork hphase1 hphase2
  simp only [Step.gates, actGates_append]
  rw [hpre, hrem, hqinc, hswap, hsuffix, hphase, hownership]

theorem reverseCircuit_recovers_phaseOne
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
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
    simpa [act, Step.circuit] using gates_act_phaseOne
      h hwork hwidths hphase1 hphase2
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
