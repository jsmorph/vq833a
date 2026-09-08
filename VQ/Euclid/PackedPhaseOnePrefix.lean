/-
Encoded-state refinement for the packed phase-one prefix.
-/
import VQ.Euclid.PackedPhaseFourPrefix
import VQ.Euclid.StepState.PhaseOne

namespace VQ
namespace Euclid
namespace PackedPhaseOnePrefix

open Reversible

private theorem checkpoint_read
    {s : State} {off width : Nat}
    (hwork : PackedStepLayout.workTwoOffset + 259 ≤ off ∨
      off + width ≤ PackedStepLayout.workTwoOffset)
    (hshift : PackedStepLayout.shiftOffset + 9 ≤ off ∨
      off + width ≤ PackedStepLayout.shiftOffset) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s) off width =
      readField (PackedState.encoded s) off width := by
  rw [PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint,
    readField_writeField_of_disjoint hwork,
    readField_writeField_of_disjoint hshift]

private theorem checkpoint_bit
    {s : State} {q : Nat}
    (hwork : PackedStepLayout.workTwoOffset + 259 ≤ q ∨
      q + 1 ≤ PackedStepLayout.workTwoOffset)
    (hshift : PackedStepLayout.shiftOffset + 9 ≤ q ∨
      q + 1 ≤ PackedStepLayout.shiftOffset) :
    bitValue (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s) q =
      bitValue (PackedState.encoded s) q := by
  simpa [readField_one] using checkpoint_read hwork hshift

theorem checkpoint_workOne (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 s % 2 ^ 259 := by
  rw [checkpoint_read (by decide +kernel) (by decide +kernel),
    PackedState.read_workOne]

theorem checkpoint_workTwo (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 { s with shift := s.shift - 1 } := by
  rw [PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint,
    readField_writeField]
  exact Nat.mod_eq_of_lt (by
    simpa [workWidth, encodeWork2] using
      rotatePositionsLeft_lt 259 (s.shift - 1)
        (encodeWork2Raw 256 { s with shift := s.shift - 1 }))

theorem checkpoint_lengthT (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.lengthTOffset 9 = encodeLength 9 s.lenT := by
  rw [checkpoint_read (by decide +kernel) (by decide +kernel),
    PackedState.read_lengthT]

theorem checkpoint_lengthQ (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.lengthQOffset 9 = encodeLength 9 s.lenQ := by
  rw [checkpoint_read (by decide +kernel) (by decide +kernel),
    PackedState.read_lengthQ]

theorem checkpoint_shift (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.shiftOffset 9 = encodeLength 9 (s.shift - 1) := by
  rw [PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint,
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField, Nat.mod_eq_of_lt (encodeLength_lt 9 _)]

theorem checkpoint_pool (s : State) :
    readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.poolOffset 13 = 0 := by
  rw [checkpoint_read (by decide +kernel) (by decide +kernel),
    PackedState.read_pool]

theorem checkpoint_phaseOne (s : State) :
    bitValue (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.phaseOneWire = boolValue s.phase1 := by
  rw [checkpoint_bit (by decide +kernel) (by decide +kernel),
    PackedState.read_phaseOne]

theorem checkpoint_phaseTwo (s : State) :
    bitValue (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.phaseTwoWire = boolValue s.phase2 := by
  rw [checkpoint_bit (by decide +kernel) (by decide +kernel),
    PackedState.read_phaseTwo]

theorem checkpoint_sign (s : State) :
    bitValue (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.signWire = boolValue s.sign := by
  rw [checkpoint_bit (by decide +kernel) (by decide +kernel),
    PackedState.read_sign]

private theorem checkpoint_extension (s : State) :
    bitValue (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.extensionWire = 0 := by
  rw [checkpoint_bit (by decide +kernel) (by decide +kernel)]
  simpa using PackedState.read_extension s

theorem remainderSubBlock_act_phaseOne
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth 256 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
    actGates PackedPhaseFourPrefix.remainderSubBlock I =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 subSign := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let C := writeField I PackedPhaseFourPrefix.controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  let input := PackedInterval.remainderInput P
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hR : right < 259 := by
    dsimp [right, workWidth]
    omega
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    exact checkpoint_pool s
  have hcontrol : bitValue I PackedPhaseFourPrefix.controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [PackedPhaseFourPrefix.controlWire])
      (by simp [PackedPhaseFourPrefix.controlWire]) hpool
  have hextension : bitValue I PackedStepLayout.extensionWire = 0 :=
    checkpoint_extension s
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact readField_narrow (by omega) htail
  have hcarryC : bitValue C (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact readField_sub_zero (by omega) (by omega) htail
  have hprepare := PackedEndpointState.remainderPrepare_act_mod
    (I := C) hscratchC hcarryC
  have hlenTC : readField C PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact checkpoint_lengthT s
  have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact checkpoint_lengthQ s
  have hshiftC : readField C PackedStepLayout.shiftOffset 9 =
      encodeLength 9 (s.shift - 1) := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact checkpoint_shift s
  have hleftP : readField P PackedStepLayout.lengthTOffset 9 = left := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField, hlenTC, hlenQC, Nat.mod_mod]
    simpa [left] using StepState.phaseOne_remainderLeftEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hrightP : readField P PackedStepLayout.shiftOffset 9 = right := by
    simp only [P]
    rw [hprepare, readField_writeField, Nat.mod_mod, hshiftC]
    have hencode : encodeLength 9 (s.shift - 1) < 2 ^ 9 :=
      encodeLength_lt 9 _
    have hreassociate :
        257 + 2 ^ 9 - encodeLength 9 (s.shift - 1) =
          257 + (2 ^ 9 - encodeLength 9 (s.shift - 1)) := by
      omega
    rw [hreassociate]
    simpa [right] using StepState.phaseOne_remainderRightEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hworkOneP : readField P PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 s % 2 ^ 259 := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact checkpoint_workOne s
  have hworkTwoP : readField P PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 { s with shift := s.shift - 1 } := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact checkpoint_workTwo s
  have hsignP : bitValue P PackedStepLayout.signWire = 0 := by
    have hready := h.stepDomain.valid.2
    simp [PhaseReady, hphaseOne, hphaseTwo] at hready
    rw [← readField_one]
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel), readField_one,
      checkpoint_sign, hready.1]
    simp [boolValue]
  have hsourceFull : readField input Interval.sourceOffset 259 =
      encodeWork2 256 { s with shift := s.shift - 1 } := by
    calc
      readField input Interval.sourceOffset 259 =
          readField P PackedStepLayout.workTwoOffset 259 := by
        simpa [input, PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.sourceOffset,
          Layout.read, Layout.offset, Layout.size] using
          PackedInterval.remainderInput_field 0 P (by decide)
      _ = _ := hworkTwoP
  have htargetFull : readField input (Interval.targetOffset 259) 259 =
      encodeWork1 256 s % 2 ^ 259 := by
    calc
      readField input (Interval.targetOffset 259) 259 =
          readField P PackedStepLayout.workOneOffset 259 := by
        simpa [input, PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.targetOffset,
          Layout.read, Layout.offset, Layout.size] using
          PackedInterval.remainderInput_field 1 P (by decide)
      _ = _ := hworkOneP
  have hsignInput : bitValue input (Interval.signWire 259 9) = 0 := by
    rw [← readField_one]
    change readField input 537 1 = 0
    calc
      readField input 537 1 =
          readField P PackedStepLayout.signWire 1 := by
        simpa [input, PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.signWire,
          Layout.read, Layout.offset, Layout.size] using
          PackedInterval.remainderInput_field 5 P (by decide)
      _ = 0 := by simpa [readField_one] using hsignP
  have hpure := StepState.phaseOne_remainderOperands
    h (by decide) hphaseOne hphaseTwo
  dsimp only at hpure
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) = s.rPrime := by
    have hpureSource := hpure.2.1
    rw [hpure.1] at hpureSource
    rw [← hpureSource]
    rw [← readField_readField hfit, hsourceFull]
  have htargetSlice :
      readField input (Interval.targetOffset 259 + left) width =
        readField (encodeWork1 256 s) left width := by
    calc
      readField input (Interval.targetOffset 259 + left) width =
          readField
            (readField input (Interval.targetOffset 259) 259) left width := by
        symm
        exact readField_readField hfit
      _ = readField (encodeWork1 256 s % 2 ^ 259) left width := by
        rw [htargetFull]
      _ = readField (encodeWork1 256 s) left width := by
        apply Nat.eq_of_testBit_eq
        intro b
        rw [testBit_readField, testBit_readField]
        by_cases hb : b < width
        · simp [hb, Nat.testBit_mod_two_pow,
            show left + b < 259 by omega]
        · simp [hb]
  have htargetValue : reverseBits width
      (readField input (Interval.targetOffset 259 + left) width) =
        targetWord := by
    have hpureTarget := hpure.2.2.2.1
    rw [hpure.2.2.1] at hpureTarget
    change reverseBits width
      (readField (encodeWork1 256 s) left width) = targetWord at hpureTarget
    rw [htargetSlice]
    exact hpureTarget
  have hdecoded := StepState.phaseOne_remainderDecodedSubValues
    h hphaseOne hphaseTwo
  dsimp only at hdecoded
  have hsubTarget : StepPlaced.intervalSubTargetValue left right 259 9 input =
      writeField (encodeWork1 256 s % 2 ^ 259) left width
        (reverseBits width subWord) := by
    simp only [StepPlaced.intervalSubTargetValue]
    rw [htargetFull, hsourceValue, htargetValue, hdecoded.1]
  have hsubSign : StepPlaced.intervalSubSignValue left right 259 9 input =
      subSign := by
    simp only [StepPlaced.intervalSubSignValue]
    rw [hsignInput, hsourceValue, htargetValue, hdecoded.2]
    by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r <;>
      simp [subSign, take, k, htake]
  have hblock := PackedPhaseFourPrefix.remainderSubBlock_act
    (I := I) (left := left) (right := right)
    (by simp [I, checkpoint_phaseOne, hphaseOne, boolValue])
    hcontrol hextension hLR hR hleftP hrightP htail
  dsimp only at hblock
  rw [hsubTarget, hsubSign] at hblock
  rw [← checkpoint_workOne s, ← writeField_subfield hfit] at hblock
  exact hblock

def phaseOneRemainderCheckpoint (s : State) : Nat :=
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let resultWord := if take then targetWord - s.rPrime else targetWord
  let takeBit := if take then 1 else 0
  writeField
    (writeField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
      (PackedStepLayout.workOneOffset + left) width
      (reverseBits width resultWord))
    PackedStepLayout.signWire 1 takeBit

theorem phaseOneRemainderCheckpoint_workOne
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth 256 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
    readField (phaseOneRemainderCheckpoint s)
        PackedStepLayout.workOneOffset 259 =
      writeField (encodeWork1 256 s % 2 ^ 259)
        left width (reverseBits width resultWord) := by
  dsimp only
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
    h hphaseOne hphaseTwo
  dsimp only at hbounds
  have hLR : left ≤ right := by
    simpa [left, right] using hbounds.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hbounds.2.1
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hupdatedBound : writeField
      (readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.workOneOffset 259)
      left width
      (reverseBits width
        (if shifted s.rPrime (s.shift - 1) ≤ s.r then
          s.r >>> (s.shift - 1) - s.rPrime else s.r >>> (s.shift - 1))) <
      2 ^ 259 :=
    writeField_lt hfit
      (readField_lt (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
        PackedStepLayout.workOneOffset 259)
  change readField
      (writeField
        (writeField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
          (PackedStepLayout.workOneOffset + left) width
          (reverseBits width
            (if shifted s.rPrime (s.shift - 1) ≤ s.r then
              s.r >>> (s.shift - 1) - s.rPrime else
              s.r >>> (s.shift - 1))))
        PackedStepLayout.signWire 1
        (if shifted s.rPrime (s.shift - 1) ≤ s.r then 1 else 0))
      PackedStepLayout.workOneOffset 259 = _
  rw [readField_writeField_of_disjoint (by decide +kernel),
    writeField_subfield hfit, readField_writeField,
    Nat.mod_eq_of_lt hupdatedBound, checkpoint_workOne]

theorem remainderFlip_act_phaseOnePostSub
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth 256 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let resultSign := if take then 1 else 0
    let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
    let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
    actGates PackedPhaseFourPrefix.remainderFlipGates S =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 resultSign := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let resultSign := if take then 1 else 0
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hR : right < 259 := by
    dsimp [right, workWidth]
    omega
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hsub := remainderSubBlock_act_phaseOne h hphaseOne hphaseTwo
  dsimp only at hsub
  have hS : S =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 subSign := by
    simpa [S, I, k, left, right, width, take, targetWord, subWord,
      subSign] using hsub
  have hp1S : bitValue S PackedStepLayout.phaseOneWire = 0 := by
    rw [hS, bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseOneWire, PackedStepLayout.shiftOffset]
        omega))]
    simpa [I, hphaseOne, boolValue] using checkpoint_phaseOne s
  have hp2S : bitValue S PackedStepLayout.phaseTwoWire = 1 := by
    rw [hS, bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseTwoWire, PackedStepLayout.phaseOneWire,
          PackedStepLayout.shiftOffset]
        omega))]
    simpa [I, hphaseTwo, boolValue] using checkpoint_phaseTwo s
  rw [PackedPhaseFourPrefix.remainderFlip_act hp1S hp2S, hS,
    bitValue_write_self, writeField_writeField]
  by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r <;>
    simp [I, left, right, width, take, k, targetWord, subWord, subSign,
      resultSign, htake]

theorem remainderAddBlock_act_phaseOnePostSub
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    let take := shifted s.rPrime (s.shift - 1) ≤ s.r
    let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
    let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
    let F := actGates PackedPhaseFourPrefix.remainderFlipGates S
    actGates PackedPhaseFourPrefix.remainderAddBlock F =
      if take then F else I := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let resultSign := if take then 1 else 0
  let base := encodeWork1 256 s % 2 ^ 259
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
  let F := actGates PackedPhaseFourPrefix.remainderFlipGates S
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hR : right < 259 := by
    dsimp [right, workWidth]
    omega
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hpost := remainderFlip_act_phaseOnePostSub h hphaseOne hphaseTwo
  dsimp only at hpost
  have hF : F =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 resultSign := by
    simpa [F, S, I, k, left, right, width, take, targetWord, subWord,
      resultSign] using hpost
  have hread (off len : Nat) (hoff : 259 ≤ off)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField F off len = readField I off len := by
    rw [hF, readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset]
        omega))]
  have hp1F : bitValue F PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    simpa [I, hphaseOne, boolValue] using checkpoint_phaseOne s
  have hp2F : bitValue F PackedStepLayout.phaseTwoWire = 1 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    simpa [I, hphaseTwo, boolValue] using checkpoint_phaseTwo s
  have hextensionF : bitValue F PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    exact checkpoint_extension s
  have hpoolF : readField F PackedStepLayout.poolOffset 13 = 0 := by
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    exact checkpoint_pool s
  have hcontrolF :
      bitValue F PackedPhaseFourPrefix.controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [PackedPhaseFourPrefix.controlWire])
      (by simp [PackedPhaseFourPrefix.controlWire]) hpoolF
  have htailF : readField F (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpoolF
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphaseOne, hphaseTwo] at hready
  have hsignI : bitValue I PackedStepLayout.signWire = 0 := by
    simpa [I, hready.1, boolValue] using checkpoint_sign s
  by_cases htake : take
  · rw [if_pos htake]
    have hsignF : bitValue F PackedStepLayout.signWire = 1 := by
      rw [hF, bitValue_write_self]
      simp [resultSign, htake]
    exact PackedPhaseFourPrefix.remainderAddBlock_identity_phaseOne
      hp1F hp2F hsignF hextensionF hpoolF
  · rw [if_neg htake]
    have htakeLogical : ¬ shifted s.rPrime (s.shift - 1) ≤ s.r := by
      simpa [take, k] using htake
    have hsignF : bitValue F PackedStepLayout.signWire = 0 := by
      rw [hF, bitValue_write_self]
      simp [resultSign, htake]
    let C := writeField F PackedPhaseFourPrefix.controlWire 1 1
    let P := actGates PackedStepLayout.remainderPrepareGates C
    let input := PackedInterval.remainderInput P
    have hscratchC :
        readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_narrow (by omega) htailF
    have hcarryC : bitValue C (PackedStepLayout.poolOffset + 10) = 0 := by
      rw [← readField_one]
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_sub_zero (by omega) (by omega) htailF
    have hprepare := PackedEndpointState.remainderPrepare_act_mod
      (I := C) hscratchC hcarryC
    have hlenTC : readField C PackedStepLayout.lengthTOffset 9 =
        encodeLength 9 s.lenT := by
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        hread _ _ (by decide +kernel) (by decide +kernel)]
      exact checkpoint_lengthT s
    have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
        encodeLength 9 s.lenQ := by
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        hread _ _ (by decide +kernel) (by decide +kernel)]
      exact checkpoint_lengthQ s
    have hshiftC : readField C PackedStepLayout.shiftOffset 9 =
        encodeLength 9 (s.shift - 1) := by
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        hread _ _ (by decide +kernel) (by decide +kernel)]
      exact checkpoint_shift s
    have hleftP : readField P PackedStepLayout.lengthTOffset 9 = left := by
      simp only [P]
      rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField, hlenTC, hlenQC, Nat.mod_mod]
      simpa [left] using StepState.phaseOne_remainderLeftEndpoint
        h (by norm_num [workWidth]) hphaseOne hphaseTwo
    have hrightP : readField P PackedStepLayout.shiftOffset 9 = right := by
      simp only [P]
      rw [hprepare, readField_writeField, Nat.mod_mod, hshiftC]
      have hencode : encodeLength 9 (s.shift - 1) < 2 ^ 9 :=
        encodeLength_lt 9 _
      have hreassociate :
          257 + 2 ^ 9 - encodeLength 9 (s.shift - 1) =
            257 + (2 ^ 9 - encodeLength 9 (s.shift - 1)) := by
        omega
      rw [hreassociate]
      simpa [right] using StepState.phaseOne_remainderRightEndpoint
        h (by norm_num [workWidth]) hphaseOne hphaseTwo
    have hworkTwoP : readField P PackedStepLayout.workTwoOffset 259 =
        encodeWork2 256 { s with shift := s.shift - 1 } := by
      simp only [P]
      rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        hread _ _ (by decide +kernel) (by decide +kernel)]
      exact checkpoint_workTwo s
    have hdecoded := StepState.phaseOne_remainderDecodedSubValues
      h hphaseOne hphaseTwo
    dsimp only at hdecoded
    have hx : subWord = Adder.difference width s.rPrime targetWord := by
      exact hdecoded.1.symm
    have hbaseRead : readField I PackedStepLayout.workOneOffset 259 =
        base := by
      simpa [I, base] using checkpoint_workOne s
    have hupdatedBound :
        writeField base left width (reverseBits width subWord) < 2 ^ 259 :=
      writeField_lt hfit (Nat.mod_lt _ (Nat.two_pow_pos 259))
    have hworkOneF : readField F PackedStepLayout.workOneOffset 259 =
        writeField base left width (reverseBits width subWord) := by
      rw [hF, readField_writeField_of_disjoint (by decide +kernel),
        writeField_subfield hfit, readField_writeField, hbaseRead,
        Nat.mod_eq_of_lt hupdatedBound]
    have hworkOneP : readField P PackedStepLayout.workOneOffset 259 =
        writeField base left width (reverseBits width subWord) := by
      simp only [P]
      rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      simp only [C]
      rw [readField_writeField_of_disjoint (by decide +kernel), hworkOneF]
    have hsourceFull : readField input Interval.sourceOffset 259 =
        encodeWork2 256 { s with shift := s.shift - 1 } := by
      calc
        readField input Interval.sourceOffset 259 =
            readField P PackedStepLayout.workTwoOffset 259 := by
          simpa [input, PackedStepLayout.intervalLayout,
            PackedStepLayout.remainderIntervalWiring, Interval.sourceOffset,
            Layout.read, Layout.offset, Layout.size] using
            PackedInterval.remainderInput_field 0 P (by decide)
        _ = _ := hworkTwoP
    have htargetFull : readField input (Interval.targetOffset 259) 259 =
        writeField base left width
          (reverseBits width (Adder.difference width s.rPrime targetWord)) := by
      calc
        readField input (Interval.targetOffset 259) 259 =
            readField P PackedStepLayout.workOneOffset 259 := by
          simpa [input, PackedStepLayout.intervalLayout,
            PackedStepLayout.remainderIntervalWiring, Interval.targetOffset,
            Layout.read, Layout.offset, Layout.size] using
            PackedInterval.remainderInput_field 1 P (by decide)
        _ = writeField base left width (reverseBits width subWord) :=
          hworkOneP
        _ = _ := by rw [hx]
    have hpure := StepState.phaseOne_remainderOperands
      h (by decide) hphaseOne hphaseTwo
    dsimp only at hpure
    have hsourceValue : reverseBits width
        (readField input (Interval.sourceOffset + left) width) =
          s.rPrime := by
      have hpureSource := hpure.2.1
      rw [hpure.1] at hpureSource
      rw [← hpureSource]
      rw [← readField_readField hfit, hsourceFull]
    have hbaseSlice : readField base left width =
        readField (encodeWork1 256 s) left width := by
      apply Nat.eq_of_testBit_eq
      intro b
      simp only [base]
      rw [testBit_readField, testBit_readField]
      by_cases hb : b < width
      · simp [hb, Nat.testBit_mod_two_pow,
          show left + b < 259 by omega]
      · simp [hb]
    have horiginal : reverseBits width (readField base left width) =
        targetWord := by
      have hpureTarget := hpure.2.2.2.1
      rw [hpure.2.2.1] at hpureTarget
      change reverseBits width
        (readField (encodeWork1 256 s) left width) = targetWord at hpureTarget
      rw [hbaseSlice]
      exact hpureTarget
    have hbounds := StepState.phaseOne_remainderOperandBounds
      h hphaseOne hphaseTwo
    dsimp only at hbounds
    have htargetRestored :
        StepPlaced.intervalAddTargetValue left right 259 9 input = base := by
      exact StepPlaced.intervalAddTargetValue_difference hfit htargetFull
        hsourceValue horiginal hbounds.1 hbounds.2
    have hblock := PackedPhaseFourPrefix.remainderAddBlock_act
      (I := F) (left := left) (right := right) hp1F hp2F hsignF
      hcontrolF hextensionF hLR hR hleftP hrightP htailF
    dsimp only at hblock
    rw [htargetRestored] at hblock
    have hresultSign : resultSign = 0 := by
      simp [resultSign, htake]
    have hrestore :
        writeField F PackedStepLayout.workOneOffset 259 base = I := by
      rw [hF, writeField_comm (by decide +kernel),
        writeField_subfield hfit, writeField_writeField,
        ← hbaseRead, writeField_read,
        hresultSign, ← hsignI, ← readField_one, writeField_read]
    exact hblock.trans hrestore

theorem remainderBody_act_phaseOneCheckpoint
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    actGates
        (PackedPhaseFourPrefix.remainderSubBlock ++
          PackedPhaseFourPrefix.remainderFlipGates ++
          PackedPhaseFourPrefix.remainderAddBlock)
        (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s) =
      phaseOneRemainderCheckpoint s := by
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let resultWord := if take then targetWord - s.rPrime else targetWord
  let takeBit := if take then 1 else 0
  let base := encodeWork1 256 s % 2 ^ 259
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
  let F := actGates PackedPhaseFourPrefix.remainderFlipGates S
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hR : right < 259 := by
    dsimp [right, workWidth]
    omega
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hadd := remainderAddBlock_act_phaseOnePostSub
    h hphaseOne hphaseTwo
  dsimp only at hadd
  have hpost := remainderFlip_act_phaseOnePostSub h hphaseOne hphaseTwo
  dsimp only at hpost
  have hbaseRead : readField I PackedStepLayout.workOneOffset 259 =
      base := by
    simpa [I, base] using checkpoint_workOne s
  have hISlice :
      readField I (PackedStepLayout.workOneOffset + left) width =
        readField base left width := by
    calc
      readField I (PackedStepLayout.workOneOffset + left) width =
          readField
            (readField I PackedStepLayout.workOneOffset 259) left width := by
        symm
        simpa using readField_readField (i := I)
          (D := PackedStepLayout.workOneOffset) (W := 259)
          (off := left) (len := width) hfit
      _ = readField base left width := by rw [hbaseRead]
  have hbaseSlice : readField base left width =
      readField (encodeWork1 256 s) left width := by
    apply Nat.eq_of_testBit_eq
    intro b
    simp only [base]
    rw [testBit_readField, testBit_readField]
    by_cases hb : b < width
    · simp [hb, Nat.testBit_mod_two_pow,
        show left + b < 259 by omega]
    · simp [hb]
  have hpure := StepState.phaseOne_remainderOperands
    h (by decide) hphaseOne hphaseTwo
  dsimp only at hpure
  have hpureTarget := hpure.2.2.2.1
  rw [hpure.2.2.1] at hpureTarget
  change reverseBits width
    (readField (encodeWork1 256 s) left width) = targetWord at hpureTarget
  have htargetPhysical :
      readField I (PackedStepLayout.workOneOffset + left) width =
        reverseBits width targetWord := by
    rw [hISlice, hbaseSlice, ← hpureTarget]
    exact (reverseBits_involutive
      (readField_lt (encodeWork1 256 s) left width)).symm
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphaseOne, hphaseTwo] at hready
  have hsignI : bitValue I PackedStepLayout.signWire = 0 := by
    simpa [I, hready.1, boolValue] using checkpoint_sign s
  have hcanonical : (if take then F else I) =
      phaseOneRemainderCheckpoint s := by
    by_cases htake : take
    · rw [if_pos htake]
      simpa [F, S, I, phaseOneRemainderCheckpoint, k, left, right, width,
        take, targetWord, resultWord, takeBit, htake] using hpost
    · rw [if_neg htake]
      have htakeLogical : ¬ shifted s.rPrime (s.shift - 1) ≤ s.r := by
        simpa [take, k] using htake
      have hcheckpoint : phaseOneRemainderCheckpoint s =
          writeField
            (writeField I (PackedStepLayout.workOneOffset + left) width
              (reverseBits width targetWord))
            PackedStepLayout.signWire 1 0 := by
        simp [phaseOneRemainderCheckpoint, I, left, right, width,
          targetWord, k, htakeLogical]
      rw [hcheckpoint]
      symm
      rw [← htargetPhysical, writeField_read,
        ← hsignI, ← readField_one, writeField_read]
  simp only [actGates_append]
  change actGates PackedPhaseFourPrefix.remainderAddBlock F = _
  exact hadd.trans hcanonical

theorem remainderBlocks_act_phaseOneCheckpoint
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourPrefix.remainderBlocks
        (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s) =
      phaseOneRemainderCheckpoint s := by
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let R := phaseOneRemainderCheckpoint s
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hLR : left ≤ right := by
    dsimp [left, right]
    omega
  have hRbound : right < 259 := by
    dsimp [right, workWidth]
    omega
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hlengthRPrimeFit : s.lenRPrime < 2 ^ 8 := by
    norm_num
    omega
  have hsourceI :
      readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
        encodedZero 8 := by
    have hlengthRead :
        readField I PackedStepLayout.lengthRPrimeOffset 8 =
          encodeLength 8 s.lenRPrime := by
      calc
        readField I PackedStepLayout.lengthRPrimeOffset 8 =
            readField (PackedState.encoded s)
              PackedStepLayout.lengthRPrimeOffset 8 := by
          simpa [I] using checkpoint_read
            (s := s) (off := PackedStepLayout.lengthRPrimeOffset) (width := 8)
            (by decide +kernel) (by decide +kernel)
        _ = encodeLength 8 s.lenRPrime := PackedState.read_lengthRPrime s
    rw [hlengthRead]
    exact (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).not.mpr
      (Nat.ne_of_gt hlengthRPrimePositive)
  have hextensionI : bitValue I PackedStepLayout.extensionWire = 0 := by
    simpa [I] using checkpoint_extension s
  have hpoolI : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using checkpoint_pool s
  have hscratchI :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpoolI
  have hselectI :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = I :=
    PackedPhaseFourPrefix.rPrimeSelector_identity
      hsourceI hextensionI hscratchI
  have hbody : actGates
      (PackedPhaseFourPrefix.remainderSubBlock ++
        PackedPhaseFourPrefix.remainderFlipGates ++
        PackedPhaseFourPrefix.remainderAddBlock) I = R := by
    simpa [I, R] using remainderBody_act_phaseOneCheckpoint
      h hphaseOne hphaseTwo
  have hbody' :
      actGates PackedPhaseFourPrefix.remainderAddBlock
          (actGates PackedPhaseFourPrefix.remainderFlipGates
            (actGates PackedPhaseFourPrefix.remainderSubBlock I)) = R := by
    simpa only [actGates_append] using hbody
  have hRread (off len : Nat) (hoff : 259 ≤ off)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField R off len = readField I off len := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset]
        omega))]
  have hsourceR :
      readField R PackedStepLayout.lengthRPrimeOffset 8 ≠
        encodedZero 8 := by
    rw [hRread _ _ (by decide +kernel) (by decide +kernel)]
    exact hsourceI
  have hextensionR : bitValue R PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hRread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    exact hextensionI
  have hscratchR :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    rw [hRread _ _ (by decide +kernel) (by decide +kernel)]
    exact hscratchI
  have hselectR :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates R = R :=
    PackedPhaseFourPrefix.rPrimeSelector_identity
      hsourceR hextensionR hscratchR
  have hselectReverseR :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse R = R := by
    have hinverse := actGates_reverse
      (w := PackedStepLayout.width)
      PackedPhaseFourPrefix.rPrimeSelector_wellFormed R
    rw [hselectR] at hinverse
    exact hinverse
  simp only [PackedPhaseFourPrefix.remainderBlocks, Step.around,
    actGates_append]
  rw [show PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s = I by rfl,
    hselectI, hbody', hselectReverseR]

theorem quotientIncrementBlock_act_phaseOneRemainderCheckpoint
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    actGates PackedPhaseFourPrefix.quotientIncrementBlock
        (phaseOneRemainderCheckpoint s) =
      writeField (phaseOneRemainderCheckpoint s)
        PackedStepLayout.lengthQOffset 9
        (encodeLength 9 (s.lenQ + 1)) := by
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let R := phaseOneRemainderCheckpoint s
  have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
    h hphaseOne hphaseTwo
  dsimp only at hbounds
  have hLR : left ≤ right := by
    simpa [left, right] using hbounds.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hbounds.2.1
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hphaseOneR : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseOneWire, PackedStepLayout.shiftOffset]
        omega))]
    simpa [hphaseOne, boolValue] using checkpoint_phaseOne s
  have hphaseTwoR : bitValue R PackedStepLayout.phaseTwoWire = 1 := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseTwoWire, PackedStepLayout.phaseOneWire,
          PackedStepLayout.shiftOffset]
        omega))]
    simpa [hphaseTwo, boolValue] using checkpoint_phaseTwo s
  have hpoolR : readField R PackedStepLayout.poolOffset 13 = 0 := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.poolOffset]
        omega))]
    exact checkpoint_pool s
  have hlengthQR : readField R PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.lengthQOffset]
        omega))]
    exact checkpoint_lengthQ s
  rw [PackedPhaseFourPrefix.quotientIncrementBlock_act
      hphaseOneR hphaseTwoR hpoolR,
    hlengthQR,
    encodeLength_succ
      (ReachableStepDomain.phaseOne_lenQ_noWrap
        h (by norm_num [workWidth]) hphaseOne hphaseTwo)]

def phaseOnePostSwapCheckpoint (s : State) : Nat :=
  let Q := writeField (phaseOneRemainderCheckpoint s)
    PackedStepLayout.lengthQOffset 9
    (encodeLength 9 (s.lenQ + 1))
  writeField
    (writeField Q PackedStepLayout.workOneOffset 259
      (encodeWork1 256 (step 9 9 s) % 2 ^ 259))
    PackedStepLayout.signWire 1 0

theorem swapBlock_act_phaseOnePostSwapCheckpoint
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    let Q := writeField (phaseOneRemainderCheckpoint s)
      PackedStepLayout.lengthQOffset 9
      (encodeLength 9 (s.lenQ + 1))
    actGates PackedPhaseFourPrefix.swapBlock Q =
      phaseOnePostSwapCheckpoint s := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let takeBit := if take then 1 else 0
  let resultWord := if take then s.r >>> k - s.rPrime else s.r >>> k
  let R := phaseOneRemainderCheckpoint s
  let Q := writeField R PackedStepLayout.lengthQOffset 9
    (encodeLength 9 (s.lenQ + 1))
  let I := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hwindow := ReachableStepDomain.phaseOne_window
    h hphaseOne hphaseTwo
  have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
    h hphaseOne hphaseTwo
  dsimp only at hbounds
  have hLR : left ≤ right := by
    simpa [left, right] using hbounds.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hbounds.2.1
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hleftBound : left < 259 := by
    dsimp [left]
    norm_num [workWidth] at hwindow
    omega
  have hwidthPos : 0 < width := by
    dsimp [width, right, left]
    omega
  have hQread (off len : Nat)
      (hout : PackedStepLayout.lengthQOffset + 9 ≤ off ∨
        off + len ≤ PackedStepLayout.lengthQOffset) :
      readField Q off len = readField R off len := by
    simp only [Q]
    exact readField_writeField_of_disjoint hout
  have hQbit (q : Nat)
      (hout : PackedStepLayout.lengthQOffset + 9 ≤ q ∨
        q + 1 ≤ PackedStepLayout.lengthQOffset) :
      bitValue Q q = bitValue R q := by
    simpa [readField_one] using hQread q 1 hout
  have hRread (off len : Nat)
      (hwork : 259 ≤ off)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField R off len = readField I off len := by
    simp only [R, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset]
        omega))]
  have hphaseOneQ : bitValue Q PackedStepLayout.phaseOneWire = 0 := by
    exact (hQbit _ (by decide +kernel)).trans <| by
      rw [← readField_one, hRread _ _ (by decide +kernel) (by decide +kernel),
        readField_one]
      simpa [I, hphaseOne, boolValue] using checkpoint_phaseOne s
  have hphaseTwoQ : bitValue Q PackedStepLayout.phaseTwoWire = 1 := by
    exact (hQbit _ (by decide +kernel)).trans <| by
      rw [← readField_one, hRread _ _ (by decide +kernel) (by decide +kernel),
        readField_one]
      simpa [I, hphaseTwo, boolValue] using checkpoint_phaseTwo s
  have hpoolQ : readField Q PackedStepLayout.poolOffset 13 = 0 := by
    rw [hQread _ _ (by decide +kernel),
      hRread _ _ (by decide +kernel) (by decide +kernel)]
    simpa [I] using checkpoint_pool s
  have hlenTQ : readField Q PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
    rw [hQread _ _ (by decide +kernel),
      hRread _ _ (by decide +kernel) (by decide +kernel)]
    simpa [I] using checkpoint_lengthT s
  have hlenQQ : readField Q PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 (s.lenQ + 1) := by
    simp only [Q]
    rw [readField_writeField_self (encodeLength_lt 9 _)]
  have hsignR : bitValue R PackedStepLayout.signWire = takeBit := by
    by_cases htake : take <;>
      simp [R, phaseOneRemainderCheckpoint, takeBit, take, k,
        htake, bitValue_write_self]
  have hsignQ : bitValue Q PackedStepLayout.signWire = takeBit := by
    exact (hQbit _ (by decide +kernel)).trans hsignR
  have hRwork : readField R PackedStepLayout.workOneOffset 259 =
      writeField (encodeWork1 256 s % 2 ^ 259)
        left width (reverseBits width resultWord) := by
    simpa [R, k, left, right, width, take, resultWord] using
      phaseOneRemainderCheckpoint_workOne h hphaseOne hphaseTwo
  have hQwork : readField Q PackedStepLayout.workOneOffset 259 =
      writeField (encodeWork1 256 s % 2 ^ 259)
        left width (reverseBits width resultWord) := by
    rw [hQread _ _ (by decide +kernel)]
    exact hRwork
  have hnewRFit :
      (if take then s.r - shifted s.rPrime k else s.r) <
        2 ^ (workWidth 256 - (left + 1)) := by
    simpa [take, k, left, Nat.add_assoc] using
      ReachableStepDomain.phaseOne_remainderFit_after_step
        h hphaseOne hphaseTwo
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
        2 ^ (workWidth 256 - (left + 1)) := by
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
  have hRbit : bitValue R (PackedStepLayout.workOneOffset + left) = 0 := by
    have htest : R.testBit (PackedStepLayout.workOneOffset + left) = false := by
      simp only [R, phaseOneRemainderCheckpoint]
      rw [testBit_writeField_outside (Or.inl (by
          simp [PackedStepLayout.signWire, PackedStepLayout.workOneOffset]
          omega)),
        testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
      exact hresultFirst
    simp [bitValue, htest]
  have hQbitAtLeft : bitValue Q
      (PackedStepLayout.workOneOffset + left) = 0 := by
    exact (hQbit _ (Or.inr (by
      simp [PackedStepLayout.lengthQOffset,
        PackedStepLayout.workOneOffset]
      omega))).trans hRbit
  have htPos : 0 < s.t := h.positiveLiveCoefficient hstate.1
  have hlenTPos : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPos
  have hencodedLenT : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPos),
      Nat.mod_eq_of_lt (by
        have := h.stepDomain.valid.1.2.2.1
        omega)]
  have hencodedLenQ : encodeLength 9 (s.lenQ + 1) = s.lenQ := by
    rw [encodeLength, if_neg (by omega), Nat.add_sub_cancel,
      Nat.mod_eq_of_lt h.stepDomain.valid.1.2.2.2.1]
  have htfit : readField Q PackedStepLayout.lengthTOffset 9 +
      readField Q PackedStepLayout.lengthQOffset 9 + 2 < 2 ^ 9 := by
    rw [hlenTQ, hlenQQ, hencodedLenT, hencodedLenQ]
    omega
  have hjValue : readField Q PackedStepLayout.lengthTOffset 9 +
      readField Q PackedStepLayout.lengthQOffset 9 + 2 = left := by
    rw [hlenTQ, hlenQQ, hencodedLenT, hencodedLenQ]
    dsimp [left]
    omega
  have hswap := PackedPhaseFourPrefix.swapBlock_act_phaseOne
    (I := Q) (j := left) hleftBound hphaseOneQ hphaseTwoQ hpoolQ
    htfit hjValue
  rw [hsignQ, hQbitAtLeft, hQwork] at hswap
  have hsemantic :=
    ReachableStepDomain.phaseOne_work1_after_quotientInsertion
      h (by norm_num [workWidth]) hphaseOne hphaseTwo
  dsimp only at hsemantic
  have hsemantic' :
      writeField
          (writeField (encodeWork1 256 s % 2 ^ 259)
            left width (reverseBits width resultWord))
          left 1 takeBit =
        encodeWork1 256 (step 9 9 s) % 2 ^ 259 := by
    simpa [k, left, right, width, take, resultWord, takeBit, workWidth]
      using hsemantic
  rw [hswap, hsemantic']
  rfl

theorem gates_act_phaseOne
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourPrefix.gates (PackedState.encoded s) =
      phaseOnePostSwapCheckpoint s := by
  let P := phaseOnePostSwapCheckpoint s
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
    h hphaseOne hphaseTwo
  dsimp only at hbounds
  have hLR : left ≤ right := by
    simpa [left, right] using hbounds.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hbounds.2.1
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hphaseTwoP : bitValue P PackedStepLayout.phaseTwoWire = 1 := by
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel))]
    simp only [phaseOneRemainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseTwoWire]
        dsimp [left, width, right] at hfit
        omega))]
    simpa [hphaseTwo, boolValue] using checkpoint_phaseTwo s
  have hpoolP : readField P PackedStepLayout.poolOffset 13 = 0 := by
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (Or.inl (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.poolOffset]
        dsimp [left, width, right] at hfit
        omega))]
    exact checkpoint_pool s
  have hqdec : actGates PackedPhaseFourPrefix.quotientDecrementBlock P = P :=
    PackedPhaseFourPrefix.quotientDecrementBlock_identity hphaseTwoP hpoolP
  have hpre := PackedPhaseFourPrefix.preShiftBlock_act_phaseOne
    hphaseOne hphaseTwo hstate.2.1
      h.stepDomain.valid.1.2.2.2.2.2.1
  have hrem := remainderBlocks_act_phaseOneCheckpoint
    h hphaseOne hphaseTwo hlengthRPrimeBound
  have hqinc := quotientIncrementBlock_act_phaseOneRemainderCheckpoint
    h hphaseOne hphaseTwo
  have hswap := swapBlock_act_phaseOnePostSwapCheckpoint
    h hphaseOne hphaseTwo
  simp only [PackedPhaseFourPrefix.gates, actGates_append]
  rw [hpre, hrem, hqinc, hswap, show phaseOnePostSwapCheckpoint s = P by rfl,
    hqdec]

theorem phaseOnePostSwapCheckpoint_eq_encoded
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true) :
    phaseOnePostSwapCheckpoint s =
      PackedState.encoded
        { step 9 9 s with phase1 := false, phase2 := true } := by
  let L := PackedStepLayout.layout
  let s' := step 9 9 s
  let s01 : State := { s' with phase1 := false, phase2 := true }
  let P := phaseOnePostSwapCheckpoint s
  let left := s.lenT + 1 + s.lenQ
  let right := workWidth 256 - s.shift
  let width := right - left + 1
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hbounds := ReachableStepDomain.phaseOne_remainderEndpointFacts
    h hphaseOne hphaseTwo
  dsimp only at hbounds
  have hLR : left ≤ right := by
    simpa [left, right] using hbounds.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hbounds.2.1
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hworkWrite :
      PackedStepLayout.workOneOffset + left + width ≤
        PackedStepLayout.width := by
    have hwidth : PackedStepLayout.width = 571 :=
      PackedStepLayout.layout_width
    simp only [PackedStepLayout.workOneOffset, hwidth]
    omega
  have hpreLt :
      PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s <
        2 ^ PackedStepLayout.width := by
    exact writeField_lt (by decide +kernel)
      (writeField_lt (by decide +kernel) (PackedState.encoded_lt s))
  have hremLt : phaseOneRemainderCheckpoint s <
      2 ^ PackedStepLayout.width := by
    exact writeField_lt (by decide +kernel)
      (writeField_lt hworkWrite hpreLt)
  have hPLt : P < 2 ^ L.width := by
    dsimp only [P, phaseOnePostSwapCheckpoint]
    exact writeField_lt (by decide +kernel)
      (writeField_lt (by decide +kernel)
        (writeField_lt (by decide +kernel) hremLt))
  have hPreadPre (off fieldWidth : Nat)
      (hoff : 259 ≤ off)
      (hlenQ : PackedStepLayout.lengthQOffset + 9 ≤ off ∨
        off + fieldWidth ≤ PackedStepLayout.lengthQOffset)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + fieldWidth ≤ PackedStepLayout.signWire) :
      readField P off fieldWidth =
        readField (PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s)
          off fieldWidth := by
    simp only [P, phaseOnePostSwapCheckpoint, phaseOneRemainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simpa [PackedStepLayout.workOneOffset] using hoff)),
      readField_writeField_of_disjoint hlenQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint (Or.inl (by
        simp only [PackedStepLayout.workOneOffset, Nat.zero_add]
        omega))]
  apply Layout.ext hPLt (PackedState.encoded_lt s01)
  intro j hj
  have hj' : j < 12 := by
    simpa [L, PackedStepLayout.layout] using hj
  interval_cases j
  · change readField P PackedStepLayout.workOneOffset 259 =
      readField (PackedState.encoded s01) PackedStepLayout.workOneOffset 259
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField, Nat.mod_mod, PackedState.read_workOne]
    simp [s01, s', encodeWork1]
  · change readField P PackedStepLayout.workTwoOffset 259 =
      readField (PackedState.encoded s01) PackedStepLayout.workTwoOffset 259
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), checkpoint_workTwo, PackedState.read_workTwo]
    simp [s01, s', hstep, encodeWork2, encodeWork2Raw]
  · change readField P PackedStepLayout.lengthTOffset 9 =
      readField (PackedState.encoded s01) PackedStepLayout.lengthTOffset 9
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), checkpoint_lengthT, PackedState.read_lengthT]
    simp [s01, s', hstep]
  · change readField P PackedStepLayout.lengthQOffset 9 =
      readField (PackedState.encoded s01) PackedStepLayout.lengthQOffset 9
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField, Nat.mod_eq_of_lt (encodeLength_lt 9 _),
      PackedState.read_lengthQ]
    simp [s01, s', hstep]
  · change readField P PackedStepLayout.lengthRPrimeOffset 8 =
      readField (PackedState.encoded s01)
        PackedStepLayout.lengthRPrimeOffset 8
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel)]
    rw [checkpoint_read (by decide +kernel) (by decide +kernel)]
    rw [PackedState.read_lengthRPrime, PackedState.read_lengthRPrime]
    simp [s01, s', hstep]
  · change readField P PackedStepLayout.extensionWire 1 =
      readField (PackedState.encoded s01) PackedStepLayout.extensionWire 1
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one,
      checkpoint_extension, PackedState.read_extension]
  · change readField P PackedStepLayout.shiftOffset 9 =
      readField (PackedState.encoded s01) PackedStepLayout.shiftOffset 9
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), checkpoint_shift, PackedState.read_shift]
    simp [s01, s', hstep]
  · change readField P PackedStepLayout.phaseOneWire 1 =
      readField (PackedState.encoded s01) PackedStepLayout.phaseOneWire 1
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one]
    rw [checkpoint_phaseOne, PackedState.read_phaseOne]
    simp [s01, hphaseOne, boolValue]
  · change readField P PackedStepLayout.phaseTwoWire 1 =
      readField (PackedState.encoded s01) PackedStepLayout.phaseTwoWire 1
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one]
    rw [checkpoint_phaseTwo, PackedState.read_phaseTwo]
    simp [s01, hphaseTwo, boolValue]
  · change readField P PackedStepLayout.iterationWire 1 =
      readField (PackedState.encoded s01) PackedStepLayout.iterationWire 1
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one]
    rw [checkpoint_bit (by decide +kernel) (by decide +kernel),
      PackedState.read_iteration, PackedState.read_iteration]
    simp [s01, s', hstep]
  · change readField P PackedStepLayout.signWire 1 =
      readField (PackedState.encoded s01) PackedStepLayout.signWire 1
    simp only [P, phaseOnePostSwapCheckpoint]
    rw [readField_writeField_self (by decide), readField_one,
      PackedState.read_sign]
    simp [s01, s', hstep, boolValue]
  · change readField P PackedStepLayout.poolOffset 13 =
      readField (PackedState.encoded s01) PackedStepLayout.poolOffset 13
    rw [hPreadPre _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel), checkpoint_pool, PackedState.read_pool]

end PackedPhaseOnePrefix
end Euclid
end VQ
