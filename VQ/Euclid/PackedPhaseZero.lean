/-
Encoded-state refinement for the packed phase-zero transition.
-/
import VQ.Euclid.PackedPhaseFourPrefix
import VQ.Euclid.PackedPhaseFourTail
import VQ.Euclid.StepState.PhaseZero

namespace VQ
namespace Euclid
namespace PackedPhaseZero

open Reversible

def preShiftState (s : State) : State :=
  { s with shift := s.shift + 1 }

theorem remainderSubBlock_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let k := s.shift + 1
    let left := s.lenT + 1
    let right := 257 - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let targetWord := s.r >>> k
    let subWord := if take then targetWord - s.rPrime
      else targetWord + (2 ^ width - s.rPrime)
    let subSign := if take then 0 else 1
    let s0 := preShiftState s
    let I := PackedState.encoded s0
    actGates PackedPhaseFourPrefix.remainderSubBlock I =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 subSign := by
  dsimp only
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := 257 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let s0 := preShiftState s
  let I := PackedState.encoded s0
  let C := writeField I PackedPhaseFourPrefix.controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  let input := PackedInterval.remainderInput P
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphaseOne hphaseTwo hrPrime
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphaseOne hphaseTwo hrPrime
  dsimp only at hendpoint
  have hLR : left ≤ right := by
    simpa [left, right] using hendpoint.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hendpoint.2
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    exact PackedState.read_pool s0
  have hcontrol : bitValue I PackedPhaseFourPrefix.controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [PackedPhaseFourPrefix.controlWire])
      (by simp [PackedPhaseFourPrefix.controlWire]) hpool
  have hextension : bitValue I PackedStepLayout.extensionWire = 0 := by
    exact PackedState.read_extension s0
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
    exact PackedState.read_lengthT s0
  have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_lengthQ s0
  have hshiftC : readField C PackedStepLayout.shiftOffset 9 =
      encodeLength 9 (s.shift + 1) := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_shift s0
  have hleftP : readField P PackedStepLayout.lengthTOffset 9 = left := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField, hlenTC, hlenQC, Nat.mod_mod]
    simpa [left] using StepState.phaseZero_remainderLeftEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo hrPrime
  have hrightP : readField P PackedStepLayout.shiftOffset 9 = right := by
    simp only [P]
    rw [hprepare, readField_writeField, Nat.mod_mod, hshiftC]
    have hencode : encodeLength 9 (s.shift + 1) < 2 ^ 9 :=
      encodeLength_lt 9 _
    have hreassociate :
        257 + 2 ^ 9 - encodeLength 9 (s.shift + 1) =
          257 + (2 ^ 9 - encodeLength 9 (s.shift + 1)) := by
      omega
    rw [hreassociate]
    simpa [right] using StepState.phaseZero_remainderRightEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo hrPrime
  have hworkOneP : readField P PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 s0 % 2 ^ 259 := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_workOne s0
  have hworkTwoP : readField P PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 s0 := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_workTwo s0
  have hsignP : bitValue P PackedStepLayout.signWire = 0 := by
    have hready := h.stepDomain.valid.2
    simp [PhaseReady, hphaseOne, hphaseTwo] at hready
    rw [← readField_one]
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel), readField_one,
      PackedState.read_sign]
    simp [s0, preShiftState, hready.1, boolValue]
  have hsourceFull : readField input Interval.sourceOffset 259 =
      encodeWork2 256 s0 := by
    calc
      readField input Interval.sourceOffset 259 =
          readField P PackedStepLayout.workTwoOffset 259 := by
        simpa [input, PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.sourceOffset,
          Layout.read, Layout.offset, Layout.size] using
          PackedInterval.remainderInput_field 0 P (by decide)
      _ = _ := hworkTwoP
  have htargetFull : readField input (Interval.targetOffset 259) 259 =
      encodeWork1 256 s0 % 2 ^ 259 := by
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
      readField input 537 1 = readField P PackedStepLayout.signWire 1 := by
        simpa [input, PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.signWire,
          Layout.read, Layout.offset, Layout.size] using
          PackedInterval.remainderInput_field 5 P (by decide)
      _ = 0 := by simpa [readField_one] using hsignP
  have hpure := StepState.phaseZero_remainderOperands
    h (by decide) hphaseOne hphaseTwo hrPrime
  dsimp only at hpure
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) = s.rPrime := by
    have hpureSource := hpure.2.1
    rw [hpure.1] at hpureSource
    rw [← hpureSource]
    rw [← readField_readField hfit, hsourceFull]
    simp [s0, preShiftState, left, width, right, workWidth]
  have htargetSlice :
      readField input (Interval.targetOffset 259 + left) width =
        readField (encodeWork1 256 s0) left width := by
    calc
      readField input (Interval.targetOffset 259 + left) width =
          readField
            (readField input (Interval.targetOffset 259) 259) left width := by
        symm
        exact readField_readField hfit
      _ = readField (encodeWork1 256 s0 % 2 ^ 259) left width := by
        rw [htargetFull]
      _ = readField (encodeWork1 256 s0) left width := by
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
      (readField (encodeWork1 256 s0) left width) = targetWord at hpureTarget
    rw [htargetSlice]
    simpa [s0, preShiftState, left, width, right, targetWord, k, workWidth]
      using hpureTarget
  have hdecoded := StepState.phaseZero_remainderDecodedSubValues
    h hphaseOne hphaseTwo hrPrime
  dsimp only at hdecoded
  have hsubTarget : StepPlaced.intervalSubTargetValue left right 259 9 input =
      writeField (encodeWork1 256 s0 % 2 ^ 259) left width
        (reverseBits width subWord) := by
    simp only [StepPlaced.intervalSubTargetValue]
    rw [htargetFull, hsourceValue, htargetValue, hdecoded.1]
  have hsubSign : StepPlaced.intervalSubSignValue left right 259 9 input =
      subSign := by
    simp only [StepPlaced.intervalSubSignValue]
    rw [hsignInput, hsourceValue, htargetValue, hdecoded.2]
    by_cases htake : shifted s.rPrime (s.shift + 1) ≤ s.r <;>
      simp [subSign, take, k, htake]
  have hblock := PackedPhaseFourPrefix.remainderSubBlock_act
    (I := I) (left := left) (right := right)
    (by simp [I, PackedState.read_phaseOne, s0, preShiftState,
      hphaseOne, boolValue])
    hcontrol hextension hLR hR hleftP hrightP htail
  dsimp only at hblock
  rw [hsubTarget, hsubSign] at hblock
  rw [← PackedState.read_workOne s0, ← writeField_subfield hfit] at hblock
  exact hblock

def remainderCheckpoint (s : State) : Nat :=
  let borrow := decide (s.r < shifted s.rPrime (s.shift + 1))
  writeField (PackedState.encoded (preShiftState s))
    PackedStepLayout.signWire 1 (boolValue borrow)

theorem remainderBody_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    actGates
        (PackedPhaseFourPrefix.remainderSubBlock ++
          PackedPhaseFourPrefix.remainderFlipGates ++
          PackedPhaseFourPrefix.remainderAddBlock)
        (PackedState.encoded (preShiftState s)) =
      remainderCheckpoint s := by
  let k := s.shift + 1
  let left := s.lenT + 1
  let right := 257 - s.shift
  let width := right - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let targetWord := s.r >>> k
  let subWord := if take then targetWord - s.rPrime
    else targetWord + (2 ^ width - s.rPrime)
  let subSign := if take then 0 else 1
  let base := encodeWork1 256 (preShiftState s) % 2 ^ 259
  let I := PackedState.encoded (preShiftState s)
  let S := actGates PackedPhaseFourPrefix.remainderSubBlock I
  let F := actGates PackedPhaseFourPrefix.remainderFlipGates S
  have hendpoint := ReachableStepDomain.phaseZero_remainderEndpointFacts
    h hphaseOne hphaseTwo hrPrime
  dsimp only at hendpoint
  have hLR : left ≤ right := by
    simpa [left, right] using hendpoint.1
  have hR : right < 259 := by
    simpa [right, workWidth] using hendpoint.2
  have hfit : left + width ≤ 259 := by
    dsimp [width]
    omega
  have hsub := remainderSubBlock_act h hphaseOne hphaseTwo hrPrime
  dsimp only at hsub
  have hS : S =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 subSign := by
    simpa [S, I, k, left, right, width, take, targetWord, subWord,
      subSign] using hsub
  have hp2S : bitValue S PackedStepLayout.phaseTwoWire = 0 := by
    rw [hS, bitValue_write_ne (by decide +kernel),
      bitValue_write_out (Or.inr (by
        simp [PackedStepLayout.workOneOffset,
          PackedStepLayout.phaseTwoWire, PackedStepLayout.phaseOneWire,
          PackedStepLayout.shiftOffset]
        omega))]
    simpa [I, PackedState.read_phaseTwo, preShiftState, hphaseTwo, boolValue]
  have hflip : F = S := by
    exact PackedPhaseFourPrefix.remainderFlip_identity_phaseTwo_clear hp2S
  have hF : F =
      writeField
        (writeField I (PackedStepLayout.workOneOffset + left) width
          (reverseBits width subWord))
        PackedStepLayout.signWire 1 subSign := hflip.trans hS
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
    simpa [I, PackedState.read_phaseOne, preShiftState, hphaseOne, boolValue]
  have hp2F : bitValue F PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    simpa [I, PackedState.read_phaseTwo, preShiftState, hphaseTwo, boolValue]
  have hextensionF : bitValue F PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one]
    exact PackedState.read_extension (preShiftState s)
  have hpoolF : readField F PackedStepLayout.poolOffset 13 = 0 := by
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_pool (preShiftState s)
  have hcontrolF : bitValue F PackedPhaseFourPrefix.controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [PackedPhaseFourPrefix.controlWire])
      (by simp [PackedPhaseFourPrefix.controlWire]) hpoolF
  have htailF : readField F (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpoolF
  let C := writeField F PackedPhaseFourPrefix.controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  let input := PackedInterval.remainderInput P
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
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
    exact PackedState.read_lengthT (preShiftState s)
  have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_lengthQ (preShiftState s)
  have hshiftC : readField C PackedStepLayout.shiftOffset 9 =
      encodeLength 9 (s.shift + 1) := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_shift (preShiftState s)
  have hleftP : readField P PackedStepLayout.lengthTOffset 9 = left := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField, hlenTC, hlenQC, Nat.mod_mod]
    simpa [left] using StepState.phaseZero_remainderLeftEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo hrPrime
  have hrightP : readField P PackedStepLayout.shiftOffset 9 = right := by
    simp only [P]
    rw [hprepare, readField_writeField, Nat.mod_mod, hshiftC]
    have hreassociate :
        257 + 2 ^ 9 - encodeLength 9 (s.shift + 1) =
          257 + (2 ^ 9 - encodeLength 9 (s.shift + 1)) := by
      have hencode := encodeLength_lt 9 (s.shift + 1)
      omega
    rw [hreassociate]
    simpa [right] using StepState.phaseZero_remainderRightEndpoint
      h (by norm_num [workWidth]) hphaseOne hphaseTwo hrPrime
  have hdecoded := StepState.phaseZero_remainderDecodedSubValues
    h hphaseOne hphaseTwo hrPrime
  dsimp only at hdecoded
  have hx : subWord = Adder.difference width s.rPrime targetWord := by
    exact hdecoded.1.symm
  have hbaseRead : readField I PackedStepLayout.workOneOffset 259 = base := by
    simpa [I, base] using PackedState.read_workOne (preShiftState s)
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
  have hworkTwoP : readField P PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 (preShiftState s) := by
    simp only [P]
    rw [hprepare, readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_workTwo (preShiftState s)
  have hsourceFull : readField input Interval.sourceOffset 259 =
      encodeWork2 256 (preShiftState s) := by
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
      _ = writeField base left width (reverseBits width subWord) := hworkOneP
      _ = _ := by rw [hx]
  have hpure := StepState.phaseZero_remainderOperands
    h (by decide) hphaseOne hphaseTwo hrPrime
  dsimp only at hpure
  have hsourceValue : reverseBits width
      (readField input (Interval.sourceOffset + left) width) = s.rPrime := by
    have hpureSource := hpure.2.1
    rw [hpure.1] at hpureSource
    rw [← hpureSource]
    rw [← readField_readField hfit, hsourceFull]
    simp [preShiftState, left, width, right]
  have hbaseSlice : readField base left width =
      readField (encodeWork1 256 (preShiftState s)) left width := by
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
    rw [hbaseSlice]
    simpa [preShiftState, left, width, right, targetWord, k, workWidth]
      using hpureTarget
  have hbounds := StepState.phaseZero_remainderOperandBounds
    h hphaseOne hphaseTwo hrPrime
  dsimp only at hbounds
  have htargetRestored :
      StepPlaced.intervalAddTargetValue left right 259 9 input = base := by
    exact StepPlaced.intervalAddTargetValue_difference hfit htargetFull
      hsourceValue horiginal hbounds.1 hbounds.2
  have hblock := PackedPhaseFourPrefix.remainderAddBlock_act_phaseZero
    (I := F) (left := left) (right := right) hp1F hp2F
      hcontrolF hextensionF hLR hR hleftP hrightP htailF
  dsimp only at hblock
  rw [htargetRestored] at hblock
  have hrestore :
      writeField F PackedStepLayout.workOneOffset 259 base =
        writeField I PackedStepLayout.signWire 1 subSign := by
    rw [hF, writeField_comm (by decide +kernel),
      writeField_subfield hfit, writeField_writeField,
      ← hbaseRead, writeField_read]
  simp only [actGates_append]
  change actGates PackedPhaseFourPrefix.remainderAddBlock F = _
  rw [hblock, hrestore]
  change writeField I PackedStepLayout.signWire 1 subSign =
    writeField I PackedStepLayout.signWire 1
      (boolValue (decide (s.r < shifted s.rPrime (s.shift + 1))))
  by_cases htake : shifted s.rPrime (s.shift + 1) ≤ s.r
  · have hnlt : ¬ s.r < shifted s.rPrime (s.shift + 1) :=
      Nat.not_lt_of_ge htake
    simp [subSign, take, k, htake, hnlt, boolValue]
  · have hlt : s.r < shifted s.rPrime (s.shift + 1) :=
      Nat.lt_of_not_ge htake
    simp [subSign, take, k, htake, hlt, boolValue]

theorem remainderBlocks_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourPrefix.remainderBlocks
        (PackedState.encoded (preShiftState s)) =
      remainderCheckpoint s := by
  let I := PackedState.encoded (preShiftState s)
  let R := remainderCheckpoint s
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlengthRPrimeFit : s.lenRPrime < 2 ^ 8 := by
    norm_num
    omega
  have hsourceI :
      readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
        encodedZero 8 := by
    rw [show readField I PackedStepLayout.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime by
      simpa [I, preShiftState] using
        PackedState.read_lengthRPrime (preShiftState s)]
    exact (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).not.mpr
      (Nat.ne_of_gt hlengthRPrimePositive)
  have hextensionI : bitValue I PackedStepLayout.extensionWire = 0 := by
    simpa [I] using PackedState.read_extension (preShiftState s)
  have hpoolI : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using PackedState.read_pool (preShiftState s)
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
    simpa [I, R] using remainderBody_act
      h hphaseOne hphaseTwo hrPrime
  have hbody' :
      actGates PackedPhaseFourPrefix.remainderAddBlock
          (actGates PackedPhaseFourPrefix.remainderFlipGates
            (actGates PackedPhaseFourPrefix.remainderSubBlock I)) = R := by
    simpa only [actGates_append] using hbody
  have hRread (off len : Nat)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField R off len = readField I off len := by
    simp only [R, remainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign]
  have hsourceR :
      readField R PackedStepLayout.lengthRPrimeOffset 8 ≠
        encodedZero 8 := by
    rw [hRread _ _ (by decide +kernel)]
    exact hsourceI
  have hextensionR : bitValue R PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hRread _ _ (by decide +kernel), readField_one]
    exact hextensionI
  have hscratchR :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    rw [hRread _ _ (by decide +kernel)]
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
  rw [show PackedState.encoded (preShiftState s) = I by rfl,
    hselectI, hbody', hselectReverseR]

theorem prefixGates_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourPrefix.gates (PackedState.encoded s) =
      remainderCheckpoint s := by
  let R := remainderCheckpoint s
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphaseOne hphaseTwo hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    norm_num [workWidth] at hlive ⊢
    omega
  have hpre :
      actGates PackedPhaseFourPrefix.preShiftBlock
          (PackedState.encoded s) =
        PackedState.encoded (preShiftState s) := by
    simpa [preShiftState] using
      PackedPhaseFourPrefix.preShiftBlock_act_phaseZero
        hphaseOne hphaseTwo hlive.2.1 hshiftFit
  have hrem :
      actGates PackedPhaseFourPrefix.remainderBlocks
          (PackedState.encoded (preShiftState s)) = R := by
    simpa [R] using remainderBlocks_act
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
  have hp1R : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R, remainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel)]
    simpa [preShiftState, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2R : bitValue R PackedStepLayout.phaseTwoWire = 0 := by
    simp only [R, remainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel)]
    simpa [preShiftState, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hpoolR : readField R PackedStepLayout.poolOffset 13 = 0 := by
    simp only [R, remainderCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_pool (preShiftState s)
  simp only [PackedPhaseFourPrefix.gates, actGates_append]
  rw [hpre, hrem,
    PackedPhaseFourPrefix.quotientIncrementBlock_identity_phaseZero hp2R hpoolR,
    PackedPhaseFourPrefix.swapBlock_identity_phaseZero hp1R hp2R hpoolR,
    PackedPhaseFourPrefix.quotientDecrementBlock_identity_phaseZero hp1R hpoolR]

theorem coefficientGates_identity
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedStepLayout.coefficientGates (remainderCheckpoint s) =
      remainderCheckpoint s := by
  let R := remainderCheckpoint s
  have hread (off len : Nat)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField R off len =
        readField (PackedState.encoded (preShiftState s)) off len := by
    simp only [R, remainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign]
  have hp1R : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    simpa [preShiftState, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2R : bitValue R PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    simpa [preShiftState, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hextensionR : bitValue R PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    exact PackedState.read_extension (preShiftState s)
  have hpoolR : readField R PackedStepLayout.poolOffset 13 = 0 := by
    rw [hread _ _ (by decide +kernel)]
    exact PackedState.read_pool (preShiftState s)
  have hlengthT : readField R PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
    rw [hread _ _ (by decide +kernel)]
    exact PackedState.read_lengthT (preShiftState s)
  have hlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime := by
    rw [hread _ _ (by decide +kernel)]
    exact PackedState.read_lengthRPrime (preShiftState s)
  have hshift : readField R PackedStepLayout.shiftOffset 9 =
      encodeLength 9 (s.shift + 1) := by
    rw [hread _ _ (by decide +kernel)]
    exact PackedState.read_shift (preShiftState s)
  have htPositive := ReachableStepDomain.phaseZero_t_pos
    h hphaseOne hrPrime
  have hlenTPositive : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPositive
  have hlenRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphaseOne hphaseTwo hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    norm_num [workWidth] at hlive ⊢
    omega
  have hlenTCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive),
      Nat.mod_eq_of_lt]
    have hlength := ReachableStepDomain.phaseZero_length_shift_le
      h hphaseOne hphaseTwo hrPrime
    norm_num at ⊢
    omega
  have hlenRPrimeCode :
      encodeLength 8 s.lenRPrime = s.lenRPrime - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenRPrimePositive),
      Nat.mod_eq_of_lt]
    norm_num
    omega
  have hshiftCode :
      encodeLength 9 (s.shift + 1) = s.shift := by
    rw [encodeLength, if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  apply PackedCoefficient.gates_identity_phaseZero hp1R hp2R hextensionR
    hpoolR
  · rw [hlengthT, hlenTCode]
    norm_num
    have hlength := ReachableStepDomain.phaseZero_length_shift_le
      h hphaseOne hphaseTwo hrPrime
    omega

theorem postShiftGates_identity
    {s : State}
    (hphaseOne : s.phase1 = false) :
    actGates PackedShift.postShiftGates (remainderCheckpoint s) =
      remainderCheckpoint s := by
  let R := remainderCheckpoint s
  have hp1R : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R, remainderCheckpoint]
    rw [bitValue_write_ne (by decide +kernel)]
    simpa [preShiftState, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hpoolR : readField R PackedStepLayout.poolOffset 11 = 0 := by
    simp only [R, remainderCheckpoint]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  exact PackedShift.postShiftGates_identity_phaseOneClear hp1R hpoolR

theorem phaseGates_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedStepLayout.phaseGates (remainderCheckpoint s) =
      PackedState.encoded (step 9 9 s) := by
  let borrow := decide (s.r < shifted s.rPrime (s.shift + 1))
  let E := PackedState.encoded (preShiftState s)
  let R := remainderCheckpoint s
  have hread (off len : Nat)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.signWire) :
      readField R off len = readField E off len := by
    simp only [R, E, remainderCheckpoint]
    rw [readField_writeField_of_disjoint hsign]
  have hp1R : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    simpa [E, preShiftState, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2R : bitValue R PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    simpa [E, preShiftState, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hextensionR : bitValue R PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel), readField_one]
    exact PackedState.read_extension (preShiftState s)
  have htailR : readField R (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    rw [hread _ _ (by decide +kernel)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphaseOne hphaseTwo hrPrime
  have hlengthQ : readField R PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    rw [hread _ _ (by decide +kernel), show readField E
        PackedStepLayout.lengthQOffset 9 = encodeLength 9 s.lenQ by
      simpa [E, preShiftState] using
        PackedState.read_lengthQ (preShiftState s)]
    simp [hlive.2.1, encodeLength, encodedZero]
  have hlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime := by
    rw [hread _ _ (by decide +kernel)]
    simpa [E, preShiftState] using
      PackedState.read_lengthRPrime (preShiftState s)
  have hshift : readField R PackedStepLayout.shiftOffset 9 =
      encodeLength 9 (s.shift + 1) := by
    rw [hread _ _ (by decide +kernel)]
    simpa [E, preShiftState] using PackedState.read_shift (preShiftState s)
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    norm_num [workWidth] at hlive ⊢
    omega
  have hphase := PackedPhase.gates_act_phaseZero
    hextensionR htailR hp1R hp2R hlengthQ hlengthRPrime
    hlengthRPrimePositive hlengthRPrimeBound hshift (by omega) hshiftFit
  have hsignR : bitValue R PackedStepLayout.signWire = boolValue borrow := by
    simp only [R, remainderCheckpoint]
    rw [bitValue_write_self,
      Nat.mod_eq_of_lt (StepState.Internal.boolValue_lt borrow)]
  rw [hphase, hsignR]
  have hcommOne :
      writeField
          (writeField E PackedStepLayout.signWire 1 (boolValue borrow))
          PackedStepLayout.phaseOneWire 1 0 =
        writeField
          (writeField E PackedStepLayout.phaseOneWire 1 0)
          PackedStepLayout.signWire 1 (boolValue borrow) :=
    writeField_comm (by decide +kernel)
  have hcommTwo :
      writeField
          (writeField
            (writeField E PackedStepLayout.phaseOneWire 1 0)
            PackedStepLayout.signWire 1 (boolValue borrow))
          PackedStepLayout.phaseTwoWire 1 (boolValue borrow) =
        writeField
          (writeField
            (writeField E PackedStepLayout.phaseOneWire 1 0)
            PackedStepLayout.phaseTwoWire 1 (boolValue borrow))
          PackedStepLayout.signWire 1 (boolValue borrow) :=
    writeField_comm (by decide +kernel)
  have hnormalize :
      writeField
          (writeField
            (writeField R PackedStepLayout.phaseOneWire 1 0)
            PackedStepLayout.phaseTwoWire 1 (boolValue borrow))
          PackedStepLayout.signWire 1 0 =
        writeField
          (writeField
            (writeField E PackedStepLayout.phaseOneWire 1 0)
            PackedStepLayout.phaseTwoWire 1 (boolValue borrow))
          PackedStepLayout.signWire 1 0 := by
    simp only [R, remainderCheckpoint, E]
    rw [hcommOne, hcommTwo, writeField_writeField]
  rw [hnormalize]
  calc
    writeField
          (writeField
            (writeField E PackedStepLayout.phaseOneWire 1 0)
            PackedStepLayout.phaseTwoWire 1 (boolValue borrow))
          PackedStepLayout.signWire 1 0 =
        PackedState.encoded
          { preShiftState s with
            phase1 := false
            phase2 := borrow
            sign := false } := by
      simpa [E, boolValue] using
        PackedState.encoded_write_phaseSign
          (preShiftState s) false borrow false
    _ = PackedState.encoded (step 9 9 s) := by
      rw [ReachableStepDomain.phaseZero_step_eq
        h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo]
      simp [preShiftState, borrow, hphaseOne]

theorem ownershipGates_identity
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false) :
    actGates PackedOwnership.gates (PackedState.encoded (step 9 9 s)) =
      PackedState.encoded (step 9 9 s) := by
  have hstep := ReachableStepDomain.phaseZero_step_eq
    h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo
  have hshiftFit : s.shift + 1 < 2 ^ 9 :=
    StepDomain.increment_noWrap h.stepDomain
      (by norm_num [workWidth]) (by norm_num) hphaseTwo
  have hcontrol : bitValue (PackedState.encoded (step 9 9 s))
      PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hshift : readField (PackedState.encoded (step 9 9 s))
      PackedStepLayout.shiftOffset 9 ≠ encodedZero 9 := by
    rw [PackedState.read_shift]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff (by
      rw [hstep]
      exact hshiftFit)).mp hzero
    rw [hstep] at hdecoded
    simp at hdecoded
  have htail : readField (PackedState.encoded (step 9 9 s))
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by decide) (by decide)
  exact PackedOwnership.gates_inactive hcontrol hshift htail

theorem tailGates_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourTail.gates (remainderCheckpoint s) =
      PackedState.encoded (step 9 9 s) := by
  simp only [PackedPhaseFourTail.gates, PackedPhaseFourSuffix.gates,
    PackedPhaseOwnership.gates, actGates_append]
  rw [coefficientGates_identity h hphaseOne hphaseTwo hrPrime
      hlengthRPrimeBound,
    postShiftGates_identity hphaseOne,
    phaseGates_act h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound,
    ownershipGates_identity h hphaseOne hphaseTwo]

end PackedPhaseZero
end Euclid
end VQ
