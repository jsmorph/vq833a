import VQ.Euclid.StepBlocks.Phase

namespace VQ
namespace Euclid
namespace StepBlocks

open Reversible
open Internal

def ownershipSelectState
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  let result := Phase.ownershipSelected lengthWidth shiftWidth
    (StepPlaced.phaseInput n lengthWidth shiftWidth I)
  writeField
    (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
      (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
    (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
    (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth))

theorem ownershipSelectState_zeroQ
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.zeroQWire n lengthWidth shiftWidth) =
      Phase.selectorValue lengthWidth
        (StepLayout.lenQOffset n lengthWidth) I := by
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let result := Phase.ownershipSelected lengthWidth shiftWidth input
  have hflags := Phase.ownershipSelected_flags lengthWidth shiftWidth input
  simp only at hflags
  rw [show ownershipSelectState n lengthWidth shiftWidth I =
      writeField
        (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) by
    rfl]
  rw [bitValue_write_ne (by
      simp [StepLayout.zeroQWire, StepLayout.zeroShiftWire]),
    bitValue_write_self,
    Nat.mod_eq_of_lt (bitValue_lt result
      (Phase.zeroQWire lengthWidth shiftWidth)), hflags.1]
  unfold Phase.selectorValue
  rw [phaseInputLenQ]

theorem ownershipSelectState_zeroShift
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) =
      Phase.selectorValue shiftWidth
        (StepLayout.shiftOffset n lengthWidth) I := by
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let result := Phase.ownershipSelected lengthWidth shiftWidth input
  have hflags := Phase.ownershipSelected_flags lengthWidth shiftWidth input
  simp only at hflags
  rw [show ownershipSelectState n lengthWidth shiftWidth I =
      writeField
        (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) by
    rfl]
  rw [bitValue_write_self,
    Nat.mod_eq_of_lt (bitValue_lt result
      (Phase.zeroShiftWire lengthWidth shiftWidth)), hflags.2]
  unfold Phase.selectorValue
  rw [phaseInputShift]

theorem ownershipSelectState_pool
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) := by
  simp only [ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.selectorWidth]),
    readField_writeField_of_disjoint (by
      simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.selectorWidth])]

theorem ownershipSelectState_lenQ
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
  simp only [ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipSelectState_shift
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth := by
  simp only [ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]

def ownershipControlState
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  Phase.ccxOut
    (StepLayout.zeroQWire n lengthWidth shiftWidth)
    (StepLayout.zeroShiftWire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth)
    (ownershipSelectState n lengthWidth shiftWidth I)

theorem ownershipControlState_work1
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipControlState n lengthWidth shiftWidth I)
        StepLayout.work1Offset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
  simp only [ownershipControlState, Phase.ccxOut, ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.work1Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work1Offset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work1Offset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipControlState_work2
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipControlState n lengthWidth shiftWidth I)
        (StepLayout.work2Offset n) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
  simp only [ownershipControlState, Phase.ccxOut, ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.work2Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work2Offset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work2Offset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipControlState_lenT
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipControlState n lengthWidth shiftWidth I)
        (StepLayout.lenTOffset n) lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
  simp only [ownershipControlState, Phase.ccxOut, ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenTOffset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenTOffset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenTOffset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipControlState_lenRPrime
    (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipControlState n lengthWidth shiftWidth I)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth := by
  simp only [ownershipControlState, Phase.ccxOut, ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipControlState_enabled
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth)
      lengthWidth = encodedZero lengthWidth)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth)
      shiftWidth = encodedZero shiftWidth) :
    SwapLength.Enabled (workWidth n) lengthWidth
      (StepPlaced.ownershipInput n lengthWidth shiftWidth
        (ownershipControlState n lengthWidth shiftWidth I)) := by
  have hclear {off width : Nat}
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
      (hhi : off + width ≤
        StepLayout.auxOffset n lengthWidth shiftWidth +
          StepLayout.auxWidth lengthWidth shiftWidth) :
      readField I off width = 0 :=
    auxSubfieldClear haux hlo hhi
  have hselectedControl :
      bitValue (ownershipSelectState n lengthWidth shiftWidth I)
          (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    simp only [ownershipSelectState]
    rw [bitValue_write_ne (by
        simp [StepLayout.controlWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega),
      bitValue_write_ne (by
        simp [StepLayout.controlWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega), hcontrol]
  have hcontrolState : bitValue
      (ownershipControlState n lengthWidth shiftWidth I)
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1 := by
    rw [ownershipControlState, Phase.ccxOut_target,
      ownershipSelectState_zeroQ, ownershipSelectState_zeroShift,
      hselectedControl]
    simp [Phase.selectorValue, hlenQ, hshift]
  have hpreserved {q : Nat}
      (hqControl : q ≠ StepLayout.controlWire n lengthWidth shiftWidth)
      (hqZeroQ : q ≠ StepLayout.zeroQWire n lengthWidth shiftWidth)
      (hqZeroShift : q ≠
        StepLayout.zeroShiftWire n lengthWidth shiftWidth) :
      bitValue (ownershipControlState n lengthWidth shiftWidth I) q =
        bitValue I q := by
    rw [ownershipControlState, Phase.ccxOut_ne hqControl]
    simp only [ownershipSelectState]
    rw [bitValue_write_ne hqZeroShift, bitValue_write_ne hqZeroQ]
  have hpoolI : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply hclear
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth]
      omega
  have hpoolState : readField
      (ownershipControlState n lengthWidth shiftWidth I)
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    simp only [ownershipControlState, Phase.ccxOut]
    rw [readField_writeField_of_disjoint (by
        simp [StepLayout.poolOffset, StepLayout.controlWire,
          StepLayout.carryWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.auxOffset]
        omega), ownershipSelectState_pool, hpoolI]
  apply StepPlaced.ownershipInput_enabled_of_scratch hcontrolState
  · rw [hpreserved (by
        simp [StepLayout.carryWire, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.carryWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.carryWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · rw [hpreserved (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  · rw [hpreserved (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  · rw [hpreserved (by
        simp [StepLayout.rightFlagWire, StepLayout.carryWire,
          StepLayout.controlWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.rightFlagWire, StepLayout.carryWire,
          StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.rightFlagWire, StepLayout.carryWire,
          StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  · exact readField_sub_zero (Nat.le_refl _)
      (by simp [StepLayout.selectorWidth])
      hpoolState
  · rw [hpreserved (by
        simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.controlWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.zeroQWire, StepLayout.cellScratchWire]) (by
        simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire])]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth] <;>
      omega

theorem ownershipControlState_eq_selected_of_inactive
    {n lengthWidth shiftWidth I : Nat}
    (hinactive :
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth ≠
          encodedZero lengthWidth ∨
        readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
          encodedZero shiftWidth) :
    ownershipControlState n lengthWidth shiftWidth I =
      ownershipSelectState n lengthWidth shiftWidth I := by
  have hproduct :
      Phase.selectorValue lengthWidth
          (StepLayout.lenQOffset n lengthWidth) I *
        Phase.selectorValue shiftWidth
          (StepLayout.shiftOffset n lengthWidth) I = 0 := by
    rcases hinactive with hlenQ | hshift
    · simp [Phase.selectorValue, hlenQ]
    · simp [Phase.selectorValue, hshift]
  simp only [ownershipControlState, Phase.ccxOut]
  rw [ownershipSelectState_zeroQ, ownershipSelectState_zeroShift, hproduct,
    Nat.add_zero]
  apply write_of_bitValue
  have hbit := bitValue_lt
    (ownershipSelectState n lengthWidth shiftWidth I)
    (StepLayout.controlWire n lengthWidth shiftWidth)
  omega

structure OwnershipControlClean
    (n lengthWidth shiftWidth I : Nat) : Prop where
  controlClear : bitValue I
    (StepLayout.controlWire n lengthWidth shiftWidth) = 0
  carryClear : bitValue I
    (StepLayout.carryWire n lengthWidth shiftWidth) = 0
  accumulatorClear : bitValue I
    (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0
  leftFlagClear : bitValue I
    (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0
  poolClear : readField I
    (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0
  cellScratchClear : bitValue I
    (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0

theorem OwnershipControlClean.gathered
    {n lengthWidth shiftWidth I : Nat}
    (h : OwnershipControlClean n lengthWidth shiftWidth I) :
    SwapLength.Clean (workWidth n) lengthWidth
      (StepPlaced.ownershipInput n lengthWidth shiftWidth I) :=
  StepPlaced.ownershipInput_clean_of_scratch h.controlClear h.carryClear
    h.accumulatorClear h.leftFlagClear h.poolClear h.cellScratchClear

theorem ownershipControlState_clean
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hinactive :
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth ≠
          encodedZero lengthWidth ∨
        readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
          encodedZero shiftWidth) :
    OwnershipControlClean n lengthWidth shiftWidth
      (ownershipControlState n lengthWidth shiftWidth I) := by
  have heq := ownershipControlState_eq_selected_of_inactive hinactive
  have hclear {off width : Nat}
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
      (hhi : off + width ≤
        StepLayout.auxOffset n lengthWidth shiftWidth +
          StepLayout.auxWidth lengthWidth shiftWidth) :
      readField I off width = 0 :=
    auxSubfieldClear haux hlo hhi
  have hpreserved {q : Nat}
      (hqZeroQ : q ≠ StepLayout.zeroQWire n lengthWidth shiftWidth)
      (hqZeroShift : q ≠
        StepLayout.zeroShiftWire n lengthWidth shiftWidth) :
      bitValue (ownershipControlState n lengthWidth shiftWidth I) q =
        bitValue I q := by
    rw [heq]
    simp only [ownershipSelectState]
    rw [bitValue_write_ne hqZeroShift, bitValue_write_ne hqZeroQ]
  constructor
  · rw [hpreserved (by
        simp [StepLayout.controlWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega) (by
        simp [StepLayout.controlWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega), hcontrol]
  · rw [hpreserved (by
        simp [StepLayout.carryWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.carryWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · rw [hpreserved (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  · rw [hpreserved (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega) (by
        simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset]
        omega)]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  · rw [heq]
    have hpool : readField
        (ownershipSelectState n lengthWidth shiftWidth I)
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
      rw [ownershipSelectState_pool]
      apply hclear
      · simp [StepLayout.poolOffset, StepLayout.carryWire]
        omega
      · simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth]
        omega
    exact readField_narrow (Nat.le_max_left _ _) hpool
  · rw [hpreserved (by
        simp [StepLayout.zeroQWire, StepLayout.cellScratchWire]) (by
        simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire])]
    rw [← readField_one]
    apply hclear <;>
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth] <;>
      omega

def ownershipIterState
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  writeField I (StepLayout.iterWire n lengthWidth shiftWidth) 1
    ((bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) +
      bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)) % 2)

def ownershipBodyState
    (n lengthWidth _shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField I StepLayout.work1Offset (workWidth n) newWork1)
        (StepLayout.work2Offset n) (workWidth n) newWork2)
      (StepLayout.lenTOffset n) lengthWidth newLenT)
    (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth newLenRPrime

def ownershipControlClearedState
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  Phase.ccxOut
    (StepLayout.zeroQWire n lengthWidth shiftWidth)
    (StepLayout.zeroShiftWire n lengthWidth shiftWidth)
    (StepLayout.controlWire n lengthWidth shiftWidth) I

def ownershipPostState
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) : Nat :=
  ownershipControlClearedState n lengthWidth shiftWidth
    (ownershipIterState n lengthWidth shiftWidth
      (ownershipBodyState n lengthWidth shiftWidth
        (ownershipControlState n lengthWidth shiftWidth I)
        newWork1 newWork2 newLenT newLenRPrime))

def ownershipCleanedState
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  writeField
    (writeField I (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1 0)
    (StepLayout.zeroQWire n lengthWidth shiftWidth) 1 0

theorem ownershipCleanedPostState_eq_result
    {n lengthWidth shiftWidth I w1 w2 newLenT newLenRPrime : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      encodedZero shiftWidth) :
    ownershipCleanedState n lengthWidth shiftWidth
        (ownershipPostState n lengthWidth shiftWidth I
          w1 w2 newLenT newLenRPrime) =
      writeField
        (ownershipBodyState n lengthWidth shiftWidth I
          w1 w2 newLenT newLenRPrime)
        (StepLayout.iterWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) + 1) %
          2) := by
  let zq := StepLayout.zeroQWire n lengthWidth shiftWidth
  let zs := StepLayout.zeroShiftWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  let iter := StepLayout.iterWire n lengthWidth shiftWidth
  let C := ownershipControlState n lengthWidth shiftWidth I
  let B := ownershipBodyState n lengthWidth shiftWidth C
    w1 w2 newLenT newLenRPrime
  let T := ownershipIterState n lengthWidth shiftWidth B
  have hzqI : bitValue I zq = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [zq, StepLayout.zeroQWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hzsI : bitValue I zs = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [zs, StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hSctrl : bitValue
      (ownershipSelectState n lengthWidth shiftWidth I) ctrl = 0 := by
    simp only [ownershipSelectState]
    rw [bitValue_write_ne (by
        simp [ctrl, StepLayout.controlWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega),
      bitValue_write_ne (by
        simp [ctrl, StepLayout.controlWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega), hcontrol]
  have hSiter : bitValue
      (ownershipSelectState n lengthWidth shiftWidth I) iter =
        bitValue I iter := by
    simp only [ownershipSelectState]
    rw [bitValue_write_ne (by
        simp [iter, StepLayout.iterWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega),
      bitValue_write_ne (by
        simp [iter, StepLayout.iterWire, StepLayout.zeroQWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)]
  have hCzq : bitValue C zq = 1 := by
    rw [show bitValue C zq = bitValue
        (ownershipSelectState n lengthWidth shiftWidth I) zq by
      simp only [C, ownershipControlState]
      apply Phase.ccxOut_ne
      simp [zq, StepLayout.zeroQWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega]
    simpa [zq, Phase.selectorValue, hlenQ] using
      ownershipSelectState_zeroQ n lengthWidth shiftWidth I
  have hCzs : bitValue C zs = 1 := by
    rw [show bitValue C zs = bitValue
        (ownershipSelectState n lengthWidth shiftWidth I) zs by
      simp only [C, ownershipControlState]
      apply Phase.ccxOut_ne
      simp [zs, StepLayout.zeroShiftWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega]
    simpa [zs, Phase.selectorValue, hshift] using
      ownershipSelectState_zeroShift n lengthWidth shiftWidth I
  have hCctrl : bitValue C ctrl = 1 := by
    simp only [C, ownershipControlState]
    rw [Phase.ccxOut_target, ownershipSelectState_zeroQ,
      ownershipSelectState_zeroShift, hSctrl]
    simp [Phase.selectorValue, hlenQ, hshift]
  have hCiter : bitValue C iter = bitValue I iter := by
    simp only [C, ownershipControlState]
    rw [Phase.ccxOut_ne (by
      simp [iter, StepLayout.iterWire, StepLayout.controlWire])]
    exact hSiter
  have hbodyPreserved {J q : Nat}
      (hq : q = zq ∨ q = zs ∨ q = ctrl ∨ q = iter) :
      bitValue
          (ownershipBodyState n lengthWidth shiftWidth J
            w1 w2 newLenT newLenRPrime) q =
        bitValue J q := by
    simp only [ownershipBodyState]
    repeat' rw [bitValue_write_out (Or.inr (by
      rcases hq with rfl | rfl | rfl | rfl <;>
        simp [zq, zs, ctrl, iter, StepLayout.zeroQWire,
          StepLayout.zeroShiftWire, StepLayout.controlWire,
          StepLayout.iterWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.work1Offset,
          StepLayout.work2Offset, StepLayout.lenTOffset,
          StepLayout.lenRPrimeOffset, workWidth] <;>
        omega))]
  have hBzq : bitValue B zq = 1 := by
    rw [show bitValue B zq = bitValue C zq by
      exact hbodyPreserved (Or.inl rfl), hCzq]
  have hBzs : bitValue B zs = 1 := by
    rw [show bitValue B zs = bitValue C zs by
      exact hbodyPreserved (Or.inr (Or.inl rfl)), hCzs]
  have hBctrl : bitValue B ctrl = 1 := by
    rw [show bitValue B ctrl = bitValue C ctrl by
      exact hbodyPreserved (Or.inr (Or.inr (Or.inl rfl))), hCctrl]
  have hBiter : bitValue B iter = bitValue I iter := by
    rw [show bitValue B iter = bitValue C iter by
      exact hbodyPreserved (Or.inr (Or.inr (Or.inr rfl))), hCiter]
  have hTzq : bitValue T zq = 1 := by
    simp only [T, ownershipIterState]
    rw [bitValue_write_ne (by
      simp [zq, StepLayout.zeroQWire, StepLayout.iterWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega), hBzq]
  have hTzs : bitValue T zs = 1 := by
    simp only [T, ownershipIterState]
    rw [bitValue_write_ne (by
      simp [zs, StepLayout.zeroShiftWire, StepLayout.iterWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega), hBzs]
  have hTctrl : bitValue T ctrl = 1 := by
    simp only [T, ownershipIterState]
    rw [bitValue_write_ne (by
      simp [ctrl, StepLayout.controlWire, StepLayout.iterWire]),
      hBctrl]
  have hT : T = writeField B iter 1
      ((bitValue I iter + 1) % 2) := by
    simp only [T, ownershipIterState]
    rw [hBiter, hBctrl]
  have hcleared :
      ownershipControlClearedState n lengthWidth shiftWidth T =
        writeField T ctrl 1 0 := by
    simp only [ownershipControlClearedState, Phase.ccxOut]
    apply write_congr
    rw [hTctrl, hTzq, hTzs]
  have hzqWrite : writeField I zq 1 0 = I := by
    apply write_of_bitValue
    simpa using hzqI.symm
  have hzsWrite : writeField I zs 1 0 = I := by
    apply write_of_bitValue
    simpa using hzsI.symm
  have hctrlWrite : writeField I ctrl 1 0 = I := by
    apply write_of_bitValue
    simpa using hcontrol.symm
  have hcleanSelect :
      ownershipCleanedState n lengthWidth shiftWidth
          (ownershipSelectState n lengthWidth shiftWidth I) = I := by
    simp only [ownershipCleanedState, ownershipSelectState]
    rw [writeField_writeField]
    rw [writeField_comm (by
      simp [StepLayout.zeroQWire, StepLayout.zeroShiftWire])]
    rw [writeField_writeField, hzqWrite, hzsWrite]
  have hrestore :
      writeField (writeField (writeField C ctrl 1 0) zs 1 0) zq 1 0 =
        I := by
    simp only [C, ownershipControlState, Phase.ccxOut]
    rw [writeField_writeField]
    change writeField
        (writeField
          (writeField
            (ownershipSelectState n lengthWidth shiftWidth I) ctrl 1 0)
          zs 1 0)
        zq 1 0 = I
    calc
      _ = writeField
          (writeField
            (writeField
              (ownershipSelectState n lengthWidth shiftWidth I) zs 1 0)
            ctrl 1 0)
          zq 1 0 := by
        apply congrArg (fun K => writeField K zq 1 0)
        exact writeField_comm (by
          simp [zs, ctrl, StepLayout.zeroShiftWire,
            StepLayout.controlWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega)
      _ = writeField
          (writeField
            (writeField
              (ownershipSelectState n lengthWidth shiftWidth I) zs 1 0)
            zq 1 0)
          ctrl 1 0 := writeField_comm (by
        simp [zq, ctrl, StepLayout.zeroQWire, StepLayout.controlWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset]
        omega)
      _ = writeField I ctrl 1 0 := by
        rw [show writeField
            (writeField
              (ownershipSelectState n lengthWidth shiftWidth I) zs 1 0)
            zq 1 0 = I by
          simpa [ownershipCleanedState] using hcleanSelect]
      _ = I := hctrlWrite
  have hbodyWrite (J q v : Nat)
      (hq : q = zq ∨ q = zs ∨ q = ctrl) :
      writeField
          (ownershipBodyState n lengthWidth shiftWidth J
            w1 w2 newLenT newLenRPrime) q 1 v =
        ownershipBodyState n lengthWidth shiftWidth
          (writeField J q 1 v) w1 w2 newLenT newLenRPrime := by
    have hlenRPrime :
        StepLayout.lenRPrimeOffset n lengthWidth + lengthWidth ≤ q := by
      rcases hq with rfl | rfl | rfl <;>
        simp [zq, zs, ctrl, StepLayout.zeroQWire,
          StepLayout.zeroShiftWire, StepLayout.controlWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset,
          StepLayout.lenRPrimeOffset, workWidth] <;>
        omega
    have hlenT : StepLayout.lenTOffset n + lengthWidth ≤ q := by
      simp only [StepLayout.lenRPrimeOffset, StepLayout.lenTOffset] at hlenRPrime ⊢
      omega
    have hwork2 : StepLayout.work2Offset n + workWidth n ≤ q := by
      simp only [StepLayout.lenRPrimeOffset, StepLayout.work2Offset] at hlenRPrime ⊢
      omega
    have hwork1 : StepLayout.work1Offset + workWidth n ≤ q := by
      simp only [StepLayout.lenRPrimeOffset, StepLayout.work1Offset] at hlenRPrime ⊢
      omega
    let J1 := writeField J StepLayout.work1Offset (workWidth n) w1
    let J2 := writeField J1 (StepLayout.work2Offset n) (workWidth n) w2
    let J3 := writeField J2 (StepLayout.lenTOffset n) lengthWidth newLenT
    change writeField
        (writeField J3 (StepLayout.lenRPrimeOffset n lengthWidth)
          lengthWidth newLenRPrime)
        q 1 v =
      writeField
        (writeField
          (writeField
            (writeField (writeField J q 1 v) StepLayout.work1Offset
              (workWidth n) w1)
            (StepLayout.work2Offset n) (workWidth n) w2)
          (StepLayout.lenTOffset n) lengthWidth newLenT)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
        newLenRPrime
    calc
      _ =
        writeField
          (writeField J3 q 1 v)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime :=
        writeField_comm (Or.inl hlenRPrime)
      _ = writeField
          (writeField
            (writeField J2 q 1 v)
            (StepLayout.lenTOffset n) lengthWidth newLenT)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime := by
        apply congrArg (fun K => writeField K
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime)
        simpa [J3] using writeField_comm (i := J2) (v := newLenT)
          (u := v) (Or.inl hlenT)
      _ = writeField
          (writeField
            (writeField
              (writeField J1 q 1 v)
              (StepLayout.work2Offset n) (workWidth n) w2)
            (StepLayout.lenTOffset n) lengthWidth newLenT)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime := by
        apply congrArg (fun K => writeField
          (writeField K (StepLayout.lenTOffset n) lengthWidth newLenT)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime)
        simpa [J2] using writeField_comm (i := J1) (v := w2)
          (u := v) (Or.inl hwork2)
      _ = writeField
          (writeField
            (writeField
              (writeField
                (writeField J q 1 v) StepLayout.work1Offset
                  (workWidth n) w1)
              (StepLayout.work2Offset n) (workWidth n) w2)
            (StepLayout.lenTOffset n) lengthWidth newLenT)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime := by
        apply congrArg (fun K => writeField
          (writeField
            (writeField K (StepLayout.work2Offset n) (workWidth n) w2)
            (StepLayout.lenTOffset n) lengthWidth newLenT)
          (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
          newLenRPrime)
        simpa [J1] using writeField_comm (i := J) (v := w1)
          (u := v) (Or.inl hwork1)
  have hbodyClean :
      writeField (writeField (writeField B ctrl 1 0) zs 1 0) zq 1 0 =
        ownershipBodyState n lengthWidth shiftWidth I
          w1 w2 newLenT newLenRPrime := by
    simp only [B]
    rw [hbodyWrite _ ctrl 0 (Or.inr (Or.inr rfl)),
      hbodyWrite _ zs 0 (Or.inr (Or.inl rfl)),
      hbodyWrite _ zq 0 (Or.inl rfl), hrestore]
  simp only [ownershipPostState, ownershipCleanedState]
  rw [show ownershipControlClearedState n lengthWidth shiftWidth
      (ownershipIterState n lengthWidth shiftWidth B) =
        writeField T ctrl 1 0 by simpa [T] using hcleared,
    hT]
  change writeField
      (writeField
        (writeField (writeField B iter 1 ((bitValue I iter + 1) % 2))
          ctrl 1 0)
        zs 1 0)
      zq 1 0 =
    writeField
      (ownershipBodyState n lengthWidth shiftWidth I
        w1 w2 newLenT newLenRPrime)
      iter 1 ((bitValue I iter + 1) % 2)
  calc
    _ = writeField
        (writeField (writeField (writeField B ctrl 1 0) zs 1 0) zq 1 0)
        iter 1 ((bitValue I iter + 1) % 2) := by
      rw [show writeField
          (writeField B iter 1 ((bitValue I iter + 1) % 2)) ctrl 1 0 =
        writeField (writeField B ctrl 1 0) iter 1
          ((bitValue I iter + 1) % 2) by
        apply writeField_comm
        simp [iter, ctrl, StepLayout.iterWire, StepLayout.controlWire]]
      rw [show writeField
          (writeField (writeField B ctrl 1 0) iter 1
            ((bitValue I iter + 1) % 2)) zs 1 0 =
        writeField (writeField (writeField B ctrl 1 0) zs 1 0) iter 1
          ((bitValue I iter + 1) % 2) by
        apply writeField_comm
        simp [iter, zs, StepLayout.iterWire, StepLayout.zeroShiftWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega]
      apply writeField_comm
      simp [iter, zq, StepLayout.iterWire, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega
    _ = _ := by rw [hbodyClean]

theorem ownershipPostState_zeroQ
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) :
    bitValue
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime)
        (StepLayout.zeroQWire n lengthWidth shiftWidth) =
      Phase.selectorValue lengthWidth
        (StepLayout.lenQOffset n lengthWidth) I := by
  simp only [ownershipPostState, ownershipControlClearedState]
  rw [Phase.ccxOut_ne (by
      simp [StepLayout.zeroQWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
  simp only [ownershipIterState]
  rw [bitValue_write_ne (by
      simp [StepLayout.zeroQWire, StepLayout.iterWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset]
      omega)]
  simp only [ownershipBodyState]
  repeat' rw [bitValue_write_out (Or.inr (by
    simp [StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.lenTOffset, StepLayout.lenRPrimeOffset,
      StepLayout.zeroQWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire,
      StepLayout.shiftOffset, workWidth]
    omega))]
  simp only [ownershipControlState]
  rw [Phase.ccxOut_ne (by
      simp [StepLayout.zeroQWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
  exact ownershipSelectState_zeroQ n lengthWidth shiftWidth I

theorem ownershipPostState_zeroShift
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) :
    bitValue
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime)
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) =
      Phase.selectorValue shiftWidth
        (StepLayout.shiftOffset n lengthWidth) I := by
  simp only [ownershipPostState, ownershipControlClearedState]
  rw [Phase.ccxOut_ne (by
      simp [StepLayout.zeroShiftWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
  simp only [ownershipIterState]
  rw [bitValue_write_ne (by
      simp [StepLayout.zeroShiftWire, StepLayout.iterWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset]
      omega)]
  simp only [ownershipBodyState]
  repeat' rw [bitValue_write_out (Or.inr (by
    simp [StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.lenTOffset, StepLayout.lenRPrimeOffset,
      StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire,
      StepLayout.shiftOffset, workWidth]
    omega))]
  simp only [ownershipControlState]
  rw [Phase.ccxOut_ne (by
      simp [StepLayout.zeroShiftWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
  exact ownershipSelectState_zeroShift n lengthWidth shiftWidth I

theorem ownershipPostState_pool
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) :
    readField
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime)
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) := by
  simp only [ownershipPostState, ownershipControlClearedState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.poolOffset, StepLayout.controlWire,
        StepLayout.carryWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset]
      omega)]
  simp only [ownershipIterState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.poolOffset, StepLayout.iterWire,
        StepLayout.carryWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset]
      omega)]
  simp only [ownershipBodyState]
  repeat' rw [readField_writeField_of_disjoint (Or.inl (by
    simp [StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.lenTOffset, StepLayout.lenRPrimeOffset,
      StepLayout.poolOffset, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire,
      StepLayout.shiftOffset,
      workWidth]
    omega))]
  simp only [ownershipControlState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.poolOffset, StepLayout.controlWire,
        StepLayout.carryWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset]
      omega)]
  exact ownershipSelectState_pool n lengthWidth shiftWidth I

theorem ownershipPostState_lenQ
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) :
    readField
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
  simp only [ownershipPostState, ownershipControlClearedState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]
  simp only [ownershipIterState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.iterWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]
  simp only [ownershipBodyState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.lenRPrimeOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.lenTOffset, workWidth]),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.work2Offset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.work1Offset, workWidth]
      omega)]
  simp only [ownershipControlState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]
  simp only [ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.zeroShiftWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenQOffset, StepLayout.zeroQWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega)]

theorem ownershipPostState_shift
    (n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat) :
    readField
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime)
        (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth := by
  simp only [ownershipPostState, ownershipControlClearedState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])]
  simp only [ownershipIterState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])]
  simp only [ownershipBodyState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.lenTOffset, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.work1Offset, StepLayout.shiftOffset, workWidth]
      omega)]
  simp only [ownershipControlState, Phase.ccxOut]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset])]
  simp only [ownershipSelectState]
  rw [readField_writeField_of_disjoint (by
      simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega),
    readField_writeField_of_disjoint (by
      simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset]
      omega)]

theorem ownershipUnselectBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue I (StepLayout.zeroQWire n lengthWidth shiftWidth) =
      Phase.selectorValue lengthWidth
        (StepLayout.lenQOffset n lengthWidth) I)
    (hzeroShift :
      bitValue I (StepLayout.zeroShiftWire n lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth
          (StepLayout.shiftOffset n lengthWidth) I)
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0) :
    actGates (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth) I =
      ownershipCleanedState n lengthWidth shiftWidth I := by
  have hqLocal :
      Phase.selectorValue lengthWidth Phase.lenQOffset
          (StepPlaced.phaseInput n lengthWidth shiftWidth I) =
        Phase.selectorValue lengthWidth
          (StepLayout.lenQOffset n lengthWidth) I := by
    unfold Phase.selectorValue
    rw [phaseInputLenQ]
  have hsLocal :
      Phase.selectorValue shiftWidth (Phase.shiftOffset lengthWidth)
          (StepPlaced.phaseInput n lengthWidth shiftWidth I) =
        Phase.selectorValue shiftWidth
          (StepLayout.shiftOffset n lengthWidth) I := by
    unfold Phase.selectorValue
    rw [phaseInputShift]
  have hact := StepPlaced.ownershipUnselect_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) (I := I)
    (by rw [phaseInputZeroQ, hqLocal]; exact hzeroQ)
    (by rw [phaseInputZeroShift, hsLocal]; exact hzeroShift)
    (by rw [phaseInputPool]; exact hpool)
  simpa [ownershipCleanedState] using hact

theorem ownershipSelectBlock_eq
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0) :
    actGates (StepLayout.ownershipSelectGates n lengthWidth shiftWidth) I =
      ownershipSelectState n lengthWidth shiftWidth I := by
  simpa [ownershipSelectState] using
    (StepPlaced.ownershipSelect_act
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) (I := I)
      (by
        rw [phaseInputZeroQ, ← readField_one]
        apply auxSubfieldClear haux <;>
          simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxWidth, StepLayout.selectorWidth] <;>
          omega)
      (by
        rw [phaseInputZeroShift, ← readField_one]
        apply auxSubfieldClear haux <;>
          simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxWidth, StepLayout.selectorWidth] <;>
          omega)
      (by
        rw [phaseInputPool]
        apply auxSubfieldClear haux <;>
          simp [StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxWidth, StepLayout.selectorWidth] <;>
          omega))

theorem ownershipBlock_act_of_body
    {n lengthWidth shiftWidth I B : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hbody :
      actGates (StepLayout.ownershipGates n lengthWidth shiftWidth)
          (ownershipControlState n lengthWidth shiftWidth I) = B)
    (hcleanup :
      actGates (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth)
          (ownershipControlClearedState n lengthWidth shiftWidth
            (ownershipIterState n lengthWidth shiftWidth B)) =
        ownershipCleanedState n lengthWidth shiftWidth
          (ownershipControlClearedState n lengthWidth shiftWidth
            (ownershipIterState n lengthWidth shiftWidth B))) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth) I =
      ownershipCleanedState n lengthWidth shiftWidth
        (ownershipControlClearedState n lengthWidth shiftWidth
          (ownershipIterState n lengthWidth shiftWidth B)) := by
  let zq := StepLayout.zeroQWire n lengthWidth shiftWidth
  let zs := StepLayout.zeroShiftWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  let iter := StepLayout.iterWire n lengthWidth shiftWidth
  have hselect := ownershipSelectBlock_eq haux
  have hcontrol : actGates [.ccx zq zs ctrl]
      (ownershipSelectState n lengthWidth shiftWidth I) =
        ownershipControlState n lengthWidth shiftWidth I := by
    simpa [zq, zs, ctrl, ownershipControlState, Phase.ccxGates] using
      Phase.ccxGates_act zq zs ctrl
        (ownershipSelectState n lengthWidth shiftWidth I)
  have hiter : actGates [.cx ctrl iter] B =
      ownershipIterState n lengthWidth shiftWidth B := by
    rw [actGates_cons, actGates_nil, act_cx_write]
    rfl
  have hclear : actGates [.ccx zq zs ctrl]
      (ownershipIterState n lengthWidth shiftWidth B) =
        ownershipControlClearedState n lengthWidth shiftWidth
          (ownershipIterState n lengthWidth shiftWidth B) := by
    simpa [zq, zs, ctrl, ownershipControlClearedState, Phase.ccxGates] using
      Phase.ccxGates_act zq zs ctrl
        (ownershipIterState n lengthWidth shiftWidth B)
  simp only [Step.ownershipBlock, actGates_append]
  rw [hselect, hcontrol, hbody, hiter, hclear, hcleanup]

theorem ownershipBlock_act_of_selectors
    {n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hbody :
      actGates (StepLayout.ownershipGates n lengthWidth shiftWidth)
          (ownershipControlState n lengthWidth shiftWidth I) =
        ownershipBodyState n lengthWidth shiftWidth
          (ownershipControlState n lengthWidth shiftWidth I)
          newWork1 newWork2 newLenT newLenRPrime)
    (hzeroQ :
      let J := ownershipControlClearedState n lengthWidth shiftWidth
        (ownershipIterState n lengthWidth shiftWidth
          (ownershipBodyState n lengthWidth shiftWidth
            (ownershipControlState n lengthWidth shiftWidth I)
            newWork1 newWork2 newLenT newLenRPrime))
      bitValue J (StepLayout.zeroQWire n lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth
          (StepLayout.lenQOffset n lengthWidth) J)
    (hzeroShift :
      let J := ownershipControlClearedState n lengthWidth shiftWidth
        (ownershipIterState n lengthWidth shiftWidth
          (ownershipBodyState n lengthWidth shiftWidth
            (ownershipControlState n lengthWidth shiftWidth I)
            newWork1 newWork2 newLenT newLenRPrime))
      bitValue J (StepLayout.zeroShiftWire n lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth
          (StepLayout.shiftOffset n lengthWidth) J)
    (hpool :
      let J := ownershipControlClearedState n lengthWidth shiftWidth
        (ownershipIterState n lengthWidth shiftWidth
          (ownershipBodyState n lengthWidth shiftWidth
            (ownershipControlState n lengthWidth shiftWidth I)
            newWork1 newWork2 newLenT newLenRPrime))
      readField J (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) = 0) :
    let B := ownershipBodyState n lengthWidth shiftWidth
      (ownershipControlState n lengthWidth shiftWidth I)
      newWork1 newWork2 newLenT newLenRPrime
    let J := ownershipControlClearedState n lengthWidth shiftWidth
      (ownershipIterState n lengthWidth shiftWidth B)
    actGates (Step.ownershipBlock n lengthWidth shiftWidth) I =
      ownershipCleanedState n lengthWidth shiftWidth J := by
  dsimp only
  apply ownershipBlock_act_of_body haux hbody
  exact ownershipUnselectBlock_act hzeroQ hzeroShift hpool

theorem ownershipBlock_act
    {n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hbody :
      actGates (StepLayout.ownershipGates n lengthWidth shiftWidth)
          (ownershipControlState n lengthWidth shiftWidth I) =
        ownershipBodyState n lengthWidth shiftWidth
          (ownershipControlState n lengthWidth shiftWidth I)
          newWork1 newWork2 newLenT newLenRPrime) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth) I =
      ownershipCleanedState n lengthWidth shiftWidth
        (ownershipPostState n lengthWidth shiftWidth I
          newWork1 newWork2 newLenT newLenRPrime) := by
  have hzeroQ :
      bitValue
          (ownershipPostState n lengthWidth shiftWidth I
            newWork1 newWork2 newLenT newLenRPrime)
          (StepLayout.zeroQWire n lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth
          (StepLayout.lenQOffset n lengthWidth)
          (ownershipPostState n lengthWidth shiftWidth I
            newWork1 newWork2 newLenT newLenRPrime) := by
    rw [ownershipPostState_zeroQ]
    unfold Phase.selectorValue
    rw [ownershipPostState_lenQ]
  have hzeroShift :
      bitValue
          (ownershipPostState n lengthWidth shiftWidth I
            newWork1 newWork2 newLenT newLenRPrime)
          (StepLayout.zeroShiftWire n lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth
          (StepLayout.shiftOffset n lengthWidth)
          (ownershipPostState n lengthWidth shiftWidth I
            newWork1 newWork2 newLenT newLenRPrime) := by
    rw [ownershipPostState_zeroShift]
    unfold Phase.selectorValue
    rw [ownershipPostState_shift]
  have hpoolI : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpool : readField
      (ownershipPostState n lengthWidth shiftWidth I
        newWork1 newWork2 newLenT newLenRPrime)
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    rw [ownershipPostState_pool, hpoolI]
  simpa [ownershipPostState] using
    ownershipBlock_act_of_selectors haux hbody hzeroQ hzeroShift hpool

theorem ownershipBlock_inactive
    {n lengthWidth shiftWidth I : Nat}
    (hfit : workWidth n < 2 ^ lengthWidth)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hinactive :
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth ≠
          encodedZero lengthWidth ∨
        readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
          encodedZero shiftWidth) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth) I = I := by
  let zq := StepLayout.zeroQWire n lengthWidth shiftWidth
  let zs := StepLayout.zeroShiftWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  let iter := StepLayout.iterWire n lengthWidth shiftWidth
  let S := ownershipSelectState n lengthWidth shiftWidth I
  let J := ownershipControlState n lengthWidth shiftWidth I
  have hselect :
      actGates (StepLayout.ownershipSelectGates n lengthWidth shiftWidth) I =
        S := by
    simpa [S] using ownershipSelectBlock_eq haux
  have hcontrolGate : actGates [.ccx zq zs ctrl] S = J := by
    simpa [zq, zs, ctrl, S, J, ownershipControlState,
      Phase.ccxGates] using Phase.ccxGates_act zq zs ctrl S
  have hJ : J = S := by
    simpa [J, S] using
      ownershipControlState_eq_selected_of_inactive hinactive
  have hcheckpoint : OwnershipControlClean n lengthWidth shiftWidth J := by
    simpa [J] using ownershipControlState_clean hcontrol haux hinactive
  have hbody :
      actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) J = J := by
    have hfit' : n + 3 < 2 ^ lengthWidth := by
      simpa [workWidth] using hfit
    exact StepPlaced.ownershipGates_inactive hfit'
      hcheckpoint.controlClear hcheckpoint.carryClear
      hcheckpoint.accumulatorClear hcheckpoint.leftFlagClear
      hcheckpoint.poolClear hcheckpoint.cellScratchClear
  have hiter : actGates [.cx ctrl iter] J = J := by
    rw [actGates_cons, actGates_nil, act_cx_write]
    rw [show bitValue J ctrl = 0 by
      simpa [ctrl] using hcheckpoint.controlClear, Nat.add_zero]
    apply write_of_bitValue
    have hbit := bitValue_lt J iter
    omega
  have hclear : actGates [.ccx zq zs ctrl] J = J := by
    calc
      actGates [.ccx zq zs ctrl] J = actGates [.ccx zq zs ctrl] S := by
        rw [hJ]
      _ = J := hcontrolGate
  have hpoolI : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hzeroQ : bitValue S zq =
      Phase.selectorValue lengthWidth
        (StepLayout.lenQOffset n lengthWidth) S := by
    rw [show bitValue S zq = Phase.selectorValue lengthWidth
        (StepLayout.lenQOffset n lengthWidth) I by
      simpa [S, zq] using ownershipSelectState_zeroQ
        n lengthWidth shiftWidth I]
    unfold Phase.selectorValue
    rw [show readField S (StepLayout.lenQOffset n lengthWidth) lengthWidth =
        readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth by
      simpa [S] using ownershipSelectState_lenQ n lengthWidth shiftWidth I]
  have hzeroShift : bitValue S zs =
      Phase.selectorValue shiftWidth
        (StepLayout.shiftOffset n lengthWidth) S := by
    rw [show bitValue S zs = Phase.selectorValue shiftWidth
        (StepLayout.shiftOffset n lengthWidth) I by
      simpa [S, zs] using ownershipSelectState_zeroShift
        n lengthWidth shiftWidth I]
    unfold Phase.selectorValue
    rw [show readField S (StepLayout.shiftOffset n lengthWidth) shiftWidth =
        readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth by
      simpa [S] using ownershipSelectState_shift n lengthWidth shiftWidth I]
  have hpoolS : readField S
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    rw [show readField S
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) by
      simpa [S] using ownershipSelectState_pool n lengthWidth shiftWidth I,
      hpoolI]
  have hunselectS :
      actGates (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth) S =
        ownershipCleanedState n lengthWidth shiftWidth S :=
    ownershipUnselectBlock_act hzeroQ hzeroShift hpoolS
  have hzeroQI : bitValue I zq = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [zq, StepLayout.zeroQWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hzeroShiftI : bitValue I zs = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [zs, StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcleaned :
      ownershipCleanedState n lengthWidth shiftWidth S = I := by
    simp only [ownershipCleanedState, S, ownershipSelectState]
    rw [writeField_writeField]
    rw [writeField_comm (by
      simp [StepLayout.zeroQWire, StepLayout.zeroShiftWire])]
    rw [writeField_writeField]
    rw [show writeField I zq 1 0 = I by
      apply write_of_bitValue
      simpa [zq] using hzeroQI.symm]
    apply write_of_bitValue
    simpa [zs] using hzeroShiftI.symm
  have hunselect :
      actGates (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth) J =
        I := by
    rw [hJ, hunselectS, hcleaned]
  simp only [Step.ownershipBlock, actGates_append]
  rw [hselect, hcontrolGate, hbody, hiter, hclear, hunselect]

end StepBlocks
end Euclid
end VQ
