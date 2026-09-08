import VQ.Euclid.Step

namespace VQ
namespace Euclid
namespace StepBlocks

open Reversible

private structure WireDistinct (n lengthWidth shiftWidth : Nat) : Prop where
  p1p2 : StepLayout.phase1Wire n lengthWidth shiftWidth ≠
    StepLayout.phase2Wire n lengthWidth shiftWidth
  p1sign : StepLayout.phase1Wire n lengthWidth shiftWidth ≠
    StepLayout.signWire n lengthWidth shiftWidth
  p2sign : StepLayout.phase2Wire n lengthWidth shiftWidth ≠
    StepLayout.signWire n lengthWidth shiftWidth
  p1ctrl : StepLayout.phase1Wire n lengthWidth shiftWidth ≠
    StepLayout.controlWire n lengthWidth shiftWidth
  p2ctrl : StepLayout.phase2Wire n lengthWidth shiftWidth ≠
    StepLayout.controlWire n lengthWidth shiftWidth
  p1temp : StepLayout.phase1Wire n lengthWidth shiftWidth ≠
    StepLayout.temporaryWire n lengthWidth shiftWidth
  p2temp : StepLayout.phase2Wire n lengthWidth shiftWidth ≠
    StepLayout.temporaryWire n lengthWidth shiftWidth
  signtemp : StepLayout.signWire n lengthWidth shiftWidth ≠
    StepLayout.temporaryWire n lengthWidth shiftWidth
  tempctrl : StepLayout.temporaryWire n lengthWidth shiftWidth ≠
    StepLayout.controlWire n lengthWidth shiftWidth
  p1plus : StepLayout.phase1Wire n lengthWidth shiftWidth ≠
    StepLayout.plusWire n lengthWidth shiftWidth
  p2plus : StepLayout.phase2Wire n lengthWidth shiftWidth ≠
    StepLayout.plusWire n lengthWidth shiftWidth
  ctrlplus : StepLayout.controlWire n lengthWidth shiftWidth ≠
    StepLayout.plusWire n lengthWidth shiftWidth
  plustemp : StepLayout.plusWire n lengthWidth shiftWidth ≠
    StepLayout.temporaryWire n lengthWidth shiftWidth
  plusminus : StepLayout.plusWire n lengthWidth shiftWidth ≠
    StepLayout.minusWire n lengthWidth shiftWidth

private theorem stepWireDistinct (n lengthWidth shiftWidth : Nat) :
    WireDistinct n lengthWidth shiftWidth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [StepLayout.phase2Wire, StepLayout.signWire,
      StepLayout.controlWire, StepLayout.temporaryWire, StepLayout.plusWire,
      StepLayout.minusWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset] <;>
    omega

private theorem zeroRPrime_control_ne (n lengthWidth shiftWidth : Nat) :
    StepLayout.zeroRPrimeWire n lengthWidth shiftWidth ≠
      StepLayout.controlWire n lengthWidth shiftWidth := by
  simp [StepLayout.zeroRPrimeWire, StepLayout.controlWire,
    StepLayout.cellScratchWire, StepLayout.poolOffset, StepLayout.carryWire,
    StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
  omega

private theorem zeroRPrime_temporary_ne (n lengthWidth shiftWidth : Nat) :
    StepLayout.zeroRPrimeWire n lengthWidth shiftWidth ≠
      StepLayout.temporaryWire n lengthWidth shiftWidth := by
  simp [StepLayout.zeroRPrimeWire, StepLayout.temporaryWire]

private theorem zeroRPrime_plus_ne (n lengthWidth shiftWidth : Nat) :
    StepLayout.zeroRPrimeWire n lengthWidth shiftWidth ≠
      StepLayout.plusWire n lengthWidth shiftWidth := by
  simp [StepLayout.zeroRPrimeWire, StepLayout.plusWire]

def preShiftControlOut (n lengthWidth shiftWidth I : Nat) : Nat :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let minus := StepLayout.minusWire n lengthWidth shiftWidth
  Phase.ccxOut plus p2 minus (StepControl.negativeOut p1 plus I)

def postShiftControlOut (n lengthWidth shiftWidth I : Nat) : Nat :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let minus := StepLayout.minusWire n lengthWidth shiftWidth
  Phase.ccxOut plus p2 minus
    (writeField I plus 1 ((bitValue I plus + bitValue I p1) % 2))

def remainderAddControlOut (n lengthWidth shiftWidth I : Nat) : Nat :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temp := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  let I := Phase.ccxOut p2 sign temp I
  let I := StepControl.negativeOut p1 plus I
  Phase.negativeAndOut plus temp ctrl I

def coefficientSubControlOut (n lengthWidth shiftWidth I : Nat) : Nat :=
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temp := StepLayout.temporaryWire n lengthWidth shiftWidth
  let ctrl := StepLayout.controlWire n lengthWidth shiftWidth
  let I := Phase.negativeAndOut sign p2 temp I
  Phase.negativeAndOut p1 temp ctrl I

structure ControlClean (n lengthWidth shiftWidth I : Nat) : Prop where
  control : bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) = 0
  temporary : bitValue I
    (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0
  plus : bitValue I (StepLayout.plusWire n lengthWidth shiftWidth) = 0
  minus : bitValue I (StepLayout.minusWire n lengthWidth shiftWidth) = 0

structure RemainderScratchClean
    (n lengthWidth shiftWidth I : Nat) : Prop where
  left : readField I (StepLayout.leftOffset n lengthWidth shiftWidth)
    lengthWidth = 0
  right : readField I (StepLayout.rightOffset n lengthWidth shiftWidth)
    lengthWidth = 0
  control : bitValue I
    (StepLayout.controlWire n lengthWidth shiftWidth) = 0
  carry : bitValue I (StepLayout.carryWire n lengthWidth shiftWidth) = 0
  accumulator : bitValue I
    (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0
  leftFlag : bitValue I
    (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0
  rightFlag : bitValue I
    (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0
  pool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
    lengthWidth = 0
  cellScratch : bitValue I
    (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0

structure RemainderPreparedFrame
    (n lengthWidth shiftWidth I P : Nat) : Prop where
  stable : Interval.Stable
    ((readField I (StepLayout.lenTOffset n) lengthWidth +
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth + 3) %
      2 ^ lengthWidth)
    ((n + 1 +
      (2 ^ lengthWidth -
        readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth)) %
      2 ^ lengthWidth)
    (workWidth n) lengthWidth
    (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth P)
  accumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth P)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0
  carry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth P)
      (Interval.carryWire (workWidth n) lengthWidth) = 0
  work1 : readField P StepLayout.work1Offset (workWidth n) =
    readField I StepLayout.work1Offset (workWidth n)
  work2 : readField P (StepLayout.work2Offset n) (workWidth n) =
    readField I (StepLayout.work2Offset n) (workWidth n)
  sign : bitValue P (StepLayout.signWire n lengthWidth shiftWidth) =
    bitValue I (StepLayout.signWire n lengthWidth shiftWidth)

theorem preShiftControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.preShiftControl n lengthWidth shiftWidth) I =
      preShiftControlOut n lengthWidth shiftWidth I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  rw [Step.preShiftControl, actGates_append]
  rw [StepControl.negative_act hd.p1plus]
  simpa [preShiftControlOut, Phase.ccxGates] using
    Phase.ccxGates_act
      (StepLayout.plusWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.minusWire n lengthWidth shiftWidth)
      (StepControl.negativeOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.plusWire n lengthWidth shiftWidth) I)

theorem postShiftControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.postShiftControl n lengthWidth shiftWidth) I =
      postShiftControlOut n lengthWidth shiftWidth I := by
  rw [Step.postShiftControl, actGates_cons, act_cx_write]
  simpa [postShiftControlOut, Phase.ccxGates] using
    Phase.ccxGates_act
      (StepLayout.plusWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.minusWire n lengthWidth shiftWidth)
      (writeField I (StepLayout.plusWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.plusWire n lengthWidth shiftWidth) +
          bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)) % 2))

theorem postShiftControl_identity_of_phase1_zero_plus_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hplus : bitValue I
      (StepLayout.plusWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.postShiftControl n lengthWidth shiftWidth) I = I := by
  have hplusWrite : writeField I
      (StepLayout.plusWire n lengthWidth shiftWidth) 1
      ((bitValue I (StepLayout.plusWire n lengthWidth shiftWidth) +
        bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)) % 2) =
        I := by
    rw [hphase1, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt I
        (StepLayout.plusWire n lengthWidth shiftWidth))]
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.plusWire n lengthWidth shiftWidth)))
  rw [postShiftControl_act]
  change Phase.ccxOut
      (StepLayout.plusWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.minusWire n lengthWidth shiftWidth)
      (writeField I (StepLayout.plusWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.plusWire n lengthWidth shiftWidth) +
          bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)) % 2)) = I
  rw [hplusWrite]
  simp only [Phase.ccxOut, hplus, Nat.zero_mul, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.minusWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.minusWire n lengthWidth shiftWidth)))

theorem remainderSubControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.remainderSubControl n lengthWidth shiftWidth) I =
      StepControl.negativeOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) I := by
  exact StepControl.negative_act
    (stepWireDistinct n lengthWidth shiftWidth).p1ctrl

theorem remainderFlip_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.remainderFlip n lengthWidth shiftWidth) I =
      Phase.negativeAndOut
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.signWire n lengthWidth shiftWidth) I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  exact Phase.negativeAnd_act
    hd.p1p2.symm hd.p1sign

theorem remainderFlip_identity_of_phase2_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.remainderFlip n lengthWidth shiftWidth) I = I := by
  rw [remainderFlip_act]
  simp only [Phase.negativeAndOut, hphase2, ite_self, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.signWire n lengthWidth shiftWidth))]
  exact write_of_bitValue
    (Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth)))

theorem remainderFlip_identity_of_phase1_one
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1) :
    actGates (Step.remainderFlip n lengthWidth shiftWidth) I = I := by
  rw [remainderFlip_act]
  simp only [Phase.negativeAndOut, hphase1, one_ne_zero, if_false,
    Nat.add_zero, Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.signWire n lengthWidth shiftWidth)))

theorem remainderAddControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.remainderAddControl n lengthWidth shiftWidth) I =
      remainderAddControlOut n lengthWidth shiftWidth I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  simp only [Step.remainderAddControl, actGates_append]
  rw [show actGates
      [.ccx (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.signWire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth)] I =
      Phase.ccxOut
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.signWire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth) I by
    simpa [Phase.ccxGates] using
      Phase.ccxGates_act
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.signWire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth) I]
  rw [StepControl.negative_act hd.p1plus]
  rw [Phase.negativeAnd_act
    hd.plustemp hd.tempctrl]
  rfl

theorem remainderGuard_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.remainderGuard n lengthWidth shiftWidth) I =
      writeField I (StepLayout.controlWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) +
          bitValue I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)) %
          2) := by
  rw [Step.remainderGuard, actGates_cons, actGates_nil, act_cx_write]

theorem guardedRemainderSubControl_act
    (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I =
      writeField
        (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1
        ((bitValue
            (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)
            (StepLayout.controlWire n lengthWidth shiftWidth) +
          bitValue
            (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)
            (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)) % 2) := by
  rw [Step.guardedRemainderSubControl, actGates_append, remainderGuard_act]

theorem guardedRemainderAddControl_act
    (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I =
      writeField
        (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1
        ((bitValue
            (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
            (StepLayout.controlWire n lengthWidth shiftWidth) +
          bitValue
            (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
            (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)) % 2) := by
  rw [Step.guardedRemainderAddControl, actGates_append, remainderGuard_act]

theorem remainderSubControl_preserves_zeroRPrime
    (n lengthWidth shiftWidth I : Nat) :
    bitValue
        (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) := by
  rw [remainderSubControl_act, StepControl.negativeOut_ne
    (zeroRPrime_control_ne n lengthWidth shiftWidth)]

theorem remainderAddControl_preserves_zeroRPrime
    (n lengthWidth shiftWidth I : Nat) :
    bitValue
        (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) := by
  rw [remainderAddControl_act, remainderAddControlOut,
    Phase.negativeAndOut_ne
      (zeroRPrime_control_ne n lengthWidth shiftWidth),
    StepControl.negativeOut_ne
      (zeroRPrime_plus_ne n lengthWidth shiftWidth),
    Phase.ccxOut_ne
      (zeroRPrime_temporary_ne n lengthWidth shiftWidth)]

theorem guardedRemainderSubControl_act_live
    {n lengthWidth shiftWidth I : Nat}
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I =
      actGates (Step.remainderSubControl n lengthWidth shiftWidth) I := by
  rw [guardedRemainderSubControl_act,
    remainderSubControl_preserves_zeroRPrime, hzeroRPrime]
  simp only [Nat.add_zero]
  apply write_of_bitValue
  simp [Nat.mod_eq_of_lt (bitValue_lt _ _)]

theorem guardedRemainderAddControl_act_live
    {n lengthWidth shiftWidth I : Nat}
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I =
      actGates (Step.remainderAddControl n lengthWidth shiftWidth) I := by
  rw [guardedRemainderAddControl_act,
    remainderAddControl_preserves_zeroRPrime, hzeroRPrime]
  simp only [Nat.add_zero]
  apply write_of_bitValue
  simp [Nat.mod_eq_of_lt (bitValue_lt _ _)]

theorem guardedRemainderAddControl_act_phase00
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.plusWire n lengthWidth shiftWidth) 1 1)
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hd := stepWireDistinct n lengthWidth shiftWidth
  have hfirst : Phase.ccxOut p2 sign temporary I = I := by
    rw [Phase.ccxOut, show bitValue I p2 = 0 by exact hphase2,
      Nat.zero_mul, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt I temporary)]
    exact write_of_bitValue
      (Nat.mod_eq_of_lt (bitValue_lt I temporary))
  have hsecond : StepControl.negativeOut p1 plus I =
      writeField I plus 1 1 := by
    simp [StepControl.negativeOut, hphase1, hclean.plus, p1, plus]
  have hcontrolAfterPlus : bitValue (writeField I plus 1 1) control = 0 := by
    rw [bitValue_write_ne]
    · exact hclean.control
    · exact hd.ctrlplus
  have htemporaryAfterPlus :
      bitValue (writeField I plus 1 1) temporary = 0 := by
    rw [bitValue_write_ne]
    · exact hclean.temporary
    · exact hd.plustemp.symm
  have hplusAfterPlus : bitValue (writeField I plus 1 1) plus = 1 := by
    rw [bitValue_write_self]
  have hthird : Phase.negativeAndOut plus temporary control
      (writeField I plus 1 1) =
        writeField (writeField I plus 1 1) control 1 1 := by
    rw [Phase.negativeAndOut, hcontrolAfterPlus, htemporaryAfterPlus,
      hplusAfterPlus]
    rfl
  rw [guardedRemainderAddControl_act_live hzeroRPrime,
    remainderAddControl_act]
  simp only [remainderAddControlOut]
  rw [hfirst, hsecond, hthird]

theorem guardedRemainderSubControl_identity
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I =
      I := by
  rw [guardedRemainderSubControl_act, remainderSubControl_act]
  simp only [StepControl.negativeOut, hclean.control, hphase1, if_pos,
    Nat.zero_add, Nat.one_mod, bitValue_write_self]
  rw [bitValue_write_ne (zeroRPrime_control_ne n lengthWidth shiftWidth),
    hzeroRPrime]
  simp only [Nat.reduceAdd, Nat.reduceMod, writeField_writeField]
  rw [show writeField I (StepLayout.controlWire n lengthWidth shiftWidth) 1 0 =
      I by
    rw [← hclean.control, ← readField_one, writeField_read]]

theorem guardedRemainderSubControl_identity_of_phase1_one_live
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I =
      I := by
  rw [guardedRemainderSubControl_act_live hzeroRPrime,
    remainderSubControl_act]
  simp only [StepControl.negativeOut, hclean.control, hphase1,
    one_ne_zero, if_false, Nat.add_zero, Nat.zero_mod]
  rw [← hclean.control, ← readField_one, writeField_read]

theorem guardedRemainderAddControl_identity_of_phase10_live
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I =
      I := by
  let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
  let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  let temporary := StepLayout.temporaryWire n lengthWidth shiftWidth
  let plus := StepLayout.plusWire n lengthWidth shiftWidth
  let control := StepLayout.controlWire n lengthWidth shiftWidth
  have hfirst : Phase.ccxOut p2 sign temporary I = I := by
    rw [Phase.ccxOut, show bitValue I p2 = 0 by exact hphase2,
      Nat.zero_mul, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt I temporary)]
    exact write_of_bitValue
      (Nat.mod_eq_of_lt (bitValue_lt I temporary))
  have hsecond : StepControl.negativeOut p1 plus I = I := by
    rw [StepControl.negativeOut,
      show bitValue I p1 = 1 by exact hphase1]
    simp only [one_ne_zero, if_false, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (bitValue_lt I plus)]
    exact write_of_bitValue
      (Nat.mod_eq_of_lt (bitValue_lt I plus))
  have hthird : Phase.negativeAndOut plus temporary control I = I := by
    have hcontrol : bitValue I control = 0 := hclean.control
    have htemporary : bitValue I temporary = 0 := hclean.temporary
    have hplus : bitValue I plus = 0 := hclean.plus
    rw [Phase.negativeAndOut, htemporary]
    simp only [if_pos, hcontrol, hplus, Nat.add_zero, Nat.zero_mod]
    rw [← hcontrol, ← readField_one, writeField_read]
  rw [guardedRemainderAddControl_act_live hzeroRPrime,
    remainderAddControl_act]
  simp only [remainderAddControlOut]
  rw [hfirst, hsecond, hthird]

theorem swapControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.swapControl n lengthWidth shiftWidth) I =
      Phase.xorPairOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) I := by
  exact Phase.xorPair_act
    (stepWireDistinct n lengthWidth shiftWidth).p2ctrl

theorem swapControl_identity_of_equal_phases
    {n lengthWidth shiftWidth I : Nat}
    (hphases : bitValue I
        (StepLayout.phase1Wire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth)) :
    actGates (Step.swapControl n lengthWidth shiftWidth) I = I := by
  rw [swapControl_act]
  simp only [Phase.xorPairOut]
  apply write_of_bitValue
  have hphase2 := bitValue_lt I
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
  have hcontrol := bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)
  interval_cases hphase2Value : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) <;>
    interval_cases hcontrolValue : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) <;>
    simp_all

theorem quotientDecrementControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I =
      Phase.negativeAndOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  exact Phase.negativeAnd_act
    hd.p1p2 hd.p2ctrl

theorem quotientDecrementControl_identity_of_phase2_one
    {n lengthWidth shiftWidth I : Nat}
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1) :
    actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I := by
  rw [quotientDecrementControl_act]
  simp only [Phase.negativeAndOut, hphase2, one_ne_zero, if_false,
    Nat.add_zero, Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem quotientDecrementControl_identity_of_phase1_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I = I := by
  rw [quotientDecrementControl_act]
  simp only [Phase.negativeAndOut, hphase1, ite_self, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem quotientIncrementControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I =
      Phase.negativeAndOut
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  exact Phase.negativeAnd_act
    hd.p1p2.symm hd.p1ctrl

theorem quotientIncrementControl_identity_of_phase2_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I := by
  rw [quotientIncrementControl_act]
  simp only [Phase.negativeAndOut, hphase2, ite_self, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem quotientIncrementControl_identity_of_phase1_one
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1) :
    actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I = I := by
  rw [quotientIncrementControl_act]
  simp only [Phase.negativeAndOut, hphase1, one_ne_zero, if_false,
    Nat.add_zero, Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem coefficientSubControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I =
      coefficientSubControlOut n lengthWidth shiftWidth I := by
  have hd := stepWireDistinct n lengthWidth shiftWidth
  rw [Step.coefficientSubControl, actGates_append]
  rw [Phase.negativeAnd_act
    hd.p2sign.symm hd.p2temp]
  rw [Phase.negativeAnd_act
    hd.p1temp hd.tempctrl]
  rfl

theorem coefficientSubControl_identity_of_phase01
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1) :
    actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I = I := by
  have htemporary : Phase.negativeAndOut
      (StepLayout.signWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.temporaryWire n lengthWidth shiftWidth) I = I := by
    simp only [Phase.negativeAndOut, hphase2, one_ne_zero, if_false,
      Nat.add_zero, Nat.mod_eq_of_lt (bitValue_lt I
        (StepLayout.temporaryWire n lengthWidth shiftWidth))]
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.temporaryWire n lengthWidth shiftWidth)))
  rw [coefficientSubControl_act]
  simp only [coefficientSubControlOut]
  rw [htemporary]
  simp only [Phase.negativeAndOut, hphase1, ite_self, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem coefficientSubControl_act_phase11
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1) :
    actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I =
      writeField I (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  have htemporary : Phase.negativeAndOut
      (StepLayout.signWire n lengthWidth shiftWidth)
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
      (StepLayout.temporaryWire n lengthWidth shiftWidth) I = I := by
    simp only [Phase.negativeAndOut, hphase2, one_ne_zero, if_false,
      Nat.add_zero, Nat.mod_eq_of_lt (bitValue_lt I
        (StepLayout.temporaryWire n lengthWidth shiftWidth))]
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.temporaryWire n lengthWidth shiftWidth)))
  rw [coefficientSubControl_act]
  change Phase.negativeAndOut
      (StepLayout.phase1Wire n lengthWidth shiftWidth)
      (StepLayout.temporaryWire n lengthWidth shiftWidth)
      (StepLayout.controlWire n lengthWidth shiftWidth)
      (Phase.negativeAndOut
        (StepLayout.signWire n lengthWidth shiftWidth)
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth) I) = _
  rw [htemporary, Phase.negativeAndOut, hclean.control, hclean.temporary,
    hphase1]
  norm_num

theorem coefficientFlip_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.coefficientFlip n lengthWidth shiftWidth) I =
      writeField I (StepLayout.signWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.signWire n lengthWidth shiftWidth) +
          bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)) % 2) := by
  rw [Step.coefficientFlip, actGates_cons, actGates_nil, act_cx_write]

theorem coefficientFlip_identity_of_phase1_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.coefficientFlip n lengthWidth shiftWidth) I = I := by
  rw [coefficientFlip_act, hphase1, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.signWire n lengthWidth shiftWidth)))

theorem coefficientAddControl_act (n lengthWidth shiftWidth I : Nat) :
    actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I =
      writeField I (StepLayout.controlWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) +
          bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)) % 2) := by
  rw [Step.coefficientAddControl, actGates_cons, actGates_nil, act_cx_write]

theorem coefficientAddControl_identity_of_phase1_zero
    {n lengthWidth shiftWidth I : Nat}
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I = I := by
  rw [coefficientAddControl_act, hphase1, Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I
      (StepLayout.controlWire n lengthWidth shiftWidth))]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I
    (StepLayout.controlWire n lengthWidth shiftWidth)))

theorem preShiftControl_bits
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
    let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
    let plus := StepLayout.plusWire n lengthWidth shiftWidth
    let minus := StepLayout.minusWire n lengthWidth shiftWidth
    let J := actGates (Step.preShiftControl n lengthWidth shiftWidth) I
    bitValue J plus = (if bitValue I p1 = 0 then 1 else 0) ∧
      bitValue J minus =
        (if bitValue I p1 = 0 then bitValue I p2 else 0) := by
  dsimp only
  have hd := stepWireDistinct n lengthWidth shiftWidth
  rw [preShiftControl_act]
  constructor
  · rw [preShiftControlOut, Phase.ccxOut_ne]
    · rw [StepControl.negativeOut_target, h.plus]
      split <;> omega
    · exact hd.plusminus
  · rw [preShiftControlOut, Phase.ccxOut_target,
      StepControl.negativeOut_ne, StepControl.negativeOut_target,
      StepControl.negativeOut_ne]
    · rw [h.minus, h.plus]
      have hp2 := bitValue_lt I
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
      by_cases hp1 : bitValue I
          (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
      · simp [hp1]
        exact hp2
      · have hp1one : bitValue I
            (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1 := by
          have := bitValue_lt I
            (StepLayout.phase1Wire n lengthWidth shiftWidth)
          omega
        simp [hp1one]
    · exact hd.p2plus
    · exact hd.plusminus.symm

theorem postShiftControl_bits
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
    let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
    let plus := StepLayout.plusWire n lengthWidth shiftWidth
    let minus := StepLayout.minusWire n lengthWidth shiftWidth
    let J := actGates (Step.postShiftControl n lengthWidth shiftWidth) I
    bitValue J plus = bitValue I p1 ∧
      bitValue J minus = bitValue I p1 * bitValue I p2 := by
  dsimp only
  rw [postShiftControl_act]
  constructor
  · rw [postShiftControlOut, Phase.ccxOut_ne]
    · rw [bitValue_write_self, h.plus]
      have hp1 := bitValue_lt I
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
      omega
    · simp only [StepLayout.minusWire, StepLayout.plusWire]
      omega
  · rw [postShiftControlOut, Phase.ccxOut_target,
      bitValue_write_ne, bitValue_write_self, bitValue_write_ne]
    · rw [h.minus, h.plus]
      have hp1 := bitValue_lt I
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
      have hp2 := bitValue_lt I
        (StepLayout.phase2Wire n lengthWidth shiftWidth)
      interval_cases hp1v : bitValue I
          (StepLayout.phase1Wire n lengthWidth shiftWidth) <;>
        interval_cases hp2v : bitValue I
          (StepLayout.phase2Wire n lengthWidth shiftWidth) <;> simp_all
    · exact (stepWireDistinct n lengthWidth shiftWidth).p2plus
    · exact (stepWireDistinct n lengthWidth shiftWidth).plusminus.symm

theorem remainderSubControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    bitValue (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      if bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
        then 1 else 0 := by
  rw [remainderSubControl_act, StepControl.negativeOut_target, h.control]
  split <;> omega

theorem remainderAddControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
    let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
    let sign := StepLayout.signWire n lengthWidth shiftWidth
    bitValue (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      if bitValue I p1 = 0 then
        if bitValue I p2 * bitValue I sign = 0 then 1 else 0
      else 0 := by
  dsimp only
  have hd := stepWireDistinct n lengthWidth shiftWidth
  let K := Phase.ccxOut
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.signWire n lengthWidth shiftWidth)
    (StepLayout.temporaryWire n lengthWidth shiftWidth) I
  let L := StepControl.negativeOut
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
    (StepLayout.plusWire n lengthWidth shiftWidth) K
  have hLctrl : bitValue L
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    simp only [L, K]
    rw [StepControl.negativeOut_ne hd.ctrlplus,
      Phase.ccxOut_ne hd.tempctrl.symm, h.control]
  have hLplus : bitValue L (StepLayout.plusWire n lengthWidth shiftWidth) =
      if bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
        then 1 else 0 := by
    simp only [L, K]
    rw [StepControl.negativeOut_target,
      Phase.ccxOut_ne hd.plustemp, h.plus,
      Phase.ccxOut_ne hd.p1temp]
    split <;> omega
  have hLtemp : bitValue L
      (StepLayout.temporaryWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) *
        bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    simp only [L, K]
    rw [StepControl.negativeOut_ne hd.plustemp.symm,
      Phase.ccxOut_target, h.temporary]
    have hp2 := bitValue_lt I
      (StepLayout.phase2Wire n lengthWidth shiftWidth)
    have hs := bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth)
    interval_cases hp2v : bitValue I
        (StepLayout.phase2Wire n lengthWidth shiftWidth) <;>
      interval_cases hsv : bitValue I
        (StepLayout.signWire n lengthWidth shiftWidth) <;> simp_all
  rw [remainderAddControl_act]
  change bitValue
      (Phase.negativeAndOut
        (StepLayout.plusWire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) L)
      (StepLayout.controlWire n lengthWidth shiftWidth) = _
  rw [Phase.negativeAndOut_target, hLctrl, hLplus, hLtemp]
  have hp1 := bitValue_lt I
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
  have hp2 := bitValue_lt I
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
  have hs := bitValue_lt I
    (StepLayout.signWire n lengthWidth shiftWidth)
  interval_cases hp1v : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) <;>
    interval_cases hp2v : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) <;>
    interval_cases hsv : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) <;> simp_all

theorem guardedRemainderAddControl_bit_terminal
    {n lengthWidth shiftWidth I : Nat}
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1) :
    bitValue
        (actGates
          (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
  rw [guardedRemainderAddControl_act, bitValue_write_self]
  have hcontrol := remainderAddControl_bit hclean
  dsimp only at hcontrol
  rw [hphase1, hphase2, hsign] at hcontrol
  simp only [if_pos, Nat.zero_mul] at hcontrol
  have hzero : bitValue
      (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1 := by
    rw [remainderAddControl_act]
    rw [remainderAddControlOut,
      Phase.negativeAndOut_ne
        (zeroRPrime_control_ne n lengthWidth shiftWidth),
      StepControl.negativeOut_ne
        (zeroRPrime_plus_ne n lengthWidth shiftWidth),
      Phase.ccxOut_ne
        (zeroRPrime_temporary_ne n lengthWidth shiftWidth)]
    exact hzeroRPrime
  rw [hcontrol, hzero]

theorem swapControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    bitValue (actGates (Step.swapControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      (bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) +
        bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth)) % 2 := by
  rw [swapControl_act, Phase.xorPairOut_target, h.control]
  omega

theorem quotientDecrementControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    bitValue
        (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      if bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0
        then bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth)
        else 0 := by
  rw [quotientDecrementControl_act, Phase.negativeAndOut_target, h.control]
  have hp1 := bitValue_lt I
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
  split <;> omega

theorem quotientIncrementControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    bitValue
        (actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      if bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0
        then bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth)
        else 0 := by
  rw [quotientIncrementControl_act, Phase.negativeAndOut_target, h.control]
  have hp2 := bitValue_lt I
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
  split <;> omega

theorem coefficientSubControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    let p1 := StepLayout.phase1Wire n lengthWidth shiftWidth
    let p2 := StepLayout.phase2Wire n lengthWidth shiftWidth
    let sign := StepLayout.signWire n lengthWidth shiftWidth
    bitValue (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      if (if bitValue I p2 = 0 then bitValue I sign else 0) = 0
        then bitValue I p1 else 0 := by
  dsimp only
  have hd := stepWireDistinct n lengthWidth shiftWidth
  let K := Phase.negativeAndOut
    (StepLayout.signWire n lengthWidth shiftWidth)
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
    (StepLayout.temporaryWire n lengthWidth shiftWidth) I
  have hKctrl : bitValue K
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    simp only [K]
    rw [Phase.negativeAndOut_ne hd.tempctrl.symm, h.control]
  have hKp1 : bitValue K (StepLayout.phase1Wire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) := by
    simp only [K]
    rw [Phase.negativeAndOut_ne hd.p1temp]
  have hKtemp : bitValue K
      (StepLayout.temporaryWire n lengthWidth shiftWidth) =
      if bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0
        then bitValue I (StepLayout.signWire n lengthWidth shiftWidth)
        else 0 := by
    simp only [K]
    rw [Phase.negativeAndOut_target, h.temporary]
    have hs := bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth)
    split <;> omega
  rw [coefficientSubControl_act]
  change bitValue
      (Phase.negativeAndOut
        (StepLayout.phase1Wire n lengthWidth shiftWidth)
        (StepLayout.temporaryWire n lengthWidth shiftWidth)
        (StepLayout.controlWire n lengthWidth shiftWidth) K)
      (StepLayout.controlWire n lengthWidth shiftWidth) = _
  rw [Phase.negativeAndOut_target, hKctrl, hKp1, hKtemp]
  have hp1 := bitValue_lt I
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
  have hp2 := bitValue_lt I
    (StepLayout.phase2Wire n lengthWidth shiftWidth)
  have hs := bitValue_lt I
    (StepLayout.signWire n lengthWidth shiftWidth)
  interval_cases hp1v : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) <;>
    interval_cases hp2v : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) <;>
    interval_cases hsv : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) <;> simp_all

theorem coefficientAddControl_bit
    {n lengthWidth shiftWidth I : Nat}
    (h : ControlClean n lengthWidth shiftWidth I) :
    bitValue (actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I)
        (StepLayout.controlWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) := by
  rw [coefficientAddControl_act, bitValue_write_self, h.control]
  have hp1 := bitValue_lt I
    (StepLayout.phase1Wire n lengthWidth shiftWidth)
  omega

theorem around_identity {compute body : List RGate} {width I : Nat}
    (hwf : compute.all (RGate.wellFormed width) = true)
    (hbody : actGates body (actGates compute I) = actGates compute I) :
    actGates (Step.around compute body) I = I := by
  rw [Step.around, actGates_append, actGates_append, hbody]
  exact actGates_reverse hwf I

theorem around_write {compute body : List RGate} {width I off len value : Nat}
    (hwf : compute.all (RGate.wellFormed width) = true)
    (hout : ∀ g ∈ compute, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q)
    (hbody : actGates body (actGates compute I) =
      writeField (actGates compute I) off len value) :
    actGates (Step.around compute body) I =
      writeField I off len value := by
  rw [Step.around, actGates_append, actGates_append, hbody]
  rw [actGates_write_of_outside
    (fun g hg q hq => hout g (List.mem_reverse.mp hg) q hq)]
  rw [actGates_reverse hwf]

theorem around_write_two
    {compute body : List RGate} {width I o1 l1 v1 o2 l2 v2 : Nat}
    (hwf : compute.all (RGate.wellFormed width) = true)
    (hout1 : ∀ g ∈ compute, ∀ q ∈ g.wires, q < o1 ∨ o1 + l1 ≤ q)
    (hout2 : ∀ g ∈ compute, ∀ q ∈ g.wires, q < o2 ∨ o2 + l2 ≤ q)
    (hbody : actGates body (actGates compute I) =
      writeField (writeField (actGates compute I) o1 l1 v1) o2 l2 v2) :
    actGates (Step.around compute body) I =
      writeField (writeField I o1 l1 v1) o2 l2 v2 := by
  rw [Step.around, actGates_append, actGates_append, hbody]
  rw [actGates_write_of_outside
    (fun g hg q hq => hout2 g (List.mem_reverse.mp hg) q hq)]
  rw [actGates_write_of_outside
    (fun g hg q hq => hout1 g (List.mem_reverse.mp hg) q hq)]
  rw [actGates_reverse hwf]

end StepBlocks
end Euclid
end VQ
