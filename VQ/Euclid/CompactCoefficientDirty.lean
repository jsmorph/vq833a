/-
Coefficient arithmetic with a restored dirty temporary bit.
-/
import VQ.Euclid.CompactCoefficientPass
import VQ.Euclid.StepBlocks.Control

namespace VQ
namespace Euclid
namespace CompactCoefficientDirty

open Reversible

def count : Nat := CompactCoefficientPass.count
def layout : Layout := CompactCoefficientPass.layout

def phaseOneWire : Nat := CompactCoefficientPass.phaseOneWire
def phaseTwoWire : Nat := CompactCoefficientPass.phaseTwoWire
def signWire : Nat := CompactCoefficientPass.signWire
def workOneOffset : Nat := CompactCoefficientPass.workOneOffset
def workTwoOffset : Nat := CompactCoefficientPass.workTwoOffset
def lengthTOffset : Nat := CompactCoefficientPass.lengthTOffset
def lengthRPrimeOffset : Nat := CompactCoefficientPass.lengthRPrimeOffset
def extensionWire : Nat := CompactCoefficientPass.extensionWire
def shiftOffset : Nat := CompactCoefficientPass.shiftOffset
def controlWire : Nat := CompactCoefficientPass.controlWire
def temporaryWire : Nat := CompactCoefficientPass.temporaryWire
def scratchOffset : Nat := CompactCoefficientPass.scratchOffset
def carryWire : Nat := CompactCoefficientPass.carryWire
def accumulatorWire : Nat := CompactCoefficientPass.accumulatorWire
def cellScratchWire : Nat := CompactCoefficientPass.cellScratchWire

def preparedT (I : Nat) : Nat := CompactCoefficientPass.preparedT I
def preparedRPrime (I : Nat) : Nat := CompactCoefficientPass.preparedRPrime I

def dirtyTripleGates : List RGate :=
  [.ccx phaseOneWire signWire temporaryWire] ++
    Phase.negativeAndGates temporaryWire phaseTwoWire controlWire ++
    [.ccx phaseOneWire signWire temporaryWire] ++
    Phase.negativeAndGates temporaryWire phaseTwoWire controlWire

def subtractControlGates : List RGate :=
  [.cx phaseOneWire controlWire] ++ dirtyTripleGates

def subtractControlValue (I : Nat) : Nat :=
  (bitValue I controlWire + bitValue I phaseOneWire +
    bitValue I phaseOneWire * bitValue I signWire *
      (if bitValue I phaseTwoWire = 0 then 1 else 0)) % 2

private theorem ccx_off_left {a b target I : Nat}
    (ha : bitValue I a = 0) :
    actGates [.ccx a b target] I = I := by
  have ha' : I.testBit a = false := by simpa [bitValue] using ha
  simp [actGates, RGate.act, ha']

private theorem ccx_off_right {a b target I : Nat}
    (hb : bitValue I b = 0) :
    actGates [.ccx a b target] I = I := by
  have hb' : I.testBit b = false := by simpa [bitValue] using hb
  by_cases ha' : I.testBit a = true <;> simp [actGates, RGate.act, ha', hb']

private theorem ccx_on {a b target I : Nat}
    (ha : bitValue I a = 1) (hb : bitValue I b = 1) :
    actGates [.ccx a b target] I = I ^^^ (1 <<< target) := by
  have ha' : I.testBit a = true := by simpa [bitValue] using ha
  have hb' : I.testBit b = true := by simpa [bitValue] using hb
  simp [actGates, RGate.act, ha', hb']

private theorem negativeAnd_off {a b target I : Nat}
    (hab : a ≠ b) (ha : bitValue I a = 0) :
    actGates (Phase.negativeAndGates a b target) I = I := by
  simpa [Phase.negativeAndGates, PrunedSelectSwap.Tree.negativeAnd] using
    PrunedSelectSwap.Tree.negativeAnd_off (child := target) hab ha

private theorem negativeAnd_on_zero {a b target I : Nat}
    (hab : a ≠ b) (ha : bitValue I a = 1)
    (hb : bitValue I b = 0) :
    actGates (Phase.negativeAndGates a b target) I =
      I ^^^ (1 <<< target) := by
  simpa [Phase.negativeAndGates, PrunedSelectSwap.Tree.negativeAnd] using
    PrunedSelectSwap.Tree.negativeAnd_on_zero (child := target) hab ha hb

private theorem negativeAnd_on_one {a b target I : Nat}
    (hab : a ≠ b) (ha : bitValue I a = 1)
    (hb : bitValue I b = 1) :
    actGates (Phase.negativeAndGates a b target) I = I := by
  simpa [Phase.negativeAndGates, PrunedSelectSwap.Tree.negativeAnd] using
    PrunedSelectSwap.Tree.negativeAnd_on_one (child := target) hab ha hb

private theorem negativeAnd_preserves {a b target I q : Nat}
    (hab : a ≠ b) (hbt : b ≠ target) (hq : q ≠ target) :
    bitValue (actGates (Phase.negativeAndGates a b target) I) q =
      bitValue I q := by
  rw [Phase.negativeAnd_act hab hbt, Phase.negativeAndOut_ne hq]

private theorem negativeAnd_twice {a b target I : Nat}
    (hab : a ≠ b) (hbt : b ≠ target) (hat : a ≠ target) :
    actGates (Phase.negativeAndGates a b target)
        (actGates (Phase.negativeAndGates a b target) I) = I := by
  rcases Nat.eq_zero_or_pos (bitValue I a) with ha | ha
  · have ha' : bitValue I a = 0 := ha
    rw [negativeAnd_off hab ha', negativeAnd_off hab ha']
  · have ha' : bitValue I a = 1 := by
      have h := bitValue_lt I a
      omega
    rcases Nat.eq_zero_or_pos (bitValue I b) with hb | hb
    · have hb' : bitValue I b = 0 := hb
      rw [negativeAnd_on_zero hab ha' hb']
      have haXor : bitValue (I ^^^ (1 <<< target)) a = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne hat, ha']
      have hbXor : bitValue (I ^^^ (1 <<< target)) b = 0 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne hbt, hb']
      rw [negativeAnd_on_zero hab haXor hbXor, RGate.xor_cancel]
    · have hb' : bitValue I b = 1 := by
        have h := bitValue_lt I b
        omega
      rw [negativeAnd_on_one hab ha' hb', negativeAnd_on_one hab ha' hb']

theorem dirtyTripleGates_act (I : Nat) :
    actGates dirtyTripleGates I =
      I ^^^
        ((bitValue I phaseOneWire * bitValue I signWire *
          (if bitValue I phaseTwoWire = 0 then 1 else 0)) <<<
            controlWire) := by
  have htemporaryPhaseTwo : temporaryWire ≠ phaseTwoWire := by decide
  have hphaseTwoControl : phaseTwoWire ≠ controlWire := by decide
  have htemporaryControl : temporaryWire ≠ controlWire := by decide
  have hphaseOneControl : phaseOneWire ≠ controlWire := by decide
  have hsignControl : signWire ≠ controlWire := by decide
  have hphaseOneTemporary : phaseOneWire ≠ temporaryWire := by decide
  have hsignTemporary : signWire ≠ temporaryWire := by decide
  have hphaseTwoTemporary : phaseTwoWire ≠ temporaryWire := by decide
  let A : List RGate := [.ccx phaseOneWire signWire temporaryWire]
  let N : List RGate :=
    Phase.negativeAndGates temporaryWire phaseTwoWire controlWire
  change actGates N (actGates A (actGates N (actGates A I))) = _
  rcases Nat.eq_zero_or_pos (bitValue I phaseOneWire) with hp1 | hp1
  · have hp1' : bitValue I phaseOneWire = 0 := hp1
    have hA : actGates A I = I := ccx_off_left hp1'
    have hp1N : bitValue (actGates N I) phaseOneWire = 0 := by
      rw [negativeAnd_preserves htemporaryPhaseTwo hphaseTwoControl
        hphaseOneControl, hp1']
    have hAN : actGates A (actGates N I) = actGates N I :=
      ccx_off_left hp1N
    rw [hA, hAN, negativeAnd_twice htemporaryPhaseTwo
      hphaseTwoControl htemporaryControl]
    simp [hp1']
  · have hp1' : bitValue I phaseOneWire = 1 := by
      have h := bitValue_lt I phaseOneWire
      omega
    rcases Nat.eq_zero_or_pos (bitValue I signWire) with hs | hs
    · have hs' : bitValue I signWire = 0 := hs
      have hA : actGates A I = I := ccx_off_right hs'
      have hsN : bitValue (actGates N I) signWire = 0 := by
        rw [negativeAnd_preserves htemporaryPhaseTwo hphaseTwoControl
          hsignControl, hs']
      have hAN : actGates A (actGates N I) = actGates N I :=
        ccx_off_right hsN
      rw [hA, hAN, negativeAnd_twice htemporaryPhaseTwo
        hphaseTwoControl htemporaryControl]
      simp [hs']
    · have hs' : bitValue I signWire = 1 := by
        have h := bitValue_lt I signWire
        omega
      have hA : actGates A I = I ^^^ (1 <<< temporaryWire) :=
        ccx_on hp1' hs'
      have hp1Xor : bitValue (I ^^^ (1 <<< temporaryWire)) phaseOneWire = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne
          hphaseOneTemporary, hp1']
      have hsXor : bitValue (I ^^^ (1 <<< temporaryWire)) signWire = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne hsignTemporary, hs']
      rcases Nat.eq_zero_or_pos (bitValue I phaseTwoWire) with hp2 | hp2
      · have hp2' : bitValue I phaseTwoWire = 0 := hp2
        have hp2Xor :
            bitValue (I ^^^ (1 <<< temporaryWire)) phaseTwoWire = 0 := by
          rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne
            hphaseTwoTemporary, hp2']
        rcases Nat.eq_zero_or_pos (bitValue I temporaryWire) with ht | ht
        · have ht' : bitValue I temporaryWire = 0 := ht
          have htXor : bitValue (I ^^^ (1 <<< temporaryWire)) temporaryWire = 1 :=
            PrunedSelectSwap.Tree.bitValue_xor_self_zero ht'
          have hN1 := negativeAnd_on_zero (target := controlWire)
            htemporaryPhaseTwo htXor hp2Xor
          rw [hA, hN1]
          have hp1XorControl :
              bitValue ((I ^^^ (1 <<< temporaryWire)) ^^^
                (1 <<< controlWire)) phaseOneWire = 1 := by
            rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne hphaseOneControl,
              hp1Xor]
          have hsXorControl :
              bitValue ((I ^^^ (1 <<< temporaryWire)) ^^^
                (1 <<< controlWire)) signWire = 1 := by
            rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne hsignControl,
              hsXor]
          rw [ccx_on hp1XorControl hsXorControl]
          have hnormalize :
              ((I ^^^ (1 <<< temporaryWire)) ^^^ (1 <<< controlWire)) ^^^
                  (1 <<< temporaryWire) = I ^^^ (1 <<< controlWire) := by
            rw [Nat.xor_assoc]
            conv_lhs =>
              rhs
              rw [Nat.xor_comm]
            rw [← Nat.xor_assoc, RGate.xor_cancel]
          rw [hnormalize]
          have htControl :
              bitValue (I ^^^ (1 <<< controlWire)) temporaryWire = 0 := by
            rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne
              htemporaryControl, ht']
          rw [negativeAnd_off htemporaryPhaseTwo htControl]
          simp [hp1', hs', hp2']
        · have ht' : bitValue I temporaryWire = 1 := by
            have h := bitValue_lt I temporaryWire
            omega
          have htXor : bitValue (I ^^^ (1 <<< temporaryWire)) temporaryWire = 0 :=
            PrunedSelectSwap.Tree.bitValue_xor_self_one ht'
          rw [hA, negativeAnd_off htemporaryPhaseTwo htXor]
          rw [ccx_on hp1Xor hsXor, RGate.xor_cancel]
          rw [negativeAnd_on_zero htemporaryPhaseTwo ht' hp2']
          simp [hp1', hs', hp2']
      · have hp2' : bitValue I phaseTwoWire = 1 := by
          have h := bitValue_lt I phaseTwoWire
          omega
        have hp2Xor :
            bitValue (I ^^^ (1 <<< temporaryWire)) phaseTwoWire = 1 := by
          rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne
            hphaseTwoTemporary, hp2']
        rcases Nat.eq_zero_or_pos (bitValue I temporaryWire) with ht | ht
        · have ht' : bitValue I temporaryWire = 0 := ht
          have htXor : bitValue (I ^^^ (1 <<< temporaryWire)) temporaryWire = 1 :=
            PrunedSelectSwap.Tree.bitValue_xor_self_zero ht'
          rw [hA, negativeAnd_on_one htemporaryPhaseTwo htXor hp2Xor]
          rw [ccx_on hp1Xor hsXor, RGate.xor_cancel]
          rw [negativeAnd_off htemporaryPhaseTwo ht']
          simp [hp2']
        · have ht' : bitValue I temporaryWire = 1 := by
            have h := bitValue_lt I temporaryWire
            omega
          have htXor : bitValue (I ^^^ (1 <<< temporaryWire)) temporaryWire = 0 :=
            PrunedSelectSwap.Tree.bitValue_xor_self_one ht'
          rw [hA, negativeAnd_off htemporaryPhaseTwo htXor]
          rw [ccx_on hp1Xor hsXor, RGate.xor_cancel]
          rw [negativeAnd_on_one htemporaryPhaseTwo ht' hp2']
          simp [hp2']

theorem subtractControlGates_act (I : Nat) :
    actGates subtractControlGates I =
      writeField I controlWire 1 (subtractControlValue I) := by
  rw [subtractControlGates, actGates_append, dirtyTripleGates_act]
  rw [show actGates [.cx phaseOneWire controlWire] I =
      writeField I controlWire 1
        ((bitValue I controlWire + bitValue I phaseOneWire) % 2) by
    simp [actGates_cons, actGates_nil, act_cx_write]]
  rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
    bitValue_write_ne (by decide)]
  by_cases hproduct : bitValue I phaseOneWire * bitValue I signWire *
      (if bitValue I phaseTwoWire = 0 then 1 else 0) = 0
  · simp [hproduct, subtractControlValue]
  · have hproductOne : bitValue I phaseOneWire * bitValue I signWire *
        (if bitValue I phaseTwoWire = 0 then 1 else 0) = 1 := by
      by_cases hp2 : bitValue I phaseTwoWire = 0
      · have hp1nz : bitValue I phaseOneWire ≠ 0 := by
          intro hp1
          simp [hp1] at hproduct
        have hsnz : bitValue I signWire ≠ 0 := by
          intro hs
          simp [hs] at hproduct
        have hp1lt := bitValue_lt I phaseOneWire
        have hslt := bitValue_lt I signWire
        have hp1 : bitValue I phaseOneWire = 1 := by omega
        have hs : bitValue I signWire = 1 := by omega
        simp [hp1, hs, hp2]
      · simp [hp2] at hproduct
    rw [hproductOne, flip_eq,
      bitValue_write_self, writeField_writeField]
    simp only [subtractControlValue]
    have hp1 := bitValue_lt I phaseOneWire
    have hc := bitValue_lt I controlWire
    congr 1
    omega

theorem subtractControlGates_on
    {I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0) :
    actGates subtractControlGates I = I ^^^ (1 <<< controlWire) := by
  rw [subtractControlGates_act]
  rcases henabled with hphaseTwo | hsign
  · simpa [subtractControlValue, hphaseOne, hphaseTwo] using
      (flip_eq I controlWire).symm
  · simpa [subtractControlValue, hphaseOne, hsign] using
      (flip_eq I controlWire).symm

theorem subtractControlGates_off_phaseTwo_signSet
    {I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1) :
    actGates subtractControlGates I = I := by
  rw [subtractControlGates_act]
  simp only [subtractControlValue, hphaseOne, hphaseTwo, hsign, if_pos,
    Nat.one_mul, Nat.add_assoc]
  have hcontrol := bitValue_lt I controlWire
  have hvalue : (bitValue I controlWire + 1 + 1) % 2 =
      bitValue I controlWire := by omega
  rw [hvalue]
  exact write_of_bitValue (Nat.mod_eq_of_lt hcontrol)

theorem subtractControlGates_wellFormed :
    subtractControlGates.all (RGate.wellFormed layout.width) = true := by
  decide +kernel

theorem subtractControlGates_avoids_workTwo :
    ∀ g ∈ subtractControlGates, ∀ q ∈ g.wires,
      q < workTwoOffset ∨ workTwoOffset + count ≤ q := by
  have hall : subtractControlGates.all (fun g =>
      g.wires.all (fun q => decide
        (q < workTwoOffset ∨ workTwoOffset + count ≤ q))) = true := by
    decide +kernel
  intro g hg q hq
  have hg' := List.all_eq_true.mp hall g hg
  exact of_decide_eq_true (List.all_eq_true.mp hg' q hq)

def subtractBlockGates : List RGate :=
  Step.around subtractControlGates (LuoCoefficientPass.prefixSubGates count)

def middleGates : List RGate :=
  subtractBlockGates ++ LuoCoefficientPass.signToggleGates ++
    LuoCoefficientPass.addBlockGates count

def gates : List RGate :=
  LuoCoefficientPass.prepareGates count ++ middleGates ++
    LuoCoefficientPass.restoreGates count

def circuit : RCircuit := { width := layout.width, gates := gates }

private theorem middleGates_phaseOneClear_act
    {boundary I : Nat}
    (hboundary : readField I lengthTOffset 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0) :
    actGates middleGates I = I := by
  have hsubtractControl : actGates subtractControlGates I = I := by
    rw [subtractControlGates_act]
    simp only [subtractControlValue, hphaseOne, hcontrol, Nat.zero_add,
      Nat.zero_mul, Nat.add_zero, Nat.zero_mod]
    apply write_of_bitValue
    simpa using hcontrol.symm
  have hsubtractBody : actGates (LuoCoefficientPass.prefixSubGates count)
      (actGates subtractControlGates I) =
        actGates subtractControlGates I := by
    rw [hsubtractControl]
    exact LuoCoefficientPass.prefixSubGates_off
      (count := count) (boundary := boundary) (I := I)
      (by decide) (by decide) hboundary hcontrol hscratch
      haccumulator hcellScratch
  have hsubtract : actGates subtractBlockGates I = I :=
    StepBlocks.around_identity subtractControlGates_wellFormed hsubtractBody
  have htoggle : actGates LuoCoefficientPass.signToggleGates I = I :=
    LuoCoefficientPass.signToggleGates_off hphaseOne
  have haddControl :
      actGates (LuoCoefficientPass.addControlGates count) I = I :=
    LuoCoefficientPass.addControlGates_off hphaseOne
  have haddBody : actGates (LuoCoefficientPass.prefixAddGates count) I = I :=
    LuoCoefficientPass.prefixAddGates_off
      (count := count) (boundary := boundary) (I := I)
      (by decide) (by decide) hboundary hcontrol hscratch
      hcarry haccumulator hcellScratch
  have hadd : actGates (LuoCoefficientPass.addBlockGates count) I = I := by
    simp only [LuoCoefficientPass.addBlockGates, actGates_append]
    rw [haddControl, haddBody, haddControl]
  simp only [middleGates, actGates_append]
  rw [hsubtract, htoggle, hadd]

theorem phaseOneClear_phaseTwoSet_act_mod
    {I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hphaseTwo : bitValue I phaseTwoWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0)
    (htfit : readField I lengthTOffset 9 + 2 < 2 ^ 9) :
    actGates gates I = I := by
  let P := writeField
    (writeField I lengthTOffset 9 (preparedRPrime I))
    lengthRPrimeOffset 9 (preparedT I)
  have hprepare : actGates (LuoCoefficientPass.prepareGates count) I = P :=
    LuoCoefficientPass.prepareGates_act_phaseTwoSet hscratch hcarry hphaseTwo
  have hpreparedRPrimeFit : preparedRPrime I < 2 ^ 9 := by
    simp only [preparedRPrime, CompactCoefficientPass.preparedRPrime,
      LuoCoefficientPass.preparedLengthRPrime,
      LuoCoefficientBoundary.preparedR, Adder.difference]
    exact Nat.mod_lt _ (by norm_num)
  have hboundaryP : readField P lengthTOffset 9 = preparedRPrime I := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      readField_writeField_self hpreparedRPrimeFit]
  have hphaseOneP : bitValue P phaseOneWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseOne]
  have hcontrolP : bitValue P controlWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcontrol]
  have hscratchP : readField P scratchOffset 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hscratch]
  have hcarryP : bitValue P carryWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcarry]
  have haccumulatorP : bitValue P accumulatorWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), haccumulator]
  have hcellScratchP : bitValue P cellScratchWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcellScratch]
  have hmiddle : actGates middleGates P = P :=
    middleGates_phaseOneClear_act hboundaryP hphaseOneP
      hcontrolP hscratchP hcarryP haccumulatorP hcellScratchP
  have hrestore := LuoCoefficientPass.prepareRestoreGates_act_phaseTwoSet_mod
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit
  simp only [actGates_append, hprepare] at hrestore
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle]
  exact hrestore

theorem phaseOneClear_phaseTwoClear_act
    {I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0)
    (htfit : readField I lengthTOffset 9 + 2 < 2 ^ 9) :
    actGates gates I = I := by
  let P := writeField
    (writeField I lengthTOffset 9 (preparedT I))
    lengthRPrimeOffset 9 (preparedRPrime I)
  have hprepare : actGates (LuoCoefficientPass.prepareGates count) I = P :=
    LuoCoefficientPass.prepareGates_act_phaseTwoClear
      hscratch hcarry hphaseTwo
  have hpreparedTFit : preparedT I < 2 ^ 9 := by
    simp only [preparedT, CompactCoefficientPass.preparedT,
      LuoCoefficientPass.preparedLengthT,
      LuoCoefficientBoundary.preparedT]
    exact Nat.mod_lt _ (by norm_num)
  have hboundaryP : readField P lengthTOffset 9 = preparedT I := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      readField_writeField_self hpreparedTFit]
  have hphaseOneP : bitValue P phaseOneWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseOne]
  have hcontrolP : bitValue P controlWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcontrol]
  have hscratchP : readField P scratchOffset 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hscratch]
  have hcarryP : bitValue P carryWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcarry]
  have haccumulatorP : bitValue P accumulatorWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), haccumulator]
  have hcellScratchP : bitValue P cellScratchWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcellScratch]
  have hmiddle : actGates middleGates P = P :=
    middleGates_phaseOneClear_act hboundaryP hphaseOneP
      hcontrolP hscratchP hcarryP haccumulatorP hcellScratchP
  have hrestore := LuoCoefficientPass.prepareRestoreGates_act_phaseTwoClear_mod
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit
  simp only [actGates_append, hprepare] at hrestore
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle]
  exact hrestore

theorem subtractBlockGates_on_act
    {boundary I : Nat}
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I lengthTOffset 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0) :
    actGates subtractBlockGates I =
      writeField I workTwoOffset boundary
        (Adder.difference boundary
          (readField I workOneOffset boundary)
          (readField I workTwoOffset boundary)) := by
  let J := I ^^^ (1 <<< controlWire)
  let value := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I workTwoOffset boundary)
  have hcompute : actGates subtractControlGates I = J :=
    subtractControlGates_on hphaseOne henabled
  have hboundaryJ : readField J lengthTOffset 9 = boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hboundary]
    right
    decide +kernel
  have hcontrolJ : bitValue J controlWire = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hcontrol
  have hscratchJ : readField J scratchOffset 9 = 0 := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hscratch]
    left
    decide +kernel
  have hcarryJ : bitValue J carryWire = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hcarry]
  have haccumulatorJ : bitValue J accumulatorWire = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), haccumulator]
  have hcellScratchJ : bitValue J cellScratchWire = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hcellScratch]
  have hsourceJ : readField J workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    have hboundaryLe : boundary ≤ count := by omega
    have hoffset : workOneOffset + count ≤ controlWire := by decide +kernel
    exact le_trans (Nat.add_le_add_left hboundaryLe workOneOffset) hoffset
  have htargetJ : readField J workTwoOffset boundary =
      readField I workTwoOffset boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    have hboundaryLe : boundary ≤ count := by omega
    have hoffset : workTwoOffset + count ≤ controlWire := by decide +kernel
    exact le_trans (Nat.add_le_add_left hboundaryLe workTwoOffset) hoffset
  have hprefix := LuoCoefficientPass.prefixSubGates_act
    (count := count) (boundary := boundary) (I := J)
    (by decide) (by decide) hboundaryRange hboundaryJ hcontrolJ hscratchJ
    hcarryJ haccumulatorJ hcellScratchJ
  change actGates (LuoCoefficientPass.prefixSubGates count) J =
    writeField J workTwoOffset boundary
      (Adder.difference boundary
        (readField J workOneOffset boundary)
        (readField J workTwoOffset boundary)) at hprefix
  rw [hsourceJ, htargetJ] at hprefix
  change actGates (LuoCoefficientPass.prefixSubGates count) J =
    writeField J workTwoOffset boundary value at hprefix
  have hbody :
      actGates (LuoCoefficientPass.prefixSubGates count)
          (actGates subtractControlGates I) =
        writeField (actGates subtractControlGates I)
          workTwoOffset boundary value := by
    rw [hcompute]
    exact hprefix
  have hboundaryLe : boundary ≤ count := by omega
  have havoidsBoundary :
      ∀ g ∈ subtractControlGates, ∀ q ∈ g.wires,
        q < workTwoOffset ∨ workTwoOffset + boundary ≤ q := by
    intro g hg q hq
    rcases subtractControlGates_avoids_workTwo g hg q hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (le_trans
        (Nat.add_le_add_left hboundaryLe workTwoOffset) hq)
  have haround := StepBlocks.around_write
    (compute := subtractControlGates)
    (body := LuoCoefficientPass.prefixSubGates count)
    (width := layout.width) (I := I)
    (off := workTwoOffset) (len := boundary) (value := value)
    subtractControlGates_wellFormed havoidsBoundary hbody
  simpa [subtractBlockGates, value] using haround

theorem subtractBlockGates_off_phaseTwo_signSet_act
    {boundary I : Nat}
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I lengthTOffset 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0) :
    actGates subtractBlockGates I = I := by
  have hcompute := subtractControlGates_off_phaseTwo_signSet
    hphaseOne hphaseTwo hsign
  have hbody : actGates (LuoCoefficientPass.prefixSubGates count)
      (actGates subtractControlGates I) =
        actGates subtractControlGates I := by
    rw [hcompute]
    exact LuoCoefficientPass.prefixSubGates_off
      (count := count) (boundary := boundary) (I := I)
      (by decide) (by decide) hboundary hcontrol hscratch
      haccumulator hcellScratch
  exact StepBlocks.around_identity subtractControlGates_wellFormed hbody

theorem middleGates_phaseTwo_signSet_act
    {boundary I : Nat}
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I lengthTOffset 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0) :
    let total := readField I workTwoOffset boundary +
      readField I workOneOffset boundary
    actGates middleGates I =
      writeField
        (writeField I workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((total / 2 ^ boundary) % 2) := by
  let S := I ^^^ (1 <<< signWire)
  let total := readField I workTwoOffset boundary +
    readField I workOneOffset boundary
  let targetValue := total % 2 ^ boundary
  let signValue := (total / 2 ^ boundary) % 2
  have hsubtract := subtractBlockGates_off_phaseTwo_signSet_act
    hboundaryRange hboundary hphaseOne hphaseTwo hsign hcontrol hscratch
    haccumulator hcellScratch
  have htoggle : actGates LuoCoefficientPass.signToggleGates I = S :=
    LuoCoefficientPass.signToggleGates_on hphaseOne
  have hboundaryS : readField S lengthTOffset 9 = boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hboundary]
    left
    decide +kernel
  have hphaseOneS : bitValue S phaseOneWire = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide) |>.trans
      hphaseOne
  have hcontrolS : bitValue S controlWire = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide) |>.trans
      hcontrol
  have hscratchS : readField S scratchOffset 9 = 0 := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hscratch]
    left
    decide +kernel
  have hcarryS : bitValue S carryWire = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide) |>.trans hcarry
  have haccumulatorS : bitValue S accumulatorWire = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide) |>.trans
      haccumulator
  have hcellScratchS : bitValue S cellScratchWire = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide) |>.trans
      hcellScratch
  have hsourceS : readField S workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    left
    decide +kernel
  have htargetS : readField S workTwoOffset boundary =
      readField I workTwoOffset boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    left
    decide +kernel
  have hsignS : bitValue S signWire = 0 :=
    PrunedSelectSwap.Tree.bitValue_xor_self_one hsign
  have hadd := LuoCoefficientPass.addBlockGates_on_act
    (count := count) (boundary := boundary) (I := S)
    (by decide) (by decide) hboundaryRange hboundaryS hphaseOneS hcontrolS
    hscratchS hcarryS haccumulatorS hcellScratchS
  dsimp only at hadd
  have htargetSQ :
      readField S (LuoCoefficientPass.workTwoOffset count) boundary =
        readField I workTwoOffset boundary := htargetS
  have hsourceSQ : readField S LuoCoefficientPass.workOneOffset boundary =
      readField I workOneOffset boundary := hsourceS
  have hsignSQ : bitValue S LuoCoefficientPass.signWire = 0 := hsignS
  rw [htargetSQ, hsourceSQ, hsignSQ, Nat.zero_add] at hadd
  change actGates (LuoCoefficientPass.addBlockGates count) S =
    writeField (writeField S workTwoOffset boundary targetValue)
      signWire 1 signValue at hadd
  simp only [middleGates, actGates_append]
  rw [hsubtract, htoggle, hadd]
  simp only [S]
  rw [Selector.xor_eq_writeField_toggle,
    writeField_overwrite_of_disjoint (Or.inl (by decide +kernel))]

theorem middleGates_enabled_act
    {boundary I : Nat}
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I lengthTOffset 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0) :
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I workTwoOffset boundary)
    let total := difference + readField I workOneOffset boundary
    let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
    actGates middleGates I =
      writeField
        (writeField I workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1
          ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I workTwoOffset boundary)
  let D := writeField I workTwoOffset boundary difference
  let S := D ^^^ (1 <<< signWire)
  let total := difference + readField I workOneOffset boundary
  let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
  let targetValue := total % 2 ^ boundary
  let signValue := (signBeforeAdd + total / 2 ^ boundary) % 2
  have hsubtract := subtractBlockGates_on_act hboundaryRange hboundary
    hphaseOne hcontrol henabled hscratch hcarry haccumulator
    hcellScratch
  change actGates subtractBlockGates I = D at hsubtract
  have hphaseOneD : bitValue D phaseOneWire = 1 := by
    simp only [D]
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hphaseOne
  have htoggle : actGates LuoCoefficientPass.signToggleGates D = S :=
    LuoCoefficientPass.signToggleGates_on hphaseOneD
  have hboundaryS : readField S lengthTOffset 9 = boundary := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inl (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ lengthTOffset := by
          decide +kernel
        exact le_trans
          (Nat.add_le_add_left hboundaryLe workTwoOffset) hoffset)),
      hboundary]
    left
    decide +kernel
  have hphaseOneS : bitValue S phaseOneWire = 1 := by
    simp only [S]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hphaseOneD]
  have hcontrolS : bitValue S controlWire = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide),
      bitValue_write_out (Or.inr (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ controlWire := by
          decide +kernel
        exact le_trans
          (Nat.add_le_add_left hboundaryLe workTwoOffset) hoffset)),
      hcontrol]
  have hscratchS : readField S scratchOffset 9 = 0 := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inl (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ scratchOffset := by decide +kernel
        omega)), hscratch]
    left
    decide +kernel
  have hcarryS : bitValue S carryWire = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide),
      bitValue_write_out (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ carryWire := by decide +kernel
        omega), hcarry]
  have haccumulatorS : bitValue S accumulatorWire = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide),
      bitValue_write_out (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ accumulatorWire := by decide +kernel
        omega), haccumulator]
  have hcellScratchS : bitValue S cellScratchWire = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide),
      bitValue_write_out (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workTwoOffset + count ≤ cellScratchWire := by
          decide +kernel
        omega), hcellScratch]
  have hsourceS : readField S workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inr (by
        have hboundaryLe : boundary ≤ count := by omega
        have hoffset : workOneOffset + count ≤ workTwoOffset := by
          decide +kernel
        omega))]
    left
    decide +kernel
  have htargetS : readField S workTwoOffset boundary = difference := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_self (by
        simp only [difference, Adder.difference]
        exact Nat.mod_lt _ (Nat.two_pow_pos boundary))]
    left
    decide +kernel
  have hsignS : bitValue S signWire = signBeforeAdd := by
    simp only [S, D, signBeforeAdd]
    rw [xor_writeField_of_outside (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel))]
  have hadd := LuoCoefficientPass.addBlockGates_on_act
    (count := count) (boundary := boundary) (I := S)
    (by decide) (by decide) hboundaryRange hboundaryS hphaseOneS hcontrolS
    hscratchS hcarryS haccumulatorS hcellScratchS
  dsimp only at hadd
  have htargetSQ :
      readField S (LuoCoefficientPass.workTwoOffset count) boundary =
        difference := htargetS
  have hsourceSQ :
      readField S LuoCoefficientPass.workOneOffset boundary =
        readField I workOneOffset boundary := hsourceS
  have hsignSQ : bitValue S LuoCoefficientPass.signWire =
      signBeforeAdd := hsignS
  rw [htargetSQ, hsourceSQ, hsignSQ] at hadd
  have hadd' : actGates (LuoCoefficientPass.addBlockGates count) S =
      writeField
        (writeField S (LuoCoefficientPass.workTwoOffset count)
          boundary targetValue)
        LuoCoefficientPass.signWire 1 signValue := by
    simpa only [targetValue, total, signValue] using hadd
  have hworkTwoAlias : LuoCoefficientPass.workTwoOffset count =
      workTwoOffset := rfl
  have hsignAlias : LuoCoefficientPass.signWire = signWire := rfl
  rw [hworkTwoAlias, hsignAlias] at hadd'
  have hsignToggleValue : bitValue
      (writeField I signWire 1 ((readField I signWire 1 + 1) % 2)) signWire =
        signBeforeAdd := by
    rw [← Selector.xor_eq_writeField_toggle]
  simp only [middleGates, actGates_append]
  rw [hsubtract, htoggle, hadd']
  simp only [S, D]
  rw [xor_writeField_of_outside (Or.inl (by decide +kernel)),
    writeField_writeField,
    Selector.xor_eq_writeField_toggle,
    writeField_overwrite_of_disjoint (Or.inl (by decide +kernel))]
  rw [hsignToggleValue]

private theorem gates_of_middle_write
    {P I len targetValue signValue : Nat}
    (hlen : len ≤ count)
    (hprepare : actGates (LuoCoefficientPass.prepareGates count) I = P)
    (hrestore : actGates (LuoCoefficientPass.restoreGates count) P = I)
    (hmiddle : actGates middleGates P =
      writeField (writeField P workTwoOffset len targetValue)
        signWire 1 signValue) :
    actGates gates I =
      writeField (writeField I workTwoOffset len targetValue)
        signWire 1 signValue := by
  have hworkAlias : workTwoOffset =
      LuoCoefficientPass.workTwoOffset count := rfl
  have hsignAlias : signWire = LuoCoefficientPass.signWire := rfl
  rw [hworkAlias, hsignAlias] at hmiddle ⊢
  have hwork : ∀ g ∈ LuoCoefficientPass.restoreGates count,
      ∀ q ∈ g.wires,
        q < workTwoOffset ∨ workTwoOffset + len ≤ q := by
    intro g hg q hq
    rcases LuoCoefficientPass.restoreGates_avoids_workTwo count g hg q hq with
      hq | hq
    · exact Or.inl hq
    · exact Or.inr (le_trans
        (Nat.add_le_add_left hlen workTwoOffset) hq)
  rw [hworkAlias] at hwork
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle,
    actGates_write_of_outside (LuoCoefficientPass.restoreGates_avoids_sign count),
    actGates_write_of_outside hwork, hrestore]

theorem phaseTwo_act
    {I : Nat}
    (hboundaryRange : 1 ≤ preparedT I ∧ preparedT I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0)
    (htfit : readField I lengthTOffset 9 + 2 < 2 ^ 9) :
    let boundary := preparedT I
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I workTwoOffset boundary)
    let coefficient := if bitValue I signWire = 0 then difference else
      readField I workTwoOffset boundary
    let total := coefficient + readField I workOneOffset boundary
    let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
    actGates gates I =
      writeField
        (writeField I workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  let boundary := preparedT I
  let P := writeField
    (writeField I lengthTOffset 9 boundary)
    lengthRPrimeOffset 9 (preparedRPrime I)
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I workTwoOffset boundary)
  let coefficient := if bitValue I signWire = 0 then difference else
    readField I workTwoOffset boundary
  let total := coefficient + readField I workOneOffset boundary
  let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
  change 1 ≤ boundary ∧ boundary < 1 + count at hboundaryRange
  have hlen : boundary ≤ count := by
    dsimp only [boundary]
    omega
  have hprepare : actGates (LuoCoefficientPass.prepareGates count) I = P := by
    exact LuoCoefficientPass.prepareGates_act_phaseTwoClear hscratch hcarry
      hphaseTwo
  have hboundaryP : readField P lengthTOffset 9 = boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      readField_writeField_self
        (lt_of_le_of_lt hlen (by decide +kernel : count < 2 ^ 9))]
  have hphaseOneP : bitValue P phaseOneWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseOne]
  have hphaseTwoP : bitValue P phaseTwoWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseTwo]
  have hsignP : bitValue P signWire = bitValue I signWire := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel))]
  have hcontrolP : bitValue P controlWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcontrol]
  have hscratchP : readField P scratchOffset 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hscratch]
  have hcarryP : bitValue P carryWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcarry]
  have haccumulatorP : bitValue P accumulatorWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), haccumulator]
  have hcellScratchP : bitValue P cellScratchWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcellScratch]
  have hsourceP : readField P workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workOneOffset + count ≤ lengthRPrimeOffset := by
          decide +kernel
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workOneOffset + count ≤ lengthTOffset := by
          decide +kernel
        omega))]
  have htargetP : readField P workTwoOffset boundary =
      readField I workTwoOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workTwoOffset + count ≤ lengthRPrimeOffset := by
          decide +kernel
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workTwoOffset + count ≤ lengthTOffset := by
          decide +kernel
        omega))]
  have hsignToggleP : bitValue (P ^^^ (1 <<< signWire)) signWire =
      signBeforeAdd := by
    rcases Nat.eq_zero_or_pos (bitValue I signWire) with hsign | hsign
    · exact (PrunedSelectSwap.Tree.bitValue_xor_self_zero
        (hsignP.trans hsign)).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_zero hsign).symm
    · have hsign' : bitValue I signWire = 1 := by
        have hlt := bitValue_lt I signWire
        omega
      exact (PrunedSelectSwap.Tree.bitValue_xor_self_one
        (hsignP.trans hsign')).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_one hsign').symm
  have hmiddle : actGates middleGates P =
      writeField
        (writeField P workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
    rcases Nat.eq_zero_or_pos (bitValue I signWire) with hsign | hsign
    · have hsignPZero : bitValue P signWire = 0 := hsignP.trans hsign
      have hmiddle := middleGates_enabled_act hboundaryRange hboundaryP
        hphaseOneP (Or.inr hsignPZero) hcontrolP hscratchP hcarryP
        haccumulatorP hcellScratchP
      dsimp only at hmiddle
      rw [htargetP, hsourceP, hsignToggleP] at hmiddle
      simpa only [coefficient, hsign, if_pos, total] using hmiddle
    · have hsign' : bitValue I signWire = 1 := by
        have hlt := bitValue_lt I signWire
        omega
      have hsignPOne : bitValue P signWire = 1 := hsignP.trans hsign'
      have hmiddle := middleGates_phaseTwo_signSet_act hboundaryRange
        hboundaryP hphaseOneP hphaseTwoP hsignPOne hcontrolP hscratchP
        hcarryP haccumulatorP hcellScratchP
      dsimp only at hmiddle
      rw [htargetP, hsourceP] at hmiddle
      have hsignBeforeAddZero : signBeforeAdd = 0 :=
        PrunedSelectSwap.Tree.bitValue_xor_self_one hsign'
      simpa only [coefficient, hsign', one_ne_zero, if_false, total,
        hsignBeforeAddZero, Nat.zero_add] using hmiddle
  have hrestore := LuoCoefficientPass.prepareRestoreGates_act_phaseTwoClear_mod
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit
  simp only [actGates_append, hprepare] at hrestore
  exact gates_of_middle_write hlen hprepare hrestore hmiddle

theorem phaseFour_act
    {I : Nat}
    (hboundaryRange :
      1 ≤ preparedRPrime I ∧ preparedRPrime I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (hscratch : readField I scratchOffset 9 = 0)
    (hcarry : bitValue I carryWire = 0)
    (haccumulator : bitValue I accumulatorWire = 0)
    (hcellScratch : bitValue I cellScratchWire = 0)
    (htfit : readField I lengthTOffset 9 + 2 < 2 ^ 9)
    (hsum : readField I lengthRPrimeOffset 9 +
      readField I shiftOffset 9 ≤ 257) :
    let boundary := preparedRPrime I
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I workTwoOffset boundary)
    let total := difference + readField I workOneOffset boundary
    let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
    actGates gates I =
      writeField
        (writeField I workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  let boundary := preparedRPrime I
  let P := writeField
    (writeField I lengthTOffset 9 boundary)
    lengthRPrimeOffset 9 (preparedT I)
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I workTwoOffset boundary)
  let total := difference + readField I workOneOffset boundary
  let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
  have hlen : boundary ≤ count := by
    dsimp only [boundary]
    omega
  have hprepare : actGates (LuoCoefficientPass.prepareGates count) I = P := by
    exact LuoCoefficientPass.prepareGates_act_phaseTwoSet hscratch hcarry
      hphaseTwo
  have hboundaryP : readField P lengthTOffset 9 = boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      readField_writeField_self
        (lt_of_le_of_lt hlen (by decide +kernel : count < 2 ^ 9))]
  have hphaseOneP : bitValue P phaseOneWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseOne]
  have hphaseTwoP : bitValue P phaseTwoWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (Or.inl (by decide +kernel)),
      bitValue_write_out (Or.inl (by decide +kernel)), hphaseTwo]
  have hcontrolP : bitValue P controlWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcontrol]
  have hscratchP : readField P scratchOffset 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hscratch]
  have hcarryP : bitValue P carryWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcarry]
  have haccumulatorP : bitValue P accumulatorWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), haccumulator]
  have hcellScratchP : bitValue P cellScratchWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      bitValue_write_out (Or.inr (by decide +kernel)), hcellScratch]
  have hsourceP : readField P workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        have hboundaryLe : boundary ≤ count := hlen
        have hoffset : workOneOffset + count ≤ lengthRPrimeOffset := by
          decide +kernel
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        have hboundaryLe : boundary ≤ count := hlen
        have hoffset : workOneOffset + count ≤ lengthTOffset := by
          decide +kernel
        omega))]
  have htargetP : readField P workTwoOffset boundary =
      readField I workTwoOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workTwoOffset + count ≤ lengthRPrimeOffset := by
          decide +kernel
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        have hoffset : workTwoOffset + count ≤ lengthTOffset := by
          decide +kernel
        omega))]
  have hsignToggleP : bitValue (P ^^^ (1 <<< signWire)) signWire =
      signBeforeAdd := by
    have hsignP : bitValue P signWire = bitValue I signWire := by
      simp only [P]
      rw [bitValue_write_out (Or.inl (by decide +kernel)),
        bitValue_write_out (Or.inl (by decide +kernel))]
    rcases Nat.eq_zero_or_pos (bitValue I signWire) with hsign | hsign
    · exact (PrunedSelectSwap.Tree.bitValue_xor_self_zero
        (hsignP.trans hsign)).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_zero hsign).symm
    · have hsign' : bitValue I signWire = 1 := by
        have hlt := bitValue_lt I signWire
        omega
      exact (PrunedSelectSwap.Tree.bitValue_xor_self_one
        (hsignP.trans hsign')).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_one hsign').symm
  have hmiddle := middleGates_enabled_act hboundaryRange hboundaryP
    hphaseOneP (Or.inl hphaseTwoP) hcontrolP hscratchP hcarryP haccumulatorP
    hcellScratchP
  dsimp only at hmiddle
  rw [htargetP, hsourceP, hsignToggleP] at hmiddle
  have hrestore := LuoCoefficientPass.prepareRestoreGates_act_phaseTwoSet
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  exact gates_of_middle_write hlen hprepare hrestore hmiddle

set_option maxRecDepth 4096 in
theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hcontrol : CompactCoefficientDirty.subtractControlGates.all
      (RGate.wellFormed (LuoCoefficientPass.layout
        CompactCoefficientDirty.count).width) = true := by
    decide +kernel
  change CompactCoefficientDirty.gates.all
    (RGate.wellFormed (LuoCoefficientPass.layout
      CompactCoefficientDirty.count).width) = true
  simp only [CompactCoefficientDirty.gates, CompactCoefficientDirty.middleGates,
    CompactCoefficientDirty.subtractBlockGates, Step.around,
    LuoCoefficientPass.addBlockGates, List.all_append, List.all_reverse]
  rw [LuoCoefficientPass.prepareGates_wellFormed,
    hcontrol, LuoCoefficientPass.prefixSubGates_wellFormed (by decide) (by decide),
    LuoCoefficientPass.signToggleGates_wellFormed,
    LuoCoefficientPass.addControlGates_wellFormed,
    LuoCoefficientPass.prefixAddGates_wellFormed (by decide) (by decide),
    LuoCoefficientPass.restoreGates_wellFormed]
  rfl

end CompactCoefficientDirty
end Euclid
end VQ
