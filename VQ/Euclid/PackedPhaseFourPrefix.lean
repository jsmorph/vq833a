/-
Packed interval and control prefix for one phase-four Euclidean round.
-/
import VQ.Euclid.PackedEndpointState
import VQ.Euclid.PackedEndpointOperands
import VQ.Euclid.PackedInterval
import VQ.Euclid.PackedQuotient
import VQ.Euclid.PackedSelectSwap
import VQ.Euclid.PackedShift

namespace VQ
namespace Euclid
namespace PackedPhaseFourPrefix

open Reversible

def controlWire : Nat := PackedStepLayout.poolOffset

def preShiftControlGates : List RGate :=
  StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire ++
    [.ccx controlWire PackedStepLayout.phaseTwoWire
      (PackedStepLayout.poolOffset + 10)]

def preShiftBlock : List RGate :=
  Step.around preShiftControlGates PackedStepLayout.shiftGates

def rPrimeSelectorGates : List RGate :=
  Placed.selectorGates (encodedZero 8) 8
    PackedStepLayout.lengthRPrimeOffset PackedStepLayout.extensionWire
    (PackedStepLayout.poolOffset + 1)

def remainderSubControlGates : List RGate :=
  StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire ++
    [.cx PackedStepLayout.extensionWire controlWire]

def remainderFlipGates : List RGate :=
  Phase.negativeAndGates PackedStepLayout.phaseTwoWire
    PackedStepLayout.phaseOneWire PackedStepLayout.signWire

def dirtyTripleGates : List RGate :=
  [.x PackedStepLayout.phaseOneWire,
    .ccx PackedStepLayout.phaseOneWire PackedStepLayout.phaseTwoWire
      PackedStepLayout.iterationWire,
    .ccx PackedStepLayout.iterationWire PackedStepLayout.signWire controlWire,
    .ccx PackedStepLayout.phaseOneWire PackedStepLayout.phaseTwoWire
      PackedStepLayout.iterationWire,
    .ccx PackedStepLayout.iterationWire PackedStepLayout.signWire controlWire,
    .x PackedStepLayout.phaseOneWire]

def remainderAddControlGates : List RGate :=
  StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire ++
    dirtyTripleGates ++ [.cx PackedStepLayout.extensionWire controlWire]

def remainderSubBody : List RGate :=
  PackedStepLayout.remainderPrepareGates ++
    PackedStepLayout.remainderIntervalReverseGates ++
    PackedStepLayout.remainderCleanupGates

def remainderAddBody : List RGate :=
  PackedStepLayout.remainderPrepareGates ++
    PackedStepLayout.remainderIntervalNoSignGates ++
    PackedStepLayout.remainderCleanupGates

def remainderSubBlock : List RGate :=
  Step.around remainderSubControlGates remainderSubBody

def remainderAddBlock : List RGate :=
  Step.around remainderAddControlGates remainderAddBody

def remainderBlocks : List RGate :=
  Step.around rPrimeSelectorGates
    (remainderSubBlock ++ remainderFlipGates ++ remainderAddBlock)

def quotientIncrementControlGates : List RGate :=
  Phase.negativeAndGates PackedStepLayout.phaseTwoWire
    PackedStepLayout.phaseOneWire controlWire

def quotientIncrementBlock : List RGate :=
  Step.around quotientIncrementControlGates
    PackedStepLayout.quotientIncrementGates

def swapControlGates : List RGate :=
  Phase.xorPairGates PackedStepLayout.phaseOneWire
    PackedStepLayout.phaseTwoWire controlWire

def swapBody : List RGate :=
  PackedStepLayout.swapPrepareGates ++ PackedStepLayout.selectSwapGates ++
    PackedStepLayout.swapCleanupGates

def swapBlock : List RGate :=
  Step.around swapControlGates swapBody

def quotientDecrementControlGates : List RGate :=
  Phase.negativeAndGates PackedStepLayout.phaseOneWire
    PackedStepLayout.phaseTwoWire controlWire

def quotientDecrementBlock : List RGate :=
  Step.around quotientDecrementControlGates
    PackedStepLayout.quotientDecrementGates

def gates : List RGate :=
  preShiftBlock ++ remainderBlocks ++ quotientIncrementBlock ++ swapBlock ++
    quotientDecrementBlock

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

private theorem negative_identity_of_source_set
    {source target I : Nat}
    (hne : source ≠ target)
    (hsource : bitValue I source = 1) :
    actGates (StepControl.negativeGates source target) I = I := by
  rw [StepControl.negative_act hne]
  unfold StepControl.negativeOut
  rw [hsource]
  simp only [one_ne_zero, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I target)]
  simpa [readField_one] using writeField_read I target 1

private theorem negativeAnd_identity_of_second_set
    {a b target I : Nat}
    (hab : a ≠ b)
    (hbt : b ≠ target)
    (hb : bitValue I b = 1) :
    actGates (Phase.negativeAndGates a b target) I = I := by
  rw [Phase.negativeAnd_act hab hbt]
  unfold Phase.negativeAndOut
  rw [hb]
  simp only [one_ne_zero, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I target)]
  simpa [readField_one] using writeField_read I target 1

private theorem ccx_identity_of_first_clear
    {a b target I : Nat}
    (ha : bitValue I a = 0) :
    actGates [.ccx a b target] I = I := by
  have ha' : I.testBit a = false := by simpa [bitValue] using ha
  simp [actGates, RGate.act, ha']

private theorem ccx_identity_of_second_clear
    {a b target I : Nat}
    (hb : bitValue I b = 0) :
    actGates [.ccx a b target] I = I := by
  have hb' : I.testBit b = false := by simpa [bitValue] using hb
  by_cases ha' : I.testBit a = true <;>
    simp [actGates, RGate.act, ha', hb']

private theorem ccx_on
    {a b target I : Nat}
    (ha : bitValue I a = 1)
    (hb : bitValue I b = 1) :
    actGates [.ccx a b target] I = I ^^^ (1 <<< target) := by
  have ha' : I.testBit a = true := by simpa [bitValue] using ha
  have hb' : I.testBit b = true := by simpa [bitValue] using hb
  simp [actGates, RGate.act, ha', hb']

theorem preShiftControl_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hcontrol : bitValue I controlWire = 0) :
    actGates preShiftControlGates I = I := by
  rw [preShiftControlGates, actGates_append,
    negative_identity_of_source_set (by decide) hphaseOne]
  exact ccx_identity_of_first_clear hcontrol

theorem remainderSubControl_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates remainderSubControlGates I = I := by
  rw [remainderSubControlGates, actGates_append,
    negative_identity_of_source_set (by decide) hphaseOne]
  exact PrunedSelectSwap.Tree.cx_off hextension

theorem remainderSubControl_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates remainderSubControlGates I =
      writeField I controlWire 1 1 := by
  rw [remainderSubControlGates, actGates_append,
    StepControl.negative_act (by decide)]
  have hextension' : bitValue
      (StepControl.negativeOut PackedStepLayout.phaseOneWire controlWire I)
      PackedStepLayout.extensionWire = 0 := by
    rw [StepControl.negativeOut_ne (by decide), hextension]
  rw [PrunedSelectSwap.Tree.cx_off hextension']
  simp [StepControl.negativeOut, hphaseOne, hcontrol]

private theorem remainderSubControl_identity_terminal
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 1) :
    actGates remainderSubControlGates I = I := by
  let C := writeField I controlWire 1 1
  have hnegative : actGates
      (StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire) I =
      C := by
    rw [StepControl.negative_act (by decide)]
    simp [StepControl.negativeOut, C, hphaseOne, hcontrol]
  have hextensionC : bitValue C PackedStepLayout.extensionWire = 1 := by
    rw [show bitValue C PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire by
        exact bitValue_write_ne (by decide), hextension]
  have hC : C = I ^^^ (1 <<< controlWire) := by
    symm
    rw [Selector.xor_eq_writeField_toggle, readField_one, hcontrol]
  rw [remainderSubControlGates, actGates_append, hnegative,
    PrunedSelectSwap.Tree.cx_on hextensionC, hC, RGate.xor_cancel]

theorem remainderFlip_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1) :
    actGates remainderFlipGates I = I := by
  exact negativeAnd_identity_of_second_set (by decide) (by decide) hphaseOne

theorem dirtyTriple_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1) :
    actGates dirtyTripleGates I = I := by
  let p1 := PackedStepLayout.phaseOneWire
  let p2 := PackedStepLayout.phaseTwoWire
  let iter := PackedStepLayout.iterationWire
  let sign := PackedStepLayout.signWire
  let ctrl := controlWire
  let X := I ^^^ (1 <<< p1)
  let A : List RGate := [.ccx p1 p2 iter]
  let B : List RGate := [.ccx iter sign ctrl]
  have hx : actGates [.x p1] I = X := by
    simp [X, actGates, RGate.act]
  have hXp1 : bitValue X p1 = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_one hphaseOne
  have hA : actGates A X = X := by
    exact ccx_identity_of_first_clear hXp1
  let K := actGates B X
  have hKp1 : bitValue K p1 = 0 := by
    unfold bitValue
    rw [show K.testBit p1 = X.testBit p1 by
      exact testBit_actGates_of_outside (i := X) (by
        intro g hg
        simp only [B, List.mem_cons] at hg
        rcases hg with rfl | h <;> simp_all [RGate.wires, p1, iter, sign,
          ctrl, controlWire, PackedStepLayout.phaseOneWire,
          PackedStepLayout.iterationWire, PackedStepLayout.signWire,
          PackedStepLayout.poolOffset])]
    simpa [bitValue] using hXp1
  have hAK : actGates A K = K := by
    exact ccx_identity_of_first_clear hKp1
  have hBK : actGates B K = X := by
    have hwf : B.all (RGate.wellFormed PackedStepLayout.width) = true := by
      decide +kernel
    simpa [K, B] using (actGates_reverse hwf X)
  have hxRestore : actGates [.x p1] X = I := by
    simp [X, actGates, RGate.act]
  change actGates [.x p1]
    (actGates B (actGates A (actGates B (actGates A
      (actGates [.x p1] I))))) = I
  rw [hx, hA]
  change actGates [.x p1] (actGates B (actGates A K)) = I
  rw [hAK, hBK, hxRestore]

theorem dirtyTriple_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates dirtyTripleGates I =
      writeField I controlWire 1
        ((bitValue I controlWire + bitValue I PackedStepLayout.signWire) % 2) := by
  let p1 := PackedStepLayout.phaseOneWire
  let p2 := PackedStepLayout.phaseTwoWire
  let iter := PackedStepLayout.iterationWire
  let sign := PackedStepLayout.signWire
  let ctrl := controlWire
  let X := I ^^^ (1 <<< p1)
  let A : List RGate := [.ccx p1 p2 iter]
  let B : List RGate := [.ccx iter sign ctrl]
  have hx : actGates [.x p1] I = X := by
    simp [X, actGates, RGate.act]
  have hp1X : bitValue X p1 = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hphaseOne
  have hp2X : bitValue X p2 = 1 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hphaseTwo]
  have hiterX : bitValue X iter = bitValue I iter := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide)
  have hsignX : bitValue X sign = bitValue I sign := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide)
  have hxRestore : actGates [.x p1] X = I := by
    simp [X, actGates, RGate.act]
  change actGates [.x p1]
    (actGates B (actGates A (actGates B (actGates A
      (actGates [.x p1] I))))) = _
  rw [hx]
  rcases Nat.eq_zero_or_pos (bitValue I iter) with hi | hi
  · have hi' : bitValue I iter = 0 := hi
    have hAX : actGates A X = X ^^^ (1 <<< iter) :=
      ccx_on hp1X hp2X
    let Y := X ^^^ (1 <<< iter)
    have hp1Y : bitValue Y p1 = 1 := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp1X]
    have hp2Y : bitValue Y p2 = 1 := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp2X]
    have hiterY : bitValue Y iter = 1 := by
      exact PrunedSelectSwap.Tree.bitValue_xor_self_zero (hiterX.trans hi')
    have hsignY : bitValue Y sign = bitValue I sign := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hsignX]
    rcases Nat.eq_zero_or_pos (bitValue I sign) with hs | hs
    · have hs' : bitValue I sign = 0 := hs
      have hBY : actGates B Y = Y :=
        ccx_identity_of_second_clear (hsignY.trans hs')
      have hAY : actGates A Y = X := by
        rw [ccx_on hp1Y hp2Y]
        exact RGate.xor_cancel X iter
      rw [hAX, hBY, hAY,
        ccx_identity_of_second_clear (hsignX.trans hs'), hxRestore, hs']
      symm
      apply write_of_bitValue
      simp [Nat.mod_eq_of_lt (bitValue_lt I controlWire)]
    · have hs' : bitValue I sign = 1 := by
        have h := bitValue_lt I sign
        omega
      have hBY : actGates B Y = Y ^^^ (1 <<< ctrl) :=
        ccx_on hiterY (hsignY.trans hs')
      let Z := Y ^^^ (1 <<< ctrl)
      have hp1Z : bitValue Z p1 = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp1Y]
      have hp2Z : bitValue Z p2 = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp2Y]
      have hsignZ : bitValue Z sign = 1 := by
        rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide),
          hsignY, hs']
      let W := Z ^^^ (1 <<< iter)
      have hAZ : actGates A Z = W := by
        exact ccx_on hp1Z hp2Z
      have hiterW : bitValue W iter = 0 := by
        have hiterZ : bitValue Z iter = 1 := by
          rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hiterY]
        exact PrunedSelectSwap.Tree.bitValue_xor_self_one hiterZ
      have hBW : actGates B W = W :=
        ccx_identity_of_first_clear hiterW
      rw [hAX, hBY, hAZ, hBW]
      simp only [W, Z, Y]
      rw [show actGates [.x p1]
          ((((X ^^^ (1 <<< iter)) ^^^ (1 <<< ctrl)) ^^^ (1 <<< iter))) =
          I ^^^ (1 <<< ctrl) by
        simp [actGates, RGate.act, X, Nat.xor_assoc, Nat.xor_comm,
          Nat.xor_left_comm]]
      rw [hs']
      change I ^^^ (1 <<< controlWire) =
        writeField I controlWire 1 ((bitValue I controlWire + 1) % 2)
      exact act_x_write controlWire I

  · have hi' : bitValue I iter = 1 := by
      have h := bitValue_lt I iter
      omega
    have hAX : actGates A X = X ^^^ (1 <<< iter) :=
      ccx_on hp1X hp2X
    let Y := X ^^^ (1 <<< iter)
    have hp1Y : bitValue Y p1 = 1 := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp1X]
    have hp2Y : bitValue Y p2 = 1 := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hp2X]
    have hiterY : bitValue Y iter = 0 := by
      exact PrunedSelectSwap.Tree.bitValue_xor_self_one (hiterX.trans hi')
    have hsignY : bitValue Y sign = bitValue I sign := by
      rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hsignX]
    have hBY : actGates B Y = Y := ccx_identity_of_first_clear hiterY
    have hAY : actGates A Y = X := by
      rw [ccx_on hp1Y hp2Y]
      exact RGate.xor_cancel X iter
    rcases Nat.eq_zero_or_pos (bitValue I sign) with hs | hs
    · have hs' : bitValue I sign = 0 := hs
      rw [hAX, hBY, hAY,
        ccx_identity_of_second_clear (hsignX.trans hs'), hxRestore, hs']
      symm
      apply write_of_bitValue
      simp [Nat.mod_eq_of_lt (bitValue_lt I controlWire)]
    · have hs' : bitValue I sign = 1 := by
        have h := bitValue_lt I sign
        omega
      have hBX : actGates B X = X ^^^ (1 <<< ctrl) :=
        ccx_on (hiterX.trans hi') (hsignX.trans hs')
      rw [hAX, hBY, hAY, hBX]
      simp only [X]
      rw [show actGates [.x p1]
          ((I ^^^ (1 <<< p1)) ^^^ (1 <<< ctrl)) =
          I ^^^ (1 <<< ctrl) by
        simp [actGates, RGate.act, Nat.xor_assoc, Nat.xor_comm,
          Nat.xor_left_comm]]
      rw [hs']
      change I ^^^ (1 <<< controlWire) =
        writeField I controlWire 1 ((bitValue I controlWire + 1) % 2)
      exact act_x_write controlWire I

theorem dirtyTriple_identity_phaseTwo_clear
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0) :
    actGates dirtyTripleGates I = I := by
  let p1 := PackedStepLayout.phaseOneWire
  let p2 := PackedStepLayout.phaseTwoWire
  let iter := PackedStepLayout.iterationWire
  let sign := PackedStepLayout.signWire
  let ctrl := controlWire
  let X := I ^^^ (1 <<< p1)
  let A : List RGate := [.ccx p1 p2 iter]
  let B : List RGate := [.ccx iter sign ctrl]
  have hx : actGates [.x p1] I = X := by
    simp [X, actGates, RGate.act]
  have hp2X : bitValue X p2 = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by decide), hphaseTwo]
  have hA : actGates A X = X :=
    ccx_identity_of_second_clear hp2X
  let K := actGates B X
  have hp2K : bitValue K p2 = 0 := by
    unfold bitValue
    rw [show K.testBit p2 = X.testBit p2 by
      exact testBit_actGates_of_outside (i := X) (by
        intro g hg
        simp only [B, List.mem_cons] at hg
        rcases hg with rfl | h <;>
          simp_all [RGate.wires, p2, iter, sign, ctrl, controlWire,
            PackedStepLayout.phaseTwoWire, PackedStepLayout.iterationWire,
            PackedStepLayout.signWire, PackedStepLayout.poolOffset])]
    simpa [bitValue] using hp2X
  have hAK : actGates A K = K :=
    ccx_identity_of_second_clear hp2K
  have hBK : actGates B K = X := by
    have hwf : B.all (RGate.wellFormed PackedStepLayout.width) = true := by
      decide +kernel
    simpa [K, B] using (actGates_reverse hwf X)
  have hxRestore : actGates [.x p1] X = I := by
    simp [X, actGates, RGate.act]
  change actGates [.x p1]
    (actGates B (actGates A (actGates B (actGates A
      (actGates [.x p1] I))))) = I
  rw [hx, hA]
  change actGates [.x p1] (actGates B (actGates A K)) = I
  rw [hAK, hBK, hxRestore]

theorem remainderAddControl_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates remainderAddControlGates I = I := by
  rw [remainderAddControlGates, actGates_append, actGates_append,
    negative_identity_of_source_set (by decide) hphaseOne,
    dirtyTriple_identity hphaseOne]
  exact PrunedSelectSwap.Tree.cx_off hextension

theorem remainderAddControl_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates remainderAddControlGates I =
      writeField I controlWire 1
        ((1 + bitValue I PackedStepLayout.signWire) % 2) := by
  let C := writeField I controlWire 1 1
  let D := writeField I controlWire 1
    ((1 + bitValue I PackedStepLayout.signWire) % 2)
  have hnegative : actGates
      (StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire) I =
      C := by
    rw [StepControl.negative_act (by decide)]
    simp [StepControl.negativeOut, C, hphaseOne, hcontrol]
  have hp1C : bitValue C PackedStepLayout.phaseOneWire = 0 := by
    rw [show bitValue C PackedStepLayout.phaseOneWire =
      bitValue I PackedStepLayout.phaseOneWire by
        exact bitValue_write_ne (by decide), hphaseOne]
  have hp2C : bitValue C PackedStepLayout.phaseTwoWire = 1 := by
    rw [show bitValue C PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire by
        exact bitValue_write_ne (by decide), hphaseTwo]
  have hsignC : bitValue C PackedStepLayout.signWire =
      bitValue I PackedStepLayout.signWire := by
    exact bitValue_write_ne (by decide)
  have hdirty : actGates dirtyTripleGates C = D := by
    rw [dirtyTriple_on hp1C hp2C]
    simp [C, D, bitValue_write_self, hsignC, writeField_writeField]
  have hextensionD : bitValue D PackedStepLayout.extensionWire = 0 := by
    rw [show bitValue D PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire by
        exact bitValue_write_ne (by decide), hextension]
  rw [remainderAddControlGates, actGates_append, actGates_append,
    hnegative, hdirty, PrunedSelectSwap.Tree.cx_off hextensionD]

theorem remainderAddControl_on_phaseZero
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates remainderAddControlGates I =
      writeField I controlWire 1 1 := by
  let C := writeField I controlWire 1 1
  have hnegative : actGates
      (StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire) I =
      C := by
    rw [StepControl.negative_act (by decide)]
    simp [StepControl.negativeOut, C, hphaseOne, hcontrol]
  have hp2C : bitValue C PackedStepLayout.phaseTwoWire = 0 := by
    rw [show bitValue C PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire by
        exact bitValue_write_ne (by decide), hphaseTwo]
  have hdirty : actGates dirtyTripleGates C = C :=
    dirtyTriple_identity_phaseTwo_clear hp2C
  have hextensionC : bitValue C PackedStepLayout.extensionWire = 0 := by
    rw [show bitValue C PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire by
        exact bitValue_write_ne (by decide), hextension]
  rw [remainderAddControlGates, actGates_append, actGates_append,
    hnegative, hdirty, PrunedSelectSwap.Tree.cx_off hextensionC]

private theorem remainderAddControl_identity_terminal
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 1) :
    actGates remainderAddControlGates I = I := by
  let C := writeField I controlWire 1 1
  have hnegative : actGates
      (StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire) I =
      C := by
    rw [StepControl.negative_act (by decide)]
    simp [StepControl.negativeOut, C, hphaseOne, hcontrol]
  have hphaseTwoC : bitValue C PackedStepLayout.phaseTwoWire = 0 := by
    rw [show bitValue C PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire by
        exact bitValue_write_ne (by decide), hphaseTwo]
  have hdirty : actGates dirtyTripleGates C = C :=
    dirtyTriple_identity_phaseTwo_clear hphaseTwoC
  have hextensionC : bitValue C PackedStepLayout.extensionWire = 1 := by
    rw [show bitValue C PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire by
        exact bitValue_write_ne (by decide), hextension]
  have hC : C = I ^^^ (1 <<< controlWire) := by
    symm
    rw [Selector.xor_eq_writeField_toggle, readField_one, hcontrol]
  rw [remainderAddControlGates, actGates_append, actGates_append,
    hnegative, hdirty, PrunedSelectSwap.Tree.cx_on hextensionC,
    hC, RGate.xor_cancel]

theorem remainderFlip_identity_phaseTwo_clear
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0) :
    actGates remainderFlipGates I = I := by
  rw [remainderFlipGates, Phase.negativeAnd_act (by decide) (by decide)]
  unfold Phase.negativeAndOut
  rw [hphaseTwo]
  simp only [ite_self, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.signWire)]
  simpa [readField_one] using
    writeField_read I PackedStepLayout.signWire 1

theorem remainderFlip_act
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates remainderFlipGates I =
      writeField I PackedStepLayout.signWire 1
        ((bitValue I PackedStepLayout.signWire + 1) % 2) := by
  rw [remainderFlipGates, Phase.negativeAnd_act (by decide) (by decide)]
  simp [Phase.negativeAndOut, hphaseOne, hphaseTwo]

theorem swapControl_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates swapControlGates I = I := by
  rw [swapControlGates, Phase.xorPair_act (by decide)]
  unfold Phase.xorPairOut
  rw [hphaseOne, hphaseTwo]
  have htarget := bitValue_lt I controlWire
  have hvalue : (bitValue I controlWire + 1 + 1) % 2 =
      bitValue I controlWire := by omega
  rw [hvalue]
  simpa [readField_one] using writeField_read I controlWire 1

theorem swapControl_identity_phaseZero
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0) :
    actGates swapControlGates I = I := by
  rw [swapControlGates, Phase.xorPair_act (by decide)]
  unfold Phase.xorPairOut
  rw [hphaseOne, hphaseTwo]
  simp only [Nat.add_zero, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (bitValue_lt I controlWire)]
  simpa [readField_one] using writeField_read I controlWire 1

theorem swapControl_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0) :
    actGates swapControlGates I = writeField I controlWire 1 1 := by
  rw [swapControlGates, Phase.xorPair_act (by decide)]
  unfold Phase.xorPairOut
  rw [hphaseOne, hphaseTwo, hcontrol]

theorem swapControl_on_phaseOne
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hcontrol : bitValue I controlWire = 0) :
    actGates swapControlGates I = writeField I controlWire 1 1 := by
  rw [swapControlGates, Phase.xorPair_act (by decide)]
  unfold Phase.xorPairOut
  rw [hphaseOne, hphaseTwo, hcontrol]

private theorem rPrimeSelector_disjoint :
    Wiring.Disjoint (Selector.layout 8)
      (Placed.selectorWiring PackedStepLayout.lengthRPrimeOffset
        PackedStepLayout.extensionWire (PackedStepLayout.poolOffset + 1)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Selector.layout, Placed.selectorWiring, Layout.size,
      PackedStepLayout.lengthRPrimeOffset, PackedStepLayout.extensionWire,
      PackedStepLayout.poolOffset]

theorem rPrimeSelector_identity
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates rPrimeSelectorGates I = I := by
  rw [rPrimeSelectorGates,
    Placed.selector_act rPrimeSelector_disjoint hscratch]
  rw [Nat.mod_eq_of_lt (encodedZero_lt 8), if_neg hsource, hextension]
  norm_num
  exact write_of_bitValue (by simpa using hextension.symm)

theorem rPrimeSelector_on_zero
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates rPrimeSelectorGates I =
      writeField I PackedStepLayout.extensionWire 1 1 := by
  rw [rPrimeSelectorGates,
    Placed.selector_act rPrimeSelector_disjoint hscratch]
  norm_num [hsource, hextension, encodedZero]

private theorem remainderPrepare_avoids_poolHead :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset ∨ PackedStepLayout.poolOffset + 1 ≤ q := by
  exact PackedEndpointOperands.remainderPrepare_avoids_poolHead

private theorem remainderPrepare_avoids_poolTail :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset + 11 ∨
        PackedStepLayout.poolOffset + 13 ≤ q := by
  exact PackedEndpointOperands.remainderPrepare_avoids_poolTail

private theorem remainderPrepare_avoids_workOne :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  exact PackedEndpointOperands.remainderPrepare_avoids_workOne

private theorem remainderPrepare_avoids_sign :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨
        PackedStepLayout.signWire + 1 ≤ q := by
  exact PackedEndpointOperands.remainderPrepare_avoids_sign

private theorem swapPrepare_avoids_poolHead :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset ∨ PackedStepLayout.poolOffset + 1 ≤ q := by
  exact PackedEndpointOperands.swapPrepare_avoids_poolHead

private theorem swapPrepare_avoids_poolTail :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset + 11 ∨
        PackedStepLayout.poolOffset + 13 ≤ q := by
  exact PackedEndpointOperands.swapPrepare_avoids_poolTail

private theorem swapPrepare_avoids_workOne :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  exact PackedEndpointOperands.swapPrepare_avoids_workOne

private theorem swapPrepare_avoids_sign :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨ PackedStepLayout.signWire + 1 ≤ q := by
  exact PackedEndpointOperands.swapPrepare_avoids_sign

private theorem swapControl_avoids_workOne :
    ∀ g ∈ swapControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  decide +kernel

private theorem swapControl_avoids_sign :
    ∀ g ∈ swapControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨ PackedStepLayout.signWire + 1 ≤ q := by
  decide +kernel

private theorem remainderPrepare_pool_clear
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    readField (actGates PackedStepLayout.remainderPrepareGates I)
      PackedStepLayout.poolOffset 13 = 0 := by
  let P := actGates PackedStepLayout.remainderPrepareGates I
  have hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hclears := PackedEndpointState.remainderPrepare_clears_pool
    hscratch hcarry
  have hhead : readField P PackedStepLayout.poolOffset 1 = 0 := by
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField I PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolHead I]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hmiddle : readField P (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    apply (readField_split (a := 9) (b := 1)).2
    exact ⟨hclears.1, by simpa [P, readField_one] using hclears.2⟩
  have htail : readField P (PackedStepLayout.poolOffset + 11) 2 = 0 := by
    rw [show readField P (PackedStepLayout.poolOffset + 11) 2 =
      readField I (PackedStepLayout.poolOffset + 11) 2 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolTail I]
    exact readField_sub_zero (by omega) (by omega) hpool
  rw [show 13 = 1 + 12 by omega, readField_split]
  refine ⟨hhead, ?_⟩
  rw [show 12 = 10 + 2 by omega, readField_split]
  exact ⟨hmiddle, htail⟩

private theorem remainderPrepare_pool_tail_clear
    {I : Nat}
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    readField (actGates PackedStepLayout.remainderPrepareGates I)
      (PackedStepLayout.poolOffset + 1) 12 = 0 := by
  let P := actGates PackedStepLayout.remainderPrepareGates I
  have hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_narrow (by omega) htail
  have hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hclears := PackedEndpointState.remainderPrepare_clears_pool
    hscratch hcarry
  have hmiddle : readField P (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    apply (readField_split (a := 9) (b := 1)).2
    exact ⟨hclears.1, by simpa [P, readField_one] using hclears.2⟩
  have hlast : readField P (PackedStepLayout.poolOffset + 11) 2 = 0 := by
    rw [show readField P (PackedStepLayout.poolOffset + 11) 2 =
      readField I (PackedStepLayout.poolOffset + 11) 2 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolTail I]
    exact readField_sub_zero (by omega) (by omega) htail
  rw [show 12 = 10 + 2 by omega, readField_split]
  exact ⟨hmiddle, hlast⟩

private theorem swapPrepare_pool_clear
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    readField (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.poolOffset 13 = 0 := by
  let P := actGates PackedStepLayout.swapPrepareGates I
  have hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hclears := PackedEndpointState.swapPrepare_clears_pool hscratch hcarry
  have hhead : readField P PackedStepLayout.poolOffset 1 = 0 := by
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField I PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside swapPrepare_avoids_poolHead I]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hmiddle : readField P (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    apply (readField_split (a := 9) (b := 1)).2
    exact ⟨hclears.1, by simpa [P, readField_one] using hclears.2⟩
  have htail : readField P (PackedStepLayout.poolOffset + 11) 2 = 0 := by
    rw [show readField P (PackedStepLayout.poolOffset + 11) 2 =
      readField I (PackedStepLayout.poolOffset + 11) 2 by
        exact readField_actGates_of_outside swapPrepare_avoids_poolTail I]
    exact readField_sub_zero (by omega) (by omega) hpool
  rw [show 13 = 1 + 12 by omega, readField_split]
  refine ⟨hhead, ?_⟩
  rw [show 12 = 10 + 2 by omega, readField_split]
  exact ⟨hmiddle, htail⟩

theorem remainderSubBody_identity
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderSubBody I = I := by
  let P := actGates PackedStepLayout.remainderPrepareGates I
  have hpoolP : readField P PackedStepLayout.poolOffset 13 = 0 :=
    remainderPrepare_pool_clear hpool
  have hinterval := PackedInterval.remainderReverse_identity
    (I := P)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
  simp only [remainderSubBody, actGates_append]
  rw [show actGates PackedStepLayout.remainderPrepareGates I = P by rfl,
    hinterval]
  exact PackedStepLayout.endpoint_uncompute I

theorem remainderAddBody_identity
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderAddBody I = I := by
  let P := actGates PackedStepLayout.remainderPrepareGates I
  have hpoolP : readField P PackedStepLayout.poolOffset 13 = 0 :=
    remainderPrepare_pool_clear hpool
  have hinterval := PackedInterval.remainderNoSign_identity
    (I := P)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (readField_sub_zero (by omega) (by omega) hpoolP)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
  simp only [remainderAddBody, actGates_append]
  rw [show actGates PackedStepLayout.remainderPrepareGates I = P by rfl,
    hinterval]
  exact PackedStepLayout.endpoint_uncompute I

theorem remainderSubBody_act
    {I left right : Nat}
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.shiftOffset 9 = right)
    (houter : bitValue
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.poolOffset = 1)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    let P := actGates PackedStepLayout.remainderPrepareGates I
    actGates remainderSubBody I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (StepPlaced.intervalSubTargetValue left right 259 9
            (PackedInterval.remainderInput P)))
        PackedStepLayout.signWire 1
        (StepPlaced.intervalSubSignValue left right 259 9
          (PackedInterval.remainderInput P)) := by
  dsimp only
  have hbody := PackedInterval.remainderReverse_act hLR hR hleft hright
    houter (remainderPrepare_pool_tail_clear htail)
  simpa [remainderSubBody, Step.around,
    PackedStepLayout.remainderCleanupGates, List.append_assoc] using
    (StepBlocks.around_write_two
      PackedStepLayout.remainderPrepare_wellFormed
      remainderPrepare_avoids_workOne remainderPrepare_avoids_sign hbody)

theorem remainderAddBody_act
    {I left right : Nat}
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.shiftOffset 9 = right)
    (houter : bitValue
      (actGates PackedStepLayout.remainderPrepareGates I)
        PackedStepLayout.poolOffset = 1)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    let P := actGates PackedStepLayout.remainderPrepareGates I
    actGates remainderAddBody I =
      writeField I PackedStepLayout.workOneOffset 259
        (StepPlaced.intervalAddTargetValue left right 259 9
          (PackedInterval.remainderInput P)) := by
  dsimp only
  have hbody := PackedInterval.remainderNoSign_act hLR hR hleft hright
    houter (remainderPrepare_pool_tail_clear htail)
  simpa [remainderAddBody, Step.around,
    PackedStepLayout.remainderCleanupGates, List.append_assoc] using
    (StepBlocks.around_write
      PackedStepLayout.remainderPrepare_wellFormed
      remainderPrepare_avoids_workOne hbody)

theorem swapBody_identity
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates swapBody I = I := by
  let P := actGates PackedStepLayout.swapPrepareGates I
  have hpoolP : readField P PackedStepLayout.poolOffset 13 = 0 :=
    swapPrepare_pool_clear hpool
  have hswap := PackedSelectSwap.gates_identity
    (I := P)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpoolP)
    (readField_sub_zero (by omega) (by omega) hpoolP)
  simp only [swapBody, actGates_append]
  rw [show actGates PackedStepLayout.swapPrepareGates I = P by rfl, hswap]
  exact PackedStepLayout.swapEndpoint_uncompute I

theorem swapBody_act_general
    {I j : Nat}
    (hj : j < 259)
    (hleft : readField
      (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.lengthTOffset 9 = j)
    (houter : bitValue
      (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.poolOffset = 1)
    (htail : readField
      (actGates PackedStepLayout.swapPrepareGates I)
      (PackedStepLayout.poolOffset + 1) 10 = 0) :
    actGates swapBody I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (writeField
            (readField I PackedStepLayout.workOneOffset 259) j 1
            (bitValue I PackedStepLayout.signWire)))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  let P := actGates PackedStepLayout.swapPrepareGates I
  have hworkP : readField P PackedStepLayout.workOneOffset 259 =
      readField I PackedStepLayout.workOneOffset 259 :=
    readField_actGates_of_outside swapPrepare_avoids_workOne I
  have hworkBitP : bitValue P (PackedStepLayout.workOneOffset + j) =
      bitValue I (PackedStepLayout.workOneOffset + j) := by
    rw [← readField_one, ← readField_one]
    apply readField_actGates_of_outside
    intro g hg q hq
    rcases swapPrepare_avoids_workOne g hg q hq with hq | hq
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hsignP : bitValue P PackedStepLayout.signWire =
      bitValue I PackedStepLayout.signWire := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside swapPrepare_avoids_sign I
  have hselect := PackedSelectSwap.gates_act_general
    (I := P) (j := j) (by simpa [PackedStepLayout.workWidth] using hj)
    hleft houter htail
  simp only [PackedStepLayout.workWidth] at hselect
  rw [hworkP, hworkBitP, hsignP] at hselect
  apply StepBlocks.around_write_two PackedStepLayout.swapPrepare_wellFormed
    swapPrepare_avoids_workOne swapPrepare_avoids_sign
  simpa [P] using hselect

theorem swapBody_act
    {I j : Nat}
    (hj : j < 259)
    (hleft : readField
      (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.lengthTOffset 9 = j)
    (houter : bitValue
      (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.poolOffset = 1)
    (hsign : bitValue
      (actGates PackedStepLayout.swapPrepareGates I)
      PackedStepLayout.signWire = 0)
    (htail : readField
      (actGates PackedStepLayout.swapPrepareGates I)
      (PackedStepLayout.poolOffset + 1) 10 = 0) :
    actGates swapBody I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (writeField
            (readField I PackedStepLayout.workOneOffset 259) j 1 0))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  have hsignI : bitValue I PackedStepLayout.signWire = 0 := by
    have hread : readField
        (actGates PackedStepLayout.swapPrepareGates I)
          PackedStepLayout.signWire 1 =
        readField I PackedStepLayout.signWire 1 :=
      readField_actGates_of_outside swapPrepare_avoids_sign I
    have hbit : bitValue
        (actGates PackedStepLayout.swapPrepareGates I)
          PackedStepLayout.signWire =
        bitValue I PackedStepLayout.signWire := by
      simpa [readField_one] using hread
    exact hbit.symm.trans hsign
  simpa [hsignI] using
    swapBody_act_general hj hleft houter htail

theorem quotientIncrementControl_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1) :
    actGates quotientIncrementControlGates I = I := by
  exact negativeAnd_identity_of_second_set (by decide) (by decide) hphaseOne

theorem quotientIncrementControl_identity_phaseTwo_clear
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0) :
    actGates quotientIncrementControlGates I = I := by
  rw [quotientIncrementControlGates,
    Phase.negativeAnd_act (by decide) (by decide)]
  unfold Phase.negativeAndOut
  rw [hphaseTwo]
  simp only [ite_self, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I controlWire)]
  simpa [readField_one] using writeField_read I controlWire 1

theorem quotientIncrementControl_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates quotientIncrementControlGates I =
      I ^^^ (1 <<< controlWire) := by
  simpa [quotientIncrementControlGates, Phase.negativeAndGates,
    PrunedSelectSwap.Tree.negativeAnd] using
    (PrunedSelectSwap.Tree.negativeAnd_on_zero
      (child := controlWire) (by decide) hphaseTwo hphaseOne)

theorem quotientDecrementControl_identity
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates quotientDecrementControlGates I = I := by
  exact negativeAnd_identity_of_second_set (by decide) (by decide) hphaseTwo

theorem quotientDecrementControl_identity_phaseOne_clear
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0) :
    actGates quotientDecrementControlGates I = I := by
  rw [quotientDecrementControlGates,
    Phase.negativeAnd_act (by decide) (by decide)]
  unfold Phase.negativeAndOut
  rw [hphaseOne]
  simp only [ite_self, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt I controlWire)]
  simpa [readField_one] using writeField_read I controlWire 1

theorem quotientDecrementControl_on
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0) :
    actGates quotientDecrementControlGates I =
      I ^^^ (1 <<< controlWire) := by
  simpa [quotientDecrementControlGates, Phase.negativeAndGates,
    PrunedSelectSwap.Tree.negativeAnd] using
    (PrunedSelectSwap.Tree.negativeAnd_on_zero
      (child := controlWire) (by decide) hphaseOne hphaseTwo)

private theorem preShiftControl_wellFormed :
    preShiftControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem preShiftControl_avoids_shift :
    ∀ g ∈ preShiftControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.shiftOffset ∨
        PackedStepLayout.shiftOffset + 9 ≤ q := by
  decide +kernel

private theorem preShiftControl_avoids_workTwo :
    ∀ g ∈ preShiftControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workTwoOffset ∨
        PackedStepLayout.workTwoOffset + 259 ≤ q := by
  decide +kernel

private theorem remainderSubControl_wellFormed :
    remainderSubControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem remainderAddControl_wellFormed :
    remainderAddControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem remainderSubControl_avoids_workOne :
    ∀ g ∈ remainderSubControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  decide +kernel

private theorem remainderSubControl_avoids_sign :
    ∀ g ∈ remainderSubControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨
        PackedStepLayout.signWire + 1 ≤ q := by
  decide +kernel

private theorem remainderAddControl_avoids_workOne :
    ∀ g ∈ remainderAddControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem rPrimeSelector_wellFormed :
    rPrimeSelectorGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem quotientIncrementControl_wellFormed :
    quotientIncrementControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem quotientIncrementControl_avoids_lengthQ :
    ∀ g ∈ quotientIncrementControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.lengthQOffset ∨
        PackedStepLayout.lengthQOffset + 9 ≤ q := by
  decide +kernel

private theorem quotientDecrementControl_wellFormed :
    quotientDecrementControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

private theorem quotientDecrementControl_avoids_lengthQ :
    ∀ g ∈ quotientDecrementControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.lengthQOffset ∨
        PackedStepLayout.lengthQOffset + 9 ≤ q := by
  decide +kernel

private theorem swapControl_wellFormed :
    swapControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

def phaseOnePreShiftCheckpoint (s : State) : Nat :=
  writeField
    (writeField (PackedState.encoded s) PackedStepLayout.shiftOffset 9
      (encodeLength 9 (s.shift - 1)))
    PackedStepLayout.workTwoOffset 259
    (encodeWork2 256 { s with shift := s.shift - 1 })

theorem preShiftBlock_act_phaseOne
    {s : State}
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hshiftPositive : 0 < s.shift)
    (hshiftFit : s.shift < 2 ^ 9) :
    actGates preShiftBlock (PackedState.encoded s) =
      phaseOnePreShiftCheckpoint s := by
  let I := PackedState.encoded s
  let C := actGates preShiftControlGates I
  let J := PackedShift.input C
  let result := Shift.out 259 9 J
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 0 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2 : bitValue I PackedStepLayout.phaseTwoWire = 1 := by
    simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hplusI : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hminusI : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hcontrol : C = writeField
      (writeField I controlWire 1 1)
      (PackedStepLayout.poolOffset + 10) 1 1 := by
    simp only [C, preShiftControlGates, actGates_append,
      actGates_cons, actGates_nil, act_ccx_write]
    rw [StepControl.negative_act (by decide)]
    simp only [StepControl.negativeOut]
    rw [hp1, hplusI]
    norm_num
    rw [bitValue_write_ne (by decide), hminusI,
      bitValue_write_self, bitValue_write_ne (by decide), hp2]
  have hplusC : bitValue C PackedStepLayout.poolOffset = 1 := by
    change bitValue C controlWire = 1
    rw [hcontrol, bitValue_write_ne (by decide), bitValue_write_self]
  have hminusC : bitValue C (PackedStepLayout.poolOffset + 10) = 1 := by
    rw [hcontrol, bitValue_write_self]
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    rw [hcontrol, readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hplus : bitValue J (Shift.plusWire 9) = 1 := by
    dsimp only [J]
    rw [PackedShift.input_plus]
    exact hplusC
  have hminus : bitValue J (Shift.minusWire 259 9) = 1 := by
    dsimp only [J]
    rw [PackedShift.input_minus]
    exact hminusC
  have hposition : Shift.position 9 J = encodeLength 9 s.shift := by
    dsimp only [J]
    rw [PackedShift.input_position, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_shift s
  have hwork : Shift.work 259 9 J = encodeWork2 256 s := by
    dsimp only [J]
    rw [PackedShift.input_work, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_workTwo s
  have hout := Shift.out_decrement hplus hminus
  have hresultPosition : Shift.position 9 result =
      encodeLength 9 (s.shift - 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_pred hshiftPositive hshiftFit]
  have hresultWork : Shift.work 259 9 result =
      encodeWork2 256 { s with shift := s.shift - 1 } := by
    dsimp only [result]
    rw [hout.2, hwork]
    change rotateLeftValue 259
        (rotatePositionsLeft 259 s.shift (encodeWork2Raw 256 s)) =
      rotatePositionsLeft 259 (s.shift - 1) (encodeWork2Raw 256 s)
    have hshift : s.shift - 1 + 1 = s.shift := by omega
    calc
      rotateLeftValue 259
          (rotatePositionsLeft 259 s.shift (encodeWork2Raw 256 s)) =
          rotateLeftValue 259
            (rotatePositionsLeft 259 (s.shift - 1 + 1)
              (encodeWork2Raw 256 s)) := by rw [hshift]
      _ = rotatePositionsLeft 259 (s.shift - 1) (encodeWork2Raw 256 s) :=
        rotatePositionsLeft_pred 259 (s.shift - 1) (encodeWork2Raw 256 s)
  have hbody := PackedShift.gates_act (I := C) hscratchC
  dsimp only at hbody
  rw [hresultPosition, hresultWork] at hbody
  apply StepBlocks.around_write_two preShiftControl_wellFormed
    preShiftControl_avoids_shift preShiftControl_avoids_workTwo
  simpa only [C, I] using hbody

theorem preShiftBlock_act_phaseZero
    {s : State}
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hlenQ : s.lenQ = 0)
    (hshiftFit : s.shift + 1 < 2 ^ 9) :
    actGates preShiftBlock (PackedState.encoded s) =
      PackedState.encoded { s with shift := s.shift + 1 } := by
  let I := PackedState.encoded s
  let C := actGates preShiftControlGates I
  let J := PackedShift.input C
  let result := Shift.out 259 9 J
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 0 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2 : bitValue I PackedStepLayout.phaseTwoWire = 0 := by
    simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hplusI : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  let C0 := writeField I controlWire 1 1
  have hnegative : actGates
      (StepControl.negativeGates PackedStepLayout.phaseOneWire controlWire) I =
      C0 := by
    rw [StepControl.negative_act (by decide)]
    simp [StepControl.negativeOut, C0, hp1, hplusI]
  have hp2C0 : bitValue C0 PackedStepLayout.phaseTwoWire = 0 := by
    rw [show bitValue C0 PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire by
        exact bitValue_write_ne (by decide), hp2]
  have hcontrol : C = C0 := by
    simp only [C, preShiftControlGates, actGates_append]
    rw [hnegative]
    exact ccx_identity_of_second_clear hp2C0
  have hplusC : bitValue C PackedStepLayout.poolOffset = 1 := by
    change bitValue C controlWire = 1
    rw [hcontrol, bitValue_write_self]
  have hminusC : bitValue C (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [hcontrol, bitValue_write_ne (by decide)]
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    rw [hcontrol, readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hplus : bitValue J (Shift.plusWire 9) = 1 := by
    dsimp only [J]
    rw [PackedShift.input_plus]
    exact hplusC
  have hminus : bitValue J (Shift.minusWire 259 9) = 0 := by
    dsimp only [J]
    rw [PackedShift.input_minus]
    exact hminusC
  have hposition : Shift.position 9 J = encodeLength 9 s.shift := by
    dsimp only [J]
    rw [PackedShift.input_position, hcontrol,
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_shift s
  have hwork : Shift.work 259 9 J = encodeWork2 256 s := by
    dsimp only [J]
    rw [PackedShift.input_work, hcontrol,
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_workTwo s
  have hout := Shift.out_increment hplus hminus
  have hresultPosition : Shift.position 9 result =
      encodeLength 9 (s.shift + 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_succ hshiftFit]
  have hresultWork : Shift.work 259 9 result =
      encodeWork2 256 { s with shift := s.shift + 1 } := by
    dsimp only [result]
    rw [hout.2, hwork]
    calc
      rotateRightValue 259 (encodeWork2 256 s) =
          rotateRightValue 259
            (rotatePositionsLeft 259 s.shift (encodeWork2Raw 256 s)) := by
        rfl
      _ = rotatePositionsLeft 259 (s.shift + 1)
          (encodeWork2Raw 256 s) :=
        (rotatePositionsLeft_succ 259 s.shift (encodeWork2Raw 256 s)).symm
      _ = encodeWork2 256 { s with shift := s.shift + 1 } := by
        rfl
  have hbody := PackedShift.gates_act (I := C) hscratchC
  dsimp only at hbody
  rw [hresultPosition, hresultWork] at hbody
  have haround := StepBlocks.around_write_two preShiftControl_wellFormed
    preShiftControl_avoids_shift preShiftControl_avoids_workTwo hbody
  have hencoded := PackedState.encoded_write_shiftWorkTwo
    (s.shift + 1) s hlenQ
  simpa [preShiftBlock, I, encodeWork2, encodeWork2Raw] using
    haround.trans hencoded

theorem preShiftBlock_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates preShiftBlock I = I := by
  apply StepBlocks.around_identity preShiftControl_wellFormed
  rw [preShiftControl_identity hphaseOne
    (by
      change bitValue I PackedStepLayout.poolOffset = 0
      rw [← readField_one]
      exact readField_sub_zero (by omega) (by omega) hpool)]
  exact PackedShift.gates_identity
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpool)
    (readField_sub_zero (by omega) (by omega) hpool)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpool)

theorem remainderSubBlock_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderSubBlock I = I := by
  apply StepBlocks.around_identity remainderSubControl_wellFormed
  rw [remainderSubControl_identity hphaseOne hextension]
  exact remainderSubBody_identity hpool

theorem remainderSubBlock_act
    {I left right : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.shiftOffset 9 = right)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    let P := actGates PackedStepLayout.remainderPrepareGates
      (writeField I controlWire 1 1)
    actGates remainderSubBlock I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (StepPlaced.intervalSubTargetValue left right 259 9
            (PackedInterval.remainderInput P)))
        PackedStepLayout.signWire 1
        (StepPlaced.intervalSubSignValue left right 259 9
          (PackedInterval.remainderInput P)) := by
  dsimp only
  let C := writeField I controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  have hcompute : actGates remainderSubControlGates I = C :=
    remainderSubControl_on hphaseOne hcontrol hextension
  have htailC : readField C (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact htail
  have houter : bitValue P PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField C PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolHead C]
    simpa [C, controlWire] using
      (readField_writeField_self (i := I)
        (off := PackedStepLayout.poolOffset) (n := 1) (v := 1) (by decide))
  have hbody := remainderSubBody_act hLR hR hleft hright houter htailC
  apply StepBlocks.around_write_two remainderSubControl_wellFormed
    remainderSubControl_avoids_workOne remainderSubControl_avoids_sign
  rw [hcompute]
  exact hbody

theorem remainderAddBlock_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderAddBlock I = I := by
  apply StepBlocks.around_identity remainderAddControl_wellFormed
  rw [remainderAddControl_identity hphaseOne hextension]
  exact remainderAddBody_identity hpool

theorem remainderAddBlock_identity_phaseOne
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderAddBlock I = I := by
  apply StepBlocks.around_identity remainderAddControl_wellFormed
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  rw [remainderAddControl_on hphaseOne hphaseTwo hcontrol hextension,
    hsign]
  norm_num
  rw [write_of_bitValue (by simpa using hcontrol.symm)]
  exact remainderAddBody_identity hpool

private theorem remainderSubBlock_identity_terminal
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderSubBlock I = I := by
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  apply StepBlocks.around_identity remainderSubControl_wellFormed
  rw [remainderSubControl_identity_terminal hphaseOne hcontrol hextension]
  exact remainderSubBody_identity hpool

private theorem remainderAddBlock_identity_terminal
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderAddBlock I = I := by
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  apply StepBlocks.around_identity remainderAddControl_wellFormed
  rw [remainderAddControl_identity_terminal hphaseOne hphaseTwo hcontrol
    hextension]
  exact remainderAddBody_identity hpool

theorem remainderAddBlock_act
    {I left right : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.shiftOffset 9 = right)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    let P := actGates PackedStepLayout.remainderPrepareGates
      (writeField I controlWire 1 1)
    actGates remainderAddBlock I =
      writeField I PackedStepLayout.workOneOffset 259
        (StepPlaced.intervalAddTargetValue left right 259 9
          (PackedInterval.remainderInput P)) := by
  dsimp only
  let C := writeField I controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  have hcompute : actGates remainderAddControlGates I = C := by
    rw [remainderAddControl_on hphaseOne hphaseTwo hcontrol hextension,
      hsign]
  have htailC : readField C (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact htail
  have houter : bitValue P PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField C PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolHead C]
    simpa [C, controlWire] using
      (readField_writeField_self (i := I)
        (off := PackedStepLayout.poolOffset) (n := 1) (v := 1) (by decide))
  have hbody := remainderAddBody_act hLR hR hleft hright houter htailC
  apply StepBlocks.around_write remainderAddControl_wellFormed
    remainderAddControl_avoids_workOne
  rw [hcompute]
  exact hbody

theorem remainderAddBlock_act_phaseZero
    {I left right : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField
      (actGates PackedStepLayout.remainderPrepareGates
        (writeField I controlWire 1 1))
      PackedStepLayout.shiftOffset 9 = right)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    let P := actGates PackedStepLayout.remainderPrepareGates
      (writeField I controlWire 1 1)
    actGates remainderAddBlock I =
      writeField I PackedStepLayout.workOneOffset 259
        (StepPlaced.intervalAddTargetValue left right 259 9
          (PackedInterval.remainderInput P)) := by
  dsimp only
  let C := writeField I controlWire 1 1
  let P := actGates PackedStepLayout.remainderPrepareGates C
  have hcompute : actGates remainderAddControlGates I = C :=
    remainderAddControl_on_phaseZero
      hphaseOne hphaseTwo hcontrol hextension
  have htailC : readField C (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact htail
  have houter : bitValue P PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField C PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside
          remainderPrepare_avoids_poolHead C]
    simpa [C, controlWire] using
      (readField_writeField_self (i := I)
        (off := PackedStepLayout.poolOffset) (n := 1) (v := 1) (by decide))
  have hbody := remainderAddBody_act hLR hR hleft hright houter htailC
  apply StepBlocks.around_write remainderAddControl_wellFormed
    remainderAddControl_avoids_workOne
  rw [hcompute]
  exact hbody

theorem remainderBlocks_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderBlocks I = I := by
  apply StepBlocks.around_identity rPrimeSelector_wellFormed
  rw [rPrimeSelector_identity hsource hextension
    (readField_sub_zero (by omega) (by omega) hpool)]
  simp only [actGates_append]
  rw [remainderSubBlock_identity hphaseOne hextension hpool,
    remainderFlip_identity hphaseOne,
    remainderAddBlock_identity hphaseOne hextension hpool]

theorem remainderBlocks_identity_terminal
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates remainderBlocks I = I := by
  let S := writeField I PackedStepLayout.extensionWire 1 1
  have hselect : actGates rPrimeSelectorGates I = S := by
    simpa [S] using rPrimeSelector_on_zero hsource hextension
      (readField_sub_zero (by omega) (by omega) hpool)
  have hp1S : bitValue S PackedStepLayout.phaseOneWire = 0 := by
    rw [show bitValue S PackedStepLayout.phaseOneWire =
      bitValue I PackedStepLayout.phaseOneWire by
        exact bitValue_write_ne (by decide), hphaseOne]
  have hp2S : bitValue S PackedStepLayout.phaseTwoWire = 0 := by
    rw [show bitValue S PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire by
        exact bitValue_write_ne (by decide), hphaseTwo]
  have hextensionS : bitValue S PackedStepLayout.extensionWire = 1 := by
    simp [S, bitValue_write_self]
  have hpoolS : readField S PackedStepLayout.poolOffset 13 = 0 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide), hpool]
  have hsub := remainderSubBlock_identity_terminal hp1S hextensionS hpoolS
  have hflip := remainderFlip_identity_phaseTwo_clear hp2S
  have hadd := remainderAddBlock_identity_terminal
    hp1S hp2S hextensionS hpoolS
  have hreverse : actGates rPrimeSelectorGates.reverse S = I := by
    have hinverse := actGates_reverse rPrimeSelector_wellFormed I
    rw [hselect] at hinverse
    exact hinverse
  simp only [remainderBlocks, Step.around, actGates_append]
  rw [hselect, hsub, hflip, hadd, hreverse]

theorem quotientIncrementBlock_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientIncrementBlock I = I := by
  apply StepBlocks.around_identity quotientIncrementControl_wellFormed
  rw [quotientIncrementControl_identity hphaseOne]
  exact PackedQuotient.increment_identity
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpool)
    (readField_sub_zero (by omega) (by omega) hpool)

theorem quotientIncrementBlock_identity_phaseZero
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientIncrementBlock I = I := by
  apply StepBlocks.around_identity quotientIncrementControl_wellFormed
  rw [quotientIncrementControl_identity_phaseTwo_clear hphaseTwo]
  exact PackedQuotient.increment_identity
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpool)
    (readField_sub_zero (by omega) (by omega) hpool)

theorem quotientIncrementBlock_act
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientIncrementBlock I =
      writeField I PackedStepLayout.lengthQOffset 9
        ((readField I PackedStepLayout.lengthQOffset 9 + 1) % 2 ^ 9) := by
  let C := I ^^^ (1 <<< controlWire)
  have hcompute : actGates quotientIncrementControlGates I = C := by
    exact quotientIncrementControl_on hphaseOne hphaseTwo
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [C]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    · exact readField_sub_zero (by omega) (by omega) hpool
    · left
      simp [controlWire, PackedStepLayout.poolOffset]
  have hcontrolI : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  have hcontrolC : bitValue C controlWire = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hcontrolI
  have hlengthQC : readField C PackedStepLayout.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simp only [C]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    decide +kernel
  have hcontrolC' : bitValue C PackedStepLayout.poolOffset = 1 := by
    simpa [controlWire] using hcontrolC
  have hbody := PackedQuotient.increment_act (I := C) hscratchC
  rw [PackedQuotient.incrementValue, hcontrolC', hlengthQC] at hbody
  apply StepBlocks.around_write quotientIncrementControl_wellFormed
    quotientIncrementControl_avoids_lengthQ
  rw [hcompute]
  exact hbody

private theorem quotientDecrement_identity
    {I : Nat}
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates PackedStepLayout.quotientDecrementGates I = I := by
  have hincrement := PackedQuotient.increment_identity
    (I := I)
    (by rw [← readField_one]; exact readField_sub_zero (by omega) (by omega) hpool)
    (readField_sub_zero (by omega) (by omega) hpool)
  have hinverse := actGates_reverse
    PackedStepLayout.quotientIncrement_wellFormed I
  rw [hincrement] at hinverse
  exact hinverse

theorem quotientDecrementBlock_identity
    {I : Nat}
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientDecrementBlock I = I := by
  apply StepBlocks.around_identity quotientDecrementControl_wellFormed
  rw [quotientDecrementControl_identity hphaseTwo]
  exact quotientDecrement_identity hpool

theorem quotientDecrementBlock_identity_phaseZero
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientDecrementBlock I = I := by
  apply StepBlocks.around_identity quotientDecrementControl_wellFormed
  rw [quotientDecrementControl_identity_phaseOne_clear hphaseOne]
  exact quotientDecrement_identity hpool

theorem quotientDecrementBlock_act
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates quotientDecrementBlock I =
      writeField I PackedStepLayout.lengthQOffset 9
        ((readField I PackedStepLayout.lengthQOffset 9 + 2 ^ 9 - 1) %
          2 ^ 9) := by
  let C := I ^^^ (1 <<< controlWire)
  have hcompute : actGates quotientDecrementControlGates I = C := by
    exact quotientDecrementControl_on hphaseOne hphaseTwo
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [C]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    · exact readField_sub_zero (by omega) (by omega) hpool
    · left
      simp [controlWire, PackedStepLayout.poolOffset]
  have hcontrolI : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire]) (by simp [controlWire]) hpool
  have hcontrolC : bitValue C controlWire = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hcontrolI
  have hlengthQC : readField C PackedStepLayout.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simp only [C]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    decide +kernel
  have hbody := PackedQuotient.decrement_act (I := C) hscratchC
  have hcontrolC' : bitValue C PackedStepLayout.poolOffset = 1 := by
    simpa [controlWire] using hcontrolC
  rw [PackedQuotient.decrementValue, hcontrolC', hlengthQC] at hbody
  apply StepBlocks.around_write quotientDecrementControl_wellFormed
    quotientDecrementControl_avoids_lengthQ
  rw [hcompute]
  exact hbody

theorem swapBlock_identity
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates swapBlock I = I := by
  apply StepBlocks.around_identity swapControl_wellFormed
  rw [swapControl_identity hphaseOne hphaseTwo]
  exact swapBody_identity hpool

theorem swapBlock_identity_phaseZero
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates swapBlock I = I := by
  apply StepBlocks.around_identity swapControl_wellFormed
  rw [swapControl_identity_phaseZero hphaseOne hphaseTwo]
  exact swapBody_identity hpool

theorem swapBlock_act_phaseOne
    {I j : Nat}
    (hj : j < 259)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 2 < 2 ^ 9)
    (hjValue : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 2 = j) :
    actGates swapBlock I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (writeField
            (readField I PackedStepLayout.workOneOffset 259) j 1
            (bitValue I PackedStepLayout.signWire)))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  let C := writeField I controlWire 1 1
  let P := actGates PackedStepLayout.swapPrepareGates C
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  have hcompute : actGates swapControlGates I = C := by
    exact swapControl_on_phaseOne hphaseOne hphaseTwo hcontrol
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hcarryC : bitValue C (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hlenTC : readField C PackedStepLayout.lengthTOffset 9 =
      readField I PackedStepLayout.lengthTOffset 9 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hprepare := PackedEndpointState.swapPrepare_act
    (I := C) hscratchC hcarryC (by simpa [hlenTC, hlenQC] using htfit)
  have hleft : readField P PackedStepLayout.lengthTOffset 9 = j := by
    simp only [P]
    rw [hprepare, readField_writeField_self (by omega), hlenTC, hlenQC,
      hjValue]
  have houter : bitValue P PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField C PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside
          swapPrepare_avoids_poolHead C]
    simpa [C, controlWire] using
      (readField_writeField_self (i := I)
        (off := PackedStepLayout.poolOffset) (n := 1) (v := 1) (by decide))
  have htailP : readField P (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    have hclear := PackedEndpointState.swapPrepare_clears_pool
      (I := C) hscratchC hcarryC
    apply (readField_split (a := 9) (b := 1)).2
    exact ⟨hclear.1, by simpa [P, readField_one] using hclear.2⟩
  have hworkBitC : bitValue C (PackedStepLayout.workOneOffset + j) =
      bitValue I (PackedStepLayout.workOneOffset + j) := by
    rw [← readField_one, ← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      right
      simp [controlWire, PackedStepLayout.poolOffset,
        PackedStepLayout.workOneOffset]
      omega)]
  have hworkC : readField C PackedStepLayout.workOneOffset 259 =
      readField I PackedStepLayout.workOneOffset 259 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hsignC : bitValue C PackedStepLayout.signWire =
      bitValue I PackedStepLayout.signWire := by
    rw [← readField_one, ← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hbody := swapBody_act_general hj hleft houter htailP
  rw [hworkBitC, hworkC, hsignC] at hbody
  apply StepBlocks.around_write_two swapControl_wellFormed
    swapControl_avoids_workOne swapControl_avoids_sign
  rw [hcompute]
  exact hbody

theorem swapBlock_act
    {I j : Nat}
    (hj : j < 259)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 2 < 2 ^ 9)
    (hjValue : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 2 = j) :
    actGates swapBlock I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (writeField
            (readField I PackedStepLayout.workOneOffset 259) j 1 0))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  let C := writeField I controlWire 1 1
  let P := actGates PackedStepLayout.swapPrepareGates C
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [controlWire])
      (by simp [controlWire]) hpool
  have hcompute : actGates swapControlGates I = C := by
    exact swapControl_on hphaseOne hphaseTwo hcontrol
  have hscratchC : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hcarryC : bitValue C (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      left
      simp [controlWire, PackedStepLayout.poolOffset])]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hlenTC : readField C PackedStepLayout.lengthTOffset 9 =
      readField I PackedStepLayout.lengthTOffset 9 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hlenQC : readField C PackedStepLayout.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hprepare := PackedEndpointState.swapPrepare_act
    (I := C) hscratchC hcarryC (by simpa [hlenTC, hlenQC] using htfit)
  have hleft : readField P PackedStepLayout.lengthTOffset 9 = j := by
    simp only [P]
    rw [hprepare, readField_writeField_self (by omega), hlenTC, hlenQC,
      hjValue]
  have houter : bitValue P PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.poolOffset 1 =
      readField C PackedStepLayout.poolOffset 1 by
        exact readField_actGates_of_outside swapPrepare_avoids_poolHead C]
    simpa [C, controlWire] using
      (readField_writeField_self (i := I)
        (off := PackedStepLayout.poolOffset) (n := 1) (v := 1) (by decide))
  have hsignC : bitValue C PackedStepLayout.signWire = 0 := by
    rw [← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel), readField_one]
    exact hsign
  have hsignP : bitValue P PackedStepLayout.signWire = 0 := by
    rw [← readField_one]
    rw [show readField P PackedStepLayout.signWire 1 =
      readField C PackedStepLayout.signWire 1 by
        exact readField_actGates_of_outside swapPrepare_avoids_sign C]
    simpa [readField_one] using hsignC
  have htailP : readField P (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    have hclear := PackedEndpointState.swapPrepare_clears_pool
      (I := C) hscratchC hcarryC
    apply (readField_split (a := 9) (b := 1)).2
    exact ⟨hclear.1, by simpa [P, readField_one] using hclear.2⟩
  have hworkBitC : bitValue C (PackedStepLayout.workOneOffset + j) =
      bitValue I (PackedStepLayout.workOneOffset + j) := by
    rw [← readField_one, ← readField_one]
    simp only [C]
    rw [readField_writeField_of_disjoint (by
      right
      simp [controlWire, PackedStepLayout.poolOffset,
        PackedStepLayout.workOneOffset]
      omega)]
  have hworkC : readField C PackedStepLayout.workOneOffset 259 =
      readField I PackedStepLayout.workOneOffset 259 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
  have hbody := swapBody_act hj hleft houter hsignP htailP
  rw [hworkBitC, hworkC] at hbody
  apply StepBlocks.around_write_two swapControl_wellFormed
    swapControl_avoids_workOne swapControl_avoids_sign
  rw [hcompute]
  exact hbody

def phaseTwoPostSwap (s : State) : Nat :=
  writeField
    (writeField (PackedState.encoded s) PackedStepLayout.workOneOffset 259
      (encodeWork1 256 (step 9 9 s) % 2 ^ 259))
    PackedStepLayout.signWire 1
    (boolValue (s.q.testBit s.shift))

def phaseTwoOutput (s : State) : Nat :=
  writeField (phaseTwoPostSwap s) PackedStepLayout.lengthQOffset 9
    (encodeLength 9 (s.lenQ - 1))

theorem swapBlock_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false) :
    actGates swapBlock (PackedState.encoded s) = phaseTwoPostSwap s := by
  let I := PackedState.encoded s
  let j := s.lenT + s.lenQ
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, _hlenRPrime, _hlenTFit, hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht, _hq, _hlenQ,
      _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have hlenQPositive : 0 < s.lenQ := hstate.2.2.1
  have htPositive := ReachableStepDomain.phaseTwo_t_pos
    h hphaseOne hphaseTwo
  have hlenTPositive : 0 < s.lenT := by
    rw [hlenT]
    exact bitLength_pos htPositive
  have hj : j < 259 := by
    dsimp only [j]
    simpa [workWidth] using (show s.lenT + s.lenQ < workWidth 256 by omega)
  have hlenTCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive),
      Nat.mod_eq_of_lt]
    omega
  have hlenQCode : encodeLength 9 s.lenQ = s.lenQ - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenQPositive),
      Nat.mod_eq_of_lt]
    omega
  have hselected : bitValue I (PackedStepLayout.workOneOffset + j) =
      boolValue (s.q.testBit s.shift) := by
    have hwork := PackedState.read_workOne s
    have htest := congrArg (fun z => z.testBit j) hwork
    have hlogical := testBit_encodeWork1_currentQuotient
      (n := 256) (s := s) ht hlenQPositive
    have hphysical : I.testBit (PackedStepLayout.workOneOffset + j) =
        (encodeWork1 256 s).testBit j := by
      simpa [I, testBit_readField, hj, PackedStepLayout.workOneOffset,
        Nat.testBit_mod_two_pow] using htest
    change boolValue (I.testBit (PackedStepLayout.workOneOffset + j)) =
      boolValue (s.q.testBit s.shift)
    exact congrArg boolValue (hphysical.trans (by simpa [j] using hlogical))
  have hswap := swapBlock_act
    (I := I) (j := j) hj
    (by simp [I, PackedState.read_phaseOne, hphaseOne, boolValue])
    (by simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue])
    (by simp [I, PackedState.read_sign, hstate.1, boolValue])
    (by simpa [I] using PackedState.read_pool s)
    (by
      rw [show readField I PackedStepLayout.lengthTOffset 9 =
          encodeLength 9 s.lenT by simpa [I] using PackedState.read_lengthT s,
        show readField I PackedStepLayout.lengthQOffset 9 =
          encodeLength 9 s.lenQ by simpa [I] using PackedState.read_lengthQ s,
        hlenTCode, hlenQCode]
      omega)
    (by
      rw [show readField I PackedStepLayout.lengthTOffset 9 =
          encodeLength 9 s.lenT by simpa [I] using PackedState.read_lengthT s,
        show readField I PackedStepLayout.lengthQOffset 9 =
          encodeLength 9 s.lenQ by simpa [I] using PackedState.read_lengthQ s,
        hlenTCode, hlenQCode]
      simp only [j]
      omega)
  rw [hselected] at hswap
  have hworkRead : readField I PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 s % 2 ^ 259 := by
    simpa [I] using PackedState.read_workOne s
  rw [hworkRead] at hswap
  have hworkUpdated :=
    ReachableStepDomain.phaseTwo_work1_after_quotientRemoval
      h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo
  norm_num [workWidth] at hworkUpdated
  rw [hworkUpdated] at hswap
  simpa [I, j, phaseTwoPostSwap] using hswap

theorem quotientDecrementBlock_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false) :
    actGates quotientDecrementBlock (phaseTwoPostSwap s) =
      phaseTwoOutput s := by
  let S := phaseTwoPostSwap s
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have hlenQPositive : 0 < s.lenQ := hstate.2.2.1
  have hlenQFit : s.lenQ < 2 ^ 9 := h.stepDomain.valid.1.2.2.2.1
  have hread (off width : Nat)
      (hwork : PackedStepLayout.workOneOffset + 259 ≤ off ∨
        off + width ≤ PackedStepLayout.workOneOffset)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + width ≤ PackedStepLayout.signWire) :
      readField S off width = readField (PackedState.encoded s) off width := by
    simp only [S, phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hwork]
  have hphaseOnePhysical : bitValue S PackedStepLayout.phaseOneWire = 1 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one, PackedState.read_phaseOne, hphaseOne]
    rfl
  have hphaseTwoPhysical : bitValue S PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel),
      readField_one, PackedState.read_phaseTwo, hphaseTwo]
    rfl
  have hpool : readField S PackedStepLayout.poolOffset 13 = 0 := by
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_pool s
  have hlengthQ : readField S PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    exact PackedState.read_lengthQ s
  rw [quotientDecrementBlock_act hphaseOnePhysical hphaseTwoPhysical hpool,
    hlengthQ, encodeLength_pred hlenQPositive hlenQFit]
  rfl

theorem gates_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) = phaseTwoOutput s := by
  let I := PackedState.encoded s
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2 : bitValue I PackedStepLayout.phaseTwoWire = 0 := by
    simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hextension : bitValue I PackedStepLayout.extensionWire = 0 := by
    simpa [I] using PackedState.read_extension s
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using PackedState.read_pool s
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.2.1
  have hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    rw [show readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime by simpa [I] using
        PackedState.read_lengthRPrime s]
    exact (encodeLength_eq_encodedZero_iff (by omega)).not.mpr (by omega)
  simp only [gates, actGates_append]
  rw [show PackedState.encoded s = I by rfl,
    preShiftBlock_identity hp1 hpool,
    remainderBlocks_identity hp1 hsource hextension hpool,
    quotientIncrementBlock_identity hp1 hpool,
    swapBlock_act_phaseTwo h hphaseOne hphaseTwo,
    quotientDecrementBlock_act_phaseTwo h hphaseOne hphaseTwo]

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) = PackedState.encoded s := by
  let I := PackedState.encoded s
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hp2 : bitValue I PackedStepLayout.phaseTwoWire = 1 := by
    simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hextension : bitValue I PackedStepLayout.extensionWire = 0 := by
    simpa [I] using PackedState.read_extension s
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using PackedState.read_pool s
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    rw [show readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime by simpa [I] using
        PackedState.read_lengthRPrime s]
    exact (encodeLength_eq_encodedZero_iff (by omega)).not.mpr
      (by omega)
  simp only [gates, actGates_append]
  rw [show PackedState.encoded s = I by rfl,
    preShiftBlock_identity hp1 hpool,
    remainderBlocks_identity hp1 hsource hextension hpool,
    quotientIncrementBlock_identity hp1 hpool,
    swapBlock_identity hp1 hp2 hpool,
    quotientDecrementBlock_identity hp2 hpool]

private theorem around_wellFormed
    {compute body : List RGate}
    (hcompute : compute.all
      (RGate.wellFormed PackedStepLayout.width) = true)
    (hbody : body.all
      (RGate.wellFormed PackedStepLayout.width) = true) :
    (Step.around compute body).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [Step.around, hcompute, hbody, List.all_reverse]

private theorem remainderSubBody_wellFormed :
    remainderSubBody.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [remainderSubBody, PackedStepLayout.remainderCleanupGates,
    PackedStepLayout.remainderPrepare_wellFormed,
    PackedStepLayout.remainderIntervalReverse_wellFormed, List.all_reverse]

private theorem remainderAddBody_wellFormed :
    remainderAddBody.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [remainderAddBody, PackedStepLayout.remainderCleanupGates,
    PackedStepLayout.remainderPrepare_wellFormed,
    PackedStepLayout.remainderIntervalNoSign_wellFormed, List.all_reverse]

private theorem swapBody_wellFormed :
    swapBody.all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [swapBody, PackedStepLayout.swapCleanupGates,
    PackedStepLayout.swapPrepare_wellFormed,
    PackedStepLayout.selectSwap_wellFormed, List.all_reverse]

private theorem remainderFlip_wellFormed :
    remainderFlipGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hpre := around_wellFormed preShiftControl_wellFormed
    PackedStepLayout.shift_wellFormed
  have hrsub := around_wellFormed remainderSubControl_wellFormed
    remainderSubBody_wellFormed
  have hradd := around_wellFormed remainderAddControl_wellFormed
    remainderAddBody_wellFormed
  have hpre' : preShiftBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [preShiftBlock] using hpre
  have hrsub' : remainderSubBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [remainderSubBlock] using hrsub
  have hradd' : remainderAddBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [remainderAddBlock] using hradd
  have hremainder : remainderBlocks.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    apply around_wellFormed rPrimeSelector_wellFormed
    simp [hrsub', hradd', remainderFlip_wellFormed]
  have hqinc := around_wellFormed quotientIncrementControl_wellFormed
    PackedStepLayout.quotientIncrement_wellFormed
  have hswap := around_wellFormed swapControl_wellFormed
    swapBody_wellFormed
  have hqdecBody : PackedStepLayout.quotientDecrementGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedStepLayout.quotientDecrementGates, List.all_reverse] using
      PackedStepLayout.quotientIncrement_wellFormed
  have hqdec := around_wellFormed quotientDecrementControl_wellFormed
    hqdecBody
  have hqinc' : quotientIncrementBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [quotientIncrementBlock] using hqinc
  have hswap' : swapBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [swapBlock] using hswap
  have hqdec' : quotientDecrementBlock.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [quotientDecrementBlock] using hqdec
  simp [circuit, RCircuit.wellFormed, gates, hpre', hremainder, hqinc',
    hswap', hqdec']

end PackedPhaseFourPrefix
end Euclid
end VQ
