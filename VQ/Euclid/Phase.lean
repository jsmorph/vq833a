/-
The phase-update block from Algorithm 3.

Length zero uses the paper's truth-minus-one representation, so the three
zero tests compare their source registers with all ones.  The selector scratch
pool is shared sequentially and every flag, control, and scratch wire returns
to zero after the complete block on its validity domain.
-/
import VQ.Euclid.Placed
import VQ.Euclid.State
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace Phase

open Reversible

def poolWidth (lengthWidth shiftWidth : Nat) : Nat :=
  max lengthWidth shiftWidth

def phase1Wire : Nat := 0

def phase2Wire : Nat := 1

def signWire : Nat := 2

def lenQOffset : Nat := 3

def lenRPrimeOffset (lengthWidth : Nat) : Nat := 3 + lengthWidth

def shiftOffset (lengthWidth : Nat) : Nat := 3 + 2 * lengthWidth

def zeroQWire (lengthWidth shiftWidth : Nat) : Nat :=
  shiftOffset lengthWidth + shiftWidth

def zeroRPrimeWire (lengthWidth shiftWidth : Nat) : Nat :=
  zeroQWire lengthWidth shiftWidth + 1

def zeroShiftWire (lengthWidth shiftWidth : Nat) : Nat :=
  zeroQWire lengthWidth shiftWidth + 2

def conditionWire (lengthWidth shiftWidth : Nat) : Nat :=
  zeroQWire lengthWidth shiftWidth + 3

def temporaryWire (lengthWidth shiftWidth : Nat) : Nat :=
  zeroQWire lengthWidth shiftWidth + 4

def poolOffset (lengthWidth shiftWidth : Nat) : Nat :=
  zeroQWire lengthWidth shiftWidth + 5

def layout (lengthWidth shiftWidth : Nat) : Layout :=
  [1, 1, 1, lengthWidth, lengthWidth, shiftWidth,
    1, 1, 1, 1, 1, poolWidth lengthWidth shiftWidth]

def qSelector (lengthWidth shiftWidth : Nat) : List RGate :=
  Placed.selectorGates (encodedZero lengthWidth) lengthWidth lenQOffset
    (zeroQWire lengthWidth shiftWidth) (poolOffset lengthWidth shiftWidth)

def rPrimeSelector (lengthWidth shiftWidth : Nat) : List RGate :=
  Placed.selectorGates (encodedZero lengthWidth) lengthWidth
    (lenRPrimeOffset lengthWidth) (zeroRPrimeWire lengthWidth shiftWidth)
    (poolOffset lengthWidth shiftWidth)

def shiftSelector (lengthWidth shiftWidth : Nat) : List RGate :=
  Placed.selectorGates (encodedZero shiftWidth) shiftWidth
    (shiftOffset lengthWidth) (zeroShiftWire lengthWidth shiftWidth)
    (poolOffset lengthWidth shiftWidth)

def selectorValue (width source i : Nat) : Nat :=
  if readField i source width = encodedZero width then 1 else 0

theorem selectorValue_lt (width source i : Nat) :
    selectorValue width source i < 2 := by
  unfold selectorValue
  split <;> omega

def selectGates (lengthWidth shiftWidth : Nat) : List RGate :=
  qSelector lengthWidth shiftWidth ++
    rPrimeSelector lengthWidth shiftWidth ++
    shiftSelector lengthWidth shiftWidth

def unselectGates (lengthWidth shiftWidth : Nat) : List RGate :=
  shiftSelector lengthWidth shiftWidth ++
    rPrimeSelector lengthWidth shiftWidth ++
    qSelector lengthWidth shiftWidth

def ownershipSelectGates (lengthWidth shiftWidth : Nat) : List RGate :=
  qSelector lengthWidth shiftWidth ++ shiftSelector lengthWidth shiftWidth

def ownershipUnselectGates (lengthWidth shiftWidth : Nat) : List RGate :=
  shiftSelector lengthWidth shiftWidth ++ qSelector lengthWidth shiftWidth

def ownershipSelected (lengthWidth shiftWidth i : Nat) : Nat :=
  let i := writeField i (zeroQWire lengthWidth shiftWidth) 1
    (selectorValue lengthWidth lenQOffset i)
  writeField i (zeroShiftWire lengthWidth shiftWidth) 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i)

def ownershipCleaned (lengthWidth shiftWidth i : Nat) : Nat :=
  let i := writeField i (zeroShiftWire lengthWidth shiftWidth) 1 0
  writeField i (zeroQWire lengthWidth shiftWidth) 1 0

theorem ownershipSelected_flags (lengthWidth shiftWidth i : Nat) :
    let out := ownershipSelected lengthWidth shiftWidth i
    bitValue out (zeroQWire lengthWidth shiftWidth) =
      selectorValue lengthWidth lenQOffset i ∧
    bitValue out (zeroShiftWire lengthWidth shiftWidth) =
      selectorValue shiftWidth (shiftOffset lengthWidth) i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  set i1 := writeField i zq 1
    (selectorValue lengthWidth lenQOffset i) with hi1
  set i2 := writeField i1 zs 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i1) with hi2
  have hsourceShift :
      readField i1 (shiftOffset lengthWidth) shiftWidth =
        readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, zeroQWire, shiftOffset])]
  change bitValue i2 zq = _ ∧ bitValue i2 zs = _
  constructor
  · rw [hi2, bitValue_write_ne (by
      simp [zq, zs, zeroQWire, zeroShiftWire]), hi1,
      bitValue_write_self,
      Nat.mod_eq_of_lt (selectorValue_lt lengthWidth lenQOffset i)]
  · rw [hi2, bitValue_write_self,
      Nat.mod_eq_of_lt (selectorValue_lt shiftWidth
        (shiftOffset lengthWidth) i1)]
    unfold selectorValue
    rw [hsourceShift]

theorem ownershipSelected_eq_writeFields (lengthWidth shiftWidth i : Nat) :
    let result := ownershipSelected lengthWidth shiftWidth i
    result =
      writeField
        (writeField i (zeroQWire lengthWidth shiftWidth) 1
          (bitValue result (zeroQWire lengthWidth shiftWidth)))
        (zeroShiftWire lengthWidth shiftWidth) 1
        (bitValue result (zeroShiftWire lengthWidth shiftWidth)) := by
  let result := ownershipSelected lengthWidth shiftWidth i
  have hflags := ownershipSelected_flags lengthWidth shiftWidth i
  dsimp only at hflags ⊢
  rw [hflags.1, hflags.2]
  simp only [ownershipSelected]
  congr 1
  unfold selectorValue
  rw [readField_writeField_of_disjoint (by
    simp [zeroQWire, shiftOffset])]

theorem ownershipCleaned_eq_writeFields (lengthWidth shiftWidth i : Nat) :
    ownershipCleaned lengthWidth shiftWidth i =
      writeField
        (writeField i (zeroShiftWire lengthWidth shiftWidth) 1 0)
        (zeroQWire lengthWidth shiftWidth) 1 0 := by
  rfl

def selected (lengthWidth shiftWidth i : Nat) : Nat :=
  let i := writeField i (zeroQWire lengthWidth shiftWidth) 1
    (selectorValue lengthWidth lenQOffset i)
  let i := writeField i (zeroRPrimeWire lengthWidth shiftWidth) 1
    (selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i)
  writeField i (zeroShiftWire lengthWidth shiftWidth) 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i)

def cleaned (lengthWidth shiftWidth i : Nat) : Nat :=
  let i := writeField i (zeroShiftWire lengthWidth shiftWidth) 1 0
  let i := writeField i (zeroRPrimeWire lengthWidth shiftWidth) 1 0
  writeField i (zeroQWire lengthWidth shiftWidth) 1 0

theorem selected_preserves_field {lengthWidth shiftWidth i off width : Nat}
    (hq : zeroQWire lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ zeroQWire lengthWidth shiftWidth)
    (hr : zeroRPrimeWire lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ zeroRPrimeWire lengthWidth shiftWidth)
    (hs : zeroShiftWire lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ zeroShiftWire lengthWidth shiftWidth) :
    readField (selected lengthWidth shiftWidth i) off width =
      readField i off width := by
  simp only [selected]
  rw [readField_writeField_of_disjoint hs,
    readField_writeField_of_disjoint hr,
    readField_writeField_of_disjoint hq]

theorem selected_preserves_bit {lengthWidth shiftWidth i q : Nat}
    (hq : q ≠ zeroQWire lengthWidth shiftWidth)
    (hr : q ≠ zeroRPrimeWire lengthWidth shiftWidth)
    (hs : q ≠ zeroShiftWire lengthWidth shiftWidth) :
    bitValue (selected lengthWidth shiftWidth i) q = bitValue i q := by
  simp [selected, bitValue_write_ne hq, bitValue_write_ne hr,
    bitValue_write_ne hs]

theorem selected_flags (lengthWidth shiftWidth i : Nat) :
    let out := selected lengthWidth shiftWidth i
    bitValue out (zeroQWire lengthWidth shiftWidth) =
      selectorValue lengthWidth lenQOffset i ∧
    bitValue out (zeroRPrimeWire lengthWidth shiftWidth) =
      selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i ∧
    bitValue out (zeroShiftWire lengthWidth shiftWidth) =
      selectorValue shiftWidth (shiftOffset lengthWidth) i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  set i1 := writeField i zq 1
    (selectorValue lengthWidth lenQOffset i) with hi1
  set i2 := writeField i1 zrp 1
    (selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i1) with hi2
  set i3 := writeField i2 zs 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i2) with hi3
  have hsourceRPrime :
      readField i1 (lenRPrimeOffset lengthWidth) lengthWidth =
        readField i (lenRPrimeOffset lengthWidth) lengthWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, zeroQWire, lenRPrimeOffset, shiftOffset]
      omega)]
  have hsourceShift :
      readField i2 (shiftOffset lengthWidth) shiftWidth =
        readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hi2, readField_writeField_of_disjoint (by
      simp [zrp, zeroRPrimeWire, zeroQWire, shiftOffset]), hi1,
      readField_writeField_of_disjoint (by
        simp [zq, zeroQWire, shiftOffset])]
  change bitValue i3 zq = _ ∧ bitValue i3 zrp = _ ∧
    bitValue i3 zs = _
  refine ⟨?_, ?_, ?_⟩
  · rw [hi3, bitValue_write_ne (by
      simp [zq, zs, zeroQWire, zeroShiftWire]), hi2,
      bitValue_write_ne (by simp [zq, zrp, zeroQWire, zeroRPrimeWire]), hi1,
      bitValue_write_self,
      Nat.mod_eq_of_lt (selectorValue_lt lengthWidth lenQOffset i)]
  · rw [hi3, bitValue_write_ne (by
      simp [zrp, zs, zeroRPrimeWire, zeroShiftWire]), hi2,
      bitValue_write_self,
      Nat.mod_eq_of_lt (selectorValue_lt lengthWidth
        (lenRPrimeOffset lengthWidth) i1)]
    unfold selectorValue
    rw [hsourceRPrime]
  · rw [hi3, bitValue_write_self,
      Nat.mod_eq_of_lt (selectorValue_lt shiftWidth
        (shiftOffset lengthWidth) i2)]
    unfold selectorValue
    rw [hsourceShift]

theorem selected_testBit_outside
    {lengthWidth shiftWidth i q : Nat}
    (hq : q ≠ zeroQWire lengthWidth shiftWidth)
    (hr : q ≠ zeroRPrimeWire lengthWidth shiftWidth)
    (hs : q ≠ zeroShiftWire lengthWidth shiftWidth) :
    (selected lengthWidth shiftWidth i).testBit q = i.testBit q := by
  simp only [selected]
  rw [testBit_writeField_outside (by omega),
    testBit_writeField_outside (by omega),
    testBit_writeField_outside (by omega)]

theorem selected_eq_writeFields (lengthWidth shiftWidth i : Nat) :
    let result := selected lengthWidth shiftWidth i
    result =
      writeField
        (writeField
          (writeField i (zeroQWire lengthWidth shiftWidth) 1
            (bitValue result (zeroQWire lengthWidth shiftWidth)))
          (zeroRPrimeWire lengthWidth shiftWidth) 1
          (bitValue result (zeroRPrimeWire lengthWidth shiftWidth)))
        (zeroShiftWire lengthWidth shiftWidth) 1
        (bitValue result (zeroShiftWire lengthWidth shiftWidth)) := by
  let result := selected lengthWidth shiftWidth i
  have hframe := eq_write_three_fields
    (i := i) (j := result)
    (o₁ := zeroQWire lengthWidth shiftWidth) (n₁ := 1)
    (o₂ := zeroRPrimeWire lengthWidth shiftWidth) (n₂ := 1)
    (o₃ := zeroShiftWire lengthWidth shiftWidth) (n₃ := 1)
    (by simp [zeroQWire, zeroRPrimeWire])
    (by simp [zeroQWire, zeroShiftWire])
    (by simp [zeroRPrimeWire, zeroShiftWire])
    (fun b hq hr hs => by
      exact selected_testBit_outside (by omega) (by omega) (by omega))
  simpa [result, readField_one] using hframe

theorem cleaned_eq_writeFields (lengthWidth shiftWidth i : Nat) :
    cleaned lengthWidth shiftWidth i =
      writeField
        (writeField
          (writeField i (zeroShiftWire lengthWidth shiftWidth) 1 0)
          (zeroRPrimeWire lengthWidth shiftWidth) 1 0)
        (zeroQWire lengthWidth shiftWidth) 1 0 := by
  rfl

def negativeAndGates (a b target : Nat) : List RGate :=
  [.x b, .ccx a b target, .x b]

def xorPairGates (a b target : Nat) : List RGate :=
  [.cx a target, .cx b target]

def negativeAndOut (a b target i : Nat) : Nat :=
  writeField i target 1
    ((bitValue i target + if bitValue i b = 0 then bitValue i a else 0) % 2)

def xorPairOut (a b target i : Nat) : Nat :=
  writeField i target 1
    ((bitValue i target + bitValue i a + bitValue i b) % 2)

def ccxOut (a b target i : Nat) : Nat :=
  writeField i target 1
    ((bitValue i target + bitValue i a * bitValue i b) % 2)

theorem negativeAnd_act {a b target i : Nat} (hab : a ≠ b)
    (hbt : b ≠ target) :
    actGates (negativeAndGates a b target) i = negativeAndOut a b target i := by
  let j := writeField i b 1 ((bitValue i b + 1) % 2)
  let u := (bitValue i target +
    bitValue i a * (((bitValue i b + 1) % 2) % 2)) % 2
  let k := writeField j target 1 u
  have e1 : RGate.act (.x b) i = j := by
    simp only [j, act_x_write]
  have hja : bitValue j a = bitValue i a := by
    exact bitValue_write_ne hab
  have hjb : bitValue j b = ((bitValue i b + 1) % 2) % 2 := by
    exact bitValue_write_self _ _ _
  have hjt : bitValue j target = bitValue i target := by
    exact bitValue_write_ne (Ne.symm hbt)
  have e2 : RGate.act (.ccx a b target) j = k := by
    rw [act_ccx_write, hja, hjb, hjt]
  have hkb : bitValue k b = bitValue j b := by
    exact bitValue_write_ne hbt
  have hb := bitValue_lt i b
  have hrestore : ((((bitValue i b + 1) % 2) % 2 + 1) % 2) = bitValue i b := by
    omega
  have hu : u =
      (bitValue i target +
        if bitValue i b = 0 then bitValue i a else 0) % 2 := by
    have ha := bitValue_lt i a
    by_cases hbzero : bitValue i b = 0
    · simp [u, hbzero]
    · have hbone : bitValue i b = 1 := by omega
      simp [u, hbone]
  rw [negativeAndGates, actGates_cons, actGates_cons, actGates_cons,
    actGates_nil, e1, e2, act_x_write, hkb, hjb, hrestore]
  change writeField (writeField j target 1 u) b 1 (bitValue i b) = _
  have hdis : target + 1 ≤ b ∨ b + 1 ≤ target := by omega
  have hwriteb : writeField i b 1 (bitValue i b) = i := by
    exact write_of_bitValue (by omega)
  rw [writeField_comm hdis]
  simp only [j, writeField_writeField]
  rw [hwriteb, negativeAndOut, hu]

theorem xorPair_act {a b target i : Nat} (hbt : b ≠ target) :
    actGates (xorPairGates a b target) i = xorPairOut a b target i := by
  rw [xorPairGates, actGates_cons, actGates_cons, actGates_nil,
    act_cx_write, act_cx_write]
  rw [bitValue_write_self, bitValue_write_ne hbt, writeField_writeField]
  apply write_congr
  have ha := bitValue_lt i a
  have hb := bitValue_lt i b
  have ht := bitValue_lt i target
  omega

def ccxGates (a b target : Nat) : List RGate :=
  [.ccx a b target]

theorem ccxGates_act (a b target i : Nat) :
    actGates (ccxGates a b target) i = ccxOut a b target i := by
  rw [ccxGates, actGates_cons, actGates_nil, act_ccx_write]
  rfl

def twoTargetsGates (control a b : Nat) : List RGate :=
  [.cx control a, .cx control b]

def twoTargetsOut (control a b i : Nat) : Nat :=
  let i := writeField i a 1
    ((bitValue i a + bitValue i control) % 2)
  writeField i b 1
    ((bitValue i b + bitValue i control) % 2)

theorem negativeAndOut_target (a b target i : Nat) :
    bitValue (negativeAndOut a b target i) target =
      (bitValue i target +
        if bitValue i b = 0 then bitValue i a else 0) % 2 := by
  simp [negativeAndOut, bitValue_write_self]

theorem negativeAndOut_ne {a b target i q : Nat} (h : q ≠ target) :
    bitValue (negativeAndOut a b target i) q = bitValue i q := by
  exact bitValue_write_ne h

theorem xorPairOut_target (a b target i : Nat) :
    bitValue (xorPairOut a b target i) target =
      (bitValue i target + bitValue i a + bitValue i b) % 2 := by
  simp [xorPairOut, bitValue_write_self]

theorem xorPairOut_ne {a b target i q : Nat} (h : q ≠ target) :
    bitValue (xorPairOut a b target i) q = bitValue i q := by
  exact bitValue_write_ne h

theorem ccxOut_target (a b target i : Nat) :
    bitValue (ccxOut a b target i) target =
      (bitValue i target + bitValue i a * bitValue i b) % 2 := by
  simp [ccxOut, bitValue_write_self]

theorem ccxOut_ne {a b target i q : Nat} (h : q ≠ target) :
    bitValue (ccxOut a b target i) q = bitValue i q := by
  exact bitValue_write_ne h

theorem twoTargetsOut_first {control a b i : Nat} (hab : a ≠ b) :
    bitValue (twoTargetsOut control a b i) a =
      (bitValue i a + bitValue i control) % 2 := by
  simp [twoTargetsOut, bitValue_write_ne hab, bitValue_write_self]

theorem twoTargetsOut_second {control a b i : Nat} (hba : b ≠ a)
    (hca : control ≠ a) :
    bitValue (twoTargetsOut control a b i) b =
      (bitValue i b + bitValue i control) % 2 := by
  simp [twoTargetsOut, bitValue_write_self, bitValue_write_ne hba,
    bitValue_write_ne hca]

theorem twoTargetsOut_ne {control a b i q : Nat} (hqa : q ≠ a)
    (hqb : q ≠ b) :
    bitValue (twoTargetsOut control a b i) q = bitValue i q := by
  simp [twoTargetsOut, bitValue_write_ne hqa, bitValue_write_ne hqb]

theorem twoTargets_act (control a b i : Nat) :
    actGates (twoTargetsGates control a b) i =
      twoTargetsOut control a b i := by
  rw [twoTargetsGates, actGates_cons, actGates_cons, actGates_nil,
    act_cx_write, act_cx_write]
  rfl

def logicGates (lengthWidth shiftWidth : Nat) : List RGate :=
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let cond := conditionWire lengthWidth shiftWidth
  let tmp := temporaryWire lengthWidth shiftWidth
  negativeAndGates zq zrp cond ++
    xorPairGates signWire phase1Wire tmp ++
    ccxGates cond tmp phase2Wire ++
    xorPairGates phase1Wire signWire tmp ++
    ccxGates cond phase2Wire signWire ++
    negativeAndGates zq zrp cond ++
    twoTargetsGates zs phase1Wire phase2Wire

def logicOut (lengthWidth shiftWidth i : Nat) : Nat :=
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let cond := conditionWire lengthWidth shiftWidth
  let tmp := temporaryWire lengthWidth shiftWidth
  let i := negativeAndOut zq zrp cond i
  let i := xorPairOut signWire phase1Wire tmp i
  let i := ccxOut cond tmp phase2Wire i
  let i := xorPairOut phase1Wire signWire tmp i
  let i := ccxOut cond phase2Wire signWire i
  let i := negativeAndOut zq zrp cond i
  twoTargetsOut zs phase1Wire phase2Wire i

def out (lengthWidth shiftWidth i : Nat) : Nat :=
  cleaned lengthWidth shiftWidth
    (logicOut lengthWidth shiftWidth (selected lengthWidth shiftWidth i))

theorem logicOut_preserves_field {lengthWidth shiftWidth i off width : Nat}
    (hp1 : phase1Wire + 1 ≤ off ∨ off + width ≤ phase1Wire)
    (hp2 : phase2Wire + 1 ≤ off ∨ off + width ≤ phase2Wire)
    (hsign : signWire + 1 ≤ off ∨ off + width ≤ signWire)
    (hcondition : conditionWire lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ conditionWire lengthWidth shiftWidth)
    (htemporary : temporaryWire lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ temporaryWire lengthWidth shiftWidth) :
    readField (logicOut lengthWidth shiftWidth i) off width =
      readField i off width := by
  simp only [logicOut, twoTargetsOut, negativeAndOut, ccxOut, xorPairOut]
  rw [readField_writeField_of_disjoint hp2,
    readField_writeField_of_disjoint hp1,
    readField_writeField_of_disjoint hcondition,
    readField_writeField_of_disjoint hsign,
    readField_writeField_of_disjoint htemporary,
    readField_writeField_of_disjoint hp2,
    readField_writeField_of_disjoint htemporary,
    readField_writeField_of_disjoint hcondition]

def conditionValue (lengthWidth shiftWidth i : Nat) : Nat :=
  if bitValue i (zeroRPrimeWire lengthWidth shiftWidth) = 0 then
    bitValue i (zeroQWire lengthWidth shiftWidth)
  else 0

def middlePhase2Value (lengthWidth shiftWidth i : Nat) : Nat :=
  (bitValue i phase2Wire +
    conditionValue lengthWidth shiftWidth i *
      ((bitValue i signWire + bitValue i phase1Wire) % 2)) % 2

def phase1Value (lengthWidth shiftWidth i : Nat) : Nat :=
  (bitValue i phase1Wire +
    bitValue i (zeroShiftWire lengthWidth shiftWidth)) % 2

def phase2Value (lengthWidth shiftWidth i : Nat) : Nat :=
  (middlePhase2Value lengthWidth shiftWidth i +
    bitValue i (zeroShiftWire lengthWidth shiftWidth)) % 2

def signValue (lengthWidth shiftWidth i : Nat) : Nat :=
  (bitValue i signWire +
    conditionValue lengthWidth shiftWidth i *
      middlePhase2Value lengthWidth shiftWidth i) % 2

theorem logic_bits {lengthWidth shiftWidth i : Nat}
    (hcondition : bitValue i (conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue i (temporaryWire lengthWidth shiftWidth) = 0) :
    let out := logicOut lengthWidth shiftWidth i
    bitValue out phase1Wire = phase1Value lengthWidth shiftWidth i ∧
    bitValue out phase2Wire = phase2Value lengthWidth shiftWidth i ∧
    bitValue out signWire = signValue lengthWidth shiftWidth i ∧
    bitValue out (zeroQWire lengthWidth shiftWidth) =
      bitValue i (zeroQWire lengthWidth shiftWidth) ∧
    bitValue out (zeroRPrimeWire lengthWidth shiftWidth) =
      bitValue i (zeroRPrimeWire lengthWidth shiftWidth) ∧
    bitValue out (zeroShiftWire lengthWidth shiftWidth) =
      bitValue i (zeroShiftWire lengthWidth shiftWidth) ∧
    bitValue out (conditionWire lengthWidth shiftWidth) = 0 ∧
    bitValue out (temporaryWire lengthWidth shiftWidth) = 0 := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let cond := conditionWire lengthWidth shiftWidth
  let tmp := temporaryWire lengthWidth shiftWidth
  let c := conditionValue lengthWidth shiftWidth i
  let mix := (bitValue i signWire + bitValue i phase1Wire) % 2
  let middle := middlePhase2Value lengthWidth shiftWidth i
  set i1 := negativeAndOut zq zrp cond i with hi1
  set i2 := xorPairOut signWire phase1Wire tmp i1 with hi2
  set i3 := ccxOut cond tmp phase2Wire i2 with hi3
  set i4 := xorPairOut phase1Wire signWire tmp i3 with hi4
  set i5 := ccxOut cond phase2Wire signWire i4 with hi5
  set i6 := negativeAndOut zq zrp cond i5 with hi6
  set i7 := twoTargetsOut zs phase1Wire phase2Wire i6 with hi7
  have hzq_ge : 3 ≤ zq := by
    simp [zq, zeroQWire, shiftOffset]
    omega
  have hzrp_ge : 3 ≤ zrp := by
    simp [zrp, zeroRPrimeWire, zeroQWire, shiftOffset]
    omega
  have hc_lt : c < 2 := by
    unfold c conditionValue
    split
    · exact bitValue_lt _ _
    · omega
  have h1cond : bitValue i1 cond = c := by
    rw [hi1, negativeAndOut_target, hcondition]
    simp only [c, conditionValue, zrp, zq]
    split
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (bitValue_lt _ _)]
    · rfl
  have h1tmp : bitValue i1 tmp = 0 := by
    rw [hi1, negativeAndOut_ne (by
      simp [tmp, cond, temporaryWire, conditionWire])]
    exact htemporary
  have h1p1 : bitValue i1 phase1Wire = bitValue i phase1Wire := by
    exact negativeAndOut_ne (by
      simp [cond, phase1Wire, conditionWire, zeroQWire, shiftOffset])
  have h1p2 : bitValue i1 phase2Wire = bitValue i phase2Wire := by
    exact negativeAndOut_ne (by
      simp [cond, phase2Wire, conditionWire, zeroQWire, shiftOffset])
  have h1sign : bitValue i1 signWire = bitValue i signWire := by
    exact negativeAndOut_ne (by
      simp [cond, signWire, conditionWire, zeroQWire, shiftOffset])
  have h1zq : bitValue i1 zq = bitValue i zq := by
    exact negativeAndOut_ne (by
      simp [zq, cond, zeroQWire, conditionWire])
  have h1zrp : bitValue i1 zrp = bitValue i zrp := by
    exact negativeAndOut_ne (by
      simp [zrp, cond, zeroRPrimeWire, conditionWire])
  have h1zs : bitValue i1 zs = bitValue i zs := by
    exact negativeAndOut_ne (by
      simp [zs, cond, zeroShiftWire, conditionWire])
  have h2tmp : bitValue i2 tmp = mix := by
    rw [hi2, xorPairOut_target, h1tmp, h1sign, h1p1]
    simp [mix]
  have h2cond : bitValue i2 cond = c := by
    rw [hi2, xorPairOut_ne (by
      simp [cond, tmp, conditionWire, temporaryWire]), h1cond]
  have h2p1 : bitValue i2 phase1Wire = bitValue i phase1Wire := by
    rw [hi2, xorPairOut_ne (by
      simp [phase1Wire, tmp, temporaryWire, zeroQWire, shiftOffset]), h1p1]
  have h2p2 : bitValue i2 phase2Wire = bitValue i phase2Wire := by
    rw [hi2, xorPairOut_ne (by
      simp [phase2Wire, tmp, temporaryWire, zeroQWire, shiftOffset]), h1p2]
  have h2sign : bitValue i2 signWire = bitValue i signWire := by
    rw [hi2, xorPairOut_ne (by
      simp [signWire, tmp, temporaryWire, zeroQWire, shiftOffset]), h1sign]
  have h2zq : bitValue i2 zq = bitValue i zq := by
    rw [hi2, xorPairOut_ne (by
      simp [zq, tmp, zeroQWire, temporaryWire]), h1zq]
  have h2zrp : bitValue i2 zrp = bitValue i zrp := by
    rw [hi2, xorPairOut_ne (by
      simp [zrp, tmp, zeroRPrimeWire, temporaryWire]), h1zrp]
  have h2zs : bitValue i2 zs = bitValue i zs := by
    rw [hi2, xorPairOut_ne (by
      simp [zs, tmp, zeroShiftWire, temporaryWire]), h1zs]
  have h3p2 : bitValue i3 phase2Wire = middle := by
    rw [hi3, ccxOut_target, h2p2, h2cond, h2tmp]
    rfl
  have h3tmp : bitValue i3 tmp = mix := by
    rw [hi3, ccxOut_ne (by
      simp [tmp, phase2Wire, temporaryWire]), h2tmp]
  have h3cond : bitValue i3 cond = c := by
    rw [hi3, ccxOut_ne (by
      simp [cond, phase2Wire, conditionWire]), h2cond]
  have h3p1 : bitValue i3 phase1Wire = bitValue i phase1Wire := by
    rw [hi3, ccxOut_ne (by simp [phase1Wire, phase2Wire]), h2p1]
  have h3sign : bitValue i3 signWire = bitValue i signWire := by
    rw [hi3, ccxOut_ne (by simp [signWire, phase2Wire]), h2sign]
  have h3zq : bitValue i3 zq = bitValue i zq := by
    rw [hi3, ccxOut_ne (by
      simp [phase2Wire]; omega), h2zq]
  have h3zrp : bitValue i3 zrp = bitValue i zrp := by
    rw [hi3, ccxOut_ne (by
      simp [zrp, phase2Wire, zeroRPrimeWire, zeroQWire, shiftOffset]), h2zrp]
  have h3zs : bitValue i3 zs = bitValue i zs := by
    rw [hi3, ccxOut_ne (by
      simp [zs, phase2Wire, zeroShiftWire, zeroQWire, shiftOffset]), h2zs]
  have h4tmp : bitValue i4 tmp = 0 := by
    rw [hi4, xorPairOut_target, h3tmp, h3p1, h3sign]
    have hp1 := bitValue_lt i phase1Wire
    have hs := bitValue_lt i signWire
    unfold mix
    omega
  have h4p2 : bitValue i4 phase2Wire = middle := by
    rw [hi4, xorPairOut_ne (by simp [phase2Wire, tmp, temporaryWire,
      zeroQWire, shiftOffset]), h3p2]
  have h4cond : bitValue i4 cond = c := by
    rw [hi4, xorPairOut_ne (by
      simp [cond, tmp, conditionWire, temporaryWire]), h3cond]
  have h4p1 : bitValue i4 phase1Wire = bitValue i phase1Wire := by
    rw [hi4, xorPairOut_ne (by simp [phase1Wire, tmp, temporaryWire,
      zeroQWire, shiftOffset]), h3p1]
  have h4sign : bitValue i4 signWire = bitValue i signWire := by
    rw [hi4, xorPairOut_ne (by simp [signWire, tmp, temporaryWire,
      zeroQWire, shiftOffset]), h3sign]
  have h4zq : bitValue i4 zq = bitValue i zq := by
    rw [hi4, xorPairOut_ne (by
      simp [zq, tmp, zeroQWire, temporaryWire]), h3zq]
  have h4zrp : bitValue i4 zrp = bitValue i zrp := by
    rw [hi4, xorPairOut_ne (by
      simp [zrp, tmp, zeroRPrimeWire, temporaryWire]), h3zrp]
  have h4zs : bitValue i4 zs = bitValue i zs := by
    rw [hi4, xorPairOut_ne (by
      simp [zs, tmp, zeroShiftWire, temporaryWire]), h3zs]
  have h5sign : bitValue i5 signWire = signValue lengthWidth shiftWidth i := by
    rw [hi5, ccxOut_target, h4sign, h4cond, h4p2]
    rfl
  have h5tmp : bitValue i5 tmp = 0 := by
    rw [hi5, ccxOut_ne (by simp [tmp, signWire, temporaryWire]), h4tmp]
  have h5p2 : bitValue i5 phase2Wire = middle := by
    rw [hi5, ccxOut_ne (by simp [phase2Wire, signWire]), h4p2]
  have h5cond : bitValue i5 cond = c := by
    rw [hi5, ccxOut_ne (by
      simp [cond, signWire, conditionWire, zeroQWire, shiftOffset]), h4cond]
  have h5p1 : bitValue i5 phase1Wire = bitValue i phase1Wire := by
    rw [hi5, ccxOut_ne (by simp [phase1Wire, signWire]), h4p1]
  have h5zq : bitValue i5 zq = bitValue i zq := by
    rw [hi5, ccxOut_ne (by
      simp [signWire]; omega), h4zq]
  have h5zrp : bitValue i5 zrp = bitValue i zrp := by
    rw [hi5, ccxOut_ne (by
      simp [signWire]; omega), h4zrp]
  have h5zs : bitValue i5 zs = bitValue i zs := by
    rw [hi5, ccxOut_ne (by
      simp [zs, signWire, zeroShiftWire, zeroQWire, shiftOffset]), h4zs]
  have h6cond : bitValue i6 cond = 0 := by
    rw [hi6, negativeAndOut_target, h5cond, h5zrp, h5zq]
    unfold c conditionValue zrp zq
    split
    · have hzq := bitValue_lt i (zeroQWire lengthWidth shiftWidth)
      omega
    · omega
  have h6sign : bitValue i6 signWire = signValue lengthWidth shiftWidth i := by
    rw [hi6, negativeAndOut_ne (by
      simp [signWire, cond, conditionWire, zeroQWire, shiftOffset]), h5sign]
  have h6tmp : bitValue i6 tmp = 0 := by
    rw [hi6, negativeAndOut_ne (by
      simp [tmp, cond, temporaryWire, conditionWire]), h5tmp]
  have h6p2 : bitValue i6 phase2Wire = middle := by
    rw [hi6, negativeAndOut_ne (by
      simp [phase2Wire, cond, conditionWire, zeroQWire, shiftOffset]), h5p2]
  have h6p1 : bitValue i6 phase1Wire = bitValue i phase1Wire := by
    rw [hi6, negativeAndOut_ne (by
      simp [phase1Wire, cond, conditionWire, zeroQWire, shiftOffset]), h5p1]
  have h6zq : bitValue i6 zq = bitValue i zq := by
    rw [hi6, negativeAndOut_ne (by
      simp [zq, cond, zeroQWire, conditionWire]), h5zq]
  have h6zrp : bitValue i6 zrp = bitValue i zrp := by
    rw [hi6, negativeAndOut_ne (by
      simp [zrp, cond, zeroRPrimeWire, conditionWire]), h5zrp]
  have h6zs : bitValue i6 zs = bitValue i zs := by
    rw [hi6, negativeAndOut_ne (by
      simp [zs, cond, zeroShiftWire, conditionWire]), h5zs]
  change bitValue i7 phase1Wire = _ ∧ bitValue i7 phase2Wire = _ ∧
    bitValue i7 signWire = _ ∧ bitValue i7 zq = _ ∧
    bitValue i7 zrp = _ ∧ bitValue i7 zs = _ ∧
    bitValue i7 cond = 0 ∧ bitValue i7 tmp = 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi7, twoTargetsOut_first (by simp [phase1Wire, phase2Wire]),
      h6p1, h6zs]
    rfl
  · rw [hi7, twoTargetsOut_second (by simp [phase1Wire, phase2Wire])
      (by simp [zs, phase1Wire, zeroShiftWire, zeroQWire, shiftOffset]),
      h6p2, h6zs]
    rfl
  · rw [hi7, twoTargetsOut_ne (by simp [signWire, phase1Wire])
      (by simp [signWire, phase2Wire]), h6sign]
  · rw [hi7, twoTargetsOut_ne (by
      simp [zq, phase1Wire, zeroQWire, shiftOffset]) (by
      simp [phase2Wire]; omega), h6zq]
  · rw [hi7, twoTargetsOut_ne (by
      simp [zrp, phase1Wire, zeroRPrimeWire, zeroQWire, shiftOffset]) (by
      simp [zrp, phase2Wire, zeroRPrimeWire, zeroQWire, shiftOffset]), h6zrp]
  · rw [hi7, twoTargetsOut_ne (by
      simp [zs, phase1Wire, zeroShiftWire, zeroQWire, shiftOffset]) (by
      simp [zs, phase2Wire, zeroShiftWire, zeroQWire, shiftOffset]), h6zs]
  · rw [hi7, twoTargetsOut_ne (by
      simp [cond, phase1Wire, conditionWire, zeroQWire, shiftOffset]) (by
      simp [cond, phase2Wire, conditionWire, zeroQWire, shiftOffset]), h6cond]
  · rw [hi7, twoTargetsOut_ne (by
      simp [tmp, phase1Wire, temporaryWire, zeroQWire, shiftOffset]) (by
      simp [tmp, phase2Wire, temporaryWire, zeroQWire, shiftOffset]), h6tmp]

theorem logic_act (lengthWidth shiftWidth i : Nat) :
    actGates (logicGates lengthWidth shiftWidth) i =
      logicOut lengthWidth shiftWidth i := by
  simp only [logicGates, actGates_append]
  rw [negativeAnd_act (by simp [zeroQWire, zeroRPrimeWire])
      (by simp [zeroRPrimeWire, conditionWire]),
    xorPair_act (by
      simp [signWire, temporaryWire, zeroQWire, shiftOffset]),
    ccxGates_act,
    xorPair_act (by
      simp [phase1Wire, temporaryWire, zeroQWire, shiftOffset]),
    ccxGates_act,
    negativeAnd_act (by simp [zeroQWire, zeroRPrimeWire])
      (by simp [zeroRPrimeWire, conditionWire]),
    twoTargets_act]
  rfl

def gates (lengthWidth shiftWidth : Nat) : List RGate :=
  qSelector lengthWidth shiftWidth ++
    rPrimeSelector lengthWidth shiftWidth ++
    shiftSelector lengthWidth shiftWidth ++
    logicGates lengthWidth shiftWidth ++
    shiftSelector lengthWidth shiftWidth ++
    rPrimeSelector lengthWidth shiftWidth ++
    qSelector lengthWidth shiftWidth

def circuit (lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout lengthWidth shiftWidth).width,
    gates := gates lengthWidth shiftWidth }

theorem qSelector_disjoint (lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Selector.layout lengthWidth)
      (Placed.selectorWiring lenQOffset (zeroQWire lengthWidth shiftWidth)
        (poolOffset lengthWidth shiftWidth)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size, lenQOffset,
      zeroQWire, shiftOffset, poolOffset] <;> omega

theorem rPrimeSelector_disjoint (lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Selector.layout lengthWidth)
      (Placed.selectorWiring (lenRPrimeOffset lengthWidth)
        (zeroRPrimeWire lengthWidth shiftWidth)
        (poolOffset lengthWidth shiftWidth)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size,
      lenRPrimeOffset, zeroRPrimeWire, zeroQWire, shiftOffset, poolOffset] <;>
    omega

theorem shiftSelector_disjoint (lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Selector.layout shiftWidth)
      (Placed.selectorWiring (shiftOffset lengthWidth)
        (zeroShiftWire lengthWidth shiftWidth)
        (poolOffset lengthWidth shiftWidth)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size,
      zeroShiftWire, zeroQWire, shiftOffset, poolOffset]

theorem qSelector_bound (lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Selector.layout lengthWidth).length →
      (Placed.selectorWiring lenQOffset (zeroQWire lengthWidth shiftWidth)
          (poolOffset lengthWidth shiftWidth)).getD j 0 +
          (Selector.layout lengthWidth).size j ≤
        (layout lengthWidth shiftWidth).width := by
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size, layout,
      Layout.width, lenQOffset, zeroQWire, shiftOffset, poolOffset, poolWidth] <;>
    omega

theorem rPrimeSelector_bound (lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Selector.layout lengthWidth).length →
      (Placed.selectorWiring (lenRPrimeOffset lengthWidth)
          (zeroRPrimeWire lengthWidth shiftWidth)
          (poolOffset lengthWidth shiftWidth)).getD j 0 +
          (Selector.layout lengthWidth).size j ≤
        (layout lengthWidth shiftWidth).width := by
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size, layout,
      Layout.width, lenRPrimeOffset, zeroRPrimeWire, zeroQWire, shiftOffset,
      poolOffset, poolWidth] <;> omega

theorem shiftSelector_bound (lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Selector.layout shiftWidth).length →
      (Placed.selectorWiring (shiftOffset lengthWidth)
          (zeroShiftWire lengthWidth shiftWidth)
          (poolOffset lengthWidth shiftWidth)).getD j 0 +
          (Selector.layout shiftWidth).size j ≤
        (layout lengthWidth shiftWidth).width := by
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Placed.selectorWiring, Selector.layout, Layout.size, layout,
      Layout.width, zeroShiftWire, zeroQWire, shiftOffset, poolOffset,
      poolWidth] <;> omega

theorem ownershipSelect_act {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    actGates (ownershipSelectGates lengthWidth shiftWidth) i =
      ownershipSelected lengthWidth shiftWidth i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let pool := poolOffset lengthWidth shiftWidth
  set i1 := writeField i zq 1
    (selectorValue lengthWidth lenQOffset i) with hi1
  set i2 := writeField i1 zs 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i1) with hi2
  have hpoolLength : readField i pool lengthWidth = 0 :=
    readField_narrow (Nat.le_max_left _ _) hpool
  have hpoolShift : readField i pool shiftWidth = 0 :=
    readField_narrow (Nat.le_max_right _ _) hpool
  have hq : actGates (qSelector lengthWidth shiftWidth) i = i1 := by
    rw [qSelector, Placed.selector_act (qSelector_disjoint _ _) hpoolLength]
    simp only [hi1, zq, selectorValue]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth), hzeroQ, Nat.zero_add]
    split <;> rfl
  have hpool1 : readField i1 pool shiftWidth = 0 := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, pool, zeroQWire, poolOffset])]
    exact hpoolShift
  have hsourceShift :
      readField i1 (shiftOffset lengthWidth) shiftWidth =
        readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, zeroQWire, shiftOffset])]
  have hflagShift : bitValue i1 zs = 0 := by
    rw [hi1, bitValue_write_ne (by
      simp [zs, zq, zeroShiftWire, zeroQWire]), hzeroShift]
  have hs : actGates (shiftSelector lengthWidth shiftWidth) i1 = i2 := by
    rw [shiftSelector,
      Placed.selector_act (shiftSelector_disjoint _ _) hpool1]
    simp only [hi2, zs, selectorValue, hsourceShift]
    rw [Nat.mod_eq_of_lt (encodedZero_lt shiftWidth), hflagShift,
      Nat.zero_add]
    split <;> rfl
  rw [ownershipSelectGates, actGates_append, hq, hs]
  simp only [ownershipSelected, hi1, hi2, zq, zs]

theorem ownershipUnselect_act {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) =
      selectorValue lengthWidth lenQOffset i)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) =
      selectorValue shiftWidth (shiftOffset lengthWidth) i)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    actGates (ownershipUnselectGates lengthWidth shiftWidth) i =
      ownershipCleaned lengthWidth shiftWidth i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let pool := poolOffset lengthWidth shiftWidth
  set i1 := writeField i zs 1 0 with hi1
  set i2 := writeField i1 zq 1 0 with hi2
  have hpoolLength : readField i pool lengthWidth = 0 :=
    readField_narrow (Nat.le_max_left _ _) hpool
  have hpoolShift : readField i pool shiftWidth = 0 :=
    readField_narrow (Nat.le_max_right _ _) hpool
  have hs : actGates (shiftSelector lengthWidth shiftWidth) i = i1 := by
    rw [shiftSelector,
      Placed.selector_act (shiftSelector_disjoint _ _) hpoolShift]
    simp only [hi1, zs]
    rw [Nat.mod_eq_of_lt (encodedZero_lt shiftWidth),
      show (if readField i (shiftOffset lengthWidth) shiftWidth =
        encodedZero shiftWidth then 1 else 0) =
        selectorValue shiftWidth (shiftOffset lengthWidth) i from rfl,
      hzeroShift]
    have hvalue := selectorValue_lt shiftWidth (shiftOffset lengthWidth) i
    apply write_congr
    omega
  have hpool1 : readField i1 pool lengthWidth = 0 := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zs, pool, zeroShiftWire, poolOffset])]
    exact hpoolLength
  have hsourceQ : readField i1 lenQOffset lengthWidth =
      readField i lenQOffset lengthWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zs, lenQOffset, zeroShiftWire, zeroQWire, shiftOffset]
      omega)]
  have hflagQ : bitValue i1 zq = selectorValue lengthWidth lenQOffset i1 := by
    rw [hi1, bitValue_write_ne (by
      simp [zq, zs, zeroQWire, zeroShiftWire]), hzeroQ]
    unfold selectorValue
    rw [hsourceQ]
  have hq : actGates (qSelector lengthWidth shiftWidth) i1 = i2 := by
    rw [qSelector, Placed.selector_act (qSelector_disjoint _ _) hpool1]
    simp only [hi2, zq]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth),
      show (if readField i1 lenQOffset lengthWidth = encodedZero lengthWidth
        then 1 else 0) = selectorValue lengthWidth lenQOffset i1 from rfl,
      hflagQ]
    have hvalue := selectorValue_lt lengthWidth lenQOffset i1
    apply write_congr
    omega
  rw [ownershipUnselectGates, actGates_append, hs, hq]
  simp only [ownershipCleaned, hi1, hi2, zq, zs]

theorem select_act {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue i (zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    actGates (selectGates lengthWidth shiftWidth) i =
      selected lengthWidth shiftWidth i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let pool := poolOffset lengthWidth shiftWidth
  set i1 := writeField i zq 1
    (selectorValue lengthWidth lenQOffset i) with hi1
  set i2 := writeField i1 zrp 1
    (selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i1) with hi2
  set i3 := writeField i2 zs 1
    (selectorValue shiftWidth (shiftOffset lengthWidth) i2) with hi3
  have hpoolLength : readField i pool lengthWidth = 0 := by
    exact readField_narrow (Nat.le_max_left _ _) hpool
  have hpoolShift : readField i pool shiftWidth = 0 := by
    exact readField_narrow (Nat.le_max_right _ _) hpool
  have hq : actGates (qSelector lengthWidth shiftWidth) i = i1 := by
    rw [qSelector, Placed.selector_act (qSelector_disjoint _ _) hpoolLength]
    simp only [hi1, zq, selectorValue]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth), hzeroQ,
      Nat.zero_add]
    split <;> rfl
  have hpool1 : readField i1 pool lengthWidth = 0 := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, pool, zeroQWire, poolOffset])]
    exact hpoolLength
  have hsourceRPrime :
      readField i1 (lenRPrimeOffset lengthWidth) lengthWidth =
        readField i (lenRPrimeOffset lengthWidth) lengthWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zq, zeroQWire, lenRPrimeOffset, shiftOffset]
      omega)]
  have hflagRPrime : bitValue i1 zrp = 0 := by
    rw [hi1, bitValue_write_ne (by
      simp [zrp, zq, zeroRPrimeWire, zeroQWire]), hzeroRPrime]
  have hr : actGates (rPrimeSelector lengthWidth shiftWidth) i1 = i2 := by
    rw [rPrimeSelector,
      Placed.selector_act (rPrimeSelector_disjoint _ _) hpool1]
    simp only [hi2, zrp, selectorValue, hsourceRPrime]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth), hflagRPrime,
      Nat.zero_add]
    split <;> rfl
  have hpool2 : readField i2 pool shiftWidth = 0 := by
    rw [hi2, readField_writeField_of_disjoint (by
      simp [zrp, pool, zeroRPrimeWire, poolOffset]), hi1,
      readField_writeField_of_disjoint (by
        simp [zq, pool, zeroQWire, poolOffset])]
    exact hpoolShift
  have hsourceShift :
      readField i2 (shiftOffset lengthWidth) shiftWidth =
        readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hi2, readField_writeField_of_disjoint (by
      simp [zrp, zeroRPrimeWire, zeroQWire, shiftOffset]), hi1,
      readField_writeField_of_disjoint (by
        simp [zq, zeroQWire, shiftOffset])]
  have hflagShift : bitValue i2 zs = 0 := by
    rw [hi2, bitValue_write_ne (by
      simp [zs, zrp, zeroShiftWire, zeroRPrimeWire]), hi1,
      bitValue_write_ne (by simp [zs, zq, zeroShiftWire, zeroQWire]),
      hzeroShift]
  have hs : actGates (shiftSelector lengthWidth shiftWidth) i2 = i3 := by
    rw [shiftSelector,
      Placed.selector_act (shiftSelector_disjoint _ _) hpool2]
    simp only [hi3, zs, selectorValue, hsourceShift]
    rw [Nat.mod_eq_of_lt (encodedZero_lt shiftWidth), hflagShift,
      Nat.zero_add]
    split <;> rfl
  rw [selectGates, actGates_append, actGates_append, hq, hr, hs]
  simp only [selected, hi1, hi2, hi3, zq, zrp, zs]

theorem unselect_act {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) =
      selectorValue lengthWidth lenQOffset i)
    (hzeroRPrime : bitValue i (zeroRPrimeWire lengthWidth shiftWidth) =
      selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) =
      selectorValue shiftWidth (shiftOffset lengthWidth) i)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    actGates (unselectGates lengthWidth shiftWidth) i =
      cleaned lengthWidth shiftWidth i := by
  let zq := zeroQWire lengthWidth shiftWidth
  let zrp := zeroRPrimeWire lengthWidth shiftWidth
  let zs := zeroShiftWire lengthWidth shiftWidth
  let pool := poolOffset lengthWidth shiftWidth
  set i1 := writeField i zs 1 0 with hi1
  set i2 := writeField i1 zrp 1 0 with hi2
  set i3 := writeField i2 zq 1 0 with hi3
  have hpoolLength : readField i pool lengthWidth = 0 := by
    exact readField_narrow (Nat.le_max_left _ _) hpool
  have hpoolShift : readField i pool shiftWidth = 0 := by
    exact readField_narrow (Nat.le_max_right _ _) hpool
  have hs : actGates (shiftSelector lengthWidth shiftWidth) i = i1 := by
    rw [shiftSelector,
      Placed.selector_act (shiftSelector_disjoint _ _) hpoolShift]
    simp only [hi1, zs]
    rw [Nat.mod_eq_of_lt (encodedZero_lt shiftWidth),
      show (if readField i (shiftOffset lengthWidth) shiftWidth =
        encodedZero shiftWidth then 1 else 0) =
        selectorValue shiftWidth (shiftOffset lengthWidth) i from rfl,
      hzeroShift]
    have hvalue := selectorValue_lt shiftWidth (shiftOffset lengthWidth) i
    apply write_congr
    omega
  have hpool1 : readField i1 pool lengthWidth = 0 := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zs, pool, zeroShiftWire, poolOffset])]
    exact hpoolLength
  have hsourceRPrime :
      readField i1 (lenRPrimeOffset lengthWidth) lengthWidth =
        readField i (lenRPrimeOffset lengthWidth) lengthWidth := by
    rw [hi1, readField_writeField_of_disjoint (by
      simp [zs, zeroShiftWire, zeroQWire, lenRPrimeOffset, shiftOffset]
      omega)]
  have hflagRPrime : bitValue i1 zrp =
      selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i1 := by
    rw [hi1, bitValue_write_ne (by
      simp [zrp, zs, zeroRPrimeWire, zeroShiftWire]), hzeroRPrime]
    unfold selectorValue
    rw [hsourceRPrime]
  have hr : actGates (rPrimeSelector lengthWidth shiftWidth) i1 = i2 := by
    rw [rPrimeSelector,
      Placed.selector_act (rPrimeSelector_disjoint _ _) hpool1]
    simp only [hi2, zrp]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth),
      show (if readField i1 (lenRPrimeOffset lengthWidth) lengthWidth =
        encodedZero lengthWidth then 1 else 0) =
        selectorValue lengthWidth (lenRPrimeOffset lengthWidth) i1 from rfl,
      hflagRPrime]
    have hvalue := selectorValue_lt lengthWidth
      (lenRPrimeOffset lengthWidth) i1
    apply write_congr
    omega
  have hpool2 : readField i2 pool lengthWidth = 0 := by
    rw [hi2, readField_writeField_of_disjoint (by
      simp [zrp, pool, zeroRPrimeWire, poolOffset]), hi1,
      readField_writeField_of_disjoint (by
        simp [zs, pool, zeroShiftWire, poolOffset])]
    exact hpoolLength
  have hsourceQ : readField i2 lenQOffset lengthWidth =
      readField i lenQOffset lengthWidth := by
    rw [hi2, readField_writeField_of_disjoint (by
      simp [zrp, lenQOffset, zeroRPrimeWire, zeroQWire, shiftOffset]
      omega), hi1,
      readField_writeField_of_disjoint (by
        simp [zs, lenQOffset, zeroShiftWire, zeroQWire, shiftOffset]
        omega)]
  have hflagQ : bitValue i2 zq =
      selectorValue lengthWidth lenQOffset i2 := by
    rw [hi2, bitValue_write_ne (by
      simp [zq, zrp, zeroQWire, zeroRPrimeWire]), hi1,
      bitValue_write_ne (by simp [zq, zs, zeroQWire, zeroShiftWire]), hzeroQ]
    unfold selectorValue
    rw [hsourceQ]
  have hq : actGates (qSelector lengthWidth shiftWidth) i2 = i3 := by
    rw [qSelector, Placed.selector_act (qSelector_disjoint _ _) hpool2]
    simp only [hi3, zq]
    rw [Nat.mod_eq_of_lt (encodedZero_lt lengthWidth),
      show (if readField i2 lenQOffset lengthWidth = encodedZero lengthWidth
        then 1 else 0) = selectorValue lengthWidth lenQOffset i2 from rfl,
      hflagQ]
    have hvalue := selectorValue_lt lengthWidth lenQOffset i2
    apply write_congr
    omega
  rw [unselectGates, actGates_append, actGates_append, hs, hr, hq]
  simp only [cleaned, hi1, hi2, hi3, zq, zrp, zs]

theorem act_circuit {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue i (zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) = 0)
    (hcondition : bitValue i (conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue i (temporaryWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    act (circuit lengthWidth shiftWidth) i = out lengthWidth shiftWidth i := by
  set s := selected lengthWidth shiftWidth i with hs
  set j := logicOut lengthWidth shiftWidth s with hj
  have hselect : actGates (selectGates lengthWidth shiftWidth) i = s := by
    rw [hs]
    exact select_act hzeroQ hzeroRPrime hzeroShift hpool
  have hscondition : bitValue s (conditionWire lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_bit (by
      simp [conditionWire, zeroQWire]) (by
      simp [conditionWire, zeroRPrimeWire, zeroQWire]) (by
      simp [conditionWire, zeroShiftWire, zeroQWire]), hcondition]
  have hstemporary : bitValue s (temporaryWire lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_bit (by
      simp [temporaryWire, zeroQWire]) (by
      simp [temporaryWire, zeroRPrimeWire, zeroQWire]) (by
      simp [temporaryWire, zeroShiftWire, zeroQWire]), htemporary]
  have hbits := logic_bits hscondition hstemporary
  simp only at hbits
  rw [← hj] at hbits
  rcases hbits with ⟨_, _, _, hjzq, hjzrp, hjzs, _, _⟩
  have hflags := selected_flags lengthWidth shiftWidth i
  simp only at hflags
  rw [← hs] at hflags
  rcases hflags with ⟨hszq, hszrp, hszs⟩
  have hsQ : readField s lenQOffset lengthWidth =
      readField i lenQOffset lengthWidth := by
    rw [hs]
    exact selected_preserves_field (by
      simp [lenQOffset, zeroQWire, shiftOffset]; omega) (by
      simp [lenQOffset, zeroRPrimeWire, zeroQWire, shiftOffset]; omega) (by
      simp [lenQOffset, zeroShiftWire, zeroQWire, shiftOffset]; omega)
  have hsRPrime : readField s (lenRPrimeOffset lengthWidth) lengthWidth =
      readField i (lenRPrimeOffset lengthWidth) lengthWidth := by
    rw [hs]
    exact selected_preserves_field (by
      simp [lenRPrimeOffset, zeroQWire, shiftOffset]; omega) (by
      simp [lenRPrimeOffset, zeroRPrimeWire, zeroQWire, shiftOffset]; omega) (by
      simp [lenRPrimeOffset, zeroShiftWire, zeroQWire, shiftOffset]; omega)
  have hsShift : readField s (shiftOffset lengthWidth) shiftWidth =
      readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hs]
    exact selected_preserves_field (by
      simp [zeroQWire, shiftOffset]) (by
      simp [zeroRPrimeWire, zeroQWire, shiftOffset]) (by
      simp [zeroShiftWire, zeroQWire, shiftOffset])
  have hsPool : readField s (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_field (by
      simp [zeroQWire, poolOffset]) (by
      simp [zeroRPrimeWire, poolOffset]) (by
      simp [zeroShiftWire, poolOffset]), hpool]
  have hjQ : readField j lenQOffset lengthWidth =
      readField i lenQOffset lengthWidth := by
    rw [hj, logicOut_preserves_field (by
      simp [phase1Wire, lenQOffset]) (by
      simp [phase2Wire, lenQOffset]) (by
      simp [signWire, lenQOffset]) (by
      simp [conditionWire, lenQOffset, zeroQWire, shiftOffset]; omega) (by
      simp [temporaryWire, lenQOffset, zeroQWire, shiftOffset]; omega), hsQ]
  have hjRPrime : readField j (lenRPrimeOffset lengthWidth) lengthWidth =
      readField i (lenRPrimeOffset lengthWidth) lengthWidth := by
    rw [hj, logicOut_preserves_field (by
      simp [phase1Wire, lenRPrimeOffset]; omega) (by
      simp [phase2Wire, lenRPrimeOffset]; omega) (by
      simp [signWire, lenRPrimeOffset]) (by
      simp [conditionWire, lenRPrimeOffset, zeroQWire, shiftOffset]; omega) (by
      simp [temporaryWire, lenRPrimeOffset, zeroQWire, shiftOffset]; omega),
      hsRPrime]
  have hjShift : readField j (shiftOffset lengthWidth) shiftWidth =
      readField i (shiftOffset lengthWidth) shiftWidth := by
    rw [hj, logicOut_preserves_field (by
      simp [phase1Wire, shiftOffset]; omega) (by
      simp [phase2Wire, shiftOffset]; omega) (by
      simp [signWire, shiftOffset]) (by
      simp [conditionWire, zeroQWire, shiftOffset]) (by
      simp [temporaryWire, zeroQWire, shiftOffset]), hsShift]
  have hjPool : readField j (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
    rw [hj, logicOut_preserves_field (by
      simp [phase1Wire, poolOffset, zeroQWire]) (by
      simp [phase2Wire, poolOffset, zeroQWire]) (by
      simp [signWire, poolOffset, zeroQWire]) (by
      simp [conditionWire, poolOffset, zeroQWire]) (by
      simp [temporaryWire, poolOffset, zeroQWire]), hsPool]
  have hjflagQ : bitValue j (zeroQWire lengthWidth shiftWidth) =
      selectorValue lengthWidth lenQOffset j := by
    rw [hjzq, hszq]
    unfold selectorValue
    rw [hjQ]
  have hjflagRPrime : bitValue j (zeroRPrimeWire lengthWidth shiftWidth) =
      selectorValue lengthWidth (lenRPrimeOffset lengthWidth) j := by
    rw [hjzrp, hszrp]
    unfold selectorValue
    rw [hjRPrime]
  have hjflagShift : bitValue j (zeroShiftWire lengthWidth shiftWidth) =
      selectorValue shiftWidth (shiftOffset lengthWidth) j := by
    rw [hjzs, hszs]
    unfold selectorValue
    rw [hjShift]
  have hunselect : actGates (unselectGates lengthWidth shiftWidth) j =
      cleaned lengthWidth shiftWidth j :=
    unselect_act hjflagQ hjflagRPrime hjflagShift hjPool
  have hgates : gates lengthWidth shiftWidth =
      selectGates lengthWidth shiftWidth ++ logicGates lengthWidth shiftWidth ++
        unselectGates lengthWidth shiftWidth := by
    simp [gates, selectGates, unselectGates, List.append_assoc]
  change actGates (gates lengthWidth shiftWidth) i = _
  rw [hgates, actGates_append, actGates_append, hselect, logic_act, ← hj,
    hunselect]
  simp only [out, hs, hj]

theorem out_bits {lengthWidth shiftWidth i : Nat}
    (hcondition : bitValue i (conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue i (temporaryWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    let s := selected lengthWidth shiftWidth i
    let result := out lengthWidth shiftWidth i
    bitValue result phase1Wire = phase1Value lengthWidth shiftWidth s ∧
    bitValue result phase2Wire = phase2Value lengthWidth shiftWidth s ∧
    bitValue result signWire = signValue lengthWidth shiftWidth s ∧
    bitValue result (zeroQWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (zeroRPrimeWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (zeroShiftWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (conditionWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (temporaryWire lengthWidth shiftWidth) = 0 ∧
    readField result (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
  set s := selected lengthWidth shiftWidth i with hs
  set j := logicOut lengthWidth shiftWidth s with hj
  have hscondition : bitValue s (conditionWire lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_bit (by
      simp [conditionWire, zeroQWire]) (by
      simp [conditionWire, zeroRPrimeWire, zeroQWire]) (by
      simp [conditionWire, zeroShiftWire, zeroQWire]), hcondition]
  have hstemporary : bitValue s (temporaryWire lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_bit (by
      simp [temporaryWire, zeroQWire]) (by
      simp [temporaryWire, zeroRPrimeWire, zeroQWire]) (by
      simp [temporaryWire, zeroShiftWire, zeroQWire]), htemporary]
  have hbits := logic_bits hscondition hstemporary
  simp only at hbits
  rw [← hj] at hbits
  rcases hbits with ⟨hphase1, hphase2, hsign, _, _, _, hcond, htmp⟩
  have hsPool : readField s (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
    rw [hs, selected_preserves_field (by
      simp [zeroQWire, poolOffset]) (by
      simp [zeroRPrimeWire, poolOffset]) (by
      simp [zeroShiftWire, poolOffset]), hpool]
  have hjPool : readField j (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
    rw [hj, logicOut_preserves_field (by
      simp [phase1Wire, poolOffset, zeroQWire]) (by
      simp [phase2Wire, poolOffset, zeroQWire]) (by
      simp [signWire, poolOffset, zeroQWire]) (by
      simp [conditionWire, poolOffset, zeroQWire]) (by
      simp [temporaryWire, poolOffset, zeroQWire]), hsPool]
  change bitValue (cleaned lengthWidth shiftWidth j) phase1Wire = _ ∧
    bitValue (cleaned lengthWidth shiftWidth j) phase2Wire = _ ∧
    bitValue (cleaned lengthWidth shiftWidth j) signWire = _ ∧
    bitValue (cleaned lengthWidth shiftWidth j)
      (zeroQWire lengthWidth shiftWidth) = 0 ∧
    bitValue (cleaned lengthWidth shiftWidth j)
      (zeroRPrimeWire lengthWidth shiftWidth) = 0 ∧
    bitValue (cleaned lengthWidth shiftWidth j)
      (zeroShiftWire lengthWidth shiftWidth) = 0 ∧
    bitValue (cleaned lengthWidth shiftWidth j)
      (conditionWire lengthWidth shiftWidth) = 0 ∧
    bitValue (cleaned lengthWidth shiftWidth j)
      (temporaryWire lengthWidth shiftWidth) = 0 ∧
    readField (cleaned lengthWidth shiftWidth j)
      (poolOffset lengthWidth shiftWidth) (poolWidth lengthWidth shiftWidth) = 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cleaned]
    rw [bitValue_write_ne (by
      simp [phase1Wire, zeroQWire, shiftOffset]
      omega),
      bitValue_write_ne (by
        simp [phase1Wire, zeroRPrimeWire, zeroQWire, shiftOffset]),
      bitValue_write_ne (by
        simp [phase1Wire, zeroShiftWire, zeroQWire, shiftOffset]), hphase1]
  · simp only [cleaned]
    rw [bitValue_write_ne (by
      simp [phase2Wire, zeroQWire, shiftOffset]
      omega),
      bitValue_write_ne (by
        simp [phase2Wire, zeroRPrimeWire, zeroQWire, shiftOffset]),
      bitValue_write_ne (by
        simp [phase2Wire, zeroShiftWire, zeroQWire, shiftOffset]), hphase2]
  · simp only [cleaned]
    rw [bitValue_write_ne (by
      simp [signWire, zeroQWire, shiftOffset]
      omega),
      bitValue_write_ne (by
        simp [signWire, zeroRPrimeWire, zeroQWire, shiftOffset]
        omega),
      bitValue_write_ne (by
        simp [signWire, zeroShiftWire, zeroQWire, shiftOffset]), hsign]
  · simp [cleaned, bitValue_write_self, zeroQWire, zeroRPrimeWire,
      zeroShiftWire]
  · simp [cleaned, bitValue_write_self, bitValue_write_ne, zeroQWire,
      zeroRPrimeWire, zeroShiftWire]
  · simp [cleaned, bitValue_write_self, bitValue_write_ne, zeroQWire,
      zeroRPrimeWire, zeroShiftWire]
  · simp only [cleaned]
    rw [bitValue_write_ne (by simp [conditionWire, zeroQWire]),
      bitValue_write_ne (by
        simp [conditionWire, zeroRPrimeWire, zeroQWire]),
      bitValue_write_ne (by
        simp [conditionWire, zeroShiftWire, zeroQWire]), hcond]
  · simp only [cleaned]
    rw [bitValue_write_ne (by simp [temporaryWire, zeroQWire]),
      bitValue_write_ne (by
        simp [temporaryWire, zeroRPrimeWire, zeroQWire]),
      bitValue_write_ne (by
        simp [temporaryWire, zeroShiftWire, zeroQWire]), htmp]
  · simp only [cleaned]
    rw [readField_writeField_of_disjoint (by
      simp [zeroQWire, poolOffset]),
      readField_writeField_of_disjoint (by
        simp [zeroRPrimeWire, poolOffset]),
      readField_writeField_of_disjoint (by
        simp [zeroShiftWire, poolOffset]), hjPool]

theorem out_testBit_of_ne
    {lengthWidth shiftWidth i q : Nat}
    (hp1 : q ≠ phase1Wire) (hp2 : q ≠ phase2Wire)
    (hsign : q ≠ signWire)
    (hzq : q ≠ zeroQWire lengthWidth shiftWidth)
    (hzrp : q ≠ zeroRPrimeWire lengthWidth shiftWidth)
    (hzs : q ≠ zeroShiftWire lengthWidth shiftWidth)
    (hcondition : q ≠ conditionWire lengthWidth shiftWidth)
    (htemporary : q ≠ temporaryWire lengthWidth shiftWidth) :
    (out lengthWidth shiftWidth i).testBit q = i.testBit q := by
  simp only [out, cleaned, logicOut, selected, twoTargetsOut,
    negativeAndOut, ccxOut, xorPairOut]
  repeat rw [testBit_writeField_outside (by omega)]

theorem out_eq_writeFields
    {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue i (zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) = 0)
    (hcondition : bitValue i (conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue i (temporaryWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    let result := out lengthWidth shiftWidth i
    result =
      writeField
        (writeField
          (writeField i phase1Wire 1 (bitValue result phase1Wire))
          phase2Wire 1 (bitValue result phase2Wire))
        signWire 1 (bitValue result signWire) := by
  let result := out lengthWidth shiftWidth i
  have hbits := out_bits hcondition htemporary hpool
  simp only at hbits
  change let _ := selected lengthWidth shiftWidth i
    let result' := out lengthWidth shiftWidth i
    _ at hbits
  simp only at hbits
  rcases hbits with
    ⟨_, _, _, hzeroQOut, hzeroRPrimeOut, hzeroShiftOut,
      hconditionOut, htemporaryOut, _⟩
  have zeroBit {j q : Nat} (h : bitValue j q = 0) :
      j.testBit q = false := by
    unfold bitValue at h
    split at h <;> simp_all
  have valueBit {j q : Nat} :
      (bitValue j q).testBit 0 = j.testBit q := by
    unfold bitValue
    split <;> simp_all
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hp1 : b = phase1Wire
  · subst b
    rw [testBit_writeField_outside (by
        simp [phase1Wire, signWire]),
      testBit_writeField_outside (by
        simp [phase1Wire, phase2Wire]),
      testBit_writeField_inside (Nat.le_refl _) (by omega)]
    exact valueBit.symm
  · by_cases hp2 : b = phase2Wire
    · subst b
      rw [testBit_writeField_outside (by
          simp [phase2Wire, signWire]),
        testBit_writeField_inside (Nat.le_refl _) (by omega)]
      exact valueBit.symm
    · by_cases hsign : b = signWire
      · subst b
        rw [testBit_writeField_inside (Nat.le_refl _) (by omega)]
        exact valueBit.symm
      · by_cases hzq : b = zeroQWire lengthWidth shiftWidth
        · subst b
          rw [testBit_writeField_outside (by
              simp [zeroQWire, shiftOffset, signWire]
              omega),
            testBit_writeField_outside (by
              simp [zeroQWire, shiftOffset, phase2Wire]
              omega),
            testBit_writeField_outside (by
              simp [zeroQWire, shiftOffset, phase1Wire]
              omega),
            zeroBit hzeroQOut, zeroBit hzeroQ]
        · by_cases hzrp : b = zeroRPrimeWire lengthWidth shiftWidth
          · subst b
            rw [testBit_writeField_outside (by
                simp [zeroRPrimeWire, zeroQWire, shiftOffset, signWire]
                omega),
              testBit_writeField_outside (by
                simp [zeroRPrimeWire, zeroQWire, shiftOffset, phase2Wire]
                omega),
              testBit_writeField_outside (by
                simp [zeroRPrimeWire, zeroQWire, shiftOffset, phase1Wire]),
              zeroBit hzeroRPrimeOut, zeroBit hzeroRPrime]
          · by_cases hzs : b = zeroShiftWire lengthWidth shiftWidth
            · subst b
              rw [testBit_writeField_outside (by
                  simp [zeroShiftWire, zeroQWire, shiftOffset, signWire]
                  omega),
                testBit_writeField_outside (by
                  simp [zeroShiftWire, zeroQWire, shiftOffset, phase2Wire]),
                testBit_writeField_outside (by
                  simp [zeroShiftWire, zeroQWire, shiftOffset, phase1Wire]),
                zeroBit hzeroShiftOut, zeroBit hzeroShift]
            · by_cases hc : b = conditionWire lengthWidth shiftWidth
              · subst b
                rw [testBit_writeField_outside (by
                    simp [conditionWire, zeroQWire, shiftOffset, signWire]),
                  testBit_writeField_outside (by
                    simp [conditionWire, zeroQWire, shiftOffset, phase2Wire]),
                  testBit_writeField_outside (by
                    simp [conditionWire, zeroQWire, shiftOffset, phase1Wire]),
                  zeroBit hconditionOut, zeroBit hcondition]
              · by_cases ht : b = temporaryWire lengthWidth shiftWidth
                · subst b
                  rw [testBit_writeField_outside (by
                      simp [temporaryWire, zeroQWire, shiftOffset, signWire]),
                    testBit_writeField_outside (by
                      simp [temporaryWire, zeroQWire, shiftOffset, phase2Wire]),
                    testBit_writeField_outside (by
                      simp [temporaryWire, zeroQWire, shiftOffset, phase1Wire]),
                    zeroBit htemporaryOut, zeroBit htemporary]
                · rw [testBit_writeField_outside (by omega),
                    testBit_writeField_outside (by omega),
                    testBit_writeField_outside (by omega)]
                  exact out_testBit_of_ne hp1 hp2 hsign hzq hzrp hzs hc ht

theorem circuit_bits {lengthWidth shiftWidth i : Nat}
    (hzeroQ : bitValue i (zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue i (zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue i (zeroShiftWire lengthWidth shiftWidth) = 0)
    (hcondition : bitValue i (conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue i (temporaryWire lengthWidth shiftWidth) = 0)
    (hpool : readField i (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0) :
    let s := selected lengthWidth shiftWidth i
    let result := act (circuit lengthWidth shiftWidth) i
    bitValue result phase1Wire = phase1Value lengthWidth shiftWidth s ∧
    bitValue result phase2Wire = phase2Value lengthWidth shiftWidth s ∧
    bitValue result signWire = signValue lengthWidth shiftWidth s ∧
    bitValue result (zeroQWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (zeroRPrimeWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (zeroShiftWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (conditionWire lengthWidth shiftWidth) = 0 ∧
    bitValue result (temporaryWire lengthWidth shiftWidth) = 0 ∧
    readField result (poolOffset lengthWidth shiftWidth)
      (poolWidth lengthWidth shiftWidth) = 0 := by
  rw [act_circuit hzeroQ hzeroRPrime hzeroShift hcondition htemporary hpool]
  exact out_bits hcondition htemporary hpool

theorem logic_wellFormed (lengthWidth shiftWidth : Nat) :
    (logicGates lengthWidth shiftWidth).all
      (RGate.wellFormed (layout lengthWidth shiftWidth).width) = true := by
  simp [logicGates, negativeAndGates, xorPairGates, ccxGates,
    twoTargetsGates, RGate.wellFormed, layout, Layout.width, phase1Wire,
    phase2Wire, signWire, zeroQWire, zeroRPrimeWire, zeroShiftWire,
    conditionWire, temporaryWire, shiftOffset, poolWidth]
  omega

theorem circuit_wellFormed (lengthWidth shiftWidth : Nat) :
    (circuit lengthWidth shiftWidth).wellFormed = true := by
  have hq := Placed.selector_wellFormed
    (value := encodedZero lengthWidth) (width := lengthWidth)
    (source := lenQOffset) (flag := zeroQWire lengthWidth shiftWidth)
    (scratch := poolOffset lengthWidth shiftWidth)
    (total := (layout lengthWidth shiftWidth).width)
    (qSelector_disjoint lengthWidth shiftWidth)
    (qSelector_bound lengthWidth shiftWidth)
  have hr := Placed.selector_wellFormed
    (value := encodedZero lengthWidth) (width := lengthWidth)
    (source := lenRPrimeOffset lengthWidth)
    (flag := zeroRPrimeWire lengthWidth shiftWidth)
    (scratch := poolOffset lengthWidth shiftWidth)
    (total := (layout lengthWidth shiftWidth).width)
    (rPrimeSelector_disjoint lengthWidth shiftWidth)
    (rPrimeSelector_bound lengthWidth shiftWidth)
  have hs := Placed.selector_wellFormed
    (value := encodedZero shiftWidth) (width := shiftWidth)
    (source := shiftOffset lengthWidth)
    (flag := zeroShiftWire lengthWidth shiftWidth)
    (scratch := poolOffset lengthWidth shiftWidth)
    (total := (layout lengthWidth shiftWidth).width)
    (shiftSelector_disjoint lengthWidth shiftWidth)
    (shiftSelector_bound lengthWidth shiftWidth)
  simp only [circuit, RCircuit.wellFormed, gates, List.all_append,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hq, hr⟩, hs⟩, logic_wellFormed lengthWidth shiftWidth⟩, hs⟩,
    hr⟩, hq⟩

theorem logic_length (lengthWidth shiftWidth : Nat) :
    (logicGates lengthWidth shiftWidth).length = 14 := by
  simp [logicGates, negativeAndGates, xorPairGates, ccxGates,
    twoTargetsGates]

theorem logic_ccx (lengthWidth shiftWidth : Nat) :
    (logicGates lengthWidth shiftWidth).countP RGate.isCcx = 4 := by
  simp [logicGates, negativeAndGates, xorPairGates, ccxGates,
    twoTargetsGates, List.countP_cons, RGate.isCcx]

theorem logic_cx (lengthWidth shiftWidth : Nat) :
    (logicGates lengthWidth shiftWidth).countP RGate.isCx = 6 := by
  simp [logicGates, negativeAndGates, xorPairGates, ccxGates,
    twoTargetsGates, List.countP_cons, RGate.isCx]

theorem circuit_length (lengthWidth shiftWidth : Nat) :
    (circuit lengthWidth shiftWidth).gates.length =
      4 * (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.length +
      2 * (Selector.circuit (encodedZero shiftWidth) shiftWidth).gates.length + 14 := by
  simp only [circuit, gates, List.length_append, qSelector, rPrimeSelector,
    shiftSelector, Placed.selector_length, logic_length]
  omega

theorem circuit_ccx (lengthWidth shiftWidth : Nat) :
    (circuit lengthWidth shiftWidth).gates.countP RGate.isCcx =
      4 * (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.countP
          RGate.isCcx +
      2 * (Selector.circuit (encodedZero shiftWidth) shiftWidth).gates.countP
          RGate.isCcx + 4 := by
  simp only [circuit, gates, List.countP_append, qSelector, rPrimeSelector,
    shiftSelector, Placed.selector_ccx, logic_ccx]
  omega

theorem circuit_cx (lengthWidth shiftWidth : Nat) :
    (circuit lengthWidth shiftWidth).gates.countP RGate.isCx =
      4 * (Selector.circuit (encodedZero lengthWidth) lengthWidth).gates.countP
          RGate.isCx +
      2 * (Selector.circuit (encodedZero shiftWidth) shiftWidth).gates.countP
          RGate.isCx + 6 := by
  simp only [circuit, gates, List.countP_append, qSelector, rPrimeSelector,
    shiftSelector, Placed.selector_cx, logic_cx]
  omega

end Phase
end Euclid
end VQ
