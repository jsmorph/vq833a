/-
Controlled permutations over basis-index fields.

The Fredkin construction uses one Toffoli and two CNOTs.  Field exchange and
cyclic shifts reuse that construction, so their action and resource theorems
refer to the same generated gate lists.
-/
import VQ.Reversible.Bit
import VQ.Reversible.Compile
import VQ.Reversible.Reverse
import Mathlib.Algebra.Group.Fin.Basic

namespace VQ
namespace Reversible

def fredkin (control x y : Nat) : List RGate :=
  [.cx y x, .ccx control x y, .cx y x]

def swapWires (x y : Nat) : List RGate :=
  [.cx y x, .cx x y, .cx y x]

theorem swapWires_split (x y i : Nat) :
    actGates (swapWires x y) i =
      RGate.act (.cx y x) (RGate.act (.cx x y) (RGate.act (.cx y x) i)) := by
  rfl

theorem swapWires_act {x y i : Nat} (hxy : x ≠ y) :
    actGates (swapWires x y) i =
      writeField (writeField i x 1 (bitValue i y)) y 1 (bitValue i x) := by
  have hx := bitValue_lt i x
  have hy := bitValue_lt i y
  have e1 : RGate.act (.cx y x) i =
      writeField i x 1 ((bitValue i x + bitValue i y) % 2) :=
    act_cx_write y x i
  have h1x : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) x =
      (bitValue i x + bitValue i y) % 2 % 2 :=
    bitValue_write_self _ _ _
  have h1y : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) y = bitValue i y :=
    bitValue_write_ne (Ne.symm hxy)
  have e2 : RGate.act (.cx x y)
      (writeField i x 1 ((bitValue i x + bitValue i y) % 2)) =
      writeField
        (writeField i x 1 ((bitValue i x + bitValue i y) % 2)) y 1
        ((bitValue i y +
          (bitValue i x + bitValue i y) % 2 % 2) % 2) := by
    rw [act_cx_write, h1x, h1y]
  rw [swapWires_split, e1, e2]
  have hy2 : (bitValue i y +
      (bitValue i x + bitValue i y) % 2 % 2) % 2 = bitValue i x := by
    omega
  rw [hy2]
  have h2x : bitValue
      (writeField (writeField i x 1
        ((bitValue i x + bitValue i y) % 2)) y 1 (bitValue i x)) x =
      (bitValue i x + bitValue i y) % 2 % 2 := by
    rw [bitValue_write_ne hxy, h1x]
  have h2y : bitValue
      (writeField (writeField i x 1
        ((bitValue i x + bitValue i y) % 2)) y 1 (bitValue i x)) y =
      bitValue i x % 2 :=
    bitValue_write_self _ _ _
  have e3 : RGate.act (.cx y x)
      (writeField
        (writeField i x 1 ((bitValue i x + bitValue i y) % 2)) y 1
        (bitValue i x)) =
      writeField
        (writeField
          (writeField i x 1 ((bitValue i x + bitValue i y) % 2)) y 1
          (bitValue i x)) x 1
        (((bitValue i x + bitValue i y) % 2 % 2 +
          bitValue i x % 2) % 2) := by
    rw [act_cx_write, h2x, h2y]
  rw [e3]
  have hx2 : ((bitValue i x + bitValue i y) % 2 % 2 +
      bitValue i x % 2) % 2 = bitValue i y := by
    omega
  rw [hx2, writeField_comm (by omega), writeField_writeField]

theorem swapWires_wellFormed {x y width : Nat}
    (hx : x < width) (hy : y < width) (hxy : x ≠ y) :
    (swapWires x y).all (RGate.wellFormed width) = true := by
  simp [swapWires, RGate.wellFormed, hx, hy, hxy, Ne.symm hxy]

theorem fredkin_split (control x y i : Nat) :
    actGates (fredkin control x y) i =
      RGate.act (.cx y x) (RGate.act (.ccx control x y) (RGate.act (.cx y x) i)) := by
  rfl

theorem fredkin_off {control x y i : Nat} (hxy : x ≠ y) (hcx : control ≠ x)
    (hcontrol : bitValue i control = 0) :
    actGates (fredkin control x y) i = i := by
  have hx := bitValue_lt i x
  have hy := bitValue_lt i y
  have e1 : RGate.act (.cx y x) i =
      writeField i x 1 ((bitValue i x + bitValue i y) % 2) :=
    act_cx_write y x i
  have h1c : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) control = bitValue i control :=
    bitValue_write_ne hcx
  have h1x : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) x =
      (bitValue i x + bitValue i y) % 2 % 2 :=
    bitValue_write_self _ _ _
  have h1y : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) y = bitValue i y :=
    bitValue_write_ne (Ne.symm hxy)
  rw [fredkin_split, e1, act_ccx_write, h1c, h1x, h1y, hcontrol,
    Nat.zero_mul, write_of_bitValue (by omega), act_cx_write, h1x, h1y,
    writeField_writeField]
  exact write_of_bitValue (by omega)

theorem fredkin_on {control x y i : Nat} (hxy : x ≠ y) (hcx : control ≠ x)
    (hcy : control ≠ y) (hcontrol : bitValue i control = 1) :
    actGates (fredkin control x y) i =
      writeField (writeField i x 1 (bitValue i y)) y 1 (bitValue i x) := by
  have hx := bitValue_lt i x
  have hy := bitValue_lt i y
  have e1 : RGate.act (.cx y x) i =
      writeField i x 1 ((bitValue i x + bitValue i y) % 2) :=
    act_cx_write y x i
  have h1c : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) control = bitValue i control :=
    bitValue_write_ne hcx
  have h1x : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) x =
      (bitValue i x + bitValue i y) % 2 % 2 :=
    bitValue_write_self _ _ _
  have h1y : bitValue (writeField i x 1
      ((bitValue i x + bitValue i y) % 2)) y = bitValue i y :=
    bitValue_write_ne (Ne.symm hxy)
  rw [fredkin_split, e1, act_ccx_write, h1c, h1x, h1y, hcontrol, Nat.one_mul]
  have hy2 : (bitValue i y + (bitValue i x + bitValue i y) % 2 % 2) % 2 =
      bitValue i x := by omega
  rw [hy2]
  have h2x : bitValue
      (writeField (writeField i x 1 ((bitValue i x + bitValue i y) % 2))
        y 1 (bitValue i x)) x =
      (bitValue i x + bitValue i y) % 2 % 2 := by
    rw [bitValue_write_ne hxy, h1x]
  have h2y : bitValue
      (writeField (writeField i x 1 ((bitValue i x + bitValue i y) % 2))
        y 1 (bitValue i x)) y = bitValue i x % 2 :=
    bitValue_write_self _ _ _
  rw [act_cx_write, h2x, h2y]
  have hx2 : ((bitValue i x + bitValue i y) % 2 % 2 + bitValue i x % 2) % 2 =
      bitValue i y := by omega
  rw [hx2, writeField_comm (by omega), writeField_writeField]

theorem fredkin_wellFormed {control x y width : Nat}
    (hc : control < width) (hx : x < width) (hy : y < width)
    (hcx : control ≠ x) (hcy : control ≠ y) (hxy : x ≠ y) :
    (fredkin control x y).all (RGate.wellFormed width) = true := by
  simp [fredkin, RGate.wellFormed, hc, hx, hy, hcx, hcy, hxy,
    Ne.symm hxy]

def swapFieldsControlled (control : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | a, b, width + 1 =>
      fredkin control a b ++ swapFieldsControlled control (a + 1) (b + 1) width

theorem swapFieldsControlled_off {control : Nat} : ∀ (width a b i : Nat),
    (a + width ≤ b ∨ b + width ≤ a) →
    (control < a ∨ a + width ≤ control) →
    bitValue i control = 0 →
    actGates (swapFieldsControlled control a b width) i = i := by
  intro width
  induction width with
  | zero => intro a b i _ _ _; rfl
  | succ width ih =>
      intro a b i hab hca hc
      rw [swapFieldsControlled, actGates_append,
        fredkin_off (by omega) (by omega) hc]
      exact ih (a + 1) (b + 1) i (by omega) (by omega) hc

theorem swapFieldsControlled_on {control : Nat} : ∀ (width a b i : Nat),
    (a + width ≤ b ∨ b + width ≤ a) →
    (control < a ∨ a + width ≤ control) →
    (control < b ∨ b + width ≤ control) →
    bitValue i control = 1 →
    actGates (swapFieldsControlled control a b width) i =
      writeField (writeField i a width (readField i b width))
        b width (readField i a width) := by
  intro width
  induction width with
  | zero =>
      intro a b i _ _ _ _
      simp [swapFieldsControlled, writeField_zero]
      rfl
  | succ width ih =>
      intro a b i hab hca hcb hc
      have hba := bitValue_lt i a
      have hbb := bitValue_lt i b
      have e1 := fredkin_on (control := control) (x := a) (y := b) (i := i)
        (by omega) (by omega) (by omega) hc
      have hjc : bitValue
          (writeField (writeField i a 1 (bitValue i b)) b 1 (bitValue i a))
          control = 1 := by
        rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega), hc]
      have hja : readField
          (writeField (writeField i a 1 (bitValue i b)) b 1 (bitValue i a))
          (a + 1) width = readField i (a + 1) width := by
        rw [readField_writeField_of_disjoint (by omega),
          readField_writeField_of_disjoint (by omega)]
      have hjb : readField
          (writeField (writeField i a 1 (bitValue i b)) b 1 (bitValue i a))
          (b + 1) width = readField i (b + 1) width := by
        rw [readField_writeField_of_disjoint (by omega),
          readField_writeField_of_disjoint (by omega)]
      rw [swapFieldsControlled, actGates_append, e1,
        ih (a + 1) (b + 1) _ (by omega) (by omega) (by omega) hjc, hja, hjb]
      rw [writeField_succ i a width (readField i b (width + 1)),
        writeField_succ _ b width (readField i a (width + 1))]
      have hra : readField i a (width + 1) % 2 = bitValue i a := by
        have h := readField_succ i a width
        omega
      have hrb : readField i b (width + 1) % 2 = bitValue i b := by
        have h := readField_succ i b width
        omega
      have hda : readField i a (width + 1) / 2 = readField i (a + 1) width := by
        have h := readField_succ i a width
        omega
      have hdb : readField i b (width + 1) / 2 = readField i (b + 1) width := by
        have h := readField_succ i b width
        omega
      rw [hra, hrb, hda, hdb]
      exact congrArg
        (fun z => writeField z (b + 1) width (readField i (a + 1) width))
        (writeField_comm
          (i := writeField i a 1 (bitValue i b))
          (o₁ := b) (n₁ := 1) (v := bitValue i a)
          (o₂ := a + 1) (n₂ := width)
          (u := readField i (b + 1) width) (by omega))

theorem swapFieldsControlled_wellFormed {control a b width total : Nat}
    (hab : a + width ≤ b ∨ b + width ≤ a)
    (hca : control < a ∨ a + width ≤ control)
    (hcb : control < b ∨ b + width ≤ control)
    (hc : control < total) (ha : a + width ≤ total)
    (hb : b + width ≤ total) :
    (swapFieldsControlled control a b width).all
      (RGate.wellFormed total) = true := by
  induction width generalizing a b with
  | zero => rfl
  | succ width ih =>
      rw [swapFieldsControlled, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · exact fredkin_wellFormed hc (by omega) (by omega) (by omega) (by omega)
          (by omega)
      · exact ih (a := a + 1) (b := b + 1) (by omega) (by omega) (by omega)
          (by omega) (by omega)

theorem swapFieldsControlled_length (control a b width : Nat) :
    (swapFieldsControlled control a b width).length = 3 * width := by
  induction width generalizing a b with
  | zero => rfl
  | succ width ih =>
      simp [swapFieldsControlled, fredkin, ih]
      omega

theorem swapFieldsControlled_ccx (control a b width : Nat) :
    (swapFieldsControlled control a b width).countP RGate.isCcx = width := by
  induction width generalizing a b with
  | zero => rfl
  | succ width ih =>
      simp [swapFieldsControlled, fredkin, List.countP_cons, RGate.isCcx, ih]

theorem swapFieldsControlled_cx (control a b width : Nat) :
    (swapFieldsControlled control a b width).countP RGate.isCx = 2 * width := by
  induction width generalizing a b with
  | zero => rfl
  | succ width ih =>
      simp [swapFieldsControlled, fredkin, List.countP_cons, RGate.isCx, ih]
      omega

theorem writeField_absorb {i off narrow wide v u : Nat} (h : narrow ≤ wide) :
    writeField (writeField i off narrow v) off wide u =
      writeField i off wide u := by
  refine Nat.eq_of_testBit_eq (fun q => ?_)
  by_cases hq : off ≤ q ∧ q < off + wide
  · rw [testBit_writeField_inside hq.1 hq.2,
      testBit_writeField_inside hq.1 hq.2]
  · rw [testBit_writeField_outside (by omega),
      testBit_writeField_outside (by omega),
      testBit_writeField_outside (by omega)]

def rotateRightValue : Nat → Nat → Nat
  | 0, _ => 0
  | 1, x => x % 2
  | width + 2, x =>
      let upper := x / 2
      upper % 2 + 2 * rotateRightValue (width + 1) (x % 2 + 2 * (upper / 2))

def rotateLeftValue : Nat → Nat → Nat
  | 0, _ => 0
  | 1, x => x % 2
  | width + 2, x =>
      let rotatedUpper := rotateLeftValue (width + 1) (x / 2)
      rotatedUpper % 2 + 2 * (x % 2 + 2 * (rotatedUpper / 2))

theorem testBit_rotateRightValue_below_top : ∀ {width x b : Nat},
    b + 1 < width →
    (rotateRightValue width x).testBit b = x.testBit (b + 1) := by
  intro width
  induction width with
  | zero =>
      intro x b h
      omega
  | succ predecessor ih =>
      cases predecessor with
      | zero =>
          intro x b h
          omega
      | succ width =>
          intro x b h
          rw [rotateRightValue]
          by_cases hb : b = 0
          · subst b
            have hmod :
                (x / 2 % 2 + 2 * rotateRightValue (width + 1)
                  (x % 2 + 2 * (x / 2 / 2))) % 2 = x / 2 % 2 := by
              omega
            rw [Nat.testBit_zero, hmod, Nat.testBit_add_one,
              Nat.testBit_zero]
          · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
            rw [Nat.testBit_succ]
            have hdiv :
                (x / 2 % 2 + 2 * rotateRightValue (width + 1)
                  (x % 2 + 2 * (x / 2 / 2))) / 2 =
                  rotateRightValue (width + 1)
                    (x % 2 + 2 * (x / 2 / 2)) := by
              omega
            rw [hdiv, ih (by omega), Nat.testBit_succ]
            have hnextDiv :
                (x % 2 + 2 * (x / 2 / 2)) / 2 = x / 2 / 2 := by
              omega
            rw [hnextDiv, Nat.testBit_div_two, Nat.testBit_div_two]

theorem testBit_rotateRightValue_top
    {width x : Nat} (hwidth : 0 < width) :
    (rotateRightValue width x).testBit (width - 1) = x.testBit 0 := by
  induction width using Nat.twoStepInduction generalizing x with
  | zero => omega
  | one => simp [rotateRightValue]
  | more width _ ih =>
      rw [rotateRightValue]
      let upper := x / 2
      let rest := x % 2 + 2 * (upper / 2)
      have hdiv :
          (upper % 2 + 2 * rotateRightValue (width + 1) rest) / 2 =
            rotateRightValue (width + 1) rest := by omega
      rw [show width + 2 - 1 = width + 1 by omega,
        Nat.testBit_succ, hdiv]
      have htop := ih (x := rest) (by omega)
      rw [show width + 1 - 1 = width by omega] at htop
      rw [htop]
      simp [rest, Nat.testBit_zero]

def cyclicIndex (width value : Nat) (hwidth : 0 < width) : Fin width :=
  ⟨value % width, Nat.mod_lt _ hwidth⟩

theorem cyclicIndex_add {width a b : Nat} (hwidth : 0 < width) :
    cyclicIndex width (a + b) hwidth =
      cyclicIndex width a hwidth + cyclicIndex width b hwidth := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  apply Fin.ext
  simp [cyclicIndex, Fin.add_def, Nat.add_mod]

theorem cyclicIndex_succ {width value : Nat} (hwidth : 0 < width) :
    cyclicIndex width (value + 1) hwidth =
      cyclicIndex width value hwidth + cyclicIndex width 1 hwidth := by
  exact cyclicIndex_add hwidth

theorem testBit_rotateRightValue_cyclic
    {width x q : Nat} (hwidth : 0 < width) (hq : q < width) :
    (rotateRightValue width x).testBit q =
      x.testBit
        ((⟨q, hq⟩ + cyclicIndex width 1 hwidth).val) := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  by_cases hbelow : q + 1 < width
  · rw [testBit_rotateRightValue_below_top hbelow]
    congr 1
    simp [cyclicIndex, Fin.val_add, Nat.mod_eq_of_lt hbelow]
  · have htop : q = width - 1 := by omega
    subst q
    rw [testBit_rotateRightValue_top hwidth]
    congr 1
    simp only [cyclicIndex, Fin.val_add]
    by_cases hone : width = 1
    · subst width
      simp
    · have htwo : 1 < width := by omega
      rw [Nat.mod_eq_of_lt htwo,
        show width - 1 + 1 = width by omega, Nat.mod_self]

theorem rotateRightValue_lt : ∀ (width x : Nat),
    rotateRightValue width x < 2 ^ width
  | 0, x => by simp [rotateRightValue]
  | 1, x => by
      simpa [rotateRightValue] using Nat.mod_lt x (by decide : 0 < 2)
  | width + 2, x => by
      rw [rotateRightValue]
      have hlow := Nat.mod_lt (x / 2) (by decide : 0 < 2)
      have hrec := rotateRightValue_lt (width + 1)
        (x % 2 + 2 * (x / 2 / 2))
      have hpow : 2 ^ (width + 2) = 2 * 2 ^ (width + 1) := by
        rw [Nat.pow_succ]
        omega
      omega

theorem rotateLeftValue_lt : ∀ (width x : Nat),
    rotateLeftValue width x < 2 ^ width
  | 0, x => by simp [rotateLeftValue]
  | 1, x => by
      simpa [rotateLeftValue] using Nat.mod_lt x (by decide : 0 < 2)
  | width + 2, x => by
      rw [rotateLeftValue]
      let r := rotateLeftValue (width + 1) (x / 2)
      have hr : r < 2 ^ (width + 1) := rotateLeftValue_lt (width + 1) (x / 2)
      have hrmod := Nat.mod_lt r (by decide : 0 < 2)
      have hxmod := Nat.mod_lt x (by decide : 0 < 2)
      have hp1 : 2 ^ (width + 1) = 2 * 2 ^ width := by
        rw [Nat.pow_succ]
        omega
      have hp2 : 2 ^ (width + 2) = 2 * 2 ^ (width + 1) := by
        rw [Nat.pow_succ]
        omega
      have hrdiv : r / 2 < 2 ^ width := by omega
      omega

theorem rotateLeftValue_eq_twice_of_lt : ∀ (width x : Nat),
    x < 2 ^ (width - 1) → rotateLeftValue width x = 2 * x
  | 0, x, hx => by
      simp [rotateLeftValue] at hx ⊢
      omega
  | 1, x, hx => by
      simp [rotateLeftValue] at hx ⊢
      omega
  | width + 2, x, hx => by
      have hxpow : x < 2 ^ (width + 1) := by
        rw [show width + 2 - 1 = width + 1 by omega] at hx
        exact hx
      have hxdiv : x / 2 < 2 ^ width := by
        have hpow : 2 ^ (width + 1) = 2 * 2 ^ width := by
          rw [Nat.pow_succ]
          omega
        omega
      have ih := rotateLeftValue_eq_twice_of_lt (width + 1) (x / 2) (by
        simpa using hxdiv)
      rw [rotateLeftValue, ih]
      have hxsplit := Nat.mod_add_div x 2
      have hxmod := Nat.mod_lt x (by decide : 0 < 2)
      omega

def rotateLeftGates : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, width + 2 =>
      rotateLeftGates (off + 1) (width + 1) ++
        swapWires off (off + 1)

theorem rotateLeftGates_act : ∀ (width off i : Nat),
    actGates (rotateLeftGates off width) i =
      writeField i off width (rotateLeftValue width (readField i off width))
  | 0, off, i => by
      rw [writeField_zero]
      rfl
  | 1, off, i => by
      rw [rotateLeftGates, rotateLeftValue, writeField_mod, writeField_read]
      rfl
  | width + 2, off, i => by
      let upper := readField i (off + 1) (width + 1)
      let rotatedUpper := rotateLeftValue (width + 1) upper
      let j := writeField i (off + 1) (width + 1) rotatedUpper
      have e1 : actGates (rotateLeftGates (off + 1) (width + 1)) i = j := by
        exact rotateLeftGates_act (width + 1) (off + 1) i
      have hjlow : bitValue j (off + 1) = rotatedUpper % 2 := by
        simp only [j]
        rw [← readField_one, readField_writeField_narrow (by omega),
          Nat.pow_one]
      have hjoff : bitValue j off = bitValue i off := by
        simp only [j]
        rw [← readField_one,
          readField_writeField_of_disjoint (by omega), readField_one]
      have e2 := swapWires_act (x := off) (y := off + 1) (i := j) (by omega)
      have hxsplit := readField_succ i off (width + 1)
      rw [show width + 1 + 1 = width + 2 by omega] at hxsplit
      have hxmod : readField i off (width + 2) % 2 = bitValue i off := by
        have hb := bitValue_lt i off
        omega
      have hxdiv : readField i off (width + 2) / 2 = upper := by
        have hb := bitValue_lt i off
        simp only [upper]
        omega
      have hlow :
          rotateLeftValue (width + 2) (readField i off (width + 2)) % 2 =
            rotatedUpper % 2 := by
        rw [rotateLeftValue, hxdiv]
        simp only [rotatedUpper]
        have hm := Nat.mod_lt
          (rotateLeftValue (width + 1) (readField i off (width + 2) / 2))
          (by decide : 0 < 2)
        omega
      have hhigh :
          rotateLeftValue (width + 2) (readField i off (width + 2)) / 2 =
            bitValue i off + 2 * (rotatedUpper / 2) := by
        rw [rotateLeftValue, hxdiv, hxmod]
        simp only [rotatedUpper]
        have hm := Nat.mod_lt
          (rotateLeftValue (width + 1) (readField i off (width + 2) / 2))
          (by decide : 0 < 2)
        omega
      have hoffmod : bitValue i off % 2 = bitValue i off := by
        have hb := bitValue_lt i off
        omega
      rw [rotateLeftGates, actGates_append, e1, e2, hjlow, hjoff]
      simp only [j]
      rw [writeField_comm
          (i := i) (o₁ := off + 1) (n₁ := width + 1) (v := rotatedUpper)
          (o₂ := off) (n₂ := 1) (u := rotatedUpper % 2) (by omega),
        writeField_low, hoffmod,
        writeField_succ i off (width + 1)
          (rotateLeftValue (width + 2) (readField i off (width + 2))),
        hlow, hhigh]

theorem rotateLeftGates_wellFormed {total : Nat} : ∀ (width off : Nat),
    off + width ≤ total →
    (rotateLeftGates off width).all (RGate.wellFormed total) = true
  | 0, off, _ => rfl
  | 1, off, _ => rfl
  | width + 2, off, hfield => by
      rw [rotateLeftGates, List.all_append]
      simp only [Bool.and_eq_true]
      exact ⟨rotateLeftGates_wellFormed (width + 1) (off + 1) (by omega),
        swapWires_wellFormed (by omega) (by omega) (by omega)⟩

theorem rotateLeftGates_length : ∀ (width off : Nat),
    (rotateLeftGates off width).length = 3 * (width - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | width + 2, off => by
      rw [rotateLeftGates, List.length_append,
        rotateLeftGates_length (width + 1) (off + 1)]
      simp [swapWires]
      omega

theorem rotateLeftGates_ccx : ∀ (width off : Nat),
    (rotateLeftGates off width).countP RGate.isCcx = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | width + 2, off => by
      rw [rotateLeftGates, List.countP_append,
        rotateLeftGates_ccx (width + 1) (off + 1)]
      simp [swapWires, RGate.isCcx]

theorem rotateLeftGates_cx : ∀ (width off : Nat),
    (rotateLeftGates off width).countP RGate.isCx = 3 * (width - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | width + 2, off => by
      rw [rotateLeftGates, List.countP_append,
        rotateLeftGates_cx (width + 1) (off + 1)]
      simp [swapWires, List.countP_cons, RGate.isCx]
      omega

def rotateRightControlled (control : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, width + 2 =>
      fredkin control off (off + 1) ++
        rotateRightControlled control (off + 1) (width + 1)

def rotateLeftControlled (control : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, width + 2 =>
      rotateLeftControlled control (off + 1) (width + 1) ++
        fredkin control off (off + 1)

theorem rotateRightControlled_on {control : Nat} : ∀ (width off i : Nat),
    (control < off ∨ off + width ≤ control) → bitValue i control = 1 →
    actGates (rotateRightControlled control off width) i =
      writeField i off width (rotateRightValue width (readField i off width))
  | 0, off, i, _, _ => by
      rw [writeField_zero]
      rfl
  | 1, off, i, _, _ => by
      rw [rotateRightControlled, rotateRightValue, writeField_mod, writeField_read]
      rfl
  | width + 2, off, i, hc, hcontrol => by
      let j := writeField
        (writeField i off 1 (bitValue i (off + 1)))
        (off + 1) 1 (bitValue i off)
      have e1 : actGates (fredkin control off (off + 1)) i = j := by
        exact fredkin_on (by omega) (by omega) (by omega) hcontrol
      have hjc : bitValue j control = 1 := by
        simp only [j]
        rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega), hcontrol]
      have hjlow : bitValue j (off + 1) = bitValue i off := by
        simp only [j]
        rw [bitValue_write_self]
        have h := bitValue_lt i off
        omega
      have hjhigh : readField j (off + 2) width = readField i (off + 2) width := by
        simp only [j]
        rw [readField_writeField_of_disjoint (by omega),
          readField_writeField_of_disjoint (by omega)]
      have hiupper := readField_succ i (off + 1) width
      have hjupperSplit := readField_succ j (off + 1) width
      rw [show off + 1 + 1 = off + 2 by omega] at hiupper hjupperSplit
      have hiupperDiv : readField i (off + 1) (width + 1) / 2 =
          readField i (off + 2) width := by
        have hb := bitValue_lt i (off + 1)
        omega
      have hjupper : readField j (off + 1) (width + 1) =
          bitValue i off + 2 * (readField i (off + 1) (width + 1) / 2) := by
        rw [hjlow, hjhigh] at hjupperSplit
        rw [hiupperDiv]
        exact hjupperSplit
      have hxsplit := readField_succ i off (width + 1)
      rw [show width + 1 + 1 = width + 2 by omega] at hxsplit
      have hxmod : readField i off (width + 2) % 2 = bitValue i off := by
        have hb := bitValue_lt i off
        omega
      have hxdiv : readField i off (width + 2) / 2 =
          readField i (off + 1) (width + 1) := by
        have hb := bitValue_lt i off
        omega
      let next := rotateRightValue (width + 1)
        (bitValue i off + 2 * (readField i (off + 1) (width + 1) / 2))
      have hlow :
          rotateRightValue (width + 2) (readField i off (width + 2)) % 2 =
            bitValue i (off + 1) := by
        rw [rotateRightValue, hxdiv, hxmod]
        change (readField i (off + 1) (width + 1) % 2 + 2 * next) % 2 = _
        have hb := bitValue_lt i (off + 1)
        omega
      have hhigh :
          rotateRightValue (width + 2) (readField i off (width + 2)) / 2 =
            next := by
        rw [rotateRightValue, hxdiv, hxmod]
        change (readField i (off + 1) (width + 1) % 2 + 2 * next) / 2 = next
        have hm := Nat.mod_lt (readField i (off + 1) (width + 1)) (by decide : 0 < 2)
        omega
      rw [rotateRightControlled, actGates_append, e1,
        rotateRightControlled_on (width + 1) (off + 1) j (by omega) hjc]
      simp only [j]
      rw [writeField_absorb (by omega),
        writeField_succ i off (width + 1)
          (rotateRightValue (width + 2) (readField i off (width + 2))),
        hlow, hhigh, hjupper]

theorem rotateLeftControlled_on {control : Nat} : ∀ (width off i : Nat),
    (control < off ∨ off + width ≤ control) → bitValue i control = 1 →
    actGates (rotateLeftControlled control off width) i =
      writeField i off width (rotateLeftValue width (readField i off width))
  | 0, off, i, _, _ => by
      rw [writeField_zero]
      rfl
  | 1, off, i, _, _ => by
      rw [rotateLeftControlled, rotateLeftValue, writeField_mod, writeField_read]
      rfl
  | width + 2, off, i, hc, hcontrol => by
      let upper := readField i (off + 1) (width + 1)
      let rotatedUpper := rotateLeftValue (width + 1) upper
      let j := writeField i (off + 1) (width + 1) rotatedUpper
      have e1 : actGates (rotateLeftControlled control (off + 1) (width + 1)) i = j := by
        exact rotateLeftControlled_on (width + 1) (off + 1) i (by omega) hcontrol
      have hjc : bitValue j control = 1 := by
        simp only [j]
        rw [← readField_one,
          readField_writeField_of_disjoint (by omega), readField_one, hcontrol]
      have hjlow : bitValue j (off + 1) = rotatedUpper % 2 := by
        simp only [j]
        rw [← readField_one, readField_writeField_narrow (by omega),
          Nat.pow_one]
      have hjoff : bitValue j off = bitValue i off := by
        simp only [j]
        rw [← readField_one,
          readField_writeField_of_disjoint (by omega), readField_one]
      have e2 := fredkin_on (control := control) (x := off) (y := off + 1)
        (i := j) (by omega) (by omega) (by omega) hjc
      have hxsplit := readField_succ i off (width + 1)
      rw [show width + 1 + 1 = width + 2 by omega] at hxsplit
      have hxmod : readField i off (width + 2) % 2 = bitValue i off := by
        have hb := bitValue_lt i off
        omega
      have hxdiv : readField i off (width + 2) / 2 = upper := by
        have hb := bitValue_lt i off
        simp only [upper]
        omega
      have hlow :
          rotateLeftValue (width + 2) (readField i off (width + 2)) % 2 =
            rotatedUpper % 2 := by
        rw [rotateLeftValue, hxdiv]
        simp only [rotatedUpper]
        have hm := Nat.mod_lt
          (rotateLeftValue (width + 1) (readField i off (width + 2) / 2))
          (by decide : 0 < 2)
        omega
      have hhigh :
          rotateLeftValue (width + 2) (readField i off (width + 2)) / 2 =
            bitValue i off + 2 * (rotatedUpper / 2) := by
        rw [rotateLeftValue, hxdiv, hxmod]
        simp only [rotatedUpper]
        have hm := Nat.mod_lt
          (rotateLeftValue (width + 1) (readField i off (width + 2) / 2))
          (by decide : 0 < 2)
        omega
      have hoffmod : bitValue i off % 2 = bitValue i off := by
        have hb := bitValue_lt i off
        omega
      rw [rotateLeftControlled, actGates_append, e1, e2, hjlow, hjoff]
      simp only [j]
      rw [writeField_comm
          (i := i) (o₁ := off + 1) (n₁ := width + 1) (v := rotatedUpper)
          (o₂ := off) (n₂ := 1) (u := rotatedUpper % 2) (by omega),
        writeField_low, hoffmod,
        writeField_succ i off (width + 1)
          (rotateLeftValue (width + 2) (readField i off (width + 2))),
        hlow, hhigh]

theorem rotateRightControlled_off {control : Nat} : ∀ (width off i : Nat),
    (control < off ∨ off + width ≤ control) → bitValue i control = 0 →
    actGates (rotateRightControlled control off width) i = i
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | width + 2, off, i, hc, hcontrol => by
      rw [rotateRightControlled, actGates_append,
        fredkin_off (by omega) (by omega) hcontrol]
      exact rotateRightControlled_off (width + 1) (off + 1) i (by omega) hcontrol

theorem rotateLeftControlled_off {control : Nat} : ∀ (width off i : Nat),
    (control < off ∨ off + width ≤ control) → bitValue i control = 0 →
    actGates (rotateLeftControlled control off width) i = i
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | width + 2, off, i, hc, hcontrol => by
      rw [rotateLeftControlled, actGates_append,
        rotateLeftControlled_off (width + 1) (off + 1) i (by omega) hcontrol,
        fredkin_off (by omega) (by omega) hcontrol]

theorem fredkin_reverse (control x y : Nat) :
    (fredkin control x y).reverse = fredkin control x y := by
  rfl

theorem rotateLeftControlled_reverse (control : Nat) : ∀ (width off : Nat),
    rotateLeftControlled control off width =
      (rotateRightControlled control off width).reverse
  | 0, off => rfl
  | 1, off => rfl
  | width + 2, off => by
      rw [rotateLeftControlled, rotateRightControlled, List.reverse_append,
        rotateLeftControlled_reverse control (width + 1) (off + 1),
        fredkin_reverse]

theorem rotateRightControlled_wellFormed {control total : Nat} :
    ∀ (width off : Nat),
    (control < off ∨ off + width ≤ control) → control < total →
    off + width ≤ total →
    (rotateRightControlled control off width).all
      (RGate.wellFormed total) = true
  | 0, off, _, _, _ => rfl
  | 1, off, _, _, _ => rfl
  | width + 2, off, hcfield, hctotal, hfield => by
      rw [rotateRightControlled, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · exact fredkin_wellFormed hctotal (by omega) (by omega)
          (by omega) (by omega) (by omega)
      · exact rotateRightControlled_wellFormed (width + 1) (off + 1)
          (by omega) hctotal (by omega)

theorem rotateLeftControlled_wellFormed {control total : Nat} :
    ∀ (width off : Nat),
    (control < off ∨ off + width ≤ control) → control < total →
    off + width ≤ total →
    (rotateLeftControlled control off width).all
      (RGate.wellFormed total) = true
  | 0, off, _, _, _ => rfl
  | 1, off, _, _, _ => rfl
  | width + 2, off, hcfield, hctotal, hfield => by
      rw [rotateLeftControlled, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · exact rotateLeftControlled_wellFormed (width + 1) (off + 1)
          (by omega) hctotal (by omega)
      · exact fredkin_wellFormed hctotal (by omega) (by omega)
          (by omega) (by omega) (by omega)

theorem rotateLeft_right_value {width x : Nat} (hx : x < 2 ^ width) :
    rotateLeftValue width (rotateRightValue width x) = x := by
  let i := writeField x width 1 1
  have hiread : readField i 0 width = x := by
    simp only [i]
    rw [readField_writeField_of_disjoint (Or.inr (by omega))]
    simp [readField, Nat.mod_eq_of_lt hx]
  have hic : bitValue i width = 1 := by
    rw [← readField_one]
    simp only [i]
    rw [readField_writeField, Nat.pow_one]
  have hwf : (rotateRightControlled width 0 width).all
      (RGate.wellFormed (width + 1)) = true := by
    exact rotateRightControlled_wellFormed width 0
      (Or.inr (by omega)) (by omega) (by omega)
  have hinv := actGates_reverse hwf i
  rw [← rotateLeftControlled_reverse width width 0] at hinv
  have hright := rotateRightControlled_on width 0 i
    (Or.inr (by omega)) hic
  let j := writeField i 0 width (rotateRightValue width x)
  have hrightj : actGates (rotateRightControlled width 0 width) i = j := by
    rw [hright, hiread]
  have hjc : bitValue j width = 1 := by
    rw [← readField_one]
    simp only [j]
    rw [readField_writeField_of_disjoint (Or.inl (by omega)),
      readField_one, hic]
  have hjread : readField j 0 width = rotateRightValue width x := by
    simp only [j]
    exact readField_writeField_self (rotateRightValue_lt width x)
  have hleft := rotateLeftControlled_on width 0 j
    (Or.inr (by omega)) hjc
  rw [hrightj, hleft, hjread] at hinv
  simp only [j] at hinv
  rw [writeField_writeField] at hinv
  have hread := congrArg (fun k => readField k 0 width) hinv
  rw [readField_writeField_self
      (rotateLeftValue_lt width (rotateRightValue width x)), hiread] at hread
  exact hread

theorem rotateRightControlled_length (control : Nat) : ∀ (width off : Nat),
    (rotateRightControlled control off width).length = 3 * (width - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | width + 2, off => by
      rw [rotateRightControlled, List.length_append,
        rotateRightControlled_length control (width + 1) (off + 1)]
      simp [fredkin]
      omega

theorem rotateLeftControlled_length (control : Nat) : ∀ (width off : Nat),
    (rotateLeftControlled control off width).length = 3 * (width - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | width + 2, off => by
      rw [rotateLeftControlled, List.length_append,
        rotateLeftControlled_length control (width + 1) (off + 1)]
      simp [fredkin]
      omega

theorem rotateRightControlled_ccx (control : Nat) : ∀ (width off : Nat),
    (rotateRightControlled control off width).countP RGate.isCcx = width - 1
  | 0, off => rfl
  | 1, off => rfl
  | width + 2, off => by
      rw [rotateRightControlled, List.countP_append,
        rotateRightControlled_ccx control (width + 1) (off + 1)]
      simp [fredkin, List.countP_cons, RGate.isCcx]
      omega

theorem rotateLeftControlled_ccx (control : Nat) : ∀ (width off : Nat),
    (rotateLeftControlled control off width).countP RGate.isCcx = width - 1
  | 0, off => rfl
  | 1, off => rfl
  | width + 2, off => by
      rw [rotateLeftControlled, List.countP_append,
        rotateLeftControlled_ccx control (width + 1) (off + 1)]
      simp [fredkin, List.countP_cons, RGate.isCcx]

theorem rotateRightControlled_cx (control : Nat) : ∀ (width off : Nat),
    (rotateRightControlled control off width).countP RGate.isCx = 2 * (width - 1)
  | 0, off => rfl
  | 1, off => rfl
  | width + 2, off => by
      rw [rotateRightControlled, List.countP_append,
        rotateRightControlled_cx control (width + 1) (off + 1)]
      simp [fredkin, List.countP_cons, RGate.isCx]
      omega

theorem rotateLeftControlled_cx (control : Nat) : ∀ (width off : Nat),
    (rotateLeftControlled control off width).countP RGate.isCx = 2 * (width - 1)
  | 0, off => rfl
  | 1, off => rfl
  | width + 2, off => by
      rw [rotateLeftControlled, List.countP_append,
        rotateLeftControlled_cx control (width + 1) (off + 1)]
      simp [fredkin, List.countP_cons, RGate.isCx]
      omega

end Reversible
end VQ
