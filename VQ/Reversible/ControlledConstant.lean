/-
Classically compiled constant xor under one or two quantum controls.
-/
import VQ.Reversible.Constant
import VQ.Reversible.Bit

namespace VQ
namespace Reversible

theorem xor_mod_two (x y : Nat) :
    (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  have hxy : (x ^^^ y) % 2 = bitValue (x ^^^ y) 0 := by
    simpa using (bitValue_shift (x ^^^ y) 0).symm
  have hx : x % 2 = bitValue x 0 := by
    simpa using (bitValue_shift x 0).symm
  have hy : y % 2 = bitValue y 0 := by
    simpa using (bitValue_shift y 0).symm
  rw [hxy, hx, hy]
  unfold bitValue
  rw [Nat.testBit_xor]
  cases hx : x.testBit 0 <;> cases hy : y.testBit 0 <;> simp

theorem xor_div_two (x y : Nat) :
    (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_div_two, Nat.testBit_div_two]

def controlledXorGates (control : Nat) : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | target, width + 1, value =>
      (if value % 2 = 1 then [.cx control target] else []) ++
        controlledXorGates control (target + 1) width (value / 2)

theorem controlledXorGates_act {control : Nat} :
    ∀ width target value i,
      (control < target ∨ target + width ≤ control) →
      actGates (controlledXorGates control target width value) i =
        writeField i target width
          (readField i target width ^^^ bitValue i control * value) := by
  intro width
  induction width with
  | zero =>
      intro target value i _
      rw [writeField_zero]
      rfl
  | succ width ih =>
      intro target value i hcontrol
      have hcontrolTarget : control ≠ target := by omega
      have hcontrolHead : control < target ∨ target + 1 ≤ control := by omega
      have hcontrolValue := bitValue_lt i control
      have htargetValue := bitValue_lt i target
      have hhead :
          actGates
              (if value % 2 = 1 then [.cx control target] else []) i =
            writeField i target 1
              ((bitValue i target + bitValue i control * (value % 2)) % 2) := by
        by_cases hvalue : value % 2 = 1
        · rw [if_pos hvalue]
          simp only [actGates_cons, actGates_nil, act_cx_write]
          rw [hvalue, Nat.mul_one]
        · have hzero : value % 2 = 0 := by omega
          rw [if_neg hvalue, hzero, Nat.mul_zero, actGates_nil]
          exact (write_of_bitValue (by omega)).symm
      have hsignalMod :
          (bitValue i control * value) % 2 =
            bitValue i control * (value % 2) % 2 := by
        rcases (by omega : bitValue i control = 0 ∨ bitValue i control = 1) with
          h | h <;> rw [h] <;> simp
      have hsignalDiv :
          (bitValue i control * value) / 2 =
            bitValue i control * (value / 2) := by
        rcases (by omega : bitValue i control = 0 ∨ bitValue i control = 1) with
          h | h <;> rw [h] <;> simp
      have hlow :
          (readField i target (width + 1) ^^^
              bitValue i control * value) % 2 =
            (bitValue i target + bitValue i control * (value % 2)) % 2 := by
        rw [xor_mod_two, hsignalMod]
        have hread : readField i target (width + 1) % 2 =
            bitValue i target := by
          have := readField_succ i target width
          omega
        rw [hread]
        omega
      have hhigh :
          (readField i target (width + 1) ^^^
              bitValue i control * value) / 2 =
            readField i (target + 1) width ^^^
              bitValue i control * (value / 2) := by
        rw [xor_div_two, hsignalDiv]
        have hread : readField i target (width + 1) / 2 =
            readField i (target + 1) width := by
          have := readField_succ i target width
          omega
        rw [hread]
      have hcontrolPreserved :
          bitValue
              (writeField i target 1
                ((bitValue i target + bitValue i control * (value % 2)) % 2))
              control = bitValue i control := by
        rw [bitValue_write_ne hcontrolTarget]
      rw [controlledXorGates, actGates_append, hhead,
        ih (target + 1) (value / 2) _ (by omega),
        readField_writeField_of_disjoint (Or.inl (by omega)),
        hcontrolPreserved,
        writeField_succ i target width
          (readField i target (width + 1) ^^^
            bitValue i control * value),
        hlow, hhigh]

def doubleControlledXorGates (first second : Nat) :
    Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | target, width + 1, value =>
      (if value % 2 = 1 then [.ccx first second target] else []) ++
        doubleControlledXorGates first second (target + 1) width (value / 2)

theorem doubleControlledXorGates_act {first second : Nat} :
    ∀ width target value i,
      (first < target ∨ target + width ≤ first) →
      (second < target ∨ target + width ≤ second) →
      actGates
          (doubleControlledXorGates first second target width value) i =
        writeField i target width
          (readField i target width ^^^
            bitValue i first * bitValue i second * value) := by
  intro width
  induction width with
  | zero =>
      intro target value i _ _
      rw [writeField_zero]
      rfl
  | succ width ih =>
      intro target value i hfirst hsecond
      have hfirstTarget : first ≠ target := by omega
      have hsecondTarget : second ≠ target := by omega
      have hfirstValue := bitValue_lt i first
      have hsecondValue := bitValue_lt i second
      have htargetValue := bitValue_lt i target
      have hsignal :
          bitValue i first * bitValue i second = 0 ∨
            bitValue i first * bitValue i second = 1 := by
        rcases (by omega : bitValue i first = 0 ∨ bitValue i first = 1) with
          hfirstBit | hfirstBit <;>
          rcases (by omega : bitValue i second = 0 ∨ bitValue i second = 1) with
            hsecondBit | hsecondBit <;>
          simp [hfirstBit, hsecondBit]
      have hhead :
          actGates
              (if value % 2 = 1 then [.ccx first second target] else []) i =
            writeField i target 1
              ((bitValue i target +
                bitValue i first * bitValue i second * (value % 2)) % 2) := by
        by_cases hvalue : value % 2 = 1
        · rw [if_pos hvalue]
          simp only [actGates_cons, actGates_nil, act_ccx_write]
          rw [hvalue, Nat.mul_one]
        · have hzero : value % 2 = 0 := by omega
          rw [if_neg hvalue, hzero, Nat.mul_zero, actGates_nil]
          exact (write_of_bitValue (by omega)).symm
      have hsignalMod :
          (bitValue i first * bitValue i second * value) % 2 =
            bitValue i first * bitValue i second * (value % 2) % 2 := by
        rcases hsignal with h | h <;> rw [h] <;> simp
      have hsignalDiv :
          (bitValue i first * bitValue i second * value) / 2 =
            bitValue i first * bitValue i second * (value / 2) := by
        rcases hsignal with h | h <;> rw [h] <;> simp
      have hlow :
          (readField i target (width + 1) ^^^
              bitValue i first * bitValue i second * value) % 2 =
            (bitValue i target +
              bitValue i first * bitValue i second * (value % 2)) % 2 := by
        rw [xor_mod_two, hsignalMod]
        have hread : readField i target (width + 1) % 2 =
            bitValue i target := by
          have := readField_succ i target width
          omega
        rw [hread]
        omega
      have hhigh :
          (readField i target (width + 1) ^^^
              bitValue i first * bitValue i second * value) / 2 =
            readField i (target + 1) width ^^^
              bitValue i first * bitValue i second * (value / 2) := by
        rw [xor_div_two, hsignalDiv]
        have hread : readField i target (width + 1) / 2 =
            readField i (target + 1) width := by
          have := readField_succ i target width
          omega
        rw [hread]
      have hfirstPreserved :
          bitValue
              (writeField i target 1
                ((bitValue i target +
                  bitValue i first * bitValue i second * (value % 2)) % 2))
              first = bitValue i first := by
        rw [bitValue_write_ne hfirstTarget]
      have hsecondPreserved :
          bitValue
              (writeField i target 1
                ((bitValue i target +
                  bitValue i first * bitValue i second * (value % 2)) % 2))
              second = bitValue i second := by
        rw [bitValue_write_ne hsecondTarget]
      rw [doubleControlledXorGates, actGates_append, hhead,
        ih (target + 1) (value / 2) _ (by omega) (by omega),
        readField_writeField_of_disjoint (Or.inl (by omega)),
        hfirstPreserved, hsecondPreserved,
        writeField_succ i target width
          (readField i target (width + 1) ^^^
            bitValue i first * bitValue i second * value),
        hlow, hhigh]

theorem writeField_xor_value (i value target width : Nat) :
    writeField i target width (readField i target width ^^^ value) =
      i ^^^ (readField value 0 width <<< target) := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rcases Nat.lt_or_ge q target with hlow | hlow
  · rw [testBit_writeField_outside (Or.inl hlow), Nat.testBit_xor,
      Nat.testBit_shiftLeft]
    simp [Nat.not_le.mpr hlow]
  · rcases Nat.lt_or_ge q (target + width) with hinside | hhigh
    · rw [testBit_writeField_inside hlow hinside, Nat.testBit_xor,
        Nat.testBit_xor, testBit_readField, Nat.testBit_shiftLeft,
        testBit_readField]
      simp [hlow, show q - target < width by omega,
        show target + (q - target) = q by omega]
    · rw [testBit_writeField_outside (Or.inr hhigh), Nat.testBit_xor,
        Nat.testBit_shiftLeft]
      have hbit : (readField value 0 width).testBit (q - target) = false := by
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (readField_lt value 0 width)
            (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hlow, hbit]

theorem controlledXorGates_act_xor {control target width value i : Nat}
    (hcontrol : control < target ∨ target + width ≤ control) :
    actGates (controlledXorGates control target width value) i =
      if bitValue i control = 1 then
        i ^^^ (readField value 0 width <<< target)
      else i := by
  have hcontrolBit := bitValue_lt i control
  rw [controlledXorGates_act width target value i hcontrol]
  rcases (by omega : bitValue i control = 0 ∨ bitValue i control = 1) with
      hzero | hone
  · rw [if_neg (by omega), hzero, Nat.zero_mul, Nat.xor_zero,
      writeField_read]
  · rw [if_pos hone, hone, Nat.one_mul, writeField_xor_value]

theorem doubleControlledXorGates_act_xor
    {first second target width value i : Nat}
    (hfirst : first < target ∨ target + width ≤ first)
    (hsecond : second < target ∨ target + width ≤ second) :
    actGates
        (doubleControlledXorGates first second target width value) i =
      if bitValue i first * bitValue i second = 1 then
        i ^^^ (readField value 0 width <<< target)
      else i := by
  rw [doubleControlledXorGates_act width target value i hfirst hsecond]
  have hfirstBit := bitValue_lt i first
  have hsecondBit := bitValue_lt i second
  have hsignal : bitValue i first * bitValue i second = 0 ∨
      bitValue i first * bitValue i second = 1 := by
    rcases (by omega : bitValue i first = 0 ∨ bitValue i first = 1) with
      hf | hf <;>
      rcases (by omega : bitValue i second = 0 ∨ bitValue i second = 1) with
        hs | hs <;>
      simp [hf, hs]
  rcases hsignal with hzero | hone
  · rw [if_neg (by omega), hzero, Nat.zero_mul, Nat.xor_zero,
      writeField_read]
  · rw [if_pos hone, hone, Nat.one_mul, writeField_xor_value]

theorem controlledXorGates_wires (control : Nat) :
    ∀ width target value, ∀ g ∈ controlledXorGates control target width value,
      ∀ q ∈ g.wires,
        q = control ∨ target ≤ q ∧ q < target + width := by
  intro width
  induction width with
  | zero =>
      intro target value g hg
      simp [controlledXorGates] at hg
  | succ width ih =>
      intro target value g hg q hq
      rw [controlledXorGates, List.mem_append] at hg
      rcases hg with hg | hg
      · by_cases hvalue : value % 2 = 1
        · rw [if_pos hvalue] at hg
          simp only [List.mem_singleton] at hg
          subst g
          simp [RGate.wires] at hq
          rcases hq with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr ⟨Nat.le_refl _, by omega⟩
        · rw [if_neg hvalue] at hg
          simp at hg
      · have h := ih (target + 1) (value / 2) g hg q hq
        omega

theorem doubleControlledXorGates_wires (first second : Nat) :
    ∀ width target value,
      ∀ g ∈ doubleControlledXorGates first second target width value,
      ∀ q ∈ g.wires,
        q = first ∨ q = second ∨ target ≤ q ∧ q < target + width := by
  intro width
  induction width with
  | zero =>
      intro target value g hg
      simp [doubleControlledXorGates] at hg
  | succ width ih =>
      intro target value g hg q hq
      rw [doubleControlledXorGates, List.mem_append] at hg
      rcases hg with hg | hg
      · by_cases hvalue : value % 2 = 1
        · rw [if_pos hvalue] at hg
          simp only [List.mem_singleton] at hg
          subst g
          simp [RGate.wires] at hq
          rcases hq with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr ⟨Nat.le_refl _, by omega⟩)
        · rw [if_neg hvalue] at hg
          simp at hg
      · have h := ih (target + 1) (value / 2) g hg q hq
        omega

theorem controlledXorGates_wellFormed {control target width value total : Nat}
    (hdisjoint : control < target ∨ target + width ≤ control)
    (hcontrol : control < total) (htarget : target + width ≤ total) :
    (controlledXorGates control target width value).all
      (RGate.wellFormed total) = true := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [controlledXorGates, List.all_append, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      by_cases hvalue : value % 2 = 1
      · rw [if_pos hvalue]
        simp [RGate.wellFormed]
        omega
      · rw [if_neg hvalue]
        rfl
      · apply ih <;> omega

theorem doubleControlledXorGates_wellFormed
    {first second target width value total : Nat}
    (hcontrols : first ≠ second)
    (hfirstDisjoint : first < target ∨ target + width ≤ first)
    (hsecondDisjoint : second < target ∨ target + width ≤ second)
    (hfirst : first < total) (hsecond : second < total)
    (htarget : target + width ≤ total) :
    (doubleControlledXorGates first second target width value).all
      (RGate.wellFormed total) = true := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [doubleControlledXorGates, List.all_append, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      by_cases hvalue : value % 2 = 1
      · rw [if_pos hvalue]
        simp [RGate.wellFormed]
        omega
      · rw [if_neg hvalue]
        rfl
      · apply ih <;> omega

theorem controlledXorGates_length_le (control target value : Nat) :
    ∀ width, (controlledXorGates control target width value).length ≤ width := by
  intro width
  induction width generalizing target value with
  | zero => exact Nat.le_refl 0
  | succ width ih =>
      rw [controlledXorGates, List.length_append]
      split <;> simp only [List.length_cons, List.length_nil]
      all_goals
        have h := ih (target + 1) (value / 2)
        omega

theorem doubleControlledXorGates_length_le
    (first second target value : Nat) :
    ∀ width,
      (doubleControlledXorGates first second target width value).length ≤ width := by
  intro width
  induction width generalizing target value with
  | zero => exact Nat.le_refl 0
  | succ width ih =>
      rw [doubleControlledXorGates, List.length_append]
      split <;> simp only [List.length_cons, List.length_nil]
      all_goals
        have h := ih (target + 1) (value / 2)
        omega

theorem controlledXorGates_ccx (control target width value : Nat) :
    (controlledXorGates control target width value).countP RGate.isCcx = 0 := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [controlledXorGates, List.countP_append, ih]
      split <;> rfl

theorem controlledXorGates_cx (control target width value : Nat) :
    (controlledXorGates control target width value).countP RGate.isCx =
      (controlledXorGates control target width value).length := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [controlledXorGates, List.countP_append, List.length_append, ih]
      split <;> rfl

theorem doubleControlledXorGates_ccx
    (first second target width value : Nat) :
    (doubleControlledXorGates first second target width value).countP
        RGate.isCcx =
      (doubleControlledXorGates first second target width value).length := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [doubleControlledXorGates, List.countP_append, List.length_append, ih]
      split <;> rfl

theorem doubleControlledXorGates_cx
    (first second target width value : Nat) :
    (doubleControlledXorGates first second target width value).countP
      RGate.isCx = 0 := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
      rw [doubleControlledXorGates, List.countP_append, ih]
      split <;> rfl

end Reversible
end VQ
