/-
Loading a compiled natural number into a clear reversible field.
-/
import VQ.Reversible.Reverse

namespace VQ
namespace Reversible

def constantXorGatesAux (value : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | valueBit, wire, width + 1 =>
      (if value.testBit valueBit then [.x wire] else []) ++
        constantXorGatesAux value (valueBit + 1) (wire + 1) width

def constantXorGates (value wire width : Nat) : List RGate :=
  constantXorGatesAux value 0 wire width

def constantMask (value : Nat) : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | valueBit, wire, width + 1 =>
      (if value.testBit valueBit then 1 <<< wire else 0) ^^^
        constantMask value (valueBit + 1) (wire + 1) width

def constantXorIndex (value : Nat) : Nat → Nat → Nat → Nat → Nat
  | _, _, 0, i => i
  | valueBit, wire, width + 1, i =>
      constantXorIndex value (valueBit + 1) (wire + 1) width
        (if value.testBit valueBit then i ^^^ (1 <<< wire) else i)

theorem constantXorIndex_eq (value valueBit wire width i : Nat) :
    constantXorIndex value valueBit wire width i =
      i ^^^ constantMask value valueBit wire width := by
  induction width generalizing valueBit wire i with
  | zero => simp [constantXorIndex, constantMask]
  | succ width ih =>
      rw [constantXorIndex, constantMask, ih]
      split
      · rw [Nat.xor_assoc]
      · rw [Nat.zero_xor]

theorem testBit_constantMask (value valueBit wire width bit : Nat) :
    (constantMask value valueBit wire width).testBit bit =
      (decide (wire ≤ bit) && decide (bit < wire + width) &&
        value.testBit (valueBit + (bit - wire))) := by
  induction width generalizing valueBit wire with
  | zero =>
      by_cases hlo : wire ≤ bit
      · have hhi : ¬bit < wire := by omega
        simp [constantMask, hlo, hhi]
      · simp [constantMask, hlo]
  | succ width ih =>
      rw [constantMask, Nat.testBit_xor, ih]
      by_cases heq : bit = wire
      · subst bit
        have hrest : ¬wire + 1 ≤ wire := by omega
        by_cases hb : value.testBit valueBit = true
        · simp [Nat.one_shiftLeft, hb, hrest]
        · simp [hb, hrest]
      · by_cases hlt : bit < wire
        · have hrest : ¬wire + 1 ≤ bit := by omega
          have hnle : ¬wire ≤ bit := by omega
          have hne : wire ≠ bit := Ne.symm heq
          by_cases hb : value.testBit valueBit = true
          · simp [Nat.one_shiftLeft, hb, hne, hnle, hrest]
          · simp [hb, hnle, hrest]
        · have hrest : wire + 1 ≤ bit := by omega
          have hlo : wire ≤ bit := by omega
          have hne : wire ≠ bit := Ne.symm heq
          have hindex : valueBit + 1 + (bit - (wire + 1)) =
              valueBit + (bit - wire) := by omega
          have hupper : bit < wire + 1 + width ↔
              bit < wire + (width + 1) := by omega
          by_cases hb : value.testBit valueBit = true
          · simp [Nat.one_shiftLeft, hb, hne, hlo,
              hrest, hindex, hupper]
          · simp [hb, hlo,
              hrest, hindex, hupper]

theorem constantMask_eq_shiftedField (value valueBit wire width : Nat) :
    constantMask value valueBit wire width =
      readField value valueBit width <<< wire := by
  refine Nat.eq_of_testBit_eq fun bit => ?_
  rw [testBit_constantMask, Nat.testBit_shiftLeft, testBit_readField]
  by_cases hlo : wire ≤ bit
  · by_cases hhi : bit < wire + width
    · simp [hlo, hhi, show bit - wire < width by omega]
    · simp [hlo, hhi, show ¬bit - wire < width by omega]
  · have hlt : bit < wire := by omega
    simp [hlo]

theorem act_constantXorGatesAux (value : Nat) :
    ∀ valueBit wire width i,
    actGates (constantXorGatesAux value valueBit wire width) i =
      constantXorIndex value valueBit wire width i := by
  intro valueBit wire width
  induction width generalizing valueBit wire with
  | zero => intro i; rfl
  | succ width ih =>
      intro i
      rw [constantXorGatesAux, constantXorIndex]
      split
      · simp only [actGates_append, actGates_cons, actGates_nil, RGate.act]
        exact ih (valueBit + 1) (wire + 1) _
      · simpa using ih (valueBit + 1) (wire + 1) i

theorem act_constantXorGates (value wire width i : Nat) :
    actGates (constantXorGates value wire width) i =
      i ^^^ (readField value 0 width <<< wire) := by
  rw [constantXorGates, act_constantXorGatesAux,
    constantXorIndex_eq, constantMask_eq_shiftedField]

theorem xor_shiftedField_eq_writeField_of_clear
    {i value wire width : Nat}
    (hclear : readField i wire width = 0) (hvalue : value < 2 ^ width) :
    i ^^^ (value <<< wire) = writeField i wire width value := by
  refine Nat.eq_of_testBit_eq fun bit => ?_
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge bit wire with hlo | hlo
  · rw [testBit_writeField_outside (Or.inl hlo)]
    simp [Nat.not_le.mpr hlo]
  · rcases Nat.lt_or_ge bit (wire + width) with hhi | hhi
    · have hbit := congrArg (fun x => x.testBit (bit - wire)) hclear
      simp only [testBit_readField, Nat.zero_testBit,
        show bit - wire < width by omega, decide_true, Bool.true_and,
        show wire + (bit - wire) = bit by omega] at hbit
      rw [testBit_writeField_inside hlo hhi]
      simp [hlo, hbit]
    · rw [testBit_writeField_outside (Or.inr hhi)]
      have hv : value.testBit (bit - wire) = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hvalue
          (Nat.pow_le_pow_right (by omega) (by omega))
      simp [hlo, hv]

theorem act_constantXorGates_of_clear {value wire width i : Nat}
    (hclear : readField i wire width = 0) :
    actGates (constantXorGates value wire width) i =
      writeField i wire width (readField value 0 width) := by
  rw [act_constantXorGates]
  exact xor_shiftedField_eq_writeField_of_clear hclear
    (readField_lt value 0 width)

theorem constantXorGatesAux_wellFormed {value valueBit wire width total : Nat}
    (hbound : wire + width ≤ total) :
    (constantXorGatesAux value valueBit wire width).all
      (RGate.wellFormed total) = true := by
  induction width generalizing valueBit wire with
  | zero => rfl
  | succ width ih =>
      rw [constantXorGatesAux, List.all_append]
      split
      · simp only [List.all_cons, List.all_nil, Bool.and_true,
          RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, ih (by omega)⟩
      · exact ih (by omega)

theorem constantXorGates_wellFormed {value wire width total : Nat}
    (hbound : wire + width ≤ total) :
    (constantXorGates value wire width).all (RGate.wellFormed total) = true :=
  constantXorGatesAux_wellFormed hbound

theorem constantXorGatesAux_wires {value valueBit wire width : Nat} :
    ∀ g ∈ constantXorGatesAux value valueBit wire width,
      ∀ q ∈ g.wires, wire ≤ q ∧ q < wire + width := by
  induction width generalizing valueBit wire with
  | zero => simp [constantXorGatesAux]
  | succ width ih =>
      intro g hg q hq
      rw [constantXorGatesAux, List.mem_append] at hg
      split at hg
      · rcases hg with hg | hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          subst g
          simp only [RGate.wires, List.mem_cons, List.not_mem_nil,
            or_false] at hq
          subst q
          omega
        · have hrest := ih (valueBit := valueBit + 1)
            (wire := wire + 1) g hg q hq
          omega
      · have hrest := ih (valueBit := valueBit + 1)
          (wire := wire + 1) g (by simpa using hg) q hq
        omega

theorem constantXorGates_wires {value wire width : Nat} :
    ∀ g ∈ constantXorGates value wire width,
      ∀ q ∈ g.wires, wire ≤ q ∧ q < wire + width := by
  simpa [constantXorGates] using
    (constantXorGatesAux_wires
      (value := value) (valueBit := 0) (wire := wire) (width := width))

theorem constantXorGatesAux_no_ccx (value valueBit wire : Nat) :
    ∀ width,
      (constantXorGatesAux value valueBit wire width).countP RGate.isCcx = 0 := by
  intro width
  induction width generalizing valueBit wire with
  | zero => rfl
  | succ width ih =>
      rw [constantXorGatesAux, List.countP_append]
      split <;> simp [RGate.isCcx, ih]

theorem constantXorGates_no_ccx (value wire width : Nat) :
    (constantXorGates value wire width).countP RGate.isCcx = 0 :=
  constantXorGatesAux_no_ccx value 0 wire width

theorem constantXorGatesAux_no_cx (value valueBit wire : Nat) :
    ∀ width,
      (constantXorGatesAux value valueBit wire width).countP RGate.isCx = 0 := by
  intro width
  induction width generalizing valueBit wire with
  | zero => rfl
  | succ width ih =>
      rw [constantXorGatesAux, List.countP_append]
      split <;> simp [RGate.isCx, ih]

theorem constantXorGates_no_cx (value wire width : Nat) :
    (constantXorGates value wire width).countP RGate.isCx = 0 :=
  constantXorGatesAux_no_cx value 0 wire width

theorem constantXorGatesAux_length_le (value valueBit wire : Nat) :
    ∀ width, (constantXorGatesAux value valueBit wire width).length ≤ width := by
  intro width
  induction width generalizing valueBit wire with
  | zero => exact Nat.le_refl 0
  | succ width ih =>
      rw [constantXorGatesAux, List.length_append]
      split
      · simp only [List.length_cons, List.length_nil]
        have := ih (valueBit + 1) (wire + 1)
        omega
      · have := ih (valueBit + 1) (wire + 1)
        simpa using Nat.le_trans this (Nat.le_succ width)

theorem constantXorGates_length_le (value wire width : Nat) :
    (constantXorGates value wire width).length ≤ width :=
  constantXorGatesAux_length_le value 0 wire width

end Reversible
end VQ
