import VQ.Reversible.Permutation
import Mathlib.Tactic.SplitIfs

namespace VQ
namespace Reversible

def rotateBlocksControlled (control off : Nat) : Nat → Nat → List RGate
  | 0, _ => []
  | _, 0 => []
  | a + 1, b + 1 =>
      if h : a = b then
        swapFieldsControlled control off (off + a + 1) (a + 1)
      else if a < b then
        swapFieldsControlled control off (off + a + 1) (a + 1) ++
          rotateBlocksControlled control (off + a + 1) (a + 1) (b - a)
      else
        swapFieldsControlled control (off + (a - b)) (off + a + 1) (b + 1) ++
          rotateBlocksControlled control off (a - b) (b + 1)
termination_by a b => a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_length_le (control off a b : Nat) :
    (rotateBlocksControlled control off a b).length ≤ 3 * (a + b) := by
  cases a with
  | zero => simp [rotateBlocksControlled]
  | succ a =>
      cases b with
      | zero => simp [rotateBlocksControlled]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rw [swapFieldsControlled_length]
            omega
          · split
            · rw [List.length_append, swapFieldsControlled_length]
              have ih := rotateBlocksControlled_length_le
                control (off + a + 1) (a + 1) (b - a)
              omega
            · rw [List.length_append, swapFieldsControlled_length]
              have ih := rotateBlocksControlled_length_le
                control off (a - b) (b + 1)
              omega
termination_by a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_ccx_le (control off a b : Nat) :
    (rotateBlocksControlled control off a b).countP RGate.isCcx ≤ a + b := by
  cases a with
  | zero => simp [rotateBlocksControlled]
  | succ a =>
      cases b with
      | zero => simp [rotateBlocksControlled]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rw [swapFieldsControlled_ccx]
            omega
          · split
            · rw [List.countP_append, swapFieldsControlled_ccx]
              have ih := rotateBlocksControlled_ccx_le
                control (off + a + 1) (a + 1) (b - a)
              omega
            · rw [List.countP_append, swapFieldsControlled_ccx]
              have ih := rotateBlocksControlled_ccx_le
                control off (a - b) (b + 1)
              omega
termination_by a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_cx_le (control off a b : Nat) :
    (rotateBlocksControlled control off a b).countP RGate.isCx ≤
      2 * (a + b) := by
  cases a with
  | zero => simp [rotateBlocksControlled]
  | succ a =>
      cases b with
      | zero => simp [rotateBlocksControlled]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rw [swapFieldsControlled_cx]
            omega
          · split
            · rw [List.countP_append, swapFieldsControlled_cx]
              have ih := rotateBlocksControlled_cx_le
                control (off + a + 1) (a + 1) (b - a)
              omega
            · rw [List.countP_append, swapFieldsControlled_cx]
              have ih := rotateBlocksControlled_cx_le
                control off (a - b) (b + 1)
              omega
termination_by a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_one_length (control off n : Nat) :
    (rotateBlocksControlled control off n 1).length = 3 * n := by
  induction n with
  | zero => simp [rotateBlocksControlled]
  | succ n ih =>
      rw [rotateBlocksControlled]
      split
      · rw [swapFieldsControlled_length]
      · split
        · omega
        · rw [List.length_append, swapFieldsControlled_length]
          simp only [Nat.sub_zero, Nat.zero_add]
          rw [ih]
          omega

theorem rotateBlocksControlled_one_ccx (control off n : Nat) :
    (rotateBlocksControlled control off n 1).countP RGate.isCcx = n := by
  induction n with
  | zero => simp [rotateBlocksControlled]
  | succ n ih =>
      rw [rotateBlocksControlled]
      split
      · rw [swapFieldsControlled_ccx]
      · split
        · omega
        · rw [List.countP_append, swapFieldsControlled_ccx]
          simp only [Nat.sub_zero, Nat.zero_add]
          rw [ih]
          omega

theorem rotateBlocksControlled_one_cx (control off n : Nat) :
    (rotateBlocksControlled control off n 1).countP RGate.isCx = 2 * n := by
  induction n with
  | zero => simp [rotateBlocksControlled]
  | succ n ih =>
      rw [rotateBlocksControlled]
      split
      · rw [swapFieldsControlled_cx]
      · split
        · omega
        · rw [List.countP_append, swapFieldsControlled_cx]
          simp only [Nat.sub_zero, Nat.zero_add]
          rw [ih]
          omega

theorem rotateBlocksControlled_off {control off a b i : Nat}
    (hcontrol : control < off ∨ off + a + b ≤ control)
    (hc : bitValue i control = 0) :
    actGates (rotateBlocksControlled control off a b) i = i := by
  cases a with
  | zero => simp only [rotateBlocksControlled, actGates_nil]
  | succ a =>
      cases b with
      | zero => simp only [rotateBlocksControlled, actGates_nil]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rename_i h
            apply swapFieldsControlled_off
            · omega
            · omega
            · exact hc
          · split
            · rename_i h hlt
              rw [actGates_append]
              have hswap := swapFieldsControlled_off
                (control := control) (a + 1) off (off + a + 1) i
                (by omega) (by omega) hc
              rw [hswap]
              apply rotateBlocksControlled_off
              · omega
              · exact hc
            · rename_i h hlt
              rw [actGates_append]
              have hswap := swapFieldsControlled_off
                (control := control) (b + 1) (off + (a - b))
                (off + a + 1) i (by omega) (by omega) hc
              rw [hswap]
              apply rotateBlocksControlled_off
              · omega
              · exact hc
termination_by a + b
decreasing_by all_goals omega

def rotateBlocksState (off a b i : Nat) : Nat :=
  writeField
    (writeField i off b (readField i (off + a) b))
    (off + b) a (readField i off a)

theorem testBit_rotateBlocksState (off a b i q : Nat) :
    (rotateBlocksState off a b i).testBit q =
      if off ≤ q ∧ q < off + b then
        i.testBit (off + a + (q - off))
      else if off + b ≤ q ∧ q < off + b + a then
        i.testBit (off + (q - (off + b)))
      else i.testBit q := by
  unfold rotateBlocksState
  by_cases hlow : off ≤ q ∧ q < off + b
  · rw [if_pos hlow,
      testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_inside hlow.1 hlow.2,
      testBit_readField]
    simp [show q - off < b by omega]
  · rw [if_neg hlow]
    by_cases hhigh : off + b ≤ q ∧ q < off + b + a
    · rw [if_pos hhigh,
        testBit_writeField_inside hhigh.1 hhigh.2,
        testBit_readField]
      simp [show q - (off + b) < a by omega]
    · rw [if_neg hhigh,
        testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega)]

theorem testBit_rotateBlocksState_cyclic
    {off width b i q : Nat} (hb : b < width) (hq : q < width) :
    (rotateBlocksState off (width - b) b i).testBit (off + q) =
      i.testBit (off + ((⟨q, hq⟩ : Fin width) - ⟨b, hb⟩).val) := by
  rw [testBit_rotateBlocksState]
  by_cases hlow : q < b
  · rw [if_pos (by omega)]
    simp only [Fin.val_sub]
    have hlt : width - b + q < width := by omega
    rw [Nat.mod_eq_of_lt hlt]
    congr 1
    omega
  · rw [if_neg (by omega), if_pos (by omega)]
    simp only [Fin.val_sub]
    have hsum : width - b + q = width + (q - b) := by omega
    rw [hsum, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : q - b < width)]
    congr 1
    omega

theorem bitValue_rotateBlocksState_of_outside
    {control off a b i : Nat}
    (hcontrol : control < off ∨ off + a + b ≤ control) :
    bitValue (rotateBlocksState off a b i) control = bitValue i control := by
  have hbit : (rotateBlocksState off a b i).testBit control =
      i.testBit control := by
    rw [testBit_rotateBlocksState]
    rcases hcontrol with hcontrol | hcontrol <;>
      split_ifs <;> try omega
    all_goals congr 1
  unfold bitValue
  rw [hbit]

private theorem rotateBlocksState_left
    {off a b i : Nat} (h : a < b) :
    rotateBlocksState (off + a) a (b - a)
        (rotateBlocksState off a a i) =
      rotateBlocksState off a b i := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [testBit_rotateBlocksState]
  split_ifs <;> try omega
  all_goals congr 1 <;> omega

private theorem rotateBlocksState_right
    {off a b i : Nat} (h : b < a) :
    rotateBlocksState off (a - b) b
        (rotateBlocksState (off + (a - b)) b b i) =
      rotateBlocksState off a b i := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [testBit_rotateBlocksState]
  split_ifs <;> try omega
  all_goals congr 1 <;> omega

private theorem rotateBlocksState_left_succ
    {off a b i : Nat} (h : a < b) :
    rotateBlocksState (off + a + 1) (a + 1) (b - a)
        (rotateBlocksState off (a + 1) (a + 1) i) =
      rotateBlocksState off (a + 1) (b + 1) i := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [testBit_rotateBlocksState]
  split_ifs <;> try omega
  all_goals congr 1 <;> omega

private theorem rotateBlocksState_right_succ
    {off a b i : Nat} (h : b < a) :
    rotateBlocksState off (a - b) (b + 1)
        (rotateBlocksState (off + (a - b)) (b + 1) (b + 1) i) =
      rotateBlocksState off (a + 1) (b + 1) i := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [testBit_rotateBlocksState]
  split_ifs <;> try omega
  all_goals congr 1 <;> omega

set_option maxHeartbeats 1000000 in
theorem rotateBlocksControlled_on {control off a b i : Nat}
    (hcontrol : control < off ∨ off + a + b ≤ control)
    (hc : bitValue i control = 1) :
    actGates (rotateBlocksControlled control off a b) i =
      rotateBlocksState off a b i := by
  cases a with
  | zero =>
      simp only [rotateBlocksControlled, actGates_nil, rotateBlocksState,
        Nat.add_zero, writeField_read, writeField_zero]
  | succ a =>
      cases b with
      | zero =>
          simp only [rotateBlocksControlled, actGates_nil, rotateBlocksState,
            Nat.add_zero, writeField_read, writeField_zero]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rename_i h
            subst b
            have hswap := swapFieldsControlled_on
                (control := control) (a + 1) off (off + a + 1) i
                (by omega) (by omega) (by omega) hc
            unfold rotateBlocksState
            have hoff : off + a + 1 = off + (a + 1) := by omega
            rw [← hoff]
            exact hswap
          · split
            · rename_i h hlt
              rw [actGates_append]
              have hswap := swapFieldsControlled_on
                (control := control) (a + 1) off (off + a + 1) i
                (by omega) (by omega) (by omega) hc
              have hswap' : actGates
                  (swapFieldsControlled control off (off + a + 1) (a + 1)) i =
                  rotateBlocksState off (a + 1) (a + 1) i := by
                unfold rotateBlocksState
                have hoff : off + a + 1 = off + (a + 1) := by omega
                rw [← hoff]
                exact hswap
              rw [hswap']
              have hjc : bitValue (rotateBlocksState off (a + 1) (a + 1) i)
                  control = 1 :=
                (bitValue_rotateBlocksState_of_outside (by omega)).trans hc
              have hrec : actGates
                  (rotateBlocksControlled control (off + a + 1)
                    (a + 1) (b - a))
                  (rotateBlocksState off (a + 1) (a + 1) i) =
                  rotateBlocksState (off + a + 1) (a + 1) (b - a)
                    (rotateBlocksState off (a + 1) (a + 1) i) :=
                rotateBlocksControlled_on (by omega) hjc
              rw [hrec]
              exact rotateBlocksState_left_succ
                (off := off) (a := a) (b := b) (i := i) hlt
            · rename_i h hlt
              rw [actGates_append]
              have hswap := swapFieldsControlled_on
                (control := control) (b + 1) (off + (a - b))
                (off + a + 1) i (by omega) (by omega) (by omega) hc
              have hswap' : actGates
                  (swapFieldsControlled control (off + (a - b))
                    (off + a + 1) (b + 1)) i =
                  rotateBlocksState (off + (a - b)) (b + 1) (b + 1) i := by
                unfold rotateBlocksState
                have hoff : off + (a - b) + (b + 1) = off + a + 1 := by omega
                rw [hoff]
                exact hswap
              rw [hswap']
              have hjc : bitValue
                  (rotateBlocksState (off + (a - b)) (b + 1) (b + 1) i)
                  control = 1 :=
                (bitValue_rotateBlocksState_of_outside (by omega)).trans hc
              have hrec : actGates
                  (rotateBlocksControlled control off (a - b) (b + 1))
                  (rotateBlocksState (off + (a - b))
                    (b + 1) (b + 1) i) =
                  rotateBlocksState off (a - b) (b + 1)
                    (rotateBlocksState (off + (a - b))
                      (b + 1) (b + 1) i) :=
                rotateBlocksControlled_on (by omega) hjc
              rw [hrec]
              exact rotateBlocksState_right_succ
                (off := off) (a := a) (b := b) (i := i) (by omega)
termination_by a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_wellFormed
    {control off a b total : Nat}
    (hcontrol : control < off ∨ off + a + b ≤ control)
    (hc : control < total) (hfield : off + a + b ≤ total) :
    (rotateBlocksControlled control off a b).all
      (RGate.wellFormed total) = true := by
  cases a with
  | zero => simp [rotateBlocksControlled]
  | succ a =>
      cases b with
      | zero => simp [rotateBlocksControlled]
      | succ b =>
          rw [rotateBlocksControlled]
          split
          · rename_i h
            apply swapFieldsControlled_wellFormed
            · omega
            · omega
            · omega
            · exact hc
            · omega
            · omega
          · split
            · rename_i h hlt
              rw [List.all_append]
              simp only [Bool.and_eq_true]
              constructor
              · apply swapFieldsControlled_wellFormed
                · omega
                · omega
                · omega
                · exact hc
                · omega
                · omega
              · apply rotateBlocksControlled_wellFormed
                · omega
                · exact hc
                · omega
            · rename_i h hlt
              rw [List.all_append]
              simp only [Bool.and_eq_true]
              constructor
              · apply swapFieldsControlled_wellFormed
                · omega
                · omega
                · omega
                · exact hc
                · omega
                · omega
              · apply rotateBlocksControlled_wellFormed
                · omega
                · exact hc
                · omega
termination_by a + b
decreasing_by all_goals omega

theorem rotateBlocksControlled_reverse_after_on
    {control off a b i total : Nat}
    (hcontrol : control < off ∨ off + a + b ≤ control)
    (hc : bitValue i control = 1)
    (hctotal : control < total) (hfield : off + a + b ≤ total) :
    actGates (rotateBlocksControlled control off a b).reverse
        (rotateBlocksState off a b i) = i := by
  rw [← rotateBlocksControlled_on hcontrol hc]
  exact actGates_reverse
    (rotateBlocksControlled_wellFormed hcontrol hctotal hfield) i

end Reversible
end VQ
