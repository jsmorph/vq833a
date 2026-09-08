/-
A coherent controlled increment for encoded length registers.

The generator visits target bits from high to low.  At target `q`, it toggles
the bit when the external control and every lower target bit are set, using the
same clean conjunction chain as the equality selector.
-/
import VQ.Euclid.Selector
import VQ.Reversible.Bit

namespace VQ
namespace Euclid
namespace Increment

open Reversible

def controlWire (width : Nat) : Nat := width

def scratchOffset (width : Nat) : Nat := width + 1

def layout (width : Nat) : Layout := [width, 1, width]

def gates (width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      Selector.conjunction (controlWire width :: List.range count)
          (scratchOffset width) count ++
        gates width count

def circuit (width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates width width }

def data (width i : Nat) : Nat := (layout width).read i 0

def control (width i : Nat) : Nat := (layout width).read i 1

def scratch (width i : Nat) : Nat := (layout width).read i 2

def conjunctionLength : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | count + 3 => conjunctionLength (count + 2) + 2

def conjunctionCcx : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | count + 3 => conjunctionCcx (count + 2) + 2

def conjunctionCx : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | count + 3 => conjunctionCx (count + 2)

def lengthCost : Nat → Nat
  | 0 => 0
  | count + 1 => conjunctionLength (count + 1) + lengthCost count

def ccxCost : Nat → Nat
  | 0 => 0
  | count + 1 => conjunctionCcx (count + 1) + ccxCost count

def cxCost : Nat → Nat
  | 0 => 0
  | count + 1 => conjunctionCx (count + 1) + cxCost count

theorem conjunction_length (controls : List Nat) (scratch target : Nat) :
    (Selector.conjunction controls scratch target).length =
      conjunctionLength controls.length := by
  induction controls, scratch, target using Selector.conjunction.induct with
  | case1 scratch target => simp [Selector.conjunction, conjunctionLength]
  | case2 a scratch target => simp [Selector.conjunction, conjunctionLength]
  | case3 a b scratch target => simp [Selector.conjunction, conjunctionLength]
  | case4 a b c rest scratch target ih =>
      simp [Selector.conjunction, conjunctionLength, ih]

theorem conjunction_ccx (controls : List Nat) (scratch target : Nat) :
    (Selector.conjunction controls scratch target).countP RGate.isCcx =
      conjunctionCcx controls.length := by
  induction controls, scratch, target using Selector.conjunction.induct with
  | case1 scratch target =>
      simp [Selector.conjunction, conjunctionCcx, RGate.isCcx]
  | case2 a scratch target =>
      simp [Selector.conjunction, conjunctionCcx, RGate.isCcx]
  | case3 a b scratch target =>
      simp [Selector.conjunction, conjunctionCcx, RGate.isCcx]
  | case4 a b c rest scratch target ih =>
      simp [Selector.conjunction, conjunctionCcx, RGate.isCcx,
        List.countP_cons, List.countP_append, ih]

theorem conjunction_cx (controls : List Nat) (scratch target : Nat) :
    (Selector.conjunction controls scratch target).countP RGate.isCx =
      conjunctionCx controls.length := by
  induction controls, scratch, target using Selector.conjunction.induct with
  | case1 scratch target =>
      simp [Selector.conjunction, conjunctionCx, RGate.isCx]
  | case2 a scratch target =>
      simp [Selector.conjunction, conjunctionCx, RGate.isCx]
  | case3 a b scratch target =>
      simp [Selector.conjunction, conjunctionCx, RGate.isCx]
  | case4 a b c rest scratch target ih =>
      simp [Selector.conjunction, conjunctionCx, RGate.isCx,
        List.countP_append, ih]

theorem allSet_range_iff (count i : Nat) :
    Selector.allSet (List.range count) i = true ↔
      readField i 0 count = 2 ^ count - 1 := by
  induction count with
  | zero => simp [Selector.allSet, readField, Nat.mod_one]
  | succ count ih =>
      rw [List.range_succ]
      simp only [Selector.allSet, List.all_append, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true]
      constructor
      · intro h
        have hlow := ih.mp h.1
        have hbit : bitValue i count = 1 := by
          unfold bitValue
          rw [if_pos h.2]
        rw [readField_high]
        simp only [Nat.zero_add]
        rw [hlow, hbit, Nat.pow_succ]
        have hp : 0 < 2 ^ count := Nat.two_pow_pos count
        have hpred : 2 ^ count - 1 + 1 = 2 ^ count :=
          Nat.sub_add_cancel (by omega)
        omega
      · intro h
        have hsplit := readField_high i 0 count
        simp only [Nat.zero_add] at hsplit
        have hlowlt := readField_lt i 0 count
        have hbitlt := bitValue_lt i count
        have hp : 0 < 2 ^ count := Nat.two_pow_pos count
        have hpred : 2 ^ count - 1 + 1 = 2 ^ count :=
          Nat.sub_add_cancel (by omega)
        rw [Nat.pow_succ] at h
        have hbitCases : bitValue i count = 0 ∨ bitValue i count = 1 := by
          omega
        have hbit : bitValue i count = 1 := by
          rcases hbitCases with hbit | hbit
          · rw [hbit] at hsplit
            omega
          · exact hbit
        rw [hbit] at hsplit
        have hlow : readField i 0 count = 2 ^ count - 1 := by omega
        constructor
        · exact ih.mpr hlow
        · by_cases hb : i.testBit count <;> simp_all [bitValue]

theorem scratchClear_of_zero {width count i : Nat} (hcount : count ≤ width)
    (hscratch : scratch width i = 0) :
    Selector.scratchClear (controlWire width :: List.range count)
      (scratchOffset width) i := by
  intro q hq
  have hqw : q < width := by
    simp at hq
    omega
  have hbit := congrArg (fun x : Nat => x.testBit q) hscratch
  simp [scratch, layout, Layout.read, Layout.offset, Layout.size,
    testBit_readField, hqw] at hbit
  simpa [scratchOffset, Nat.add_assoc] using hbit

theorem high_act {width count i : Nat} (hcount : count < width)
    (hscratch : scratch width i = 0) :
    actGates
        (Selector.conjunction (controlWire width :: List.range count)
          (scratchOffset width) count) i =
      if i.testBit (controlWire width) &&
          Selector.allSet (List.range count) i then
        i ^^^ (1 <<< count)
      else i := by
  rw [Selector.conjunction_act
    (controlWire width :: List.range count) (scratchOffset width) count i]
  · rfl
  · rw [List.nodup_cons]
    constructor
    · simp [controlWire]
      omega
    · exact List.nodup_range
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [scratchOffset]
    · simp [scratchOffset] at hq ⊢
      omega
  · simp [scratchOffset]
    omega
  · simp [controlWire]
    omega
  · exact scratchClear_of_zero (Nat.le_of_lt hcount) hscratch

theorem high_state {width count i : Nat} (hcount : count < width)
    (hscratch : scratch width i = 0) :
    actGates
        (Selector.conjunction (controlWire width :: List.range count)
          (scratchOffset width) count) i =
      writeField i count 1
        ((bitValue i count +
          if i.testBit (controlWire width) &&
              Selector.allSet (List.range count) i then 1 else 0) % 2) := by
  rw [high_act hcount hscratch]
  by_cases h : i.testBit (controlWire width) &&
      Selector.allSet (List.range count) i
  · simp only [if_pos h]
    rw [Selector.xor_eq_writeField_toggle, readField_one]
  · simp only [if_neg h, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (bitValue_lt i count), ← readField_one, writeField_read]

theorem act_aux {width count i : Nat} (hcount : count ≤ width)
    (hscratch : scratch width i = 0) :
    actGates (gates width count) i =
      writeField i 0 count
        ((readField i 0 count + bitValue i (controlWire width)) % 2 ^ count) := by
  induction count generalizing i with
  | zero =>
      rw [gates, writeField_zero]
      rfl
  | succ count ih =>
      have hcount' : count < width := by omega
      let carry : Nat :=
        if i.testBit (controlWire width) &&
            Selector.allSet (List.range count) i then 1 else 0
      let high := (bitValue i count + carry) % 2
      let j := writeField i count 1 high
      have hfirst : actGates
          (Selector.conjunction (controlWire width :: List.range count)
            (scratchOffset width) count) i = j := by
        rw [high_state hcount' hscratch]
      have hjcontrol : bitValue j (controlWire width) =
          bitValue i (controlWire width) := by
        simp only [j]
        exact bitValue_write_ne (by simp [controlWire]; omega)
      have hjlow : readField j 0 count = readField i 0 count := by
        simp only [j]
        rw [readField_writeField_of_disjoint (Or.inr (by omega))]
      have hjscratch : scratch width j = 0 := by
        simp only [j, scratch, layout, Layout.read, Layout.offset, Layout.size]
        rw [readField_writeField_of_disjoint (Or.inl (by omega))]
        exact hscratch
      have hrec := ih (Nat.le_of_lt hcount') hjscratch
      rw [gates, actGates_append, hfirst, hrec, hjcontrol, hjlow]
      have hfull := readField_high i 0 count
      simp only [Nat.zero_add] at hfull
      have hlowlt := readField_lt i 0 count
      have hhighlt := bitValue_lt i count
      have hfulllt := readField_lt i 0 (count + 1)
      have hclt := bitValue_lt i (controlWire width)
      have hp : 0 < 2 ^ count := Nat.two_pow_pos count
      have hpow : 2 ^ (count + 1) = 2 ^ count * 2 := by
        rw [Nat.pow_succ]
      have hdvd : 2 ^ count ∣ 2 ^ (count + 1) := ⟨2, hpow⟩
      have hlowResult :
          ((readField i 0 (count + 1) + bitValue i (controlWire width)) %
              2 ^ (count + 1)) % 2 ^ count =
            (readField i 0 count + bitValue i (controlWire width)) %
              2 ^ count := by
        rw [Nat.mod_mod_of_dvd _ hdvd, hfull]
        simp [Nat.add_mod]
      have hhighResult :
          ((readField i 0 (count + 1) + bitValue i (controlWire width)) %
              2 ^ (count + 1)) / 2 ^ count = high := by
        by_cases hc : i.testBit (controlWire width)
        · have hcval : bitValue i (controlWire width) = 1 := by
            simp [bitValue, hc]
          by_cases hall : Selector.allSet (List.range count) i
          · have hlow := (allSet_range_iff count i).mp hall
            simp only [high, carry, hc, hall, Bool.true_and, if_true, hcval]
            have hpred : 2 ^ count - 1 + 1 = 2 ^ count :=
              Nat.sub_add_cancel (by omega)
            rcases (show bitValue i count = 0 ∨ bitValue i count = 1 by omega) with
              hh | hh
            · have heq : readField i 0 (count + 1) + 1 = 2 ^ count := by
                rw [hfull, hlow, hh]
                omega
              rw [heq, Nat.mod_eq_of_lt (by rw [hpow]; omega),
                Nat.div_self hp, hh]
            · have heq : readField i 0 (count + 1) + 1 =
                  2 ^ (count + 1) := by
                rw [hfull, hlow, hh, hpow]
                omega
              rw [heq, Nat.mod_self, Nat.zero_div, hh]
          · have hlow : readField i 0 count ≠ 2 ^ count - 1 := by
              exact fun h => hall ((allSet_range_iff count i).mpr h)
            simp only [high, carry, hc, Bool.true_and, hall, Bool.false_eq_true,
              if_false, hcval]
            have hlowBound : readField i 0 count + 1 < 2 ^ count := by
              have hpred : 2 ^ count - 1 + 1 = 2 ^ count :=
                Nat.sub_add_cancel (by omega)
              omega
            have hmulBound : 2 ^ count * bitValue i count ≤ 2 ^ count := by
              rcases (show bitValue i count = 0 ∨ bitValue i count = 1 by omega) with
                hh | hh <;> rw [hh] <;> omega
            rw [Nat.mod_eq_of_lt (by omega : bitValue i count + 0 < 2)]
            have htotal : readField i 0 (count + 1) + 1 <
                2 ^ (count + 1) := by
              rw [hfull, hpow]
              omega
            rw [Nat.mod_eq_of_lt htotal, hfull]
            have hreassoc : readField i 0 count + 2 ^ count * bitValue i count + 1 =
                (readField i 0 count + 1) + 2 ^ count * bitValue i count := by
              omega
            rw [hreassoc, Nat.add_mul_div_left _ _ hp,
              Nat.div_eq_of_lt hlowBound, Nat.zero_add, Nat.add_zero]
        · have hcval : bitValue i (controlWire width) = 0 := by
            simp [bitValue, hc]
          simp only [high, carry, hc, Bool.false_and, Bool.false_eq_true,
            if_false, hcval, Nat.add_zero]
          rw [Nat.mod_eq_of_lt hhighlt, Nat.mod_eq_of_lt hfulllt]
          rw [hfull, Nat.add_mul_div_left _ _ hp,
            Nat.div_eq_of_lt hlowlt, Nat.zero_add]
      calc
        writeField j 0 count
            ((readField i 0 count + bitValue i (controlWire width)) %
              2 ^ count) =
            writeField
              (writeField i 0 count
                ((readField i 0 count + bitValue i (controlWire width)) %
                  2 ^ count)) count 1 high := by
              simp only [j]
              rw [writeField_comm
                (i := i) (o₁ := count) (n₁ := 1) (v := high)
                (o₂ := 0) (n₂ := count)
                (u := (readField i 0 count + bitValue i (controlWire width)) %
                  2 ^ count) (Or.inr (by omega))]
        _ = writeField i 0 (count + 1)
            ((readField i 0 (count + 1) + bitValue i (controlWire width)) %
              2 ^ (count + 1)) := by
              symm
              rw [writeField_high, hlowResult, hhighResult]
              simp only [Nat.zero_add]

theorem act_circuit {width i : Nat} (hscratch : scratch width i = 0) :
    act (circuit width) i =
      writeField i 0 width
        ((data width i + bitValue i (controlWire width)) % 2 ^ width) := by
  exact act_aux (Nat.le_refl width) hscratch

theorem gates_wellFormed_aux {width count : Nat} (hcount : count ≤ width) :
    (gates width count).all
      (RGate.wellFormed (layout width).width) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hcount' : count < width := by omega
      rw [gates, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · apply Selector.conjunction_wellFormed
        · rw [List.nodup_cons]
          exact ⟨by simp [controlWire]; omega, List.nodup_range⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · simp [scratchOffset]
          · simp [scratchOffset] at hq ⊢
            omega
        · simp [scratchOffset]
          omega
        · simp [controlWire]
          omega
        · simp [scratchOffset, layout, Layout.width]
        · simp [scratchOffset, layout, Layout.width]
          omega
      · exact ih (Nat.le_of_lt hcount')

theorem circuit_wellFormed (width : Nat) :
    (circuit width).wellFormed = true :=
  gates_wellFormed_aux (Nat.le_refl width)

theorem width_exact (width : Nat) :
    (circuit width).width = 2 * width + 1 := by
  simp [circuit, layout, Layout.width]
  omega

theorem gates_length (width count : Nat) :
    (gates width count).length = lengthCost count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [gates, List.length_append, conjunction_length, ih]
      simp [lengthCost]

theorem gates_ccx (width count : Nat) :
    (gates width count).countP RGate.isCcx = ccxCost count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [gates, List.countP_append, conjunction_ccx, ih]
      simp [ccxCost]

theorem gates_cx (width count : Nat) :
    (gates width count).countP RGate.isCx = cxCost count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [gates, List.countP_append, conjunction_cx, ih]
      simp [cxCost]

theorem circuit_length (width : Nat) :
    (circuit width).gates.length = lengthCost width :=
  gates_length width width

theorem circuit_ccx (width : Nat) :
    (circuit width).gates.countP RGate.isCcx = ccxCost width :=
  gates_ccx width width

theorem circuit_cx (width : Nat) :
    (circuit width).gates.countP RGate.isCx = cxCost width :=
  gates_cx width width

def decrementValue (width i : Nat) : Nat :=
  (data width i + 2 ^ width - bitValue i (controlWire width)) % 2 ^ width

theorem increment_decrement_value (width i : Nat) :
    (decrementValue width i + bitValue i (controlWire width)) % 2 ^ width =
      data width i := by
  have hdata := (layout width).read_lt i 0
  have hcontrol := bitValue_lt i (controlWire width)
  have hp : 0 < 2 ^ width := Nat.two_pow_pos width
  change data width i < 2 ^ width at hdata
  rcases (show bitValue i (controlWire width) = 0 ∨
      bitValue i (controlWire width) = 1 by omega) with hc | hc
  · simp [decrementValue, hc, Nat.mod_eq_of_lt hdata]
  · by_cases hd : data width i = 0
    · rw [decrementValue, hc, hd]
      have hpred : 2 ^ width - 1 < 2 ^ width := by omega
      rw [Nat.zero_add, Nat.mod_eq_of_lt hpred,
        Nat.sub_add_cancel (by omega), Nat.mod_self]
    · have hpos : 0 < data width i := Nat.pos_of_ne_zero hd
      have heq : data width i + 2 ^ width - 1 =
          (data width i - 1) + 2 ^ width := by omega
      rw [decrementValue, hc, heq]
      rw [show data width i - 1 + 2 ^ width =
          data width i - 1 + 2 ^ width * 1 by omega,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : data width i - 1 < 2 ^ width),
        Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hdata]

theorem act_reverse_circuit {width i : Nat} (hscratch : scratch width i = 0) :
    act (circuit width).reverse i =
      writeField i 0 width (decrementValue width i) := by
  let j := writeField i 0 width (decrementValue width i)
  have hjscratch : scratch width j = 0 := by
    simp only [j, scratch, layout, Layout.read, Layout.offset, Layout.size]
    rw [readField_writeField_of_disjoint (Or.inl (by omega))]
    exact hscratch
  have hjcontrol : bitValue j (controlWire width) =
      bitValue i (controlWire width) := by
    simp only [j]
    rw [← readField_one,
      readField_writeField_of_disjoint (Or.inl (by simp [controlWire])),
      readField_one]
  have hjdata : data width j = decrementValue width i := by
    simp only [j, data, layout, Layout.read, Layout.offset, Layout.size]
    exact readField_writeField_self
      (Nat.mod_lt _ (Nat.two_pow_pos width))
  have hforward : act (circuit width) j = i := by
    rw [act_circuit hjscratch, hjdata, hjcontrol,
      increment_decrement_value]
    simp only [j]
    rw [writeField_writeField]
    exact writeField_read i 0 width
  have hinverse := act_reverse (circuit_wellFormed width) j
  rw [hforward] at hinverse
  exact hinverse

theorem act_reverse_after_increment {width i : Nat}
    (hscratch : scratch width i = 0) :
    act (circuit width).reverse
        (writeField i 0 width
          ((data width i + bitValue i (controlWire width)) % 2 ^ width)) = i := by
  rw [← act_circuit hscratch]
  exact act_reverse (circuit_wellFormed width) i

end Increment
end Euclid
end VQ
