import VQ.Reversible.RotateBy

namespace VQ
namespace Reversible

def barrelAmount (width bit : Nat) : Nat := 2 ^ bit % width

def barrelRotateGates (shiftOffset workOffset width : Nat) :
    Nat → List RGate
  | 0 => []
  | count + 1 =>
      barrelRotateGates shiftOffset workOffset width count ++
        rotateBlocksControlled (shiftOffset + count) workOffset
          (width - barrelAmount width count) (barrelAmount width count)

def barrelRotateState (shiftOffset workOffset width : Nat) :
    Nat → Nat → Nat
  | 0, i => i
  | count + 1, i =>
      let j := barrelRotateState shiftOffset workOffset width count i
      if bitValue j (shiftOffset + count) = 1 then
        rotateBlocksState workOffset (width - barrelAmount width count)
          (barrelAmount width count) j
      else j

theorem barrelRotate_act
    {shiftOffset workOffset width count i : Nat}
    (hwidth : 0 < width)
    (hdisjoint : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset) :
    actGates (barrelRotateGates shiftOffset workOffset width count) i =
      barrelRotateState shiftOffset workOffset width count i := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [barrelRotateGates, actGates_append, ih (by omega),
        barrelRotateState]
      let j := barrelRotateState shiftOffset workOffset width count i
      have hamount : barrelAmount width count < width := by
        exact Nat.mod_lt _ hwidth
      have hcontrol : shiftOffset + count < workOffset ∨
          workOffset + (width - barrelAmount width count) +
            barrelAmount width count ≤ shiftOffset + count := by
        rcases hdisjoint with hdisjoint | hdisjoint
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      by_cases hc : bitValue j (shiftOffset + count) = 1
      · rw [if_pos hc]
        exact rotateBlocksControlled_on hcontrol hc
      · have hzero : bitValue j (shiftOffset + count) = 0 := by
          have hlt := bitValue_lt j (shiftOffset + count)
          omega
        rw [if_neg hc]
        exact rotateBlocksControlled_off hcontrol hzero

theorem testBit_barrelRotateState_of_outside
    {shiftOffset workOffset width count i q : Nat}
    (hwidth : 0 < width)
    (houtside : q < workOffset ∨ workOffset + width ≤ q) :
    (barrelRotateState shiftOffset workOffset width count i).testBit q =
      i.testBit q := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [barrelRotateState]
      let j := barrelRotateState shiftOffset workOffset width count i
      split
      · rw [testBit_rotateBlocksState]
        rcases houtside with houtside | houtside
        · have hfirst : ¬workOffset ≤ q := by omega
          have hsecond : ¬workOffset + barrelAmount width count ≤ q := by omega
          rw [if_neg (by omega), if_neg (by omega), ih]
        · have hamount : barrelAmount width count < width :=
            Nat.mod_lt _ hwidth
          have hsum : width - barrelAmount width count +
              barrelAmount width count = width := by omega
          rw [if_neg (by omega), if_neg (by omega), ih]
      · exact ih

theorem bitValue_barrelRotateState_of_outside
    {shiftOffset workOffset width count i q : Nat}
    (hwidth : 0 < width)
    (houtside : q < workOffset ∨ workOffset + width ≤ q) :
    bitValue (barrelRotateState shiftOffset workOffset width count i) q =
      bitValue i q := by
  unfold bitValue
  rw [testBit_barrelRotateState_of_outside hwidth houtside]

theorem testBit_barrelRotateState_cyclic
    {shiftOffset workOffset width count i q : Nat}
    (hwidth : 0 < width)
    (hdisjoint : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hq : q < width) :
    (barrelRotateState shiftOffset workOffset width count i).testBit
        (workOffset + q) =
      i.testBit (workOffset +
        ((⟨q, hq⟩ : Fin width) -
          cyclicIndex width (readField i shiftOffset count) hwidth).val) := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  induction count generalizing q with
  | zero =>
      rw [barrelRotateState]
      have hread : readField i shiftOffset 0 = 0 := by
        unfold readField
        omega
      rw [hread]
      congr 1
      congr 1
      simp [cyclicIndex]
  | succ count ih =>
      rw [barrelRotateState]
      let j := barrelRotateState shiftOffset workOffset width count i
      have hdisjoint' : shiftOffset + count ≤ workOffset ∨
          workOffset + width ≤ shiftOffset := by omega
      have hcontrol : shiftOffset + count < workOffset ∨
          workOffset + width ≤ shiftOffset + count := by omega
      have hsame : bitValue j (shiftOffset + count) =
          bitValue i (shiftOffset + count) :=
        bitValue_barrelRotateState_of_outside hwidth hcontrol
      have hk : barrelAmount width count < width := Nat.mod_lt _ hwidth
      by_cases hc : bitValue j (shiftOffset + count) = 1
      · rw [if_pos hc, testBit_rotateBlocksState_cyclic hk hq]
        let q' : Fin width :=
          ⟨q, hq⟩ - ⟨barrelAmount width count, hk⟩
        rw [ih hdisjoint' q'.isLt]
        congr 1
        congr 1
        change (q' - cyclicIndex width
          (readField i shiftOffset count) hwidth).val = _
        apply congrArg Fin.val
        have hbit : bitValue i (shiftOffset + count) = 1 := by
          rw [← hsame]
          exact hc
        rw [readField_high, hbit]
        simp only [q', barrelAmount]
        rw [show (⟨2 ^ count % width, hk⟩ : Fin width) =
            cyclicIndex width (2 ^ count) hwidth by rfl]
        rw [cyclicIndex_add]
        simp [sub_eq_add_neg, add_comm, add_assoc]
      · rw [if_neg hc]
        have hjlt := bitValue_lt j (shiftOffset + count)
        have hjzero : bitValue j (shiftOffset + count) = 0 := by omega
        have hbit : bitValue i (shiftOffset + count) = 0 := by
          rw [← hsame]
          exact hjzero
        have hread : readField i shiftOffset (count + 1) =
            readField i shiftOffset count := by
          rw [readField_high, hbit]
          simp
        rw [ih hdisjoint' hq, hread]

theorem barrelRotate_length_le
    (shiftOffset workOffset width count : Nat) (hwidth : 0 < width) :
    (barrelRotateGates shiftOffset workOffset width count).length ≤
      3 * width * count := by
  induction count with
  | zero => simp [barrelRotateGates]
  | succ count ih =>
      rw [barrelRotateGates, List.length_append]
      have hamount : barrelAmount width count < width := Nat.mod_lt _ hwidth
      have hstage := rotateBlocksControlled_length_le
        (shiftOffset + count) workOffset
        (width - barrelAmount width count) (barrelAmount width count)
      have hsum : width - barrelAmount width count +
          barrelAmount width count = width := by omega
      have hstage' :
          (rotateBlocksControlled (shiftOffset + count) workOffset
            (width - barrelAmount width count)
            (barrelAmount width count)).length ≤ 3 * width := by
        simpa [hsum] using hstage
      simpa [Nat.mul_succ] using Nat.add_le_add ih hstage'

theorem barrelRotate_ccx_le
    (shiftOffset workOffset width count : Nat) (hwidth : 0 < width) :
    (barrelRotateGates shiftOffset workOffset width count).countP
        RGate.isCcx ≤ width * count := by
  induction count with
  | zero => simp [barrelRotateGates]
  | succ count ih =>
      rw [barrelRotateGates, List.countP_append]
      have hamount : barrelAmount width count < width := Nat.mod_lt _ hwidth
      have hstage := rotateBlocksControlled_ccx_le
        (shiftOffset + count) workOffset
        (width - barrelAmount width count) (barrelAmount width count)
      have hsum : width - barrelAmount width count +
          barrelAmount width count = width := by omega
      have hstage' :
          (rotateBlocksControlled (shiftOffset + count) workOffset
            (width - barrelAmount width count)
            (barrelAmount width count)).countP RGate.isCcx ≤ width := by
        simpa [hsum] using hstage
      simpa [Nat.mul_succ] using Nat.add_le_add ih hstage'

theorem barrelRotate_cx_le
    (shiftOffset workOffset width count : Nat) (hwidth : 0 < width) :
    (barrelRotateGates shiftOffset workOffset width count).countP
        RGate.isCx ≤ 2 * width * count := by
  induction count with
  | zero => simp [barrelRotateGates]
  | succ count ih =>
      rw [barrelRotateGates, List.countP_append]
      have hamount : barrelAmount width count < width := Nat.mod_lt _ hwidth
      have hstage := rotateBlocksControlled_cx_le
        (shiftOffset + count) workOffset
        (width - barrelAmount width count) (barrelAmount width count)
      have hsum : width - barrelAmount width count +
          barrelAmount width count = width := by omega
      have hstage' :
          (rotateBlocksControlled (shiftOffset + count) workOffset
            (width - barrelAmount width count)
            (barrelAmount width count)).countP RGate.isCx ≤ 2 * width := by
        simpa [hsum] using hstage
      simpa [Nat.mul_succ] using Nat.add_le_add ih hstage'

theorem barrelRotate_wellFormed
    {shiftOffset workOffset width count total : Nat}
    (hwidth : 0 < width)
    (hdisjoint : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hshift : shiftOffset + count ≤ total)
    (hwork : workOffset + width ≤ total) :
    (barrelRotateGates shiftOffset workOffset width count).all
      (RGate.wellFormed total) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [barrelRotateGates, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · exact ih (by omega) (by omega)
      · have hamount : barrelAmount width count < width := Nat.mod_lt _ hwidth
        apply rotateBlocksControlled_wellFormed
        · rcases hdisjoint with hdisjoint | hdisjoint
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · omega
        · omega

theorem barrelRotate_reverse_after
    {shiftOffset workOffset width count total i : Nat}
    (hwidth : 0 < width)
    (hdisjoint : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hshift : shiftOffset + count ≤ total)
    (hwork : workOffset + width ≤ total) :
    actGates (barrelRotateGates shiftOffset workOffset width count).reverse
        (barrelRotateState shiftOffset workOffset width count i) = i := by
  rw [← barrelRotate_act hwidth hdisjoint]
  exact actGates_reverse
    (barrelRotate_wellFormed hwidth hdisjoint hshift hwork) i

end Reversible
end VQ
