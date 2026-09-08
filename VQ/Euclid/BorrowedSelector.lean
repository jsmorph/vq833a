import VQ.Euclid.Selector
import VQ.Reversible.BorrowedControl

namespace VQ.Euclid.BorrowedSelector

open Reversible
open Selector (allSet)

def conjunction : List Nat → Nat → Nat → List RGate
  | [], _, target => [.x target]
  | [a], _, target => [.cx a target]
  | [a, b], _, target => [.ccx a b target]
  | [a, b, c], scratch, target => BorrowedControl.triple a b c target scratch
  | a :: b :: c :: d :: rest, scratch, target =>
      [.ccx a b scratch] ++
        conjunction (scratch :: c :: d :: rest) (scratch + 1) target ++
      [.ccx a b scratch]
termination_by controls _ _ => controls.length

def scratchClear (controls : List Nat) (scratch i : Nat) : Prop :=
  ∀ j, j < controls.length - 3 → i.testBit (scratch + j) = false

theorem conjunction_act (controls : List Nat) (scratch target i : Nat)
    (hnodup : controls.Nodup)
    (hbelow : ∀ q ∈ controls, q < scratch)
    (htarget : target < scratch)
    (htargets : target ∉ controls)
    (hclear : scratchClear controls scratch i) :
    actGates (conjunction controls scratch target) i =
      if allSet controls i then i ^^^ (1 <<< target) else i := by
  induction controls, scratch, target using conjunction.induct generalizing i with
  | case1 scratch target => simp [conjunction, allSet, actGates, RGate.act]
  | case2 a scratch target => simp [conjunction, allSet, actGates, RGate.act]
  | case3 a b scratch target => simp [conjunction, allSet, actGates, RGate.act]
  | case4 a b c scratch target =>
      have ha := hbelow a (by simp)
      have hb := hbelow b (by simp)
      have hc := hbelow c (by simp)
      have hat : a ≠ target := by
        intro h
        exact htargets (by simp [← h])
      have hbt : b ≠ target := by
        intro h
        exact htargets (by simp [← h])
      have hct : c ≠ target := by
        intro h
        exact htargets (by simp [← h])
      simpa [conjunction, allSet, Bool.and_assoc] using
        BorrowedControl.triple_act (by omega) (by omega) (by omega)
          hat hbt hct (by omega) i
  | case5 a b c d rest scratch target ih =>
      have ha : a < scratch := hbelow a (by simp)
      have hb : b < scratch := hbelow b (by simp)
      have hab : a ≠ b := by
        intro h
        subst b
        simp at hnodup
      have hsc : i.testBit scratch = false := hclear 0 (by simp)
      let g : RGate := .ccx a b scratch
      let j := g.act i
      have hgj : g.act j = i := by
        apply RGate.act_act (w := scratch + 1)
        simp [g, RGate.wellFormed, hab]
        omega
      have hjfuture : scratchClear (scratch :: c :: d :: rest) (scratch + 1) j := by
        intro q hq
        have hq' : q + 1 < (a :: b :: c :: d :: rest).length - 3 := by
          simp at hq ⊢
          omega
        change (g.act i).testBit (scratch + 1 + q) = false
        rw [RGate.testBit_act_of_not_mem]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hclear (q + 1) hq'
        · simp [g, RGate.wires]
          omega
      have hrecNodup : (scratch :: c :: d :: rest).Nodup := by
        rw [List.nodup_cons]
        constructor
        · intro hs
          have hlt := hbelow scratch (by simp [hs])
          omega
        · exact hnodup.tail.tail
      have hrecBelow : ∀ q ∈ scratch :: c :: d :: rest, q < scratch + 1 := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have hlt := hbelow q (by simp [hq])
          omega
      have hrecTarget : target ∉ scratch :: c :: d :: rest := by
        intro ht
        rcases List.mem_cons.mp ht with ht | ht
        · omega
        · exact htargets (by simp [ht])
      have hrec := ih j hrecNodup hrecBelow (by omega) hrecTarget hjfuture
      have hjbits : ∀ q ∈ c :: d :: rest, j.testBit q = i.testBit q := by
        intro q hq
        have hqa : q ≠ a := by
          intro h
          subst q
          exact (List.nodup_cons.mp hnodup).1 (by simp [hq])
        have hqb : q ≠ b := by
          intro h
          subst q
          exact (List.nodup_cons.mp hnodup.tail).1 hq
        have hqs : q < scratch := hbelow q (by simp [hq])
        rw [show j = g.act i from rfl, RGate.testBit_act_of_not_mem]
        simp [g, RGate.wires, hqa, hqb, Nat.ne_of_lt hqs]
      have hjtail : (c :: d :: rest).all j.testBit =
          (c :: d :: rest).all i.testBit := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        constructor
        · intro h q hq
          rw [← hjbits q hq]
          exact h q hq
        · intro h q hq
          rw [hjbits q hq]
          exact h q hq
      have hjall : allSet (scratch :: c :: d :: rest) j =
          allSet (a :: b :: c :: d :: rest) i := by
        have hjs : j.testBit scratch = (i.testBit a && i.testBit b) := by
          cases haBit : i.testBit a <;> cases hbBit : i.testBit b <;>
            simp [j, g, RGate.act, haBit, hbBit, hsc,
              Nat.one_shiftLeft, Nat.testBit_xor]
        simp only [allSet, List.all_cons, hjs] at hjtail ⊢
        rw [hjtail]
        exact Bool.and_assoc _ _ _
      simp only [conjunction, actGates_append, actGates_cons, actGates_nil]
      change g.act
        (actGates (conjunction (scratch :: c :: d :: rest) (scratch + 1) target) j) = _
      rw [hrec, hjall]
      have hta : target ≠ a := by
        intro h
        exact htargets (by simp [h])
      have htb : target ≠ b := by
        intro h
        exact htargets (by simp [h])
      split
      · rw [Selector.ccx_commute_xor hta htb (by omega), hgj]
      · exact hgj

def gates (value width : Nat) : List RGate :=
  Selector.masks value width ++
    conjunction (List.range width) (Selector.scratchOffset width)
      (Selector.flagWire width) ++
    (Selector.masks value width).reverse

theorem conjunction_use {width i : Nat}
    (hscratch : readField i (Selector.scratchOffset width) (width - 3) = 0) :
    actGates
        (conjunction (List.range width) (Selector.scratchOffset width)
          (Selector.flagWire width)) i =
      (Selector.layout width).write i 1
        ((Selector.flag width i + if allSet (List.range width) i then 1 else 0) % 2) := by
  have hclear : scratchClear (List.range width) (Selector.scratchOffset width) i := by
    intro q hq
    have hqw : q < width - 3 := by simpa using hq
    have hbit := congrArg (fun x : Nat => x.testBit q) hscratch
    simpa [testBit_readField, hqw] using hbit
  rw [conjunction_act (List.range width) (Selector.scratchOffset width)
    (Selector.flagWire width) i List.nodup_range
    (by intro q hq; simp [Selector.scratchOffset] at hq ⊢; omega)
    (by simp [Selector.flagWire, Selector.scratchOffset])
    (by simp [Selector.flagWire]) hclear]
  by_cases hall : allSet (List.range width) i
  · rw [if_pos hall, Selector.xor_eq_writeField_toggle]
    simp only [hall, if_true]
    rfl
  · rw [if_neg hall]
    simp only [hall]
    change i = writeField i width 1 ((readField i width 1 + 0) % 2)
    rw [Nat.add_zero, Nat.mod_eq_of_lt (readField_lt i width 1), writeField_read]

theorem gates_act {value width i : Nat}
    (hscratch : readField i (Selector.scratchOffset width) (width - 3) = 0) :
    actGates (gates value width) i = Selector.out value width i := by
  let j := actGates (Selector.masks value width) i
  have hscratchJ : readField j (Selector.scratchOffset width) (width - 3) = 0 := by
    rw [show readField j (Selector.scratchOffset width) (width - 3) =
        readField i (Selector.scratchOffset width) (width - 3) from ?_, hscratch]
    apply readField_actGates_of_outside
    intro g hg q hq
    obtain ⟨r, hr, rfl⟩ := Selector.masks_mem hg
    simp [RGate.wires] at hq
    left
    simp [Selector.scratchOffset]
    omega
  have huse := conjunction_use (width := width) (i := j) hscratchJ
  have houtside : ∀ g ∈ Selector.masks value width, ∀ q ∈ g.wires,
      q < Selector.flagWire width ∨ Selector.flagWire width + 1 ≤ q := by
    intro g hg q hq
    obtain ⟨r, hr, rfl⟩ := Selector.masks_mem hg
    simp [RGate.wires, Selector.flagWire] at hq ⊢
    omega
  have hrev : ∀ g ∈ (Selector.masks value width).reverse, ∀ q ∈ g.wires,
      q < Selector.flagWire width ∨ Selector.flagWire width + 1 ≤ q := by
    intro g hg
    exact houtside g (List.mem_reverse.mp hg)
  rw [gates, actGates_append, actGates_append, huse]
  change actGates (Selector.masks value width).reverse
      (writeField j (Selector.flagWire width) 1
        ((Selector.flag width j + if allSet (List.range width) j then 1 else 0) % 2)) = _
  rw [actGates_write_of_outside hrev,
    actGates_reverse (Selector.masks_wellFormed value width)]
  unfold Selector.out
  rw [Selector.masks_allSet, Selector.masks_preserves_flag]
  simp [Selector.flagWire, Selector.layout, Layout.write, Layout.offset, Layout.size]

theorem conjunction_ccx (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).countP RGate.isCcx =
      2 * (controls.length - 1) - 1 + (if 3 ≤ controls.length then 1 else 0) := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction, RGate.isCcx]
  | case2 a scratch target => simp [conjunction, RGate.isCcx]
  | case3 a b scratch target => simp [conjunction, RGate.isCcx]
  | case4 a b c scratch target =>
      simp [conjunction, BorrowedControl.triple, List.countP_cons, RGate.isCcx]
  | case5 a b c d rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction, RGate.isCcx, List.countP_cons, List.countP_append, ih]
      omega

theorem nine_bit_zero_test {i : Nat} (hclear : readField i 10 6 = 0) :
    actGates (gates 511 9) i = Selector.out 511 9 i := gates_act hclear

theorem nine_bit_zero_test_wellFormed :
    (gates 511 9).all (RGate.wellFormed 17) = true := by
  simp [gates, Selector.masks, Selector.maskBit, List.range_succ,
    Selector.scratchOffset, Selector.flagWire, conjunction, BorrowedControl.triple,
    RGate.wellFormed]

theorem nine_bit_zero_test_ccx : (gates 511 9).countP RGate.isCcx = 16 := by
  simp [gates, List.countP_append, Selector.masks_ccx, conjunction_ccx]

theorem nine_bit_zero_test_preserves_borrowed {i : Nat}
    (hclear : readField i 10 6 = 0) :
    (actGates (gates 511 9) i).testBit 16 = i.testBit 16 := by
  rw [nine_bit_zero_test hclear]
  exact testBit_writeField_outside (by decide)

end VQ.Euclid.BorrowedSelector
