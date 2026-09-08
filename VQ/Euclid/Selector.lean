/-
An equality-controlled flag for quantum length and location registers.

The source occupies the low `width` wires, the flag follows it, and a clean
scratch field of `width` wires follows the flag.  The circuit restores the
source and scratch fields while toggling the flag exactly when the source
equals a compiled constant modulo `2^width`.
-/
import VQ.Reversible.Place
import VQ.Reversible.Compile

namespace VQ
namespace Euclid
namespace Selector

open Reversible

def maskBit (value q : Nat) : List RGate :=
  if value.testBit q then [] else [.x q]

def masks (value : Nat) : Nat → List RGate
  | 0 => []
  | width + 1 => masks value width ++ maskBit value width

/-- Toggle `target` by the conjunction of `controls`, returning every scratch
wire to zero.  The recursive case computes the conjunction of the first two
controls, consumes it in the smaller conjunction, and erases it. -/
def conjunction : List Nat → Nat → Nat → List RGate
  | [], _, target => [.x target]
  | [a], _, target => [.cx a target]
  | [a, b], _, target => [.ccx a b target]
  | a :: b :: c :: rest, scratch, target =>
      [.ccx a b scratch] ++
        conjunction (scratch :: c :: rest) (scratch + 1) target ++
      [.ccx a b scratch]
termination_by controls _ _ => controls.length

def flagWire (width : Nat) : Nat := width

def scratchOffset (width : Nat) : Nat := width + 1

def layout (width : Nat) : Layout := [width, 1, width]

def gates (value width : Nat) : List RGate :=
  masks value width ++
    conjunction (List.range width) (scratchOffset width) (flagWire width) ++
    (masks value width).reverse

def circuit (value width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates value width }

def source (width i : Nat) : Nat := (layout width).read i 0

def flag (width i : Nat) : Nat := (layout width).read i 1

def scratch (width i : Nat) : Nat := (layout width).read i 2

def out (value width i : Nat) : Nat :=
  (layout width).write i 1
    ((flag width i + if source width i = value % 2 ^ width then 1 else 0) % 2)

def allSet (controls : List Nat) (i : Nat) : Bool :=
  controls.all i.testBit

def scratchClear (controls : List Nat) (scratch i : Nat) : Prop :=
  ∀ j, j < controls.length - 2 → i.testBit (scratch + j) = false

theorem maskBit_same (value q i : Nat) :
    (actGates (maskBit value q) i).testBit q = (i.testBit q == value.testBit q) := by
  cases hv : value.testBit q <;> cases hi : i.testBit q <;>
    simp [maskBit, hv, hi, actGates, RGate.act]

theorem maskBit_other {value q i r : Nat} (h : r ≠ q) :
    (actGates (maskBit value q) i).testBit r = i.testBit r := by
  cases hv : value.testBit q <;>
    simp [maskBit, hv, actGates, RGate.act, RGate.testBit_xor_of_ne h]

theorem maskBit_involutive (value q i : Nat) :
    actGates (maskBit value q) (actGates (maskBit value q) i) = i := by
  cases hv : value.testBit q <;>
    simp [maskBit, hv, actGates, RGate.act, RGate.xor_cancel]

theorem maskBit_mem {value q : Nat} {g : RGate} (h : g ∈ maskBit value q) :
    g = .x q := by
  unfold maskBit at h
  split at h
  · simp at h
  · simpa using h

theorem masks_mem {value width : Nat} {g : RGate} (h : g ∈ masks value width) :
    ∃ q, q < width ∧ g = .x q := by
  induction width with
  | zero => simp [masks] at h
  | succ width ih =>
      simp only [masks, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, hq, rfl⟩ := ih h
        exact ⟨q, by omega, rfl⟩
      · exact ⟨width, by omega, maskBit_mem h⟩

theorem masks_wellFormed (value width : Nat) :
    (masks value width).all (RGate.wellFormed (layout width).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨q, hq, rfl⟩ := masks_mem hg
  simp [layout, Layout.width, RGate.wellFormed]
  omega

theorem masks_bit_outside {value width i q : Nat} (hq : width ≤ q) :
    (actGates (masks value width) i).testBit q = i.testBit q := by
  apply testBit_actGates_of_outside
  intro g hg hwire
  obtain ⟨r, hr, rfl⟩ := masks_mem hg
  simp [RGate.wires] at hwire
  omega

theorem masks_bit {value i q : Nat} : ∀ {width}, q < width →
    (actGates (masks value width) i).testBit q =
      (i.testBit q == value.testBit q) := by
  intro width hq
  induction width with
  | zero => omega
  | succ width ih =>
      rw [masks, actGates_append]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hlt | rfl
      · rw [maskBit_other (show q ≠ width by omega), ih hlt]
      · rw [maskBit_same]
        rw [masks_bit_outside (value := value) (i := i) (Nat.le_refl _)]

theorem source_eq_value_iff (value width i : Nat) :
    source width i = value % 2 ^ width ↔
      ∀ q, q < width → i.testBit q = value.testBit q := by
  constructor
  · intro h q hq
    have hb := congrArg (fun x : Nat => x.testBit q) h
    simpa [source, layout, Layout.read, Layout.size, Layout.offset, testBit_readField,
      Nat.testBit_mod_two_pow, hq] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [source, layout, Layout.read, Layout.size, Layout.offset,
      testBit_readField, Nat.testBit_mod_two_pow]
    by_cases hq : q < width
    · simp [hq, h q hq]
    · simp [hq]

theorem masks_allSet (value width i : Nat) :
    allSet (List.range width) (actGates (masks value width) i) =
      decide (source width i = value % 2 ^ width) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, source_eq_value_iff]
  simp only [allSet, List.all_eq_true, List.mem_range]
  constructor
  · intro h q hq
    have hb := h q hq
    rw [masks_bit hq] at hb
    simpa using hb
  · intro h q hq
    rw [masks_bit hq, h q hq]
    simp

theorem masks_preserves_flag (value width i : Nat) :
    flag width (actGates (masks value width) i) = flag width i := by
  unfold flag
  apply readField_actGates_of_outside
  intro g hg q hq
  obtain ⟨r, hr, rfl⟩ := masks_mem hg
  simp [layout, Layout.offset, Layout.size, RGate.wires] at hq ⊢
  omega

theorem masks_preserves_scratch (value width i : Nat) :
    scratch width (actGates (masks value width) i) = scratch width i := by
  unfold scratch
  apply readField_actGates_of_outside
  intro g hg q hq
  obtain ⟨r, hr, rfl⟩ := masks_mem hg
  simp [layout, Layout.offset, Layout.size, RGate.wires] at hq ⊢
  omega

theorem xor_eq_writeField_toggle (i q : Nat) :
    i ^^^ (1 <<< q) = writeField i q 1 ((readField i q 1 + 1) % 2) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b = q
  · subst b
    rw [testBit_writeField_inside (Nat.le_refl q) (by omega)]
    cases hbit : i.testBit q <;>
      simp [readField_one_eq_if, hbit, Nat.one_shiftLeft, Nat.testBit_xor]
  · rw [RGate.testBit_xor_of_ne hb]
    rw [testBit_writeField_outside (by omega)]

theorem ccx_commute_xor {a b c t i : Nat}
    (hta : t ≠ a) (htb : t ≠ b) (_htc : t ≠ c) :
    RGate.act (.ccx a b c) (i ^^^ (1 <<< t)) =
      RGate.act (.ccx a b c) i ^^^ (1 <<< t) := by
  simp only [RGate.act]
  rw [RGate.testBit_xor_of_ne (Ne.symm hta),
    RGate.testBit_xor_of_ne (Ne.symm htb)]
  split
  · rw [Nat.xor_assoc, Nat.xor_comm (1 <<< t) (1 <<< c), ← Nat.xor_assoc]
  · rfl

theorem conjunction_wellFormed (controls : List Nat) (scratch target width : Nat)
    (hnodup : controls.Nodup)
    (hbelow : ∀ q ∈ controls, q < scratch)
    (htarget : target < scratch)
    (htargets : target ∉ controls)
    (hscratch : scratch ≤ width)
    (hbound : scratch + controls.length ≤ width + 2) :
    (conjunction controls scratch target).all (RGate.wellFormed width) = true := by
  induction controls, scratch, target using conjunction.induct generalizing width with
  | case1 scratch target =>
      simp [conjunction, RGate.wellFormed]
      omega
  | case2 a scratch target =>
      have ha : a < scratch := hbelow a (by simp)
      have hat : a ≠ target := by
        intro h
        exact htargets (by simp [h])
      simp [conjunction, RGate.wellFormed, hat]
      omega
  | case3 a b scratch target =>
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        not_false_eq_true, and_true, not_or] at hnodup htargets
      have ha : a < scratch := hbelow a (by simp)
      have hb : b < scratch := hbelow b (by simp)
      simp [conjunction, RGate.wellFormed, hnodup.1]
      omega
  | case4 a b c rest scratch target ih =>
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnodup htargets
      have ha : a < scratch := hbelow a (by simp)
      have hb : b < scratch := hbelow b (by simp)
      have hscratchWidth : scratch < width := by
        simp only [List.length_cons] at hbound
        omega
      have hgate : RGate.wellFormed width (.ccx a b scratch) = true := by
        simp [RGate.wellFormed, hnodup.1.1]
        omega
      have hrecNodup : (scratch :: c :: rest).Nodup := by
        rw [List.nodup_cons]
        constructor
        · intro hs
          have hlt := hbelow scratch (by simp [hs])
          omega
        · simpa only [List.nodup_cons] using hnodup.2.2
      have hrecBelow : ∀ q ∈ scratch :: c :: rest, q < scratch + 1 := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have hlt := hbelow q (by simp [hq])
          omega
      have hrecTarget : target ∉ scratch :: c :: rest := by
        intro ht
        rcases List.mem_cons.mp ht with ht | ht
        · omega
        · rcases List.mem_cons.mp ht with ht | ht
          · exact htargets.2.2.1 ht
          · exact htargets.2.2.2 ht
      have hrecBound : scratch + 1 + (scratch :: c :: rest).length ≤ width + 2 := by
        simp only [List.length_cons] at hbound ⊢
        omega
      have hrec := ih width hrecNodup hrecBelow (by omega) hrecTarget
        (by omega) hrecBound
      simp [conjunction, hgate, hrec]

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
  | case2 a scratch target =>
      have hta : target ≠ a := by simpa using htargets
      have hat : a ≠ target := Ne.symm hta
      cases ha : i.testBit a <;>
        simp [conjunction, allSet, actGates, RGate.act, ha]
  | case3 a b scratch target =>
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
        and_true, not_or] at hnodup htargets
      have hab : a ≠ b := hnodup.1
      cases ha : i.testBit a <;> cases hb : i.testBit b <;>
        simp [conjunction, allSet, actGates, RGate.act, ha, hb]
  | case4 a b c rest scratch target ih =>
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnodup htargets
      have ha : a < scratch := hbelow a (by simp)
      have hb : b < scratch := hbelow b (by simp)
      have hc : c < scratch := hbelow c (by simp)
      have hab : a ≠ b := hnodup.1.1
      have hsc : i.testBit scratch = false := hclear 0 (by simp)
      let g : RGate := .ccx a b scratch
      let j := g.act i
      have hgj : g.act j = i := by
        apply RGate.act_act (w := scratch + 1)
        simp only [g, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hab⟩, by omega⟩, by omega⟩
      have hjfuture : scratchClear (scratch :: c :: rest) (scratch + 1) j := by
        intro q hq
        have hq' : q + 1 < (a :: b :: c :: rest).length - 2 := by simp at hq ⊢; omega
        change (g.act i).testBit (scratch + 1 + q) = false
        rw [RGate.testBit_act_of_not_mem]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hclear (q + 1) hq'
        · simp [g, RGate.wires]
          omega
      have htail : (c :: rest).Nodup := by
        simpa only [List.nodup_cons] using hnodup.2.2
      have hrecNodup : (scratch :: c :: rest).Nodup := by
        rw [List.nodup_cons]
        constructor
        · intro hs
          have hlt := hbelow scratch (by simp [hs])
          omega
        · exact htail
      have hrecBelow : ∀ q ∈ scratch :: c :: rest, q < scratch + 1 := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have hlt := hbelow q (by simp [hq])
          omega
      have hrecTarget : target ∉ scratch :: c :: rest := by
        intro ht
        rcases List.mem_cons.mp ht with ht | ht
        · omega
        · rcases List.mem_cons.mp ht with ht | ht
          · exact htargets.2.2.1 ht
          · exact htargets.2.2.2 ht
      have hrec := ih j hrecNodup hrecBelow (by omega) hrecTarget hjfuture
      have hjc : j.testBit c = i.testBit c := by
        rw [show j = g.act i by rfl, RGate.testBit_act_of_not_mem]
        simp [g, RGate.wires]
        exact ⟨Ne.symm hnodup.1.2.1, Ne.symm hnodup.2.1.1, by omega⟩
      have hjrest : rest.all j.testBit = rest.all i.testBit := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        constructor <;> intro h q hq
        · have heq : j.testBit q = i.testBit q := by
            rw [show j = g.act i by rfl, RGate.testBit_act_of_not_mem]
            simp [g, RGate.wires]
            exact ⟨(by intro e; subst q; exact hnodup.1.2.2 hq),
              (by intro e; subst q; exact hnodup.2.1.2 hq), by
              have hqr := hbelow q (by simp [hq])
              omega⟩
          rw [← heq]
          exact h q hq
        · have heq : j.testBit q = i.testBit q := by
            rw [show j = g.act i by rfl, RGate.testBit_act_of_not_mem]
            simp [g, RGate.wires]
            exact ⟨(by intro e; subst q; exact hnodup.1.2.2 hq),
              (by intro e; subst q; exact hnodup.2.1.2 hq), by
              have hqr := hbelow q (by simp [hq])
              omega⟩
          rw [heq]
          exact h q hq
      have hjall : allSet (scratch :: c :: rest) j = allSet (a :: b :: c :: rest) i := by
        cases haBit : i.testBit a <;> cases hbBit : i.testBit b
        · have hj : j = i := by simp [j, g, RGate.act, haBit, hbBit]
          simp [allSet, hj, haBit, hbBit, hsc]
        · have hj : j = i := by simp [j, g, RGate.act, haBit, hbBit]
          simp [allSet, hj, haBit, hbBit, hsc]
        · have hj : j = i := by simp [j, g, RGate.act, haBit, hbBit]
          simp [allSet, hj, haBit, hbBit, hsc]
        · have hjs : j.testBit scratch = true := by
            simp [j, g, RGate.act, haBit, hbBit, hsc, Nat.one_shiftLeft,
              Nat.testBit_xor]
          simp only [allSet, List.all_cons, haBit, hbBit, Bool.true_and]
          rw [hjs, hjc, hjrest]
          simp
      simp only [conjunction, actGates_append, actGates_cons, actGates_nil]
      change g.act (actGates (conjunction (scratch :: c :: rest) (scratch + 1) target) j) = _
      rw [hrec, hjall]
      split
      · rw [ccx_commute_xor (by omega) (by omega) (by omega), hgj]
      · exact hgj

theorem conjunction_use {width i : Nat} (hscratch : scratch width i = 0) :
    actGates
        (conjunction (List.range width) (scratchOffset width) (flagWire width)) i =
      (layout width).write i 1
        ((flag width i + if allSet (List.range width) i then 1 else 0) % 2) := by
  have hclear : scratchClear (List.range width) (scratchOffset width) i := by
    intro q hq
    have hqw : q < width := by simp at hq ⊢; omega
    have hbit := congrArg (fun x : Nat => x.testBit q) hscratch
    simp [scratch, layout, Layout.read, Layout.offset, Layout.size,
      testBit_readField, hqw] at hbit
    simpa [scratchOffset, Nat.add_assoc] using hbit
  rw [conjunction_act (List.range width) (scratchOffset width) (flagWire width) i
      List.nodup_range
      (by intro q hq; simp [scratchOffset] at hq ⊢; omega)
      (by simp [flagWire, scratchOffset])
      (by simp [flagWire]) hclear]
  by_cases hall : allSet (List.range width) i
  · rw [if_pos hall, xor_eq_writeField_toggle]
    simp only [hall, if_true]
    change writeField i width 1 ((readField i width 1 + 1) % 2) =
      writeField i width 1 ((readField i width 1 + 1) % 2)
    rfl
  · have hall' : allSet (List.range width) i = false := Bool.eq_false_iff.mpr hall
    rw [if_neg hall]
    simp only [hall', Bool.false_eq_true, if_false]
    change i = writeField i width 1 ((readField i width 1 + 0) % 2)
    have hflag : readField i width 1 < 2 := by
      simpa using readField_lt i width 1
    rw [Nat.add_zero, Nat.mod_eq_of_lt hflag, writeField_read]

theorem act_gates {value width i : Nat} (hscratch : scratch width i = 0) :
    actGates (gates value width) i = out value width i := by
  let j := actGates (masks value width) i
  have hscratchJ : scratch width j = 0 := by
    rw [show scratch width j = scratch width i from
      masks_preserves_scratch value width i, hscratch]
  have huse := conjunction_use (width := width) (i := j) hscratchJ
  have houtside : ∀ g ∈ masks value width, ∀ q ∈ g.wires,
      q < flagWire width ∨ flagWire width + 1 ≤ q := by
    intro g hg q hq
    obtain ⟨r, hr, rfl⟩ := masks_mem hg
    simp [RGate.wires, flagWire] at hq ⊢
    omega
  have hrev : ∀ g ∈ (masks value width).reverse, ∀ q ∈ g.wires,
      q < flagWire width ∨ flagWire width + 1 ≤ q := by
    intro g hg
    exact houtside g (List.mem_reverse.mp hg)
  rw [gates, actGates_append, actGates_append, huse]
  change actGates (masks value width).reverse
      (writeField j (flagWire width) 1
        ((flag width j + if allSet (List.range width) j then 1 else 0) % 2)) = _
  rw [actGates_write_of_outside hrev,
    actGates_reverse (masks_wellFormed value width)]
  unfold out
  rw [masks_allSet, masks_preserves_flag]
  simp [flagWire, layout, Layout.write, Layout.offset, Layout.size]

theorem conjunction_range_wellFormed (width : Nat) :
    (conjunction (List.range width) (scratchOffset width) (flagWire width)).all
      (RGate.wellFormed (layout width).width) = true := by
  apply conjunction_wellFormed
  · exact List.nodup_range
  · intro q hq
    simp [scratchOffset] at hq ⊢
    omega
  · simp [flagWire, scratchOffset]
  · simp [flagWire]
  · simp [scratchOffset, layout, Layout.width]
  · simp [scratchOffset, layout, Layout.width]
    omega

theorem gates_wellFormed (value width : Nat) :
    (gates value width).all (RGate.wellFormed (layout width).width) = true := by
  simp [gates, masks_wellFormed, conjunction_range_wellFormed]

theorem circuit_wellFormed (value width : Nat) :
    (circuit value width).wellFormed = true := by
  exact gates_wellFormed value width

theorem act_circuit {value width i : Nat} (hscratch : scratch width i = 0) :
    act (circuit value width) i = out value width i :=
  act_gates hscratch

theorem source_out (value width i : Nat) :
    source width (out value width i) = source width i := by
  unfold source out
  rw [Layout.read_write_ne (by decide)]

theorem flag_out (value width i : Nat) :
    flag width (out value width i) =
      (flag width i + if source width i = value % 2 ^ width then 1 else 0) % 2 := by
  unfold flag out
  apply Layout.read_write_self
  simpa [layout, Layout.size] using Nat.mod_lt
    (flag width i + if source width i = value % 2 ^ width then 1 else 0)
    (by decide : 0 < 2)

theorem scratch_out (value width i : Nat) :
    scratch width (out value width i) = scratch width i := by
  unfold scratch out
  rw [Layout.read_write_ne (by decide)]

theorem act_source {value width i : Nat} (hscratch : scratch width i = 0) :
    source width (act (circuit value width) i) = source width i := by
  rw [act_circuit hscratch, source_out]

theorem act_flag {value width i : Nat} (hscratch : scratch width i = 0) :
    flag width (act (circuit value width) i) =
      (flag width i + if source width i = value % 2 ^ width then 1 else 0) % 2 := by
  rw [act_circuit hscratch, flag_out]

theorem act_scratch {value width i : Nat} (hscratch : scratch width i = 0) :
    scratch width (act (circuit value width) i) = 0 := by
  rw [act_circuit hscratch, scratch_out, hscratch]

theorem maskBit_length_le (value q : Nat) : (maskBit value q).length ≤ 1 := by
  by_cases h : value.testBit q = true <;> simp [maskBit, h]

theorem masks_length_le (value width : Nat) : (masks value width).length ≤ width := by
  induction width with
  | zero => simp [masks]
  | succ width ih =>
      rw [masks, List.length_append]
      have hbit := maskBit_length_le value width
      omega

theorem maskBit_ccx (value q : Nat) :
    (maskBit value q).countP RGate.isCcx = 0 := by
  by_cases h : value.testBit q = true <;> simp [maskBit, h, RGate.isCcx]

theorem masks_ccx (value width : Nat) :
    (masks value width).countP RGate.isCcx = 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [masks, List.countP_append, ih, maskBit_ccx]

theorem masks_eq_nil_of_all_true {value width : Nat}
    (h : ∀ q, q < width → value.testBit q = true) :
    masks value width = [] := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [masks, ih (fun q hq => h q (by omega))]
      simp [maskBit, h width (by omega)]

theorem masks_allOnes (width : Nat) :
    masks (2 ^ width - 1) width = [] := by
  apply masks_eq_nil_of_all_true
  intro q hq
  simp [Nat.testBit_two_pow_sub_one, hq]

theorem conjunction_length (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).length =
      2 * (controls.length - 2) + 1 := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction]
  | case2 a scratch target => simp [conjunction]
  | case3 a b scratch target => simp [conjunction]
  | case4 a b c rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction, ih]
      omega

theorem conjunction_ccx (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).countP RGate.isCcx =
      2 * (controls.length - 1) - 1 := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction, RGate.isCcx]
  | case2 a scratch target => simp [conjunction, RGate.isCcx]
  | case3 a b scratch target => simp [conjunction, RGate.isCcx]
  | case4 a b c rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction, RGate.isCcx, List.countP_cons, List.countP_append, ih]
      omega

theorem conjunction_cx (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).countP RGate.isCx =
      if controls.length = 1 then 1 else 0 := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction, RGate.isCx]
  | case2 a scratch target => simp [conjunction, RGate.isCx]
  | case3 a b scratch target => simp [conjunction, RGate.isCx]
  | case4 a b c rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction, RGate.isCx, List.countP_append, ih]

theorem gates_allOnes_length (width : Nat) :
    (gates (2 ^ width - 1) width).length = 2 * (width - 2) + 1 := by
  simp [gates, masks_allOnes, conjunction_length]

theorem gates_allOnes_ccx (width : Nat) :
    (gates (2 ^ width - 1) width).countP RGate.isCcx =
      2 * (width - 1) - 1 := by
  simp [gates, masks_allOnes, conjunction_ccx]

theorem gates_allOnes_cx (width : Nat) :
    (gates (2 ^ width - 1) width).countP RGate.isCx =
      if width = 1 then 1 else 0 := by
  simp [gates, masks_allOnes, conjunction_cx]

theorem conjunction_length_le (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).length ≤ 2 * controls.length + 1 := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction]
  | case2 a scratch target => simp [conjunction]
  | case3 a b scratch target => simp [conjunction]
  | case4 a b c rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction]
      omega

theorem conjunction_ccx_le (controls : List Nat) (scratch target : Nat) :
    (conjunction controls scratch target).countP RGate.isCcx ≤ 2 * controls.length := by
  induction controls, scratch, target using conjunction.induct with
  | case1 scratch target => simp [conjunction, RGate.isCcx]
  | case2 a scratch target => simp [conjunction, RGate.isCcx]
  | case3 a b scratch target => simp [conjunction, RGate.isCcx]
  | case4 a b c rest scratch target ih =>
      simp only [List.length_cons] at ih ⊢
      simp [conjunction, RGate.isCcx, List.countP_cons, List.countP_append]
      omega

theorem width_exact (value width : Nat) :
    (circuit value width).width = 2 * width + 1 := by
  simp [circuit, layout, Layout.width]
  omega

theorem gates_length_le (value width : Nat) :
    (gates value width).length ≤ 4 * width + 1 := by
  simp only [gates, List.length_append, List.length_reverse]
  have hm := masks_length_le value width
  have hc := conjunction_length_le (List.range width)
    (scratchOffset width) (flagWire width)
  simp only [List.length_range] at hc
  omega

theorem gates_ccx_le (value width : Nat) :
    (gates value width).countP RGate.isCcx ≤ 2 * width := by
  simp only [gates, List.countP_append, List.countP_reverse, masks_ccx,
    Nat.zero_add, Nat.add_zero]
  simpa using conjunction_ccx_le (List.range width)
    (scratchOffset width) (flagWire width)

theorem compiled_toffoli_le (value width : Nat) :
    VQ.Circuit.toffoliCount (compile (circuit value width)) ≤ 2 * width := by
  rw [toffoliCount_compile]
  exact gates_ccx_le value width

theorem compiled_gateCount_le (value width : Nat) :
    VQ.Circuit.gateCount (compile (circuit value width)) ≤ 8 * width + 1 := by
  rw [gateCount_compile]
  change (gates value width).length +
    2 * (gates value width).countP RGate.isCcx ≤ 8 * width + 1
  have hg := gates_length_le value width
  have ht := gates_ccx_le value width
  omega

end Selector
end Euclid
end VQ
