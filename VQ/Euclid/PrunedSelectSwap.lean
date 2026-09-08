import VQ.Euclid.SelectSwap

/-
The Euclidean step uses this total reversible selector.
The range trie emits no leaf operation for endpoints outside the physical work
range.  Its action and identity theorems match the `SelectSwap` semantic API,
while exact syntax theorems determine the resource report.
-/

namespace VQ
namespace Euclid
namespace PrunedSelectSwap

open Reversible

inductive Tree where
  | empty
  | leaf (label : Nat)
  | node (bit : Nat) (zero one : Tree)
  deriving DecidableEq, Repr

namespace Tree

def leaves : Tree → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ zero one => zero.leaves + one.leaves

def internal : Tree → Nat
  | .empty => 0
  | .leaf _ => 0
  | .node _ zero one => zero.internal + one.internal + 1

def depth : Tree → Nat
  | .empty => 0
  | .leaf _ => 0
  | .node _ zero one => Nat.max zero.depth one.depth + 1

def Valid (workWidth endpointWidth : Nat) : Tree → Prop
  | .empty => True
  | .leaf label => label < workWidth
  | .node bit zero one =>
      bit < endpointWidth ∧ zero.Valid workWidth endpointWidth ∧
        one.Valid workWidth endpointWidth

def select : Tree → Nat → Option Nat
  | .empty, _ => none
  | .leaf label, _ => some label
  | .node bit zero one, value =>
      if value.testBit bit then one.select value else zero.select value

theorem Valid.select_lt {tree : Tree} {workWidth endpointWidth value label : Nat}
    (h : tree.Valid workWidth endpointWidth)
    (hselect : tree.select value = some label) : label < workWidth := by
  induction tree with
  | empty => simp [select] at hselect
  | leaf treeLabel =>
      simp [select] at hselect
      subst label
      simpa [Valid] using h
  | node bit zero one hzero hone =>
      rcases h with ⟨_, hz, ho⟩
      simp only [select] at hselect
      split at hselect
      · exact hone ho hselect
      · exact hzero hz hselect

def childControl (workWidth endpointWidth scratchDepth : Nat) : Nat :=
  Interval.selectorScratchOffset workWidth endpointWidth + scratchDepth

def negativeAnd (ctrl selector child : Nat) : List RGate :=
  [.x selector, .ccx ctrl selector child, .x selector]

def emit (workWidth endpointWidth : Nat) : Tree → Nat → Nat → List RGate
  | .empty, _, _ => []
  | .leaf label, ctrl, _ =>
      fredkin ctrl (Interval.signWire workWidth endpointWidth)
        (Interval.sourceOffset + label)
  | .node bit zero one, ctrl, scratchDepth =>
      let selector := Interval.leftOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      let compute := negativeAnd ctrl selector child
      compute ++
        emit workWidth endpointWidth zero child (scratchDepth + 1) ++
        [.cx ctrl child] ++
        emit workWidth endpointWidth one child (scratchDepth + 1) ++
        [.cx ctrl child] ++ compute.reverse

def gates (tree : Tree) (workWidth endpointWidth : Nat) : List RGate :=
  tree.emit workWidth endpointWidth
    (Interval.outerWire workWidth endpointWidth) 0

theorem negativeAnd_ccx (ctrl selector child : Nat) :
    (negativeAnd ctrl selector child).countP RGate.isCcx = 1 := by
  rfl

theorem emit_ccx (tree : Tree) (workWidth endpointWidth ctrl scratchDepth : Nat) :
    (tree.emit workWidth endpointWidth ctrl scratchDepth).countP RGate.isCcx =
      2 * tree.internal + tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [emit, internal, leaves]
  | leaf label => simp [emit, fredkin, List.countP_cons, RGate.isCcx, internal, leaves]
  | node bit zero one hzero hone =>
      simp [emit, negativeAnd, List.countP_cons, RGate.isCcx, hzero, hone,
        internal, leaves]
      omega

theorem gates_ccx (tree : Tree) (workWidth endpointWidth : Nat) :
    (tree.gates workWidth endpointWidth).countP RGate.isCcx =
      2 * tree.internal + tree.leaves := by
  exact emit_ccx tree workWidth endpointWidth _ _

theorem emit_length (tree : Tree)
    (workWidth endpointWidth ctrl scratchDepth : Nat) :
    (tree.emit workWidth endpointWidth ctrl scratchDepth).length =
      8 * tree.internal + 3 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [emit, internal, leaves]
  | leaf label => simp [emit, fredkin, internal, leaves]
  | node bit zero one hzero hone =>
      simp [emit, negativeAnd, hzero, hone, internal, leaves]
      omega

theorem gates_length (tree : Tree) (workWidth endpointWidth : Nat) :
    (tree.gates workWidth endpointWidth).length =
      8 * tree.internal + 3 * tree.leaves := by
  exact emit_length tree workWidth endpointWidth _ _

theorem emit_cx (tree : Tree) (workWidth endpointWidth ctrl scratchDepth : Nat) :
    (tree.emit workWidth endpointWidth ctrl scratchDepth).countP RGate.isCx =
      2 * tree.internal + 2 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [emit, internal, leaves]
  | leaf label => simp [emit, fredkin, List.countP_cons, RGate.isCx, internal, leaves]
  | node bit zero one hzero hone =>
      simp [emit, negativeAnd, List.countP_cons, RGate.isCx, hzero, hone, internal, leaves]
      omega

theorem gates_cx (tree : Tree) (workWidth endpointWidth : Nat) :
    (tree.gates workWidth endpointWidth).countP RGate.isCx =
      2 * tree.internal + 2 * tree.leaves := by
  exact emit_cx tree workWidth endpointWidth _ _

theorem negativeAnd_off {ctrl selector child i : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue i ctrl = 0) :
    actGates (negativeAnd ctrl selector child) i = i := by
  have hctrlBit : i.testBit ctrl = false := by
    simpa [bitValue] using hctrl
  simp [negativeAnd, actGates, RGate.act,
    RGate.testBit_xor_of_ne hctrlSelector, hctrlBit, RGate.xor_cancel]

theorem negativeAnd_on_zero {ctrl selector child i : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue i ctrl = 1)
    (hselector : bitValue i selector = 0) :
    actGates (negativeAnd ctrl selector child) i = i ^^^ (1 <<< child) := by
  have hctrlBit : i.testBit ctrl = true := by
    simpa [bitValue] using hctrl
  have hselectorBit : i.testBit selector = false := by
    simpa [bitValue] using hselector
  have hafterCtrl : (i ^^^ (1 <<< selector)).testBit ctrl = true := by
    rw [RGate.testBit_xor_of_ne hctrlSelector, hctrlBit]
  have hafterSelector : (i ^^^ (1 <<< selector)).testBit selector = true := by
    simp [Nat.one_shiftLeft, Nat.testBit_xor, hselectorBit]
  simp only [negativeAnd, actGates, RGate.act, hafterCtrl, hafterSelector,
    Bool.true_and, if_true]
  rw [Nat.xor_assoc, Nat.xor_comm (1 <<< child) (1 <<< selector),
    ← Nat.xor_assoc, RGate.xor_cancel]

theorem negativeAnd_on_one {ctrl selector child i : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue i ctrl = 1)
    (hselector : bitValue i selector = 1) :
    actGates (negativeAnd ctrl selector child) i = i := by
  have hctrlBit : i.testBit ctrl = true := by
    simpa [bitValue] using hctrl
  have hselectorBit : i.testBit selector = true := by
    simpa [bitValue] using hselector
  have hafterCtrl : (i ^^^ (1 <<< selector)).testBit ctrl = true := by
    rw [RGate.testBit_xor_of_ne hctrlSelector, hctrlBit]
  have hafterSelector : (i ^^^ (1 <<< selector)).testBit selector = false := by
    simp [Nat.one_shiftLeft, Nat.testBit_xor, hselectorBit]
  simp only [negativeAnd, actGates, RGate.act, hafterCtrl, hafterSelector,
    Bool.true_and, Bool.false_eq_true, if_false]
  exact RGate.xor_cancel i selector

theorem cx_off {ctrl child i : Nat} (hctrl : bitValue i ctrl = 0) :
    actGates [.cx ctrl child] i = i := by
  have hctrlBit : i.testBit ctrl = false := by
    simpa [bitValue] using hctrl
  simp [actGates, RGate.act, hctrlBit]

theorem cx_on {ctrl child i : Nat} (hctrl : bitValue i ctrl = 1) :
    actGates [.cx ctrl child] i = i ^^^ (1 <<< child) := by
  have hctrlBit : i.testBit ctrl = true := by
    simpa [bitValue] using hctrl
  simp [actGates, RGate.act, hctrlBit]

theorem bitValue_xor_of_ne {i q r : Nat} (h : r ≠ q) :
    bitValue (i ^^^ (1 <<< q)) r = bitValue i r := by
  unfold bitValue
  rw [RGate.testBit_xor_of_ne h]

theorem bitValue_xor_self_zero {i q : Nat} (h : bitValue i q = 0) :
    bitValue (i ^^^ (1 <<< q)) q = 1 := by
  have hbit : i.testBit q = false := by simpa [bitValue] using h
  simp [bitValue, Nat.one_shiftLeft, Nat.testBit_xor, hbit]

theorem bitValue_xor_self_one {i q : Nat} (h : bitValue i q = 1) :
    bitValue (i ^^^ (1 <<< q)) q = 0 := by
  have hbit : i.testBit q = true := by simpa [bitValue] using h
  simp [bitValue, Nat.one_shiftLeft, Nat.testBit_xor, hbit]

theorem readField_xor_of_outside {i q off len : Nat}
    (h : q < off ∨ off + len ≤ q) :
    readField (i ^^^ (1 <<< q)) off len = readField i off len := by
  rw [Selector.xor_eq_writeField_toggle,
    readField_writeField_of_disjoint h]

theorem swapOut_bitValue_of_ne {j workWidth endpointWidth i q : Nat}
    (hqSign : q ≠ Interval.signWire workWidth endpointWidth)
    (hqSource : q ≠ Interval.sourceOffset + j) :
    bitValue (SelectSwap.swapOut j workWidth endpointWidth i) q = bitValue i q := by
  unfold SelectSwap.swapOut
  rw [bitValue_write_ne hqSource, bitValue_write_ne hqSign]

theorem swapOut_readField_of_disjoint
    {j workWidth endpointWidth i off len : Nat}
    (hsource : off + len ≤ Interval.sourceOffset + j ∨
      Interval.sourceOffset + j + 1 ≤ off)
    (hsign : off + len ≤ Interval.signWire workWidth endpointWidth ∨
      Interval.signWire workWidth endpointWidth + 1 ≤ off) :
    readField (SelectSwap.swapOut j workWidth endpointWidth i) off len =
      readField i off len := by
  unfold SelectSwap.swapOut
  rw [readField_writeField_of_disjoint (by omega),
    readField_writeField_of_disjoint (by omega)]

theorem swapOut_xor_of_outside
    {j workWidth endpointWidth i q : Nat}
    (hqSign : q ≠ Interval.signWire workWidth endpointWidth)
    (hqSource : q ≠ Interval.sourceOffset + j) :
    SelectSwap.swapOut j workWidth endpointWidth (i ^^^ (1 <<< q)) =
      SelectSwap.swapOut j workWidth endpointWidth i ^^^ (1 <<< q) := by
  unfold SelectSwap.swapOut
  rw [bitValue_xor_of_ne (q := q) (Ne.symm hqSource),
    bitValue_xor_of_ne (q := q) (Ne.symm hqSign),
    ← xor_writeField_of_outside (show q < Interval.signWire workWidth endpointWidth ∨
      Interval.signWire workWidth endpointWidth + 1 ≤ q by omega),
    ← xor_writeField_of_outside (show q < Interval.sourceOffset + j ∨
      Interval.sourceOffset + j + 1 ≤ q by omega)]

def scratchClear (workWidth endpointWidth scratchDepth count i : Nat) : Prop :=
  ∀ k, k < count →
    bitValue i
      (Interval.selectorScratchOffset workWidth endpointWidth + scratchDepth + k) = 0

theorem scratchClear_mono {workWidth endpointWidth scratchDepth m n i : Nat}
    (h : scratchClear workWidth endpointWidth scratchDepth n i)
    (hmn : m ≤ n) :
    scratchClear workWidth endpointWidth scratchDepth m i := by
  intro k hk
  exact h k (by omega)

theorem scratchClear_tail {workWidth endpointWidth scratchDepth m n i : Nat}
    (h : scratchClear workWidth endpointWidth scratchDepth (Nat.max m n + 1) i) :
    scratchClear workWidth endpointWidth (scratchDepth + 1) m i ∧
      scratchClear workWidth endpointWidth (scratchDepth + 1) n i := by
  constructor <;> intro k hk
  · have hkmax : k < Nat.max m n :=
      lt_of_lt_of_le hk (Nat.le_max_left m n)
    simpa [scratchClear, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h (k + 1) (by omega)
  · have hkmax : k < Nat.max m n :=
      lt_of_lt_of_le hk (Nat.le_max_right m n)
    simpa [scratchClear, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h (k + 1) (by omega)

theorem scratchClear_child_xor
    {workWidth endpointWidth scratchDepth count i : Nat}
    (h : scratchClear workWidth endpointWidth (scratchDepth + 1) count i) :
    scratchClear workWidth endpointWidth (scratchDepth + 1) count
      (i ^^^ (1 <<< childControl workWidth endpointWidth scratchDepth)) := by
  intro k hk
  rw [bitValue_xor_of_ne (by simp [childControl]; omega)]
  exact h k hk

theorem scratchClear_swapOut
    {j workWidth endpointWidth scratchDepth count i : Nat}
    (hj : j < workWidth)
    (h : scratchClear workWidth endpointWidth scratchDepth count i) :
    scratchClear workWidth endpointWidth scratchDepth count
      (SelectSwap.swapOut j workWidth endpointWidth i) := by
  intro k hk
  rw [swapOut_bitValue_of_ne]
  · exact h k hk
  · simp [Interval.selectorScratchOffset, Interval.signWire,
      Interval.outerWire]
    omega
  · simp [Interval.selectorScratchOffset, Interval.outerWire,
      Interval.sourceOffset]
    omega

private theorem emit_act
    {tree : Tree} {workWidth endpointWidth ctrl scratchDepth i : Nat}
    (hvalid : tree.Valid workWidth endpointWidth)
    (hdepth : scratchDepth + tree.depth ≤ endpointWidth)
    (hcontrolSource : Interval.sourceOffset + workWidth ≤ ctrl)
    (hcontrolEndpoint :
      Interval.leftOffset workWidth + endpointWidth ≤ ctrl)
    (hcontrolScratch :
      ctrl < Interval.selectorScratchOffset workWidth endpointWidth + scratchDepth)
    (hcontrolKind :
      ctrl = Interval.outerWire workWidth endpointWidth ∨
        (Interval.selectorScratchOffset workWidth endpointWidth ≤ ctrl ∧
          ctrl < Interval.selectorScratchOffset workWidth endpointWidth +
            scratchDepth))
    (hscratch : scratchClear workWidth endpointWidth scratchDepth tree.depth i) :
    actGates (tree.emit workWidth endpointWidth ctrl scratchDepth) i =
      if bitValue i ctrl = 1 then
        match tree.select
            (readField i (Interval.leftOffset workWidth) endpointWidth) with
        | none => i
        | some label => SelectSwap.swapOut label workWidth endpointWidth i
      else i := by
  induction tree generalizing ctrl scratchDepth i with
  | empty => simp [emit, select, actGates]
  | leaf label =>
      have hlabel : label < workWidth := by simpa [Valid] using hvalid
      by_cases hc : bitValue i ctrl = 1
      · rw [if_pos hc]
        simpa [emit, select, SelectSwap.swapOut] using
          fredkin_on
            (control := ctrl)
            (x := Interval.signWire workWidth endpointWidth)
            (y := Interval.sourceOffset + label)
            (i := i)
            (by simp [Interval.signWire, Interval.outerWire,
              Interval.sourceOffset]; omega)
            (by
              rcases hcontrolKind with houter | hscratch
              · subst ctrl
                simp [Interval.signWire]
              · simp [Interval.selectorScratchOffset, Interval.signWire,
                  Interval.outerWire] at hscratch ⊢
                omega)
            (by simp [Interval.sourceOffset]; omega) hc
      · have hc0 : bitValue i ctrl = 0 := by
          have := bitValue_lt i ctrl
          omega
        rw [if_neg hc]
        simpa [emit] using fredkin_off
          (control := ctrl)
          (x := Interval.signWire workWidth endpointWidth)
          (y := Interval.sourceOffset + label)
          (i := i)
          (by simp [Interval.signWire, Interval.outerWire,
            Interval.sourceOffset]; omega)
          (by
            rcases hcontrolKind with houter | hscratch
            · subst ctrl
              simp [Interval.signWire]
            · simp [Interval.selectorScratchOffset, Interval.signWire,
                Interval.outerWire] at hscratch ⊢
              omega)
          hc0
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨hbit, hzvalid, hovalid⟩
      let selector := Interval.leftOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      have hzle : zero.depth ≤ Nat.max zero.depth one.depth := Nat.le_max_left _ _
      have hole : one.depth ≤ Nat.max zero.depth one.depth := Nat.le_max_right _ _
      have hzdepth : scratchDepth + 1 + zero.depth ≤ endpointWidth := by
        simp only [depth] at hdepth
        omega
      have hodepth : scratchDepth + 1 + one.depth ≤ endpointWidth := by
        simp only [depth] at hdepth
        omega
      have hchildSource : Interval.sourceOffset + workWidth ≤ child := by
        simp [child, childControl, Interval.selectorScratchOffset,
          Interval.outerWire, Interval.sourceOffset]
        omega
      have hchildEndpoint :
          Interval.leftOffset workWidth + endpointWidth ≤ child := by
        simp [child, childControl, Interval.selectorScratchOffset,
          Interval.outerWire, Interval.leftOffset]
        omega
      have hchildScratch :
          child < Interval.selectorScratchOffset workWidth endpointWidth +
            (scratchDepth + 1) := by
        simp [child, childControl]
      have hchildKind :
          child = Interval.outerWire workWidth endpointWidth ∨
            (Interval.selectorScratchOffset workWidth endpointWidth ≤ child ∧
              child < Interval.selectorScratchOffset workWidth endpointWidth +
                (scratchDepth + 1)) := by
        right
        simp [child, childControl]
      have hctrlSelector : ctrl ≠ selector := by
        simp [selector]
        omega
      have hctrlChild : ctrl ≠ child := by
        simp [child, childControl]
        omega
      have hselectorChild : selector ≠ child := by
        simp [selector, child, childControl, Interval.selectorScratchOffset,
          Interval.leftOffset, Interval.outerWire]
        omega
      have hchild0 : bitValue i child = 0 := by
        have := hscratch 0 (by simp [depth])
        simpa [child, childControl, scratchClear] using this
      have htails := scratchClear_tail hscratch
      have hzscratch := htails.1
      have hoscratch := htails.2
      by_cases hc : bitValue i ctrl = 1
      · by_cases hs : bitValue i selector = 1
        · have hcompute := negativeAnd_on_one
            (child := child) hctrlSelector hc hs
          have hz := hzero (i := i) hzvalid hzdepth hchildSource
            hchildEndpoint hchildScratch hchildKind hzscratch
          rw [if_neg (by omega)] at hz
          have hfirstCx :
              actGates [.cx ctrl child] i = i ^^^ (1 <<< child) := cx_on hc
          have hreadXor :
              readField (i ^^^ (1 <<< child))
                  (Interval.leftOffset workWidth) endpointWidth =
                readField i (Interval.leftOffset workWidth) endpointWidth := by
            apply readField_xor_of_outside
            right
            simp [child, childControl, Interval.selectorScratchOffset,
              Interval.leftOffset, Interval.outerWire]
            omega
          have hchildOne := bitValue_xor_self_zero hchild0
          have ho := hone (i := i ^^^ (1 <<< child)) hovalid hodepth
            hchildSource hchildEndpoint hchildScratch hchildKind
            (scratchClear_child_xor hoscratch)
          rw [if_pos hchildOne, hreadXor] at ho
          have hselectOne :
              (readField i (Interval.leftOffset workWidth) endpointWidth).testBit bit =
                true := by
            have hsBit : i.testBit selector = true := by
              simpa [bitValue] using hs
            rw [testBit_readField]
            simp [hbit, selector, hsBit]
          cases hbranch : one.select
              (readField i (Interval.leftOffset workWidth) endpointWidth) with
          | none =>
              rw [hbranch] at ho
              have hsecondCx :
                  actGates [.cx ctrl child] (i ^^^ (1 <<< child)) = i := by
                rw [cx_on]
                · exact RGate.xor_cancel i child
                · rw [bitValue_xor_of_ne hctrlChild, hc]
              have hcleanup :
                  actGates (negativeAnd ctrl selector child) i = i :=
                negativeAnd_on_one (child := child) hctrlSelector hc hs
              simp only [emit, actGates_append]
              rw [hcompute, hz, hfirstCx, ho, hsecondCx]
              change actGates (negativeAnd ctrl selector child).reverse i = _
              rw [show (negativeAnd ctrl selector child).reverse =
                negativeAnd ctrl selector child by rfl, hcleanup, if_pos hc]
              simp [select, hselectOne, hbranch]
          | some label =>
              have hlabel : label < workWidth :=
                Valid.select_lt hovalid hbranch
              rw [hbranch] at ho
              change actGates (one.emit workWidth endpointWidth child
                (scratchDepth + 1)) (i ^^^ (1 <<< child)) =
                  SelectSwap.swapOut label workWidth endpointWidth
                    (i ^^^ (1 <<< child)) at ho
              have hswapXor :
                  SelectSwap.swapOut label workWidth endpointWidth
                      (i ^^^ (1 <<< child)) =
                    SelectSwap.swapOut label workWidth endpointWidth i ^^^
                      (1 <<< child) := by
                apply swapOut_xor_of_outside
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.signWire, Interval.outerWire]
                  omega
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.outerWire, Interval.sourceOffset]
                  omega
              let swapped := SelectSwap.swapOut label workWidth endpointWidth i
              have hswappedCtrl : bitValue swapped ctrl = 1 := by
                rw [swapOut_bitValue_of_ne, hc]
                · rcases hcontrolKind with houter | hscratch
                  · subst ctrl
                    simp [Interval.signWire]
                  · simp [Interval.selectorScratchOffset, Interval.signWire,
                      Interval.outerWire] at hscratch ⊢
                    omega
                · simp [Interval.sourceOffset]
                  omega
              have hswappedSelector : bitValue swapped selector = 1 := by
                rw [swapOut_bitValue_of_ne, hs]
                · simp [selector, Interval.signWire, Interval.leftOffset,
                    Interval.outerWire]
                  omega
                · simp [selector, Interval.leftOffset, Interval.sourceOffset]
                  omega
              have hsecondCx :
                  actGates [.cx ctrl child] (swapped ^^^ (1 <<< child)) =
                    swapped := by
                rw [cx_on]
                · exact RGate.xor_cancel swapped child
                · rw [bitValue_xor_of_ne hctrlChild, hswappedCtrl]
              have hcleanup :
                  actGates (negativeAnd ctrl selector child) swapped = swapped :=
                negativeAnd_on_one (child := child) hctrlSelector
                  hswappedCtrl hswappedSelector
              simp only [emit, actGates_append]
              rw [hcompute, hz, hfirstCx, ho, hswapXor, hsecondCx]
              change actGates (negativeAnd ctrl selector child).reverse swapped = _
              rw [show (negativeAnd ctrl selector child).reverse =
                negativeAnd ctrl selector child by rfl, hcleanup, if_pos hc]
              simp [select, hselectOne, hbranch, swapped]
        · have hs0 : bitValue i selector = 0 := by
            have := bitValue_lt i selector
            omega
          have hreadXor :
              readField (i ^^^ (1 <<< child))
                  (Interval.leftOffset workWidth) endpointWidth =
                readField i (Interval.leftOffset workWidth) endpointWidth := by
            apply readField_xor_of_outside
            right
            simp [child, childControl, Interval.selectorScratchOffset,
              Interval.leftOffset, Interval.outerWire]
            omega
          have hcompute := negativeAnd_on_zero (child := child)
            hctrlSelector hc hs0
          have hchildOne := bitValue_xor_self_zero hchild0
          have hz := hzero (i := i ^^^ (1 <<< child)) hzvalid hzdepth
            hchildSource hchildEndpoint hchildScratch hchildKind
            (scratchClear_child_xor hzscratch)
          rw [if_pos hchildOne, hreadXor] at hz
          have hselectZero :
              (readField i (Interval.leftOffset workWidth) endpointWidth).testBit bit =
                false := by
            have hsBit : i.testBit selector = false := by
              simpa [bitValue] using hs0
            rw [testBit_readField]
            simp [hbit, selector, hsBit]
          cases hbranch : zero.select
              (readField i (Interval.leftOffset workWidth) endpointWidth) with
          | none =>
              rw [hbranch] at hz
              have hfirstCx :
                  actGates [.cx ctrl child] (i ^^^ (1 <<< child)) = i := by
                rw [cx_on]
                · exact RGate.xor_cancel i child
                · rw [bitValue_xor_of_ne hctrlChild, hc]
              have ho := hone (i := i) hovalid hodepth hchildSource
                hchildEndpoint hchildScratch hchildKind hoscratch
              rw [if_neg (by omega)] at ho
              have hsecondCx :
                  actGates [.cx ctrl child] i = i ^^^ (1 <<< child) := cx_on hc
              have hcleanup :
                  actGates (negativeAnd ctrl selector child)
                      (i ^^^ (1 <<< child)) = i := by
                rw [negativeAnd_on_zero (child := child) hctrlSelector]
                · exact RGate.xor_cancel i child
                · rw [bitValue_xor_of_ne hctrlChild, hc]
                · rw [bitValue_xor_of_ne hselectorChild, hs0]
              simp only [emit, actGates_append]
              rw [hcompute, hz, hfirstCx, ho, hsecondCx]
              change actGates (negativeAnd ctrl selector child).reverse
                (i ^^^ (1 <<< child)) = _
              rw [show (negativeAnd ctrl selector child).reverse =
                negativeAnd ctrl selector child by rfl, hcleanup, if_pos hc]
              simp [select, hselectZero, hbranch]
          | some label =>
              have hlabel : label < workWidth :=
                Valid.select_lt hzvalid hbranch
              rw [hbranch] at hz
              change actGates (zero.emit workWidth endpointWidth child
                (scratchDepth + 1)) (i ^^^ (1 <<< child)) =
                  SelectSwap.swapOut label workWidth endpointWidth
                    (i ^^^ (1 <<< child)) at hz
              have hswapXor :
                  SelectSwap.swapOut label workWidth endpointWidth
                      (i ^^^ (1 <<< child)) =
                    SelectSwap.swapOut label workWidth endpointWidth i ^^^
                      (1 <<< child) := by
                apply swapOut_xor_of_outside
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.signWire, Interval.outerWire]
                  omega
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.outerWire, Interval.sourceOffset]
                  omega
              let swapped := SelectSwap.swapOut label workWidth endpointWidth i
              have hswappedCtrl : bitValue swapped ctrl = 1 := by
                rw [swapOut_bitValue_of_ne, hc]
                · rcases hcontrolKind with houter | hscratch
                  · subst ctrl
                    simp [Interval.signWire]
                  · simp [Interval.selectorScratchOffset, Interval.signWire,
                      Interval.outerWire] at hscratch ⊢
                    omega
                · simp [Interval.sourceOffset]
                  omega
              have hswappedChild : bitValue swapped child = 0 := by
                rw [swapOut_bitValue_of_ne, hchild0]
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.signWire, Interval.outerWire]
                  omega
                · simp [child, childControl, Interval.selectorScratchOffset,
                    Interval.outerWire, Interval.sourceOffset]
                  omega
              have hswappedSelector : bitValue swapped selector = 0 := by
                rw [swapOut_bitValue_of_ne, hs0]
                · simp [selector, Interval.signWire, Interval.leftOffset,
                    Interval.outerWire]
                  omega
                · simp [selector, Interval.leftOffset, Interval.sourceOffset]
                  omega
              have hfirstCx :
                  actGates [.cx ctrl child] (swapped ^^^ (1 <<< child)) =
                    swapped := by
                rw [cx_on]
                · exact RGate.xor_cancel swapped child
                · rw [bitValue_xor_of_ne hctrlChild, hswappedCtrl]
              have hoscratchSwapped := scratchClear_swapOut hlabel hoscratch
              have ho := hone (i := swapped) hovalid hodepth hchildSource
                hchildEndpoint hchildScratch hchildKind hoscratchSwapped
              rw [if_neg (by omega)] at ho
              have hsecondCx :
                  actGates [.cx ctrl child] swapped =
                    swapped ^^^ (1 <<< child) := cx_on hswappedCtrl
              have hcleanup :
                  actGates (negativeAnd ctrl selector child)
                      (swapped ^^^ (1 <<< child)) = swapped := by
                rw [negativeAnd_on_zero (child := child) hctrlSelector]
                · exact RGate.xor_cancel swapped child
                · rw [bitValue_xor_of_ne hctrlChild, hswappedCtrl]
                · rw [bitValue_xor_of_ne hselectorChild, hswappedSelector]
              simp only [emit, actGates_append]
              rw [hcompute, hz, hswapXor, hfirstCx, ho, hsecondCx]
              change actGates (negativeAnd ctrl selector child).reverse
                (swapped ^^^ (1 <<< child)) = _
              rw [show (negativeAnd ctrl selector child).reverse =
                negativeAnd ctrl selector child by rfl, hcleanup, if_pos hc]
              simp [select, hselectZero, hbranch, swapped]
      · have hc0 : bitValue i ctrl = 0 := by
          have := bitValue_lt i ctrl
          omega
        have hcompute := negativeAnd_off (child := child) hctrlSelector hc0
        have hz := hzero hzvalid hzdepth hchildSource hchildEndpoint
          hchildScratch hchildKind hzscratch
        have ho := hone hovalid hodepth hchildSource hchildEndpoint
          hchildScratch hchildKind hoscratch
        simp only [emit, actGates_append]
        rw [hcompute, hz, if_neg (by omega), cx_off hc0,
          ho, if_neg (by omega), cx_off hc0]
        change actGates (negativeAnd ctrl selector child).reverse i = _
        rw [show (negativeAnd ctrl selector child).reverse =
          negativeAnd ctrl selector child by rfl, hcompute, if_neg hc]

theorem gates_act {tree : Tree} {left right workWidth endpointWidth i : Nat}
    (hvalid : tree.Valid workWidth endpointWidth)
    (hdepth : tree.depth ≤ endpointWidth)
    (hstable : Interval.Stable left right workWidth endpointWidth i) :
    actGates (tree.gates workWidth endpointWidth) i =
      match tree.select
          (readField i (Interval.leftOffset workWidth) endpointWidth) with
      | none => i
      | some label => SelectSwap.swapOut label workWidth endpointWidth i := by
  have hscratch : scratchClear workWidth endpointWidth 0 tree.depth i := by
    intro k hk
    have hkWidth : k < endpointWidth := by omega
    have hbit := congrArg (fun x : Nat => x.testBit k)
      hstable.selectorScratchClear
    simp [testBit_readField, hkWidth, bitValue] at hbit ⊢
    exact hbit
  have houter :
      bitValue i (Interval.outerWire workWidth endpointWidth) = 1 := by
    simp [bitValue, hstable.outerSet]
  have hact := emit_act hvalid (by simpa using hdepth)
    (ctrl := Interval.outerWire workWidth endpointWidth)
    (scratchDepth := 0) (i := i)
    (by simp [Interval.sourceOffset, Interval.outerWire]; omega)
    (by simp [Interval.leftOffset, Interval.outerWire]; omega)
    (by simp [Interval.selectorScratchOffset])
    (Or.inl rfl) hscratch
  simpa [gates, houter] using hact

theorem gates_identity_outer_clear
    {tree : Tree} {workWidth endpointWidth i : Nat}
    (hvalid : tree.Valid workWidth endpointWidth)
    (hdepth : tree.depth ≤ endpointWidth)
    (houter : bitValue i (Interval.outerWire workWidth endpointWidth) = 0)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth i) :
    actGates (tree.gates workWidth endpointWidth) i = i := by
  have hact := emit_act hvalid (by simpa using hdepth)
    (ctrl := Interval.outerWire workWidth endpointWidth)
    (scratchDepth := 0) (i := i)
    (by simp [Interval.sourceOffset, Interval.outerWire]; omega)
    (by simp [Interval.leftOffset, Interval.outerWire]; omega)
    (by simp [Interval.selectorScratchOffset])
    (Or.inl rfl) hscratch
  simpa [gates, houter] using hact

def rangeTree (workWidth : Nat) : Nat → Nat → Tree
  | 0, base => if base < workWidth then .leaf base else .empty
  | bits + 1, base =>
      if workWidth ≤ base then .empty
      else .node bits
        (rangeTree workWidth bits base)
        (rangeTree workWidth bits (base + 2 ^ bits))

theorem rangeTree_select (workWidth bits base value : Nat) :
    (rangeTree workWidth bits base).select value =
      if base + readField value 0 bits < workWidth then
        some (base + readField value 0 bits)
      else none := by
  induction bits generalizing base with
  | zero =>
      simp only [rangeTree]
      rw [readField_size_zero]
      split <;> simp_all [select]
  | succ bits ih =>
      rw [rangeTree]
      by_cases hbase : workWidth ≤ base
      · rw [if_pos hbase]
        simp [select, show ¬base + readField value 0 (bits + 1) < workWidth by
          omega]
      · rw [if_neg hbase]
        simp only [select]
        rw [readField_high]
        by_cases hbit : value.testBit bits
        · rw [if_pos hbit, ih]
          simp [bitValue, hbit]
          congr 2 <;> omega
        · rw [if_neg hbit, ih]
          simp [bitValue, hbit]

theorem rangeTree_valid {workWidth bits base endpointWidth : Nat}
    (hbits : bits ≤ endpointWidth) :
    (rangeTree workWidth bits base).Valid workWidth endpointWidth := by
  induction bits generalizing base with
  | zero =>
      simp only [rangeTree]
      split <;> simp_all [Valid]
  | succ bits ih =>
      rw [rangeTree]
      split
      · simp [Valid]
      · simp only [Valid]
        exact ⟨by omega, ih (by omega), ih (by omega)⟩

theorem rangeTree_depth_le (workWidth bits base : Nat) :
    (rangeTree workWidth bits base).depth ≤ bits := by
  induction bits generalizing base with
  | zero =>
      simp only [rangeTree]
      split <;> simp [depth]
  | succ bits ih =>
      rw [rangeTree]
      split
      · simp [depth]
      · simp only [depth]
        exact Nat.succ_le_succ ((Nat.max_le).2
          ⟨ih base, ih (base + 2 ^ bits)⟩)

def tree (workWidth endpointWidth : Nat) : Tree :=
  rangeTree workWidth endpointWidth 0

theorem tree_valid (workWidth endpointWidth : Nat) :
    (tree workWidth endpointWidth).Valid workWidth endpointWidth :=
  rangeTree_valid (by rfl)

theorem tree_depth_le (workWidth endpointWidth : Nat) :
    (tree workWidth endpointWidth).depth ≤ endpointWidth :=
  rangeTree_depth_le workWidth endpointWidth 0

theorem tree_select (workWidth endpointWidth value : Nat)
    (hvalue : value < 2 ^ endpointWidth) :
    (tree workWidth endpointWidth).select value =
      if value < workWidth then some value else none := by
  rw [tree, rangeTree_select]
  simp [readField, Nat.mod_eq_of_lt hvalue]

private theorem emit_wellFormed
    {tree : Tree} {workWidth endpointWidth ctrl scratchDepth : Nat}
    (hvalid : tree.Valid workWidth endpointWidth)
    (hdepth : scratchDepth + tree.depth ≤ endpointWidth)
    (hcontrolTotal :
      ctrl < (Interval.layout workWidth endpointWidth).width)
    (hcontrolSource :
      Interval.sourceOffset + workWidth ≤ ctrl)
    (hcontrolEndpoint :
      Interval.leftOffset workWidth + endpointWidth ≤ ctrl)
    (hcontrolScratch :
      ctrl < Interval.selectorScratchOffset workWidth endpointWidth + scratchDepth)
    (hcontrolKind :
      ctrl = Interval.outerWire workWidth endpointWidth ∨
        (Interval.selectorScratchOffset workWidth endpointWidth ≤ ctrl ∧
          ctrl < Interval.selectorScratchOffset workWidth endpointWidth +
            scratchDepth)) :
    (tree.emit workWidth endpointWidth ctrl scratchDepth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  induction tree generalizing ctrl scratchDepth with
  | empty => rfl
  | leaf label =>
      have hlabel : label < workWidth := by simpa [Valid] using hvalid
      simp only [emit]
      apply fredkin_wellFormed
      · exact hcontrolTotal
      · rw [Interval.layout_width]
        simp [Interval.signWire, Interval.outerWire]
        omega
      · rw [Interval.layout_width]
        simp [Interval.sourceOffset]
        omega
      · simp [Interval.signWire, Interval.outerWire]
        rcases hcontrolKind with houter | hscratch
        · subst ctrl
          simp [Interval.outerWire]
        · simp [Interval.selectorScratchOffset, Interval.outerWire] at hscratch
          omega
      · simp [Interval.sourceOffset]
        omega
      · simp [Interval.signWire, Interval.outerWire,
          Interval.sourceOffset]
        omega
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨hbit, hzvalid, hovalid⟩
      have hzdepth : scratchDepth + 1 + zero.depth ≤ endpointWidth := by
        simp only [depth] at hdepth
        have hzle : zero.depth ≤ Nat.max zero.depth one.depth :=
          Nat.le_max_left _ _
        omega
      have hodepth : scratchDepth + 1 + one.depth ≤ endpointWidth := by
        simp only [depth] at hdepth
        have hole : one.depth ≤ Nat.max zero.depth one.depth :=
          Nat.le_max_right _ _
        omega
      have hscratch : scratchDepth < endpointWidth := by
        simp only [depth] at hdepth
        omega
      let selector := Interval.leftOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      let compute := negativeAnd ctrl selector child
      have hchildTotal : child < (Interval.layout workWidth endpointWidth).width := by
        rw [Interval.layout_width]
        simp [child, childControl, Interval.selectorScratchOffset,
          Interval.outerWire]
        omega
      have hchildSource : Interval.sourceOffset + workWidth ≤ child := by
        simp [child, childControl, Interval.selectorScratchOffset,
          Interval.outerWire, Interval.sourceOffset]
        omega
      have hchildEndpoint :
          Interval.leftOffset workWidth + endpointWidth ≤ child := by
        simp [child, childControl, Interval.selectorScratchOffset,
          Interval.outerWire, Interval.leftOffset]
        omega
      have hchildScratch :
          child < Interval.selectorScratchOffset workWidth endpointWidth +
            (scratchDepth + 1) := by
        simp [child, childControl]
      have hchildKind :
          child = Interval.outerWire workWidth endpointWidth ∨
            (Interval.selectorScratchOffset workWidth endpointWidth ≤ child ∧
              child < Interval.selectorScratchOffset workWidth endpointWidth +
                (scratchDepth + 1)) := by
        right
        simp [child, childControl]
      have hcompute : compute.all
          (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
        have hselectorTotal :
            selector < (Interval.layout workWidth endpointWidth).width := by
          rw [Interval.layout_width]
          simp [selector, Interval.leftOffset]
          omega
        have hctrlSelector : ctrl ≠ selector := by
          simp [selector]
          omega
        have hselectorChild : selector ≠ child := by
          simp [selector, child, childControl,
            Interval.selectorScratchOffset, Interval.leftOffset,
            Interval.outerWire]
          omega
        have hctrlChild : ctrl ≠ child := by
          simp [child, childControl]
          omega
        simp [compute, negativeAnd, RGate.wellFormed, hselectorTotal,
          hcontrolTotal, hchildTotal, hctrlSelector, hselectorChild, hctrlChild]
      have hcx : ([.cx ctrl child] : List RGate).all
          (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
        simp only [List.all_cons, List.all_nil, Bool.and_true, RGate.wellFormed,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hcontrolTotal, hchildTotal⟩, by
          simp [child, childControl]
          omega⟩
      have hzwf := hzero hzvalid hzdepth hchildTotal hchildSource
        hchildEndpoint hchildScratch hchildKind
      have howf := hone hovalid hodepth hchildTotal hchildSource
        hchildEndpoint hchildScratch hchildKind
      have hcomputeReverse : compute.reverse.all
          (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
        simpa using hcompute
      change (compute ++ zero.emit workWidth endpointWidth child
        (scratchDepth + 1) ++ [RGate.cx ctrl child] ++
        one.emit workWidth endpointWidth child (scratchDepth + 1) ++
        [RGate.cx ctrl child] ++ compute.reverse).all
          (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true
      simp only [List.all_append, hcompute, hzwf, hcx, howf,
        hcomputeReverse, Bool.and_self]

theorem gates_wellFormed {tree : Tree} {workWidth endpointWidth : Nat}
    (hvalid : tree.Valid workWidth endpointWidth)
    (hdepth : tree.depth ≤ endpointWidth) :
    (tree.gates workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  apply emit_wellFormed hvalid (by simpa using hdepth)
  · rw [Interval.layout_width]
    simp [Interval.outerWire]
    omega
  · simp [Interval.sourceOffset, Interval.outerWire]
    omega
  · simp [Interval.leftOffset, Interval.outerWire]
    omega
  · simp [Interval.selectorScratchOffset]
  · left
    rfl

end Tree

def gates (workWidth endpointWidth : Nat) : List RGate :=
  (Tree.tree workWidth endpointWidth).gates workWidth endpointWidth

def circuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width,
    gates := gates workWidth endpointWidth }

def gateBound (workWidth endpointWidth : Nat) : Nat :=
  8 * (Tree.tree workWidth endpointWidth).internal +
    3 * (Tree.tree workWidth endpointWidth).leaves

def ccxBound (workWidth endpointWidth : Nat) : Nat :=
  2 * (Tree.tree workWidth endpointWidth).internal +
    (Tree.tree workWidth endpointWidth).leaves

def cxBound (workWidth endpointWidth : Nat) : Nat :=
  2 * (Tree.tree workWidth endpointWidth).internal +
    2 * (Tree.tree workWidth endpointWidth).leaves

theorem gates_act {left right workWidth endpointWidth i : Nat}
    (_hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hstable : Interval.Stable left right workWidth endpointWidth i)
    (_haccumulator : bitValue i
      (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) i =
      if left < workWidth then SelectSwap.swapOut left workWidth endpointWidth i
      else i := by
  have hleft : left < 2 ^ endpointWidth := by
    rw [← hstable.leftValue]
    exact readField_lt i (Interval.leftOffset workWidth) endpointWidth
  have haction := Tree.gates_act
    (Tree.tree_valid workWidth endpointWidth)
    (Tree.tree_depth_le workWidth endpointWidth) hstable
  rw [hstable.leftValue,
    Tree.tree_select workWidth endpointWidth left hleft] at haction
  by_cases hin : left < workWidth
  · simpa [gates, hin] using haction
  · simpa [gates, hin] using haction

theorem gates_identity_of_outer_clear
    {workWidth endpointWidth i : Nat}
    (houter : i.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (_haccumulator : bitValue i
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (_hleftFlag : bitValue i
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hselector : readField i
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0) :
    actGates (gates workWidth endpointWidth) i = i := by
  apply Tree.gates_identity_outer_clear
    (Tree.tree_valid workWidth endpointWidth)
    (Tree.tree_depth_le workWidth endpointWidth)
  · simp [bitValue, houter]
  · intro k hk
    have hkWidth : k < endpointWidth :=
      lt_of_lt_of_le hk (Tree.tree_depth_le workWidth endpointWidth)
    have hbit := congrArg (fun x : Nat => x.testBit k) hselector
    simp [testBit_readField, hkWidth, bitValue] at hbit ⊢
    exact hbit

theorem circuit_wellFormed (workWidth endpointWidth : Nat) :
    (circuit workWidth endpointWidth).wellFormed = true := by
  exact Tree.gates_wellFormed
    (Tree.tree_valid workWidth endpointWidth)
    (Tree.tree_depth_le workWidth endpointWidth)

theorem gates_length (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).length = gateBound workWidth endpointWidth :=
  Tree.gates_length (Tree.tree workWidth endpointWidth) workWidth endpointWidth

theorem gates_ccx (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx =
      ccxBound workWidth endpointWidth :=
  Tree.gates_ccx (Tree.tree workWidth endpointWidth) workWidth endpointWidth

theorem gates_cx (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCx =
      cxBound workWidth endpointWidth :=
  Tree.gates_cx (Tree.tree workWidth endpointWidth) workWidth endpointWidth

theorem width259_gateBound : gateBound 259 9 = 2897 := by
  decide

theorem width259_ccxBound : ccxBound 259 9 = 789 := by
  decide

theorem width259_cxBound : cxBound 259 9 = 1048 := by
  decide

end PrunedSelectSwap
end Euclid
end VQ
