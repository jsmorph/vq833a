/-
The prepared-boundary prefix arithmetic from the current Luo companion source.
-/
import VQ.Euclid.IntervalNoSign
import VQ.Euclid.PrunedSelectSwap

namespace VQ.Euclid.LuoPrefixArithmetic

open Reversible

abbrev Tree := PrunedSelectSwap.Tree

namespace Tree

def RangeValid (start workWidth endpointWidth : Nat) : Tree → Prop
  | .empty => True
  | .leaf label => start ≤ label ∧ label < start + workWidth
  | .node bit zero one =>
      bit < endpointWidth ∧
        RangeValid start workWidth endpointWidth zero ∧
        RangeValid start workWidth endpointWidth one

def labels : Tree → List Nat
  | .empty => []
  | .leaf label => [label]
  | .node _ zero one => labels zero ++ labels one

theorem select_mem_labels
    {tree : Tree} {boundary label : Nat}
    (hselect : tree.select boundary = some label) : label ∈ labels tree := by
  induction tree with
  | empty => simp [PrunedSelectSwap.Tree.select] at hselect
  | leaf treeLabel =>
      simp [PrunedSelectSwap.Tree.select] at hselect
      subst label
      simp [labels]
  | node bit zero one hzero hone =>
      simp only [PrunedSelectSwap.Tree.select] at hselect
      by_cases hbit : boundary.testBit bit
      · rw [if_pos hbit] at hselect
        simp [labels, hone hselect]
      · rw [if_neg hbit] at hselect
        simp [labels, hzero hselect]

end Tree

def layout (workWidth endpointWidth scratchWidth : Nat) : Layout :=
  [1, 1, workWidth, workWidth, endpointWidth, scratchWidth, 1, 1, 1]

def outerWire : Nat := 0
def signWire : Nat := 1
def sourceOffset : Nat := 2
def targetOffset (workWidth : Nat) : Nat := 2 + workWidth
def boundaryOffset (workWidth : Nat) : Nat := 2 + 2 * workWidth
def scratchOffset (workWidth endpointWidth : Nat) : Nat :=
  boundaryOffset workWidth + endpointWidth
def carryWire (workWidth endpointWidth scratchWidth : Nat) : Nat :=
  scratchOffset workWidth endpointWidth + scratchWidth
def accumulatorWire (workWidth endpointWidth scratchWidth : Nat) : Nat :=
  carryWire workWidth endpointWidth scratchWidth + 1
def cellScratchWire (workWidth endpointWidth scratchWidth : Nat) : Nat :=
  carryWire workWidth endpointWidth scratchWidth + 2

def childControl
    (workWidth endpointWidth scratchDepth : Nat) : Nat :=
  scratchOffset workWidth endpointWidth + scratchDepth

def negativeAnd (ctrl selector child : Nat) : List RGate :=
  [.x selector, .ccx ctrl selector child, .x selector]

theorem RGate.act_xor_of_not_mem
    {g : RGate} {q I : Nat} (hq : q ∉ g.wires) :
    g.act (I ^^^ (1 <<< q)) = g.act I ^^^ (1 <<< q) := by
  cases g with
  | x r =>
      have hqr : q ≠ r := by simpa [RGate.wires] using hq
      simp only [RGate.act]
      rw [Nat.xor_assoc, Nat.xor_comm (1 <<< q) (1 <<< r), ← Nat.xor_assoc]
  | cx a b =>
      have hab : q ≠ a ∧ q ≠ b := by simpa [RGate.wires] using hq
      simp only [RGate.act, RGate.testBit_xor_of_ne hab.1.symm]
      split
      · rw [Nat.xor_assoc, Nat.xor_comm (1 <<< q) (1 <<< b), ← Nat.xor_assoc]
      · rfl
  | ccx a b c =>
      have habc : q ≠ a ∧ q ≠ b ∧ q ≠ c := by
        simpa [RGate.wires] using hq
      simp only [RGate.act, RGate.testBit_xor_of_ne habc.1.symm,
        RGate.testBit_xor_of_ne habc.2.1.symm]
      split
      · rw [Nat.xor_assoc, Nat.xor_comm (1 <<< q) (1 <<< c), ← Nat.xor_assoc]
      · rfl

theorem actGates_xor_of_outside
    {gs : List RGate} {q I : Nat} (hq : ∀ g ∈ gs, q ∉ g.wires) :
    actGates gs (I ^^^ (1 <<< q)) = actGates gs I ^^^ (1 <<< q) := by
  induction gs generalizing I with
  | nil => rfl
  | cons g gs ih =>
      rw [actGates_cons, RGate.act_xor_of_not_mem (hq g List.mem_cons_self),
        ih (fun g' hg' => hq g' (List.mem_cons_of_mem g hg')), actGates_cons]

def cellWiring
    (position workWidth endpointWidth scratchWidth : Nat) : Wiring :=
  CellPlaced.wiring (targetOffset workWidth + position)
    (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def RoutingWire
    (workWidth endpointWidth scratchWidth q : Nat) : Prop :=
  q < sourceOffset ∨
    boundaryOffset workWidth ≤ q ∧
      q < carryWire workWidth endpointWidth scratchWidth

def majAt
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.majGates
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def umaAt
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.umaGates
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def firstEmit
    (start workWidth endpointWidth scratchWidth : Nat) :
    Tree → Nat → Nat → List RGate
  | .empty, _, _ => []
  | .leaf label, ctrl, _ =>
      majAt (label - start) workWidth endpointWidth scratchWidth ++
        [.cx ctrl (accumulatorWire workWidth endpointWidth scratchWidth)]
  | .node bit zero one, ctrl, scratchDepth =>
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      let compute := negativeAnd ctrl selector child
      compute ++
        firstEmit start workWidth endpointWidth scratchWidth zero child
          (scratchDepth + 1) ++
        [.cx ctrl child] ++
        firstEmit start workWidth endpointWidth scratchWidth one child
          (scratchDepth + 1) ++
        [.cx ctrl child] ++ compute.reverse

def secondEmit
    (start workWidth endpointWidth scratchWidth : Nat) :
    Tree → Nat → Nat → List RGate
  | .empty, _, _ => []
  | .leaf label, ctrl, _ =>
      [.cx ctrl (accumulatorWire workWidth endpointWidth scratchWidth)] ++
        umaAt (label - start) workWidth endpointWidth scratchWidth
  | .node bit zero one, ctrl, scratchDepth =>
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      let compute := negativeAnd ctrl selector child
      compute ++ [.cx ctrl child] ++
        secondEmit start workWidth endpointWidth scratchWidth one child
          (scratchDepth + 1) ++
        [.cx ctrl child] ++
        secondEmit start workWidth endpointWidth scratchWidth zero child
          (scratchDepth + 1) ++ compute.reverse

def flatFirst
    (start workWidth endpointWidth scratchWidth boundary : Nat) :
    Tree → Bool → List RGate
  | .empty, _ => []
  | .leaf label, enabled =>
      majAt (label - start) workWidth endpointWidth scratchWidth ++
        if enabled then
          [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
        else []
  | .node bit zero one, enabled =>
      flatFirst start workWidth endpointWidth scratchWidth boundary zero
          (enabled && !boundary.testBit bit) ++
        flatFirst start workWidth endpointWidth scratchWidth boundary one
          (enabled && boundary.testBit bit)

def flatSecond
    (start workWidth endpointWidth scratchWidth boundary : Nat) :
    Tree → Bool → List RGate
  | .empty, _ => []
  | .leaf label, enabled =>
      (if enabled then
          [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
        else []) ++
        umaAt (label - start) workWidth endpointWidth scratchWidth
  | .node bit zero one, enabled =>
      flatSecond start workWidth endpointWidth scratchWidth boundary one
          (enabled && boundary.testBit bit) ++
      flatSecond start workWidth endpointWidth scratchWidth boundary zero
          (enabled && !boundary.testBit bit)

def firstLabelScan
    (start workWidth endpointWidth scratchWidth : Nat) :
    List Nat → Option Nat → List RGate
  | [], _ => []
  | label :: labels, selected =>
      majAt (label - start) workWidth endpointWidth scratchWidth ++
        (if selected = some label then
          [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
        else []) ++
        firstLabelScan start workWidth endpointWidth scratchWidth labels selected

def secondLabelScan
    (start workWidth endpointWidth scratchWidth : Nat) :
    List Nat → Option Nat → List RGate
  | [], _ => []
  | label :: labels, selected =>
      (if selected = some label then
          [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
        else []) ++
        umaAt (label - start) workWidth endpointWidth scratchWidth ++
        secondLabelScan start workWidth endpointWidth scratchWidth labels selected

theorem firstLabelScan_append
    (start workWidth endpointWidth scratchWidth : Nat)
    (left right : List Nat) (selected : Option Nat) :
    firstLabelScan start workWidth endpointWidth scratchWidth
        (left ++ right) selected =
      firstLabelScan start workWidth endpointWidth scratchWidth left selected ++
        firstLabelScan start workWidth endpointWidth scratchWidth right selected := by
  induction left with
  | nil => rfl
  | cons label labels ih =>
      simp [firstLabelScan, ih, List.append_assoc]

theorem secondLabelScan_append
    (start workWidth endpointWidth scratchWidth : Nat)
    (left right : List Nat) (selected : Option Nat) :
    secondLabelScan start workWidth endpointWidth scratchWidth
        (left ++ right) selected =
      secondLabelScan start workWidth endpointWidth scratchWidth left selected ++
        secondLabelScan start workWidth endpointWidth scratchWidth right selected := by
  induction left with
  | nil => rfl
  | cons label labels ih =>
      simp [secondLabelScan, ih, List.append_assoc]

theorem firstLabelScan_some_eq_none
    {start workWidth endpointWidth scratchWidth selected : Nat}
    {labels : List Nat} (hselected : selected ∉ labels) :
    firstLabelScan start workWidth endpointWidth scratchWidth labels (some selected) =
      firstLabelScan start workWidth endpointWidth scratchWidth labels none := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.mem_cons, not_or] at hselected
      simp [firstLabelScan, hselected.1, ih hselected.2]

theorem secondLabelScan_some_eq_none
    {start workWidth endpointWidth scratchWidth selected : Nat}
    {labels : List Nat} (hselected : selected ∉ labels) :
    secondLabelScan start workWidth endpointWidth scratchWidth labels (some selected) =
      secondLabelScan start workWidth endpointWidth scratchWidth labels none := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      simp only [List.mem_cons, not_or] at hselected
      simp [secondLabelScan, hselected.1, ih hselected.2]

theorem flatFirst_eq_firstLabelScan
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {enabled : Bool} (hnodup : (Tree.labels tree).Nodup) :
    flatFirst start workWidth endpointWidth scratchWidth boundary tree enabled =
      firstLabelScan start workWidth endpointWidth scratchWidth (Tree.labels tree)
        (if enabled then tree.select boundary else none) := by
  induction tree generalizing enabled with
  | empty => simp [flatFirst, firstLabelScan, Tree.labels]
  | leaf label =>
      cases enabled <;>
        simp [flatFirst, firstLabelScan, Tree.labels,
          PrunedSelectSwap.Tree.select]
  | node bit zero one hzero hone =>
      have hn := List.nodup_append.mp hnodup
      cases enabled with
      | false =>
          simp [flatFirst, Tree.labels, firstLabelScan_append,
            hzero (enabled := false) hn.1, hone (enabled := false) hn.2.1]
      | true =>
          by_cases hbit : boundary.testBit bit
          · calc
              flatFirst start workWidth endpointWidth scratchWidth boundary
                  (.node bit zero one) true =
                firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero) none ++
                  firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one) (one.select boundary) := by
                    simp [flatFirst, hbit, hzero (enabled := false) hn.1,
                      hone (enabled := true) hn.2.1]
              _ = firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero) (one.select boundary) ++
                  firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one) (one.select boundary) := by
                    cases hselect : one.select boundary with
                    | none => rfl
                    | some selected =>
                        have hmem := Tree.select_mem_labels hselect
                        have hnot : selected ∉ Tree.labels zero := by
                          intro hzmem
                          exact hn.2.2 selected hzmem selected hmem rfl
                        rw [firstLabelScan_some_eq_none hnot]
              _ = firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels (PrunedSelectSwap.Tree.node bit zero one))
                    ((PrunedSelectSwap.Tree.node bit zero one).select boundary) := by
                    rw [Tree.labels, firstLabelScan_append]
                    simp [PrunedSelectSwap.Tree.select, hbit]
          · calc
              flatFirst start workWidth endpointWidth scratchWidth boundary
                  (.node bit zero one) true =
                firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero) (zero.select boundary) ++
                  firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one) none := by
                    simp [flatFirst, hbit, hzero (enabled := true) hn.1,
                      hone (enabled := false) hn.2.1]
              _ = firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero) (zero.select boundary) ++
                  firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one) (zero.select boundary) := by
                    cases hselect : zero.select boundary with
                    | none => rfl
                    | some selected =>
                        have hmem := Tree.select_mem_labels hselect
                        have hnot : selected ∉ Tree.labels one := by
                          intro homem
                          exact hn.2.2 selected hmem selected homem rfl
                        rw [firstLabelScan_some_eq_none hnot]
              _ = firstLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels (PrunedSelectSwap.Tree.node bit zero one))
                    ((PrunedSelectSwap.Tree.node bit zero one).select boundary) := by
                    rw [Tree.labels, firstLabelScan_append]
                    simp [PrunedSelectSwap.Tree.select, hbit]

theorem flatSecond_eq_secondLabelScan
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {enabled : Bool} (hnodup : (Tree.labels tree).Nodup) :
    flatSecond start workWidth endpointWidth scratchWidth boundary tree enabled =
      secondLabelScan start workWidth endpointWidth scratchWidth
        (Tree.labels tree).reverse
        (if enabled then tree.select boundary else none) := by
  induction tree generalizing enabled with
  | empty => simp [flatSecond, secondLabelScan, Tree.labels]
  | leaf label =>
      cases enabled <;>
        simp [flatSecond, secondLabelScan, Tree.labels,
          PrunedSelectSwap.Tree.select]
  | node bit zero one hzero hone =>
      have hn := List.nodup_append.mp hnodup
      cases enabled with
      | false =>
          simp [flatSecond, Tree.labels, List.reverse_append,
            secondLabelScan_append, hzero (enabled := false) hn.1,
            hone (enabled := false) hn.2.1]
      | true =>
          by_cases hbit : boundary.testBit bit
          · calc
              flatSecond start workWidth endpointWidth scratchWidth boundary
                  (.node bit zero one) true =
                secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one).reverse (one.select boundary) ++
                  secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero).reverse none := by
                    simp [flatSecond, hbit, hzero (enabled := false) hn.1,
                      hone (enabled := true) hn.2.1]
              _ = secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one).reverse (one.select boundary) ++
                  secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero).reverse (one.select boundary) := by
                    cases hselect : one.select boundary with
                    | none => rfl
                    | some selected =>
                        have hmem := Tree.select_mem_labels hselect
                        have hnot : selected ∉ (Tree.labels zero).reverse := by
                          simpa using (show selected ∉ Tree.labels zero by
                            intro hzmem
                            exact hn.2.2 selected hzmem selected hmem rfl)
                        rw [secondLabelScan_some_eq_none hnot]
              _ = secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels
                      (PrunedSelectSwap.Tree.node bit zero one)).reverse
                    ((PrunedSelectSwap.Tree.node bit zero one).select boundary) := by
                    rw [Tree.labels, List.reverse_append, secondLabelScan_append]
                    simp [PrunedSelectSwap.Tree.select, hbit]

          · calc
              flatSecond start workWidth endpointWidth scratchWidth boundary
                  (.node bit zero one) true =
                secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one).reverse none ++
                  secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero).reverse (zero.select boundary) := by
                    simp [flatSecond, hbit, hzero (enabled := true) hn.1,
                      hone (enabled := false) hn.2.1]
              _ = secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels one).reverse (zero.select boundary) ++
                  secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels zero).reverse (zero.select boundary) := by
                    cases hselect : zero.select boundary with
                    | none => rfl
                    | some selected =>
                        have hmem := Tree.select_mem_labels hselect
                        have hnot : selected ∉ (Tree.labels one).reverse := by
                          simpa using (show selected ∉ Tree.labels one by
                            intro homem
                            exact hn.2.2 selected hmem selected homem rfl)
                        rw [secondLabelScan_some_eq_none hnot]
              _ = secondLabelScan start workWidth endpointWidth scratchWidth
                    (Tree.labels
                      (PrunedSelectSwap.Tree.node bit zero one)).reverse
                    ((PrunedSelectSwap.Tree.node bit zero one).select boundary) := by
                    rw [Tree.labels, List.reverse_append, secondLabelScan_append]
                    simp [PrunedSelectSwap.Tree.select, hbit]

theorem flatFirst_eq_contiguousScan
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    (hnodup : (Tree.labels tree).Nodup)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary) :
    flatFirst start workWidth endpointWidth scratchWidth boundary tree true =
      firstLabelScan start workWidth endpointWidth scratchWidth
        (List.range' start workWidth) (some boundary) := by
  rw [flatFirst_eq_firstLabelScan hnodup, if_pos rfl, hlabels, hselect]

theorem flatSecond_eq_contiguousScan
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    (hnodup : (Tree.labels tree).Nodup)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary) :
    flatSecond start workWidth endpointWidth scratchWidth boundary tree true =
      secondLabelScan start workWidth endpointWidth scratchWidth
        (List.range' start workWidth).reverse (some boundary) := by
  rw [flatSecond_eq_secondLabelScan hnodup, if_pos rfl, hlabels, hselect]

def signUpdateGates
    (workWidth endpointWidth scratchWidth : Nat) (updateSign : Bool) :
    List RGate :=
  if updateSign then
    [.cx (carryWire workWidth endpointWidth scratchWidth) signWire]
  else []

def addGates
    (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  [.cx outerWire (accumulatorWire workWidth endpointWidth scratchWidth)] ++
    firstEmit start workWidth endpointWidth scratchWidth tree outerWire 0 ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0 ++
    [.cx outerWire (accumulatorWire workWidth endpointWidth scratchWidth)]

def contiguousAddGates
    (start workWidth endpointWidth scratchWidth boundary : Nat)
    (updateSign : Bool) : List RGate :=
  [.x (accumulatorWire workWidth endpointWidth scratchWidth)] ++
    firstLabelScan start workWidth endpointWidth scratchWidth
      (List.range' start workWidth) (some boundary) ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    secondLabelScan start workWidth endpointWidth scratchWidth
      (List.range' start workWidth).reverse (some boundary) ++
    [.x (accumulatorWire workWidth endpointWidth scratchWidth)]

def subGates
    (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  (addGates tree start workWidth endpointWidth scratchWidth false).reverse

def scratchClear
    (workWidth endpointWidth scratchDepth count I : Nat) : Prop :=
  ∀ k, k < count →
    bitValue I (scratchOffset workWidth endpointWidth + scratchDepth + k) = 0

theorem scratchClear_tail
    {workWidth endpointWidth scratchDepth m n I : Nat}
    (h : scratchClear workWidth endpointWidth scratchDepth (Nat.max m n + 1) I) :
    scratchClear workWidth endpointWidth (scratchDepth + 1) m I ∧
      scratchClear workWidth endpointWidth (scratchDepth + 1) n I := by
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
    {workWidth endpointWidth scratchDepth count I : Nat}
    (h : scratchClear workWidth endpointWidth (scratchDepth + 1) count I) :
    scratchClear workWidth endpointWidth (scratchDepth + 1) count
      (I ^^^ (1 <<< childControl workWidth endpointWidth scratchDepth)) := by
  intro k hk
  rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne
    (by simp [childControl]; omega)]
  exact h k hk

theorem layout_width (workWidth endpointWidth scratchWidth : Nat) :
    (layout workWidth endpointWidth scratchWidth).width =
      2 * workWidth + endpointWidth + scratchWidth + 5 := by
  simp [layout, Layout.width]
  omega

theorem negativeAnd_eq_pruned (ctrl selector child : Nat) :
    negativeAnd ctrl selector child =
      PrunedSelectSwap.Tree.negativeAnd ctrl selector child := rfl

theorem negativeAnd_off {ctrl selector child I : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue I ctrl = 0) :
    actGates (negativeAnd ctrl selector child) I = I := by
  exact PrunedSelectSwap.Tree.negativeAnd_off hctrlSelector hctrl

theorem negativeAnd_on_zero {ctrl selector child I : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue I ctrl = 1)
    (hselector : bitValue I selector = 0) :
    actGates (negativeAnd ctrl selector child) I = I ^^^ (1 <<< child) := by
  exact PrunedSelectSwap.Tree.negativeAnd_on_zero hctrlSelector hctrl hselector

theorem negativeAnd_on_one {ctrl selector child I : Nat}
    (hctrlSelector : ctrl ≠ selector)
    (hctrl : bitValue I ctrl = 1)
    (hselector : bitValue I selector = 1) :
    actGates (negativeAnd ctrl selector child) I = I := by
  exact PrunedSelectSwap.Tree.negativeAnd_on_one hctrlSelector hctrl hselector

theorem cx_off {ctrl child I : Nat} (hctrl : bitValue I ctrl = 0) :
    actGates [.cx ctrl child] I = I :=
  PrunedSelectSwap.Tree.cx_off hctrl

theorem cx_on {ctrl child I : Nat} (hctrl : bitValue I ctrl = 1) :
    actGates [.cx ctrl child] I = I ^^^ (1 <<< child) :=
  PrunedSelectSwap.Tree.cx_on hctrl

theorem bitValue_xor_of_ne {I q r : Nat} (h : r ≠ q) :
    bitValue (I ^^^ (1 <<< q)) r = bitValue I r :=
  PrunedSelectSwap.Tree.bitValue_xor_of_ne h

theorem bitValue_xor_self_zero {I q : Nat} (h : bitValue I q = 0) :
    bitValue (I ^^^ (1 <<< q)) q = 1 :=
  PrunedSelectSwap.Tree.bitValue_xor_self_zero h

theorem bitValue_xor_self_one {I q : Nat} (h : bitValue I q = 1) :
    bitValue (I ^^^ (1 <<< q)) q = 0 :=
  PrunedSelectSwap.Tree.bitValue_xor_self_one h

theorem readField_xor_of_outside {I q off len : Nat}
    (h : q < off ∨ off + len ≤ q) :
    readField (I ^^^ (1 <<< q)) off len = readField I off len :=
  PrunedSelectSwap.Tree.readField_xor_of_outside h

theorem placeCell_ne_routing
    {position workWidth endpointWidth scratchWidth q r : Nat}
    (hposition : position < workWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q)
    (hr : r < 5) :
    place CellPlaced.layout
        (cellWiring position workWidth endpointWidth scratchWidth) r ≠ q := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr' with rfl | rfl | rfl | rfl | rfl <;>
    simp [cellWiring, CellPlaced.layout, CellPlaced.wiring, place,
      targetOffset, sourceOffset, carryWire, accumulatorWire,
      cellScratchWire, scratchOffset, boundaryOffset, RoutingWire] at hq ⊢ <;>
    omega

theorem routing_ne_accumulator
    {workWidth endpointWidth scratchWidth q : Nat}
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    q ≠ accumulatorWire workWidth endpointWidth scratchWidth := by
  simp [RoutingWire, accumulatorWire, carryWire, scratchOffset,
    boundaryOffset, sourceOffset] at hq ⊢
  omega

theorem cellGates_avoid_routing
    {gs : List RGate} {position workWidth endpointWidth scratchWidth q : Nat}
    (hwf : gs.all (RGate.wellFormed 5) = true)
    (hposition : position < workWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    ∀ g ∈
      CellPlaced.gates gs
        (targetOffset workWidth + position) (sourceOffset + position)
        (carryWire workWidth endpointWidth scratchWidth)
        (accumulatorWire workWidth endpointWidth scratchWidth)
        (cellScratchWire workWidth endpointWidth scratchWidth),
      q ∉ g.wires := by
  intro g hg hqmem
  obtain ⟨gate, hgate, rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hqmem
  obtain ⟨r, hr, heq⟩ := hqmem
  have hrlt : r < 5 := by
    have hgateWf := List.all_eq_true.mp hwf gate hgate
    cases gate <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega
  exact placeCell_ne_routing hposition hq hrlt heq

theorem cellGates_preserve_routing
    {gs : List RGate} {position workWidth endpointWidth scratchWidth q I : Nat}
    (hwf : gs.all (RGate.wellFormed 5) = true)
    (hposition : position < workWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    bitValue
        (actGates
          (CellPlaced.gates gs
            (targetOffset workWidth + position) (sourceOffset + position)
            (carryWire workWidth endpointWidth scratchWidth)
            (accumulatorWire workWidth endpointWidth scratchWidth)
            (cellScratchWire workWidth endpointWidth scratchWidth)) I)
        q = bitValue I q := by
  have htest :
      (actGates
          (CellPlaced.gates gs
            (targetOffset workWidth + position) (sourceOffset + position)
            (carryWire workWidth endpointWidth scratchWidth)
            (accumulatorWire workWidth endpointWidth scratchWidth)
            (cellScratchWire workWidth endpointWidth scratchWidth)) I).testBit q =
        I.testBit q := by
    apply testBit_actGates_of_outside
    exact cellGates_avoid_routing hwf hposition hq
  unfold bitValue
  rw [htest]

theorem majAt_preserve_routing
    {position workWidth endpointWidth scratchWidth q I : Nat}
    (hposition : position < workWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    bitValue
        (actGates (majAt position workWidth endpointWidth scratchWidth) I) q =
      bitValue I q := by
  exact cellGates_preserve_routing CellPlaced.maj_wellFormed hposition hq

theorem umaAt_preserve_routing
    {position workWidth endpointWidth scratchWidth q I : Nat}
    (hposition : position < workWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    bitValue
        (actGates (umaAt position workWidth endpointWidth scratchWidth) I) q =
      bitValue I q := by
  exact cellGates_preserve_routing CellPlaced.uma_wellFormed hposition hq

theorem majAt_length (position workWidth endpointWidth scratchWidth : Nat) :
    (majAt position workWidth endpointWidth scratchWidth).length = 5 := by
  simp [majAt, CellPlaced.gates, Cell.maj_length]

theorem majAt_ccx (position workWidth endpointWidth scratchWidth : Nat) :
    (majAt position workWidth endpointWidth scratchWidth).countP RGate.isCcx = 3 := by
  rw [majAt, CellPlaced.gates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), Cell.maj_ccx]

theorem majAt_cx (position workWidth endpointWidth scratchWidth : Nat) :
    (majAt position workWidth endpointWidth scratchWidth).countP RGate.isCx = 2 := by
  rw [majAt, CellPlaced.gates,
    countP_map_gates (fun g => RGate.isCx_map _ g), Cell.maj_cx]

theorem umaAt_length (position workWidth endpointWidth scratchWidth : Nat) :
    (umaAt position workWidth endpointWidth scratchWidth).length = 6 := by
  simp [umaAt, CellPlaced.gates, Cell.uma_length]

theorem umaAt_ccx (position workWidth endpointWidth scratchWidth : Nat) :
    (umaAt position workWidth endpointWidth scratchWidth).countP RGate.isCcx = 4 := by
  rw [umaAt, CellPlaced.gates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), Cell.uma_ccx]

theorem umaAt_cx (position workWidth endpointWidth scratchWidth : Nat) :
    (umaAt position workWidth endpointWidth scratchWidth).countP RGate.isCx = 2 := by
  rw [umaAt, CellPlaced.gates,
    countP_map_gates (fun g => RGate.isCx_map _ g), Cell.uma_cx]

theorem firstEmit_length
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (firstEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).length =
      8 * tree.internal + 6 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [firstEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [firstEmit, majAt_length, PrunedSelectSwap.Tree.internal,
        PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [firstEmit, negativeAnd, hzero, hone,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem secondEmit_length
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (secondEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).length =
      8 * tree.internal + 7 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [secondEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [secondEmit, umaAt_length, PrunedSelectSwap.Tree.internal,
        PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [secondEmit, negativeAnd, hzero, hone,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem firstEmit_ccx
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (firstEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).countP
        RGate.isCcx =
      2 * tree.internal + 3 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [firstEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [firstEmit, majAt_ccx, RGate.isCcx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [firstEmit, negativeAnd, List.countP_cons, hzero, hone, RGate.isCcx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem secondEmit_ccx
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (secondEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).countP
        RGate.isCcx =
      2 * tree.internal + 4 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [secondEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [secondEmit, umaAt_ccx, RGate.isCcx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [secondEmit, negativeAnd, List.countP_cons, hzero, hone, RGate.isCcx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem firstEmit_cx
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (firstEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).countP
        RGate.isCx =
      2 * tree.internal + 3 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [firstEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [firstEmit, majAt_cx, RGate.isCx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [firstEmit, negativeAnd, List.countP_cons, hzero, hone, RGate.isCx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem secondEmit_cx
    (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat) :
    (secondEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth).countP
        RGate.isCx =
      2 * tree.internal + 3 * tree.leaves := by
  induction tree generalizing ctrl scratchDepth with
  | empty => simp [secondEmit, PrunedSelectSwap.Tree.internal,
      PrunedSelectSwap.Tree.leaves]
  | leaf label =>
      simp [secondEmit, umaAt_cx, List.countP_cons, RGate.isCx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hzero hone =>
      simp [secondEmit, negativeAnd, List.countP_cons, hzero, hone, RGate.isCx,
        PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
      omega

theorem addGates_length
    (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).length =
      16 * tree.internal + 13 * tree.leaves + 2 + if updateSign then 1 else 0 := by
  cases updateSign <;>
    simp [addGates, signUpdateGates, firstEmit_length, secondEmit_length] <;> omega

theorem addGates_ccx
    (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).countP
        RGate.isCcx =
      4 * tree.internal + 7 * tree.leaves := by
  cases updateSign <;>
    simp [addGates, signUpdateGates, firstEmit_ccx, secondEmit_ccx,
      RGate.isCcx] <;> omega

theorem addGates_cx
    (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).countP
        RGate.isCx =
      4 * tree.internal + 6 * tree.leaves + 2 + if updateSign then 1 else 0 := by
  cases updateSign <;>
    simp [addGates, signUpdateGates, firstEmit_cx, secondEmit_cx,
      List.countP_cons, RGate.isCx] <;> omega

theorem flatFirst_avoid_routing
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary q : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    ∀ g ∈ flatFirst start workWidth endpointWidth scratchWidth boundary tree enabled,
      q ∉ g.wires := by
  induction tree generalizing enabled with
  | empty => simp [flatFirst]
  | leaf label =>
      rcases hvalid with ⟨hstart, hlabel⟩
      simp only [flatFirst]
      split
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact cellGates_avoid_routing CellPlaced.maj_wellFormed
            (by omega) hq g hg
        · simp at hg
          subst g
          simpa [RGate.wires] using routing_ne_accumulator hq
      · exact cellGates_avoid_routing CellPlaced.maj_wellFormed
          (by omega) hq
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨_, hzvalid, hovalid⟩
      simp only [flatFirst]
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hzero hzvalid g hg
      · exact hone hovalid g hg

theorem flatSecond_avoid_routing
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary q : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    ∀ g ∈ flatSecond start workWidth endpointWidth scratchWidth boundary tree enabled,
      q ∉ g.wires := by
  induction tree generalizing enabled with
  | empty => simp [flatSecond]
  | leaf label =>
      rcases hvalid with ⟨hstart, hlabel⟩
      simp only [flatSecond]
      split
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · simp at hg
          subst g
          simpa [RGate.wires] using routing_ne_accumulator hq
        · exact cellGates_avoid_routing CellPlaced.uma_wellFormed
            (by omega) hq g hg
      · exact cellGates_avoid_routing CellPlaced.uma_wellFormed
          (by omega) hq
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨_, hzvalid, hovalid⟩
      simp only [flatSecond]
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hone hovalid g hg
      · exact hzero hzvalid g hg

theorem flatFirst_preserve_routing
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary q I : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    bitValue
        (actGates
          (flatFirst start workWidth endpointWidth scratchWidth boundary tree enabled) I)
        q = bitValue I q := by
  unfold bitValue
  rw [testBit_actGates_of_outside (flatFirst_avoid_routing hvalid hq)]

theorem flatSecond_preserve_routing
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary q I : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hq : RoutingWire workWidth endpointWidth scratchWidth q) :
    bitValue
        (actGates
          (flatSecond start workWidth endpointWidth scratchWidth boundary tree enabled) I)
        q = bitValue I q := by
  unfold bitValue
  rw [testBit_actGates_of_outside (flatSecond_avoid_routing hvalid hq)]

theorem flatFirst_preserve_boundary
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth) :
    readField
        (actGates
          (flatFirst start workWidth endpointWidth scratchWidth boundary tree enabled) I)
        (boundaryOffset workWidth) endpointWidth =
      readField I (boundaryOffset workWidth) endpointWidth := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [testBit_readField]
  by_cases hbit : bit < endpointWidth
  · simp only [hbit, decide_true, Bool.true_and]
    exact testBit_actGates_of_outside
      (flatFirst_avoid_routing
        (scratchWidth := scratchWidth) (boundary := boundary) (enabled := enabled)
        hvalid (Or.inr ⟨by omega, by simp [carryWire, scratchOffset]; omega⟩)) I
  · simp [hbit]

theorem flatSecond_preserve_boundary
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    {enabled : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth) :
    readField
        (actGates
          (flatSecond start workWidth endpointWidth scratchWidth boundary tree enabled) I)
        (boundaryOffset workWidth) endpointWidth =
      readField I (boundaryOffset workWidth) endpointWidth := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [testBit_readField]
  by_cases hbit : bit < endpointWidth
  · simp only [hbit, decide_true, Bool.true_and]
    exact testBit_actGates_of_outside
      (flatSecond_avoid_routing
        (scratchWidth := scratchWidth) (boundary := boundary) (enabled := enabled)
        hvalid (Or.inr ⟨by omega, by simp [carryWire, scratchOffset]; omega⟩)) I
  · simp [hbit]

theorem scratchClear_flatFirst
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {enabled : Bool} {scratchDepth count I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : scratchDepth + count ≤ scratchWidth)
    (hscratch : scratchClear workWidth endpointWidth scratchDepth count I) :
    scratchClear workWidth endpointWidth scratchDepth count
      (actGates
        (flatFirst start workWidth endpointWidth scratchWidth boundary tree enabled) I) := by
  intro k hk
  rw [flatFirst_preserve_routing hvalid]
  · exact hscratch k hk
  · right
    simp [carryWire, scratchOffset]
    omega

theorem scratchClear_flatSecond
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {enabled : Bool} {scratchDepth count I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : scratchDepth + count ≤ scratchWidth)
    (hscratch : scratchClear workWidth endpointWidth scratchDepth count I) :
    scratchClear workWidth endpointWidth scratchDepth count
      (actGates
        (flatSecond start workWidth endpointWidth scratchWidth boundary tree enabled) I) := by
  intro k hk
  rw [flatSecond_preserve_routing hvalid]
  · exact hscratch k hk
  · right
    simp [carryWire, scratchOffset]
    omega

private theorem firstEmit_act_flat
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {ctrl scratchDepth I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : scratchDepth + tree.depth ≤ scratchWidth)
    (hcontrolKind :
      ctrl = outerWire ∨
        scratchOffset workWidth endpointWidth ≤ ctrl ∧
          ctrl < scratchOffset workWidth endpointWidth + scratchDepth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (hscratch :
      scratchClear workWidth endpointWidth scratchDepth tree.depth I) :
    actGates
        (firstEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth) I =
      actGates
        (flatFirst start workWidth endpointWidth scratchWidth boundary tree
          (I.testBit ctrl)) I := by
  induction tree generalizing ctrl scratchDepth I with
  | empty => simp [firstEmit, flatFirst, actGates]
  | leaf label =>
      rcases hvalid with ⟨hstart, hlabel⟩
      have hctrlRouting :
          RoutingWire workWidth endpointWidth scratchWidth ctrl := by
        rcases hcontrolKind with rfl | hctrl
        · left
          simp [outerWire, sourceOffset]
        · right
          constructor
          · exact le_trans (by simp [scratchOffset]) hctrl.1
          · simp [carryWire]
            omega
      have hposition : label - start < workWidth := by omega
      have hpreserve := majAt_preserve_routing
        (I := I) hposition hctrlRouting
      by_cases hc : I.testBit ctrl
      · have hcValue : bitValue I ctrl = 1 := by simp [bitValue, hc]
        have hcAfter :
            bitValue
                (actGates
                  (majAt (label - start) workWidth endpointWidth scratchWidth) I)
                ctrl = 1 := by
          rw [hpreserve, hcValue]
        simp only [firstEmit, flatFirst, actGates_append]
        rw [cx_on hcAfter]
        simp [hc, actGates, RGate.act]
      · have hcValue : bitValue I ctrl = 0 := by simp [bitValue, hc]
        have hcAfter :
            bitValue
                (actGates
                  (majAt (label - start) workWidth endpointWidth scratchWidth) I)
                ctrl = 0 := by
          rw [hpreserve, hcValue]
        simp only [firstEmit, flatFirst, actGates_append]
        rw [cx_off hcAfter]
        simp [hc, actGates]
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨hbit, hzvalid, hovalid⟩
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      have hzdepth : scratchDepth + 1 + zero.depth ≤ scratchWidth := by
        have hzle :
            scratchDepth + (zero.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_left zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤ scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzle.trans hnode
      have hodepth : scratchDepth + 1 + one.depth ≤ scratchWidth := by
        have hole :
            scratchDepth + (one.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_right zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤ scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hole.trans hnode
      have hctrlRouting :
          RoutingWire workWidth endpointWidth scratchWidth ctrl := by
        rcases hcontrolKind with rfl | hctrl
        · left
          simp [outerWire, sourceOffset]
        · right
          constructor
          · exact le_trans (by simp [scratchOffset]) hctrl.1
          · simp [carryWire]
            omega
      have hselectorRouting :
          RoutingWire workWidth endpointWidth scratchWidth selector := by
        right
        simp [selector, carryWire, scratchOffset]
        omega
      have hchildRouting :
          RoutingWire workWidth endpointWidth scratchWidth child := by
        right
        simp [child, childControl, carryWire, scratchOffset]
        omega
      have hchildKind :
          child = outerWire ∨
            scratchOffset workWidth endpointWidth ≤ child ∧
              child < scratchOffset workWidth endpointWidth + (scratchDepth + 1) := by
        right
        simp [child, childControl]
      have hctrlSelector : ctrl ≠ selector := by
        rcases hcontrolKind with rfl | hctrl
        · simp [selector, outerWire, boundaryOffset]
          omega
        · simp [selector, scratchOffset] at hctrl ⊢
          omega
      have hctrlChild : ctrl ≠ child := by
        rcases hcontrolKind with rfl | hctrl
        · simp [child, childControl, outerWire, scratchOffset,
            boundaryOffset]
          omega
        · simp [child, childControl] at hctrl ⊢
          omega
      have hselectorChild : selector ≠ child := by
        simp [selector, child, childControl, scratchOffset]
        omega
      have hchild0 : bitValue I child = 0 := by
        have h := hscratch 0 (by simp [PrunedSelectSwap.Tree.depth])
        simpa [child, childControl, scratchClear] using h
      have htails := scratchClear_tail hscratch
      have hzscratch := htails.1
      have hoscratch := htails.2
      have hboundarySelector : boundary.testBit bit = I.testBit selector := by
        rw [← hboundary, testBit_readField]
        simp [hbit, selector]
      by_cases hc : bitValue I ctrl = 1
      · have hctrlBit : I.testBit ctrl = true := by simpa [bitValue] using hc
        by_cases hs : bitValue I selector = 1
        · have hselectorBit : I.testBit selector = true := by
            simpa [bitValue] using hs
          have hboundaryBit : boundary.testBit bit = true := by
            rw [hboundarySelector, hselectorBit]
          have hcompute := negativeAnd_on_one
            (child := child) hctrlSelector hc hs
          have hchildBit : I.testBit child = false := by
            simpa [bitValue] using hchild0
          have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := I) hzvalid hzdepth hchildKind hboundary hzscratch
          rw [hchildBit] at hzact
          let zeroFlat :=
            flatFirst start workWidth endpointWidth scratchWidth boundary zero false
          let oneFlat :=
            flatFirst start workWidth endpointWidth scratchWidth boundary one true
          let Iz := actGates zeroFlat I
          change actGates
              (firstEmit start workWidth endpointWidth scratchWidth zero child
                (scratchDepth + 1)) I = Iz at hzact
          have hctrlIz : bitValue Iz ctrl = 1 := by
            simpa [Iz, zeroFlat, hc] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hzvalid hctrlRouting)
          have hchildIz : bitValue Iz child = 0 := by
            simpa [Iz, zeroFlat, hchild0] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hzvalid hchildRouting)
          have hboundaryIz :
              readField Iz (boundaryOffset workWidth) endpointWidth = boundary := by
            simpa [Iz, zeroFlat, hboundary] using
              (flatFirst_preserve_boundary
                (boundary := boundary) (enabled := false) (I := I) hzvalid)
          have hscratchIz :
              scratchClear workWidth endpointWidth (scratchDepth + 1) one.depth Iz := by
            simpa [Iz, zeroFlat] using
              (scratchClear_flatFirst
                (tree := zero) (boundary := boundary) (enabled := false)
                hzvalid hodepth hoscratch)
          let J := Iz ^^^ (1 <<< child)
          have hchildJ : bitValue J child = 1 := by
            simpa [J] using bitValue_xor_self_zero hchildIz
          have hchildJBit : J.testBit child = true := by
            simpa [bitValue] using hchildJ
          have hboundaryJ :
              readField J (boundaryOffset workWidth) endpointWidth = boundary := by
            dsimp [J]
            rw [readField_xor_of_outside (Or.inr (by
              simp [child, childControl, scratchOffset])), hboundaryIz]
          have hscratchJ :
              scratchClear workWidth endpointWidth (scratchDepth + 1) one.depth J := by
            simpa [J, child] using scratchClear_child_xor hscratchIz
          have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := J) hovalid hodepth hchildKind hboundaryJ hscratchJ
          rw [hchildJBit] at hoact
          have honeCommute : actGates oneFlat J = actGates oneFlat Iz ^^^ (1 <<< child) := by
            simpa [J, oneFlat] using
              (actGates_xor_of_outside
                (flatFirst_avoid_routing
                  (boundary := boundary) (enabled := true) hovalid hchildRouting)
                (I := Iz))
          let Io := actGates oneFlat Iz
          change actGates
              (firstEmit start workWidth endpointWidth scratchWidth one child
                (scratchDepth + 1)) J = actGates oneFlat J at hoact
          have hctrlIo : bitValue Io ctrl = 1 := by
            simpa [Io, oneFlat, hctrlIz] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := true) (I := Iz)
                hovalid hctrlRouting)
          have hselectorIz : bitValue Iz selector = 1 := by
            simpa [Iz, zeroFlat, hs] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hzvalid hselectorRouting)
          have hselectorIo : bitValue Io selector = 1 := by
            simpa [Io, oneFlat, hselectorIz] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := true) (I := Iz)
                hovalid hselectorRouting)
          have hfirstCx : actGates [.cx ctrl child] Iz = J := by
            simpa [J] using cx_on hctrlIz
          have hsecondCx :
              actGates [.cx ctrl child] (Io ^^^ (1 <<< child)) = Io := by
            rw [cx_on]
            · exact RGate.xor_cancel Io child
            · rw [bitValue_xor_of_ne hctrlChild, hctrlIo]
          have hcleanup : actGates (negativeAnd ctrl selector child) Io = Io :=
            negativeAnd_on_one hctrlSelector hctrlIo hselectorIo
          simp only [firstEmit, actGates_append]
          rw [hcompute, hzact, hfirstCx, hoact, honeCommute, hsecondCx]
          change actGates (negativeAnd ctrl selector child).reverse Io = _
          rw [show (negativeAnd ctrl selector child).reverse =
            negativeAnd ctrl selector child by rfl, hcleanup]
          simp [flatFirst, hctrlBit, hboundaryBit, actGates_append,
            zeroFlat, oneFlat, Iz, Io]
        · have hs0 : bitValue I selector = 0 := by
            have := bitValue_lt I selector
            omega
          have hselectorBit : I.testBit selector = false := by
            simpa [bitValue] using hs0
          have hboundaryBit : boundary.testBit bit = false := by
            rw [hboundarySelector, hselectorBit]
          have hcompute := negativeAnd_on_zero
            (child := child) hctrlSelector hc hs0
          let zeroFlat :=
            flatFirst start workWidth endpointWidth scratchWidth boundary zero true
          let oneFlat :=
            flatFirst start workWidth endpointWidth scratchWidth boundary one false
          let J := I ^^^ (1 <<< child)
          have hchildJ : bitValue J child = 1 := by
            simpa [J] using bitValue_xor_self_zero hchild0
          have hchildJBit : J.testBit child = true := by
            simpa [bitValue] using hchildJ
          have hboundaryJ :
              readField J (boundaryOffset workWidth) endpointWidth = boundary := by
            dsimp [J]
            rw [readField_xor_of_outside (Or.inr (by
              simp [child, childControl, scratchOffset])), hboundary]
          have hscratchJ :
              scratchClear workWidth endpointWidth (scratchDepth + 1) zero.depth J := by
            simpa [J, child] using scratchClear_child_xor hzscratch
          have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := J) hzvalid hzdepth hchildKind hboundaryJ hscratchJ
          rw [hchildJBit] at hzact
          have hzeroCommute : actGates zeroFlat J =
              actGates zeroFlat I ^^^ (1 <<< child) := by
            simpa [J, zeroFlat] using
              (actGates_xor_of_outside
                (flatFirst_avoid_routing
                  (boundary := boundary) (enabled := true) hzvalid hchildRouting)
                (I := I))
          let Iz := actGates zeroFlat I
          change actGates
              (firstEmit start workWidth endpointWidth scratchWidth zero child
                (scratchDepth + 1)) J = actGates zeroFlat J at hzact
          have hctrlIz : bitValue Iz ctrl = 1 := by
            simpa [Iz, zeroFlat, hc] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hzvalid hctrlRouting)
          have hchildIz : bitValue Iz child = 0 := by
            simpa [Iz, zeroFlat, hchild0] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hzvalid hchildRouting)
          have hboundaryIz :
              readField Iz (boundaryOffset workWidth) endpointWidth = boundary := by
            simpa [Iz, zeroFlat, hboundary] using
              (flatFirst_preserve_boundary
                (boundary := boundary) (enabled := true) (I := I) hzvalid)
          have hscratchIz :
              scratchClear workWidth endpointWidth (scratchDepth + 1) one.depth Iz := by
            simpa [Iz, zeroFlat] using
              (scratchClear_flatFirst
                (tree := zero) (boundary := boundary) (enabled := true)
                hzvalid hodepth hoscratch)
          have hchildIzBit : Iz.testBit child = false := by
            simpa [bitValue] using hchildIz
          have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := Iz) hovalid hodepth hchildKind hboundaryIz hscratchIz
          rw [hchildIzBit] at hoact
          let Io := actGates oneFlat Iz
          change actGates
              (firstEmit start workWidth endpointWidth scratchWidth one child
                (scratchDepth + 1)) Iz = Io at hoact
          have hctrlIo : bitValue Io ctrl = 1 := by
            simpa [Io, oneFlat, hctrlIz] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := false) (I := Iz)
                hovalid hctrlRouting)
          have hselectorIz : bitValue Iz selector = 0 := by
            simpa [Iz, zeroFlat, hs0] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hzvalid hselectorRouting)
          have hselectorIo : bitValue Io selector = 0 := by
            simpa [Io, oneFlat, hselectorIz] using
              (flatFirst_preserve_routing
                (boundary := boundary) (enabled := false) (I := Iz)
                hovalid hselectorRouting)
          have hfirstCx :
              actGates [.cx ctrl child] (Iz ^^^ (1 <<< child)) = Iz := by
            rw [cx_on]
            · exact RGate.xor_cancel Iz child
            · rw [bitValue_xor_of_ne hctrlChild, hctrlIz]
          have hsecondCx : actGates [.cx ctrl child] Io = Io ^^^ (1 <<< child) :=
            cx_on hctrlIo
          have hcleanup :
              actGates (negativeAnd ctrl selector child)
                  (Io ^^^ (1 <<< child)) = Io := by
            rw [negativeAnd_on_zero hctrlSelector]
            · exact RGate.xor_cancel Io child
            · rw [bitValue_xor_of_ne hctrlChild, hctrlIo]
            · rw [bitValue_xor_of_ne hselectorChild, hselectorIo]
          simp only [firstEmit, actGates_append]
          rw [hcompute, hzact, hzeroCommute, hfirstCx, hoact, hsecondCx]
          change actGates (negativeAnd ctrl selector child).reverse
              (Io ^^^ (1 <<< child)) = _
          rw [show (negativeAnd ctrl selector child).reverse =
            negativeAnd ctrl selector child by rfl, hcleanup]
          simp [flatFirst, hctrlBit, hboundaryBit, actGates_append,
            zeroFlat, oneFlat, Iz, Io]
      · have hc0 : bitValue I ctrl = 0 := by
          have := bitValue_lt I ctrl
          omega
        have hctrlBit : I.testBit ctrl = false := by simpa [bitValue] using hc0
        have hcompute := negativeAnd_off (child := child) hctrlSelector hc0
        have hchildBit : I.testBit child = false := by
          simpa [bitValue] using hchild0
        let zeroFlat :=
          flatFirst start workWidth endpointWidth scratchWidth boundary zero false
        let oneFlat :=
          flatFirst start workWidth endpointWidth scratchWidth boundary one false
        have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
          (I := I) hzvalid hzdepth hchildKind hboundary hzscratch
        rw [hchildBit] at hzact
        let Iz := actGates zeroFlat I
        change actGates
            (firstEmit start workWidth endpointWidth scratchWidth zero child
              (scratchDepth + 1)) I = Iz at hzact
        have hctrlIz : bitValue Iz ctrl = 0 := by
          simpa [Iz, zeroFlat, hc0] using
            (flatFirst_preserve_routing
              (boundary := boundary) (enabled := false) (I := I)
              hzvalid hctrlRouting)
        have hchildIz : bitValue Iz child = 0 := by
          simpa [Iz, zeroFlat, hchild0] using
            (flatFirst_preserve_routing
              (boundary := boundary) (enabled := false) (I := I)
              hzvalid hchildRouting)
        have hchildIzBit : Iz.testBit child = false := by
          simpa [bitValue] using hchildIz
        have hboundaryIz :
            readField Iz (boundaryOffset workWidth) endpointWidth = boundary := by
          simpa [Iz, zeroFlat, hboundary] using
            (flatFirst_preserve_boundary
              (boundary := boundary) (enabled := false) (I := I) hzvalid)
        have hscratchIz :
            scratchClear workWidth endpointWidth (scratchDepth + 1) one.depth Iz := by
          simpa [Iz, zeroFlat] using
            (scratchClear_flatFirst
              (tree := zero) (boundary := boundary) (enabled := false)
              hzvalid hodepth hoscratch)
        have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
          (I := Iz) hovalid hodepth hchildKind hboundaryIz hscratchIz
        rw [hchildIzBit] at hoact
        let Io := actGates oneFlat Iz
        change actGates
            (firstEmit start workWidth endpointWidth scratchWidth one child
              (scratchDepth + 1)) Iz = Io at hoact
        have hctrlIo : bitValue Io ctrl = 0 := by
          simpa [Io, oneFlat, hctrlIz] using
            (flatFirst_preserve_routing
              (boundary := boundary) (enabled := false) (I := Iz)
              hovalid hctrlRouting)
        have hcleanup : actGates (negativeAnd ctrl selector child) Io = Io :=
          negativeAnd_off hctrlSelector hctrlIo
        simp only [firstEmit, actGates_append]
        rw [hcompute, hzact, cx_off hctrlIz, hoact, cx_off hctrlIo]
        change actGates (negativeAnd ctrl selector child).reverse Io = _
        rw [show (negativeAnd ctrl selector child).reverse =
          negativeAnd ctrl selector child by rfl, hcleanup]
        simp [flatFirst, hctrlBit, actGates_append, zeroFlat, oneFlat, Iz, Io]

private theorem secondEmit_act_flat
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary : Nat}
    {ctrl scratchDepth I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : scratchDepth + tree.depth ≤ scratchWidth)
    (hcontrolKind :
      ctrl = outerWire ∨
        scratchOffset workWidth endpointWidth ≤ ctrl ∧
          ctrl < scratchOffset workWidth endpointWidth + scratchDepth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (hscratch :
      scratchClear workWidth endpointWidth scratchDepth tree.depth I) :
    actGates
        (secondEmit start workWidth endpointWidth scratchWidth tree ctrl scratchDepth) I =
      actGates
        (flatSecond start workWidth endpointWidth scratchWidth boundary tree
          (I.testBit ctrl)) I := by
  induction tree generalizing ctrl scratchDepth I with
  | empty => simp [secondEmit, flatSecond, actGates]
  | leaf label =>
      by_cases hc : I.testBit ctrl
      · have hcValue : bitValue I ctrl = 1 := by simp [bitValue, hc]
        simp only [secondEmit, flatSecond, actGates_append]
        rw [cx_on hcValue]
        simp [hc, actGates, RGate.act]
      · have hcValue : bitValue I ctrl = 0 := by simp [bitValue, hc]
        simp only [secondEmit, flatSecond, actGates_append]
        rw [cx_off hcValue]
        simp [hc, actGates]
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨hbit, hzvalid, hovalid⟩
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      have hzdepth : scratchDepth + 1 + zero.depth ≤ scratchWidth := by
        have hzle :
            scratchDepth + (zero.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_left zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤ scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzle.trans hnode
      have hodepth : scratchDepth + 1 + one.depth ≤ scratchWidth := by
        have hole :
            scratchDepth + (one.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_right zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤ scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hole.trans hnode
      have hctrlRouting :
          RoutingWire workWidth endpointWidth scratchWidth ctrl := by
        rcases hcontrolKind with rfl | hctrl
        · left
          simp [outerWire, sourceOffset]
        · right
          constructor
          · exact le_trans (by simp [scratchOffset]) hctrl.1
          · simp [carryWire]
            omega
      have hselectorRouting :
          RoutingWire workWidth endpointWidth scratchWidth selector := by
        right
        simp [selector, carryWire, scratchOffset]
        omega
      have hchildRouting :
          RoutingWire workWidth endpointWidth scratchWidth child := by
        right
        simp [child, childControl, carryWire, scratchOffset]
        omega
      have hchildKind :
          child = outerWire ∨
            scratchOffset workWidth endpointWidth ≤ child ∧
              child < scratchOffset workWidth endpointWidth + (scratchDepth + 1) := by
        right
        simp [child, childControl]
      have hctrlSelector : ctrl ≠ selector := by
        rcases hcontrolKind with rfl | hctrl
        · simp [selector, outerWire, boundaryOffset]
          omega
        · simp [selector, scratchOffset] at hctrl ⊢
          omega
      have hctrlChild : ctrl ≠ child := by
        rcases hcontrolKind with rfl | hctrl
        · simp [child, childControl, outerWire, scratchOffset,
            boundaryOffset]
          omega
        · simp [child, childControl] at hctrl ⊢
          omega
      have hselectorChild : selector ≠ child := by
        simp [selector, child, childControl, scratchOffset]
        omega
      have hchild0 : bitValue I child = 0 := by
        have h := hscratch 0 (by simp [PrunedSelectSwap.Tree.depth])
        simpa [child, childControl, scratchClear] using h
      have htails := scratchClear_tail hscratch
      have hzscratch := htails.1
      have hoscratch := htails.2
      have hboundarySelector : boundary.testBit bit = I.testBit selector := by
        rw [← hboundary, testBit_readField]
        simp [hbit, selector]
      by_cases hc : bitValue I ctrl = 1
      · have hctrlBit : I.testBit ctrl = true := by simpa [bitValue] using hc
        by_cases hs : bitValue I selector = 1
        · have hselectorBit : I.testBit selector = true := by
            simpa [bitValue] using hs
          have hboundaryBit : boundary.testBit bit = true := by
            rw [hboundarySelector, hselectorBit]
          have hcompute := negativeAnd_on_one
            (child := child) hctrlSelector hc hs
          let oneFlat :=
            flatSecond start workWidth endpointWidth scratchWidth boundary one true
          let zeroFlat :=
            flatSecond start workWidth endpointWidth scratchWidth boundary zero false
          let J := I ^^^ (1 <<< child)
          have hchildJ : bitValue J child = 1 := by
            simpa [J] using bitValue_xor_self_zero hchild0
          have hchildJBit : J.testBit child = true := by
            simpa [bitValue] using hchildJ
          have hboundaryJ :
              readField J (boundaryOffset workWidth) endpointWidth = boundary := by
            dsimp [J]
            rw [readField_xor_of_outside (Or.inr (by
              simp [child, childControl, scratchOffset])), hboundary]
          have hscratchJ :
              scratchClear workWidth endpointWidth (scratchDepth + 1) one.depth J := by
            simpa [J, child] using scratchClear_child_xor hoscratch
          have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := J) hovalid hodepth hchildKind hboundaryJ hscratchJ
          rw [hchildJBit] at hoact
          have honeCommute : actGates oneFlat J =
              actGates oneFlat I ^^^ (1 <<< child) := by
            simpa [J, oneFlat] using
              (actGates_xor_of_outside
                (flatSecond_avoid_routing
                  (boundary := boundary) (enabled := true) hovalid hchildRouting)
                (I := I))
          let Io := actGates oneFlat I
          change actGates
              (secondEmit start workWidth endpointWidth scratchWidth one child
                (scratchDepth + 1)) J = actGates oneFlat J at hoact
          have hctrlIo : bitValue Io ctrl = 1 := by
            simpa [Io, oneFlat, hc] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hovalid hctrlRouting)
          have hchildIo : bitValue Io child = 0 := by
            simpa [Io, oneFlat, hchild0] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hovalid hchildRouting)
          have hchildIoBit : Io.testBit child = false := by
            simpa [bitValue] using hchildIo
          have hboundaryIo :
              readField Io (boundaryOffset workWidth) endpointWidth = boundary := by
            simpa [Io, oneFlat, hboundary] using
              (flatSecond_preserve_boundary
                (boundary := boundary) (enabled := true) (I := I) hovalid)
          have hscratchIo :
              scratchClear workWidth endpointWidth (scratchDepth + 1) zero.depth Io := by
            simpa [Io, oneFlat] using
              (scratchClear_flatSecond
                (tree := one) (boundary := boundary) (enabled := true)
                hovalid hzdepth hzscratch)
          have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := Io) hzvalid hzdepth hchildKind hboundaryIo hscratchIo
          rw [hchildIoBit] at hzact
          let Iz := actGates zeroFlat Io
          change actGates
              (secondEmit start workWidth endpointWidth scratchWidth zero child
                (scratchDepth + 1)) Io = Iz at hzact
          have hctrlIz : bitValue Iz ctrl = 1 := by
            simpa [Iz, zeroFlat, hctrlIo] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := false) (I := Io)
                hzvalid hctrlRouting)
          have hselectorIo : bitValue Io selector = 1 := by
            simpa [Io, oneFlat, hs] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := true) (I := I)
                hovalid hselectorRouting)
          have hselectorIz : bitValue Iz selector = 1 := by
            simpa [Iz, zeroFlat, hselectorIo] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := false) (I := Io)
                hzvalid hselectorRouting)
          have hfirstCx : actGates [.cx ctrl child] I = J := by
            simpa [J] using cx_on hc
          have hsecondCx :
              actGates [.cx ctrl child] (Io ^^^ (1 <<< child)) = Io := by
            rw [cx_on]
            · exact RGate.xor_cancel Io child
            · rw [bitValue_xor_of_ne hctrlChild, hctrlIo]
          have hcleanup : actGates (negativeAnd ctrl selector child) Iz = Iz :=
            negativeAnd_on_one hctrlSelector hctrlIz hselectorIz
          simp only [secondEmit, actGates_append]
          rw [hcompute, hfirstCx, hoact, honeCommute, hsecondCx, hzact]
          change actGates (negativeAnd ctrl selector child).reverse Iz = _
          rw [show (negativeAnd ctrl selector child).reverse =
            negativeAnd ctrl selector child by rfl, hcleanup]
          simp [flatSecond, hctrlBit, hboundaryBit, actGates_append,
            oneFlat, zeroFlat, Io, Iz]
        · have hs0 : bitValue I selector = 0 := by
            have := bitValue_lt I selector
            omega
          have hselectorBit : I.testBit selector = false := by
            simpa [bitValue] using hs0
          have hboundaryBit : boundary.testBit bit = false := by
            rw [hboundarySelector, hselectorBit]
          have hcompute := negativeAnd_on_zero
            (child := child) hctrlSelector hc hs0
          let oneFlat :=
            flatSecond start workWidth endpointWidth scratchWidth boundary one false
          let zeroFlat :=
            flatSecond start workWidth endpointWidth scratchWidth boundary zero true
          have hchildBit : I.testBit child = false := by
            simpa [bitValue] using hchild0
          have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := I) hovalid hodepth hchildKind hboundary hoscratch
          rw [hchildBit] at hoact
          let Io := actGates oneFlat I
          change actGates
              (secondEmit start workWidth endpointWidth scratchWidth one child
                (scratchDepth + 1)) I = Io at hoact
          have hctrlIo : bitValue Io ctrl = 1 := by
            simpa [Io, oneFlat, hc] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hovalid hctrlRouting)
          have hchildIo : bitValue Io child = 0 := by
            simpa [Io, oneFlat, hchild0] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hovalid hchildRouting)
          have hboundaryIo :
              readField Io (boundaryOffset workWidth) endpointWidth = boundary := by
            simpa [Io, oneFlat, hboundary] using
              (flatSecond_preserve_boundary
                (boundary := boundary) (enabled := false) (I := I) hovalid)
          have hscratchIo :
              scratchClear workWidth endpointWidth (scratchDepth + 1) zero.depth Io := by
            simpa [Io, oneFlat] using
              (scratchClear_flatSecond
                (tree := one) (boundary := boundary) (enabled := false)
                hovalid hzdepth hzscratch)
          let K := Io ^^^ (1 <<< child)
          have hchildK : bitValue K child = 1 := by
            simpa [K] using bitValue_xor_self_zero hchildIo
          have hchildKBit : K.testBit child = true := by
            simpa [bitValue] using hchildK
          have hboundaryK :
              readField K (boundaryOffset workWidth) endpointWidth = boundary := by
            dsimp [K]
            rw [readField_xor_of_outside (Or.inr (by
              simp [child, childControl, scratchOffset])), hboundaryIo]
          have hscratchK :
              scratchClear workWidth endpointWidth (scratchDepth + 1) zero.depth K := by
            simpa [K, child] using scratchClear_child_xor hscratchIo
          have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
            (I := K) hzvalid hzdepth hchildKind hboundaryK hscratchK
          rw [hchildKBit] at hzact
          have hzeroCommute : actGates zeroFlat K =
              actGates zeroFlat Io ^^^ (1 <<< child) := by
            simpa [K, zeroFlat] using
              (actGates_xor_of_outside
                (flatSecond_avoid_routing
                  (boundary := boundary) (enabled := true) hzvalid hchildRouting)
                (I := Io))
          let Iz := actGates zeroFlat Io
          change actGates
              (secondEmit start workWidth endpointWidth scratchWidth zero child
                (scratchDepth + 1)) K = actGates zeroFlat K at hzact
          have hctrlIz : bitValue Iz ctrl = 1 := by
            simpa [Iz, zeroFlat, hctrlIo] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := true) (I := Io)
                hzvalid hctrlRouting)
          have hselectorIo : bitValue Io selector = 0 := by
            simpa [Io, oneFlat, hs0] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := false) (I := I)
                hovalid hselectorRouting)
          have hselectorIz : bitValue Iz selector = 0 := by
            simpa [Iz, zeroFlat, hselectorIo] using
              (flatSecond_preserve_routing
                (boundary := boundary) (enabled := true) (I := Io)
                hzvalid hselectorRouting)
          have hfirstCx : actGates [.cx ctrl child] (I ^^^ (1 <<< child)) = I := by
            rw [cx_on]
            · exact RGate.xor_cancel I child
            · rw [bitValue_xor_of_ne hctrlChild, hc]
          have hsecondCx : actGates [.cx ctrl child] Io = K := by
            simpa [K] using cx_on hctrlIo
          have hcleanup :
              actGates (negativeAnd ctrl selector child)
                  (Iz ^^^ (1 <<< child)) = Iz := by
            rw [negativeAnd_on_zero hctrlSelector]
            · exact RGate.xor_cancel Iz child
            · rw [bitValue_xor_of_ne hctrlChild, hctrlIz]
            · rw [bitValue_xor_of_ne hselectorChild, hselectorIz]
          simp only [secondEmit, actGates_append]
          rw [hcompute, hfirstCx, hoact, hsecondCx, hzact, hzeroCommute]
          change actGates (negativeAnd ctrl selector child).reverse
              (Iz ^^^ (1 <<< child)) = _
          rw [show (negativeAnd ctrl selector child).reverse =
            negativeAnd ctrl selector child by rfl, hcleanup]
          simp [flatSecond, hctrlBit, hboundaryBit, actGates_append,
            oneFlat, zeroFlat, Io, Iz]
      · have hc0 : bitValue I ctrl = 0 := by
          have := bitValue_lt I ctrl
          omega
        have hctrlBit : I.testBit ctrl = false := by simpa [bitValue] using hc0
        have hcompute := negativeAnd_off (child := child) hctrlSelector hc0
        have hchildBit : I.testBit child = false := by
          simpa [bitValue] using hchild0
        let oneFlat :=
          flatSecond start workWidth endpointWidth scratchWidth boundary one false
        let zeroFlat :=
          flatSecond start workWidth endpointWidth scratchWidth boundary zero false
        have hoact := hone (ctrl := child) (scratchDepth := scratchDepth + 1)
          (I := I) hovalid hodepth hchildKind hboundary hoscratch
        rw [hchildBit] at hoact
        let Io := actGates oneFlat I
        change actGates
            (secondEmit start workWidth endpointWidth scratchWidth one child
              (scratchDepth + 1)) I = Io at hoact
        have hctrlIo : bitValue Io ctrl = 0 := by
          simpa [Io, oneFlat, hc0] using
            (flatSecond_preserve_routing
              (boundary := boundary) (enabled := false) (I := I)
              hovalid hctrlRouting)
        have hchildIo : bitValue Io child = 0 := by
          simpa [Io, oneFlat, hchild0] using
            (flatSecond_preserve_routing
              (boundary := boundary) (enabled := false) (I := I)
              hovalid hchildRouting)
        have hchildIoBit : Io.testBit child = false := by
          simpa [bitValue] using hchildIo
        have hboundaryIo :
            readField Io (boundaryOffset workWidth) endpointWidth = boundary := by
          simpa [Io, oneFlat, hboundary] using
            (flatSecond_preserve_boundary
              (boundary := boundary) (enabled := false) (I := I) hovalid)
        have hscratchIo :
            scratchClear workWidth endpointWidth (scratchDepth + 1) zero.depth Io := by
          simpa [Io, oneFlat] using
            (scratchClear_flatSecond
              (tree := one) (boundary := boundary) (enabled := false)
              hovalid hzdepth hzscratch)
        have hzact := hzero (ctrl := child) (scratchDepth := scratchDepth + 1)
          (I := Io) hzvalid hzdepth hchildKind hboundaryIo hscratchIo
        rw [hchildIoBit] at hzact
        let Iz := actGates zeroFlat Io
        change actGates
            (secondEmit start workWidth endpointWidth scratchWidth zero child
              (scratchDepth + 1)) Io = Iz at hzact
        have hctrlIz : bitValue Iz ctrl = 0 := by
          simpa [Iz, zeroFlat, hctrlIo] using
            (flatSecond_preserve_routing
              (boundary := boundary) (enabled := false) (I := Io)
              hzvalid hctrlRouting)
        have hcleanup : actGates (negativeAnd ctrl selector child) Iz = Iz :=
          negativeAnd_off hctrlSelector hctrlIz
        simp only [secondEmit, actGates_append]
        rw [hcompute, cx_off hc0, hoact, cx_off hctrlIo, hzact]
        change actGates (negativeAnd ctrl selector child).reverse Iz = _
        rw [show (negativeAnd ctrl selector child).reverse =
          negativeAnd ctrl selector child by rfl, hcleanup]
        simp [flatSecond, hctrlBit, actGates_append, oneFlat, zeroFlat, Io, Iz]

theorem firstEmit_act_flat_outer
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I) :
    actGates
        (firstEmit start workWidth endpointWidth scratchWidth tree outerWire 0) I =
      actGates
        (flatFirst start workWidth endpointWidth scratchWidth boundary tree
          (I.testBit outerWire)) I := by
  exact firstEmit_act_flat hvalid (by simpa using hdepth) (Or.inl rfl)
    hboundary hscratch

theorem secondEmit_act_flat_outer
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I) :
    actGates
        (secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0) I =
      actGates
        (flatSecond start workWidth endpointWidth scratchWidth boundary tree
          (I.testBit outerWire)) I := by
  exact secondEmit_act_flat hvalid (by simpa using hdepth) (Or.inl rfl)
    hboundary hscratch

theorem signUpdateGates_preserve_bitValue
    {workWidth endpointWidth scratchWidth q I : Nat} {updateSign : Bool}
    (hq : q ≠ signWire) :
    bitValue
        (actGates
          (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I) q =
      bitValue I q := by
  cases updateSign with
  | false => rfl
  | true =>
      change bitValue
          (actGates
            [.cx (carryWire workWidth endpointWidth scratchWidth) signWire] I) q =
        bitValue I q
      by_cases hcarry :
          bitValue I (carryWire workWidth endpointWidth scratchWidth) = 1
      · rw [cx_on hcarry, bitValue_xor_of_ne hq]
      · have hcarryZero :
            bitValue I (carryWire workWidth endpointWidth scratchWidth) = 0 := by
          have hlt :=
            bitValue_lt I (carryWire workWidth endpointWidth scratchWidth)
          omega
        rw [cx_off hcarryZero]

theorem signUpdateGates_preserve_boundary
    {workWidth endpointWidth scratchWidth I : Nat} {updateSign : Bool} :
    readField
        (actGates
          (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I)
        (boundaryOffset workWidth) endpointWidth =
      readField I (boundaryOffset workWidth) endpointWidth := by
  cases updateSign with
  | false => rfl
  | true =>
      change readField
          (actGates
            [.cx (carryWire workWidth endpointWidth scratchWidth) signWire] I)
          (boundaryOffset workWidth) endpointWidth =
        readField I (boundaryOffset workWidth) endpointWidth
      by_cases hcarry :
          bitValue I (carryWire workWidth endpointWidth scratchWidth) = 1
      · rw [cx_on hcarry, readField_xor_of_outside]
        left
        simp [signWire, boundaryOffset]
        omega
      · have hcarryZero :
            bitValue I (carryWire workWidth endpointWidth scratchWidth) = 0 := by
          have hlt :=
            bitValue_lt I (carryWire workWidth endpointWidth scratchWidth)
          omega
        rw [cx_off hcarryZero]

theorem addGates_act_contiguous
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    {updateSign : Bool}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth updateSign) I =
      actGates
        (contiguousAddGates start workWidth endpointWidth scratchWidth boundary
          updateSign) I := by
  have hnodup : (Tree.labels tree).Nodup := by
    rw [hlabels]
    exact List.nodup_range'
  let acc := accumulatorWire workWidth endpointWidth scratchWidth
  let firstScan :=
    firstLabelScan start workWidth endpointWidth scratchWidth
      (List.range' start workWidth) (some boundary)
  let secondScan :=
    secondLabelScan start workWidth endpointWidth scratchWidth
      (List.range' start workWidth).reverse (some boundary)
  let signGates :=
    signUpdateGates workWidth endpointWidth scratchWidth updateSign
  let J₀ := I ^^^ (1 <<< acc)
  have hinitial : actGates [.cx outerWire acc] I = J₀ := by
    simpa [J₀] using cx_on houter
  have houterJ₀ : bitValue J₀ outerWire = 1 := by
    change bitValue (I ^^^ (1 <<< acc)) outerWire = 1
    rw [bitValue_xor_of_ne]
    · exact houter
    · simp [acc, accumulatorWire, carryWire, scratchOffset,
        boundaryOffset, outerWire]
  have houterJ₀Bit : J₀.testBit outerWire = true := by
    simpa [bitValue] using houterJ₀
  have hboundaryJ₀ :
      readField J₀ (boundaryOffset workWidth) endpointWidth = boundary := by
    change readField (I ^^^ (1 <<< acc))
        (boundaryOffset workWidth) endpointWidth = boundary
    rw [readField_xor_of_outside, hboundary]
    right
    simp [acc, accumulatorWire, carryWire, scratchOffset]
    omega
  have hscratchJ₀ :
      scratchClear workWidth endpointWidth 0 tree.depth J₀ := by
    intro k hk
    change bitValue (I ^^^ (1 <<< acc))
        (scratchOffset workWidth endpointWidth + 0 + k) = 0
    rw [bitValue_xor_of_ne]
    · exact hscratch k hk
    · simp [acc, accumulatorWire, carryWire]
      omega
  have hfirst := firstEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := J₀)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundaryJ₀ hscratchJ₀
  rw [houterJ₀Bit,
    flatFirst_eq_contiguousScan hnodup hlabels hselect] at hfirst
  let J₁ := actGates firstScan J₀
  change actGates
      (firstEmit start workWidth endpointWidth scratchWidth tree outerWire 0) J₀ =
    J₁ at hfirst
  have hboundaryJ₁ :
      readField J₁ (boundaryOffset workWidth) endpointWidth = boundary := by
    have h := flatFirst_preserve_boundary
      (scratchWidth := scratchWidth) (boundary := boundary) (enabled := true)
      (I := J₀) hvalid
    rw [flatFirst_eq_contiguousScan hnodup hlabels hselect] at h
    simpa [J₁, firstScan, hboundaryJ₀] using h
  have hscratchJ₁ :
      scratchClear workWidth endpointWidth 0 tree.depth J₁ := by
    have h := scratchClear_flatFirst
      (tree := tree) (boundary := boundary) (enabled := true)
      hvalid (by simpa using hdepth) hscratchJ₀
    rw [flatFirst_eq_contiguousScan hnodup hlabels hselect] at h
    simpa [J₁, firstScan] using h
  have houterJ₁ : bitValue J₁ outerWire = 1 := by
    have h := flatFirst_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary) (enabled := true)
      (q := outerWire) (I := J₀)
      hvalid (Or.inl (by decide))
    rw [flatFirst_eq_contiguousScan hnodup hlabels hselect] at h
    simpa [J₁, firstScan, houterJ₀] using h
  let J₂ := actGates signGates J₁
  have hboundaryJ₂ :
      readField J₂ (boundaryOffset workWidth) endpointWidth = boundary := by
    simpa [J₂, signGates, hboundaryJ₁] using
      (signUpdateGates_preserve_boundary
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth) (I := J₁) (updateSign := updateSign))
  have hscratchJ₂ :
      scratchClear workWidth endpointWidth 0 tree.depth J₂ := by
    intro k hk
    have hne :
        scratchOffset workWidth endpointWidth + 0 + k ≠ signWire := by
      simp [signWire, scratchOffset, boundaryOffset]
      omega
    simpa [J₂, signGates] using
      (signUpdateGates_preserve_bitValue
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth) (q :=
          scratchOffset workWidth endpointWidth + 0 + k)
        (I := J₁) (updateSign := updateSign) hne).trans (hscratchJ₁ k hk)
  have houterJ₂ : bitValue J₂ outerWire = 1 := by
    simpa [J₂, signGates] using
      ((signUpdateGates_preserve_bitValue
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth) (q := outerWire) (I := J₁)
        (updateSign := updateSign) (by simp [outerWire, signWire])).trans
          houterJ₁)
  have houterJ₂Bit : J₂.testBit outerWire = true := by
    simpa [bitValue] using houterJ₂
  have hsecond := secondEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := J₂)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundaryJ₂ hscratchJ₂
  rw [houterJ₂Bit,
    flatSecond_eq_contiguousScan hnodup hlabels hselect] at hsecond
  let J₃ := actGates secondScan J₂
  change actGates
      (secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0) J₂ =
    J₃ at hsecond
  have houterJ₃ : bitValue J₃ outerWire = 1 := by
    have h := flatSecond_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary) (enabled := true)
      (q := outerWire) (I := J₂)
      hvalid (Or.inl (by decide))
    rw [flatSecond_eq_contiguousScan hnodup hlabels hselect] at h
    simpa [J₃, secondScan, houterJ₂] using h
  have hfinalCx : actGates [.cx outerWire acc] J₃ = J₃ ^^^ (1 <<< acc) :=
    cx_on houterJ₃
  have hinitialX : actGates [.x acc] I = J₀ := by
    simp [J₀, actGates, RGate.act]
  have hfinalX : actGates [.x acc] J₃ = J₃ ^^^ (1 <<< acc) := by
    simp [actGates, RGate.act]
  simp only [addGates, contiguousAddGates, actGates_append]
  rw [hinitial, hfirst]
  change actGates [.cx outerWire acc]
      (actGates
        (secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0)
        (actGates signGates J₁)) =
    actGates [.x acc]
      (actGates secondScan
        (actGates signGates (actGates firstScan (actGates [.x acc] I))))
  rw [show actGates signGates J₁ = J₂ by rfl, hsecond, hfinalCx,
    hinitialX, show actGates firstScan J₀ = J₁ by rfl,
    show actGates signGates J₁ = J₂ by rfl,
    show actGates secondScan J₂ = J₃ by rfl, hfinalX]

theorem addGates_outerClear_act_flat
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 0)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth false) I =
      actGates
        (flatFirst start workWidth endpointWidth scratchWidth boundary tree false ++
          flatSecond start workWidth endpointWidth scratchWidth boundary tree false)
        I := by
  have houterBit : I.testBit outerWire = false := by
    simpa [bitValue] using houter
  have hfirst := firstEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := I)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundary hscratch
  rw [houterBit] at hfirst
  let J := actGates
    (flatFirst start workWidth endpointWidth scratchWidth boundary tree false) I
  have hboundaryJ :
      readField J (boundaryOffset workWidth) endpointWidth = boundary := by
    have h := flatFirst_preserve_boundary
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (I := I) hvalid
    simpa [J, hboundary] using h
  have hscratchJ :
      scratchClear workWidth endpointWidth 0 tree.depth J := by
    simpa [J] using scratchClear_flatFirst
      (tree := tree) (boundary := boundary) (enabled := false)
      hvalid (by simpa using hdepth) hscratch
  have houterJ : bitValue J outerWire = 0 := by
    have h := flatFirst_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (q := outerWire) (I := I) hvalid
      (Or.inl (by decide))
    simpa [J, houter] using h
  have houterJBit : J.testBit outerWire = false := by
    simpa [bitValue] using houterJ
  have hsecond := secondEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := J)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundaryJ hscratchJ
  rw [houterJBit] at hsecond
  let K := actGates
    (flatSecond start workWidth endpointWidth scratchWidth boundary tree false) J
  have houterK : bitValue K outerWire = 0 := by
    have h := flatSecond_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (q := outerWire) (I := J) hvalid
      (Or.inl (by decide))
    simpa [K, houterJ] using h
  simp only [addGates, signUpdateGates, actGates_append]
  rw [cx_off houter, hfirst]
  change actGates [.cx outerWire
      (accumulatorWire workWidth endpointWidth scratchWidth)]
      (actGates
        (secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0)
        J) = _
  rw [hsecond, cx_off houterK]

theorem addGates_outerClear_act_flat_sign
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 0)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth true) I =
      actGates
        (flatFirst start workWidth endpointWidth scratchWidth boundary tree false ++
          signUpdateGates workWidth endpointWidth scratchWidth true ++
          flatSecond start workWidth endpointWidth scratchWidth boundary tree false)
        I := by
  have houterBit : I.testBit outerWire = false := by
    simpa [bitValue] using houter
  have hfirst := firstEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := I)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundary hscratch
  rw [houterBit] at hfirst
  let J₁ := actGates
    (flatFirst start workWidth endpointWidth scratchWidth boundary tree false) I
  have hboundaryJ₁ :
      readField J₁ (boundaryOffset workWidth) endpointWidth = boundary := by
    have h := flatFirst_preserve_boundary
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (I := I) hvalid
    simpa [J₁, hboundary] using h
  have hscratchJ₁ :
      scratchClear workWidth endpointWidth 0 tree.depth J₁ := by
    simpa [J₁] using scratchClear_flatFirst
      (tree := tree) (boundary := boundary) (enabled := false)
      hvalid (by simpa using hdepth) hscratch
  have houterJ₁ : bitValue J₁ outerWire = 0 := by
    have h := flatFirst_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (q := outerWire) (I := I) hvalid
      (Or.inl (by decide))
    simpa [J₁, houter] using h
  let J₂ := actGates
    (signUpdateGates workWidth endpointWidth scratchWidth true) J₁
  have hboundaryJ₂ :
      readField J₂ (boundaryOffset workWidth) endpointWidth = boundary := by
    simpa [J₂, hboundaryJ₁] using
      (signUpdateGates_preserve_boundary
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth) (I := J₁) (updateSign := true))
  have hscratchJ₂ :
      scratchClear workWidth endpointWidth 0 tree.depth J₂ := by
    intro k hk
    have hne :
        scratchOffset workWidth endpointWidth + k ≠ signWire := by
      simp [signWire, scratchOffset, boundaryOffset]
      omega
    simpa [J₂] using
      (signUpdateGates_preserve_bitValue
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth)
        (q := scratchOffset workWidth endpointWidth + k)
        (I := J₁) (updateSign := true) hne).trans (hscratchJ₁ k hk)
  have houterJ₂ : bitValue J₂ outerWire = 0 := by
    simpa [J₂] using
      ((signUpdateGates_preserve_bitValue
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (scratchWidth := scratchWidth) (q := outerWire) (I := J₁)
        (updateSign := true) (by simp [outerWire, signWire])).trans houterJ₁)
  have houterJ₂Bit : J₂.testBit outerWire = false := by
    simpa [bitValue] using houterJ₂
  have hsecond := secondEmit_act_flat
    (ctrl := outerWire) (scratchDepth := 0) (I := J₂)
    hvalid (by simpa using hdepth) (Or.inl rfl) hboundaryJ₂ hscratchJ₂
  rw [houterJ₂Bit] at hsecond
  let J₃ := actGates
    (flatSecond start workWidth endpointWidth scratchWidth boundary tree false) J₂
  have houterJ₃ : bitValue J₃ outerWire = 0 := by
    have h := flatSecond_preserve_routing
      (scratchWidth := scratchWidth) (boundary := boundary)
      (enabled := false) (q := outerWire) (I := J₂) hvalid
      (Or.inl (by decide))
    simpa [J₃, houterJ₂] using h
  simp only [addGates, actGates_append]
  rw [cx_off houter, hfirst]
  change actGates [.cx outerWire
      (accumulatorWire workWidth endpointWidth scratchWidth)]
      (actGates
        (secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0)
        (actGates
          (signUpdateGates workWidth endpointWidth scratchWidth true) J₁)) = _
  rw [show actGates
      (signUpdateGates workWidth endpointWidth scratchWidth true) J₁ = J₂ by rfl,
    hsecond, cx_off houterJ₃]

end VQ.Euclid.LuoPrefixArithmetic
