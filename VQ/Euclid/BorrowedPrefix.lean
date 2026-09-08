import VQ.Euclid.BorrowedCell
import VQ.Euclid.LuoPrefixFixed
import VQ.Reversible.BorrowedPlacement

namespace VQ.Euclid.BorrowedPrefix

open Reversible LuoPrefixArithmetic

def cellAt (backward : Bool) (position workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  CellPlaced.gates (if backward then BorrowedCell.umaGates else BorrowedCell.majGates)
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def firstEmit (start workWidth endpointWidth scratchWidth : Nat) :
    Tree → Nat → Nat → List RGate
  | .empty, _, _ => []
  | .leaf label, ctrl, _ =>
      cellAt false (label - start) workWidth endpointWidth scratchWidth ++
        [.cx ctrl (accumulatorWire workWidth endpointWidth scratchWidth)]
  | .node bit zero one, ctrl, depth =>
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth depth
      let compute := negativeAnd ctrl selector child
      compute ++ firstEmit start workWidth endpointWidth scratchWidth zero child (depth + 1) ++
        [.cx ctrl child] ++ firstEmit start workWidth endpointWidth scratchWidth one child
          (depth + 1) ++ [.cx ctrl child] ++ compute.reverse

def secondEmit (start workWidth endpointWidth scratchWidth : Nat) :
    Tree → Nat → Nat → List RGate
  | .empty, _, _ => []
  | .leaf label, ctrl, _ =>
      [.cx ctrl (accumulatorWire workWidth endpointWidth scratchWidth)] ++
        cellAt true (label - start) workWidth endpointWidth scratchWidth
  | .node bit zero one, ctrl, depth =>
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth depth
      let compute := negativeAnd ctrl selector child
      compute ++ [.cx ctrl child] ++
        secondEmit start workWidth endpointWidth scratchWidth one child (depth + 1) ++
        [.cx ctrl child] ++
        secondEmit start workWidth endpointWidth scratchWidth zero child (depth + 1) ++
        compute.reverse

def addGates (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  [.cx outerWire (accumulatorWire workWidth endpointWidth scratchWidth)] ++
    firstEmit start workWidth endpointWidth scratchWidth tree outerWire 0 ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    secondEmit start workWidth endpointWidth scratchWidth tree outerWire 0 ++
    [.cx outerWire (accumulatorWire workWidth endpointWidth scratchWidth)]

def subGates (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  (addGates tree start workWidth endpointWidth scratchWidth false).reverse

theorem cellAt_clear (backward : Bool) {position workWidth endpointWidth scratchWidth I : Nat}
    (hp : position < workWidth) :
    writeField (actGates (cellAt backward position workWidth endpointWidth scratchWidth) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) 1 0 =
      actGates (if backward then umaAt position workWidth endpointWidth scratchWidth
        else majAt position workWidth endpointWidth scratchWidth)
        (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0) := by
  have hinj := place_inj
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
    (LuoPrefixFixed.cell_disjoint (endpointWidth := endpointWidth)
      (scratchWidth := scratchWidth) hp)
  cases backward
  · exact actGates_map_clear_bit hinj
      (CellPlaced.component_wellFormed BorrowedCell.maj_wellFormed)
      (CellPlaced.component_wellFormed CellPlaced.maj_wellFormed)
      (k := 4) (by decide) BorrowedCell.maj_clear I
  · exact actGates_map_clear_bit hinj
      (CellPlaced.component_wellFormed BorrowedCell.uma_wellFormed)
      (CellPlaced.component_wellFormed CellPlaced.uma_wellFormed)
      (k := 4) (by decide) BorrowedCell.uma_clear I

theorem cellAt_preserves (backward : Bool) {position workWidth endpointWidth scratchWidth I : Nat}
    (hp : position < workWidth) :
    (actGates (cellAt backward position workWidth endpointWidth scratchWidth) I).testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  have hinj := place_inj
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
    (LuoPrefixFixed.cell_disjoint (endpointWidth := endpointWidth)
      (scratchWidth := scratchWidth) hp)
  cases backward
  · exact actGates_map_preserves_bit hinj
      (CellPlaced.component_wellFormed BorrowedCell.maj_wellFormed)
      (k := 4) (by decide) BorrowedCell.maj_preserves_borrowed I
  · exact actGates_map_preserves_bit hinj
      (CellPlaced.component_wellFormed BorrowedCell.uma_wellFormed)
      (k := 4) (by decide) BorrowedCell.uma_preserves_borrowed I

private theorem clear_below {gs : List RGate} {q : Nat}
    (h : ∀ g ∈ gs, ∀ k ∈ g.wires, k < q) (I : Nat) :
    writeField (actGates gs I) q 1 0 = actGates gs (writeField I q 1 0) :=
  (actGates_write_of_outside (fun g hg k hk => Or.inl (h g hg k hk)) I).symm

private theorem cx_clear {a b q : Nat} (ha : a < q) (hb : b < q) (I : Nat) :
    writeField (actGates [.cx a b] I) q 1 0 =
      actGates [.cx a b] (writeField I q 1 0) := by
  apply clear_below
  intro g hg k hk
  simp only [List.mem_singleton] at hg
  subst g
  simp [RGate.wires] at hk
  rcases hk with rfl | rfl <;> assumption

private theorem negativeAnd_below {a b c q : Nat}
    (ha : a < q) (hb : b < q) (hc : c < q) :
    ∀ g ∈ negativeAnd a b c, ∀ k ∈ g.wires, k < q := by
  intro g hg k hk
  simp [negativeAnd] at hg
  rcases hg with rfl | rfl | rfl <;> simp [RGate.wires] at hk
  · subst k; exact hb
  · rcases hk with rfl | rfl | rfl <;> assumption
  · subst k; exact hb

theorem emit_clear {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth) : ∀ ctrl depth,
    depth + tree.depth ≤ scratchWidth →
    ctrl < cellScratchWire workWidth endpointWidth scratchWidth →
    (∀ I, writeField
      (actGates (firstEmit start workWidth endpointWidth scratchWidth tree ctrl depth) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) 1 0 =
      actGates (LuoPrefixArithmetic.firstEmit start workWidth endpointWidth scratchWidth
        tree ctrl depth) (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0)) ∧
    (∀ I, writeField
      (actGates (secondEmit start workWidth endpointWidth scratchWidth tree ctrl depth) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) 1 0 =
      actGates (LuoPrefixArithmetic.secondEmit start workWidth endpointWidth scratchWidth
        tree ctrl depth) (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0)) := by
  induction tree with
  | empty => intros; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | leaf label =>
    intro ctrl depth hd hc
    have hp : label - start < workWidth := by
      simp only [Tree.RangeValid] at hv
      omega
    have ha : accumulatorWire workWidth endpointWidth scratchWidth <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [accumulatorWire, cellScratchWire]; omega
    constructor <;> intro I <;>
      simp only [firstEmit, secondEmit, LuoPrefixArithmetic.firstEmit,
        LuoPrefixArithmetic.secondEmit, actGates_append]
    · rw [cx_clear hc ha, cellAt_clear false hp]
      rfl
    · rw [cellAt_clear true hp, cx_clear hc ha]
      rfl
  | node bit zero one hz ho =>
    intro ctrl depth hd hc
    rcases hv with ⟨hb, hzv, hov⟩
    have hdz : depth + 1 + zero.depth ≤ scratchWidth := by
      change depth + (max zero.depth one.depth + 1) ≤ scratchWidth at hd
      have := Nat.le_max_left zero.depth one.depth
      omega
    have hdo : depth + 1 + one.depth ≤ scratchWidth := by
      change depth + (max zero.depth one.depth + 1) ≤ scratchWidth at hd
      have := Nat.le_max_right zero.depth one.depth
      omega
    have hchild : childControl workWidth endpointWidth depth <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [childControl, cellScratchWire, carryWire]
      omega
    have hsel : boundaryOffset workWidth + bit <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [cellScratchWire, carryWire, scratchOffset]
      omega
    have hcompute := negativeAnd_below hc hsel hchild
    have hr := clear_below (gs := (negativeAnd ctrl
      (boundaryOffset workWidth + bit) (childControl workWidth endpointWidth depth)).reverse)
      (fun g hg => hcompute g (List.mem_reverse.mp hg))
    obtain ⟨hz₁, hz₂⟩ := hz hzv _ _ hdz hchild
    obtain ⟨ho₁, ho₂⟩ := ho hov _ _ hdo hchild
    constructor <;> intro I <;>
      simp only [firstEmit, secondEmit, LuoPrefixArithmetic.firstEmit,
        LuoPrefixArithmetic.secondEmit, actGates_append]
    · rw [hr, cx_clear hc hchild, ho₁, cx_clear hc hchild, hz₁, clear_below hcompute]
    · rw [hr, hz₂, cx_clear hc hchild, ho₂, cx_clear hc hchild, clear_below hcompute]

private theorem preserves_below {gs : List RGate} {q : Nat}
    (h : ∀ g ∈ gs, ∀ k ∈ g.wires, k < q) (I : Nat) :
    (actGates gs I).testBit q = I.testBit q :=
  testBit_actGates_of_outside (fun g hg hq => Nat.lt_irrefl _ (h g hg _ hq)) I

private theorem cx_preserves {a b q : Nat} (ha : a < q) (hb : b < q) (I : Nat) :
    (actGates [.cx a b] I).testBit q = I.testBit q := by
  apply testBit_actGates_of_outside
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  simp [RGate.wires]
  omega

theorem emit_preserves {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth) : ∀ ctrl depth,
    depth + tree.depth ≤ scratchWidth →
    ctrl < cellScratchWire workWidth endpointWidth scratchWidth →
    (∀ I, (actGates (firstEmit start workWidth endpointWidth scratchWidth tree ctrl depth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth)) ∧
    (∀ I, (actGates (secondEmit start workWidth endpointWidth scratchWidth tree ctrl depth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth)) := by
  induction tree with
  | empty => intros; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | leaf label =>
    intro ctrl depth hd hc
    have hp : label - start < workWidth := by
      simp only [Tree.RangeValid] at hv
      omega
    have ha : accumulatorWire workWidth endpointWidth scratchWidth <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [accumulatorWire, cellScratchWire]; omega
    constructor <;> intro I <;> simp only [firstEmit, secondEmit, actGates_append]
    · rw [cx_preserves hc ha, cellAt_preserves false hp]
    · rw [cellAt_preserves true hp, cx_preserves hc ha]
  | node bit zero one hz ho =>
    intro ctrl depth hd hc
    rcases hv with ⟨hb, hzv, hov⟩
    change depth + (max zero.depth one.depth + 1) ≤ scratchWidth at hd
    have hdz : depth + 1 + zero.depth ≤ scratchWidth := by omega
    have hdo : depth + 1 + one.depth ≤ scratchWidth := by omega
    have hchild : childControl workWidth endpointWidth depth <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [childControl, cellScratchWire, carryWire]
      omega
    have hsel : boundaryOffset workWidth + bit <
        cellScratchWire workWidth endpointWidth scratchWidth := by
      simp only [cellScratchWire, carryWire, scratchOffset]
      omega
    have hcompute := negativeAnd_below hc hsel hchild
    have hr := preserves_below (gs := (negativeAnd ctrl
      (boundaryOffset workWidth + bit) (childControl workWidth endpointWidth depth)).reverse)
      (fun g hg => hcompute g (List.mem_reverse.mp hg))
    obtain ⟨hz₁, hz₂⟩ := hz hzv _ _ hdz hchild
    obtain ⟨ho₁, ho₂⟩ := ho hov _ _ hdo hchild
    constructor <;> intro I <;> simp only [firstEmit, secondEmit, actGates_append]
    · rw [hr, cx_preserves hc hchild, ho₁, cx_preserves hc hchild,
        hz₁, preserves_below hcompute]
    · rw [hr, hz₂, cx_preserves hc hchild, ho₂, cx_preserves hc hchild,
        preserves_below hcompute]

theorem cellAt_wellFormed (backward : Bool)
    {position workWidth endpointWidth scratchWidth : Nat} (hp : position < workWidth) :
    (cellAt backward position workWidth endpointWidth scratchWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true := by
  apply wellFormed_placeGates (LuoPrefixFixed.cell_disjoint hp)
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simp [CellPlaced.layout] at hj
      omega
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
      simp [cellWiring, CellPlaced.wiring, CellPlaced.layout, Layout.size,
        layout_width, targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, scratchOffset, boundaryOffset] <;> omega
  · apply CellPlaced.component_wellFormed
    cases backward
    · exact BorrowedCell.maj_wellFormed
    · exact BorrowedCell.uma_wellFormed

theorem emit_wellFormed_of_old {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth) : ∀ ctrl depth,
    ((LuoPrefixArithmetic.firstEmit start workWidth endpointWidth scratchWidth tree ctrl depth).all
      (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true →
      (firstEmit start workWidth endpointWidth scratchWidth tree ctrl depth).all
        (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true) ∧
    ((LuoPrefixArithmetic.secondEmit start workWidth endpointWidth scratchWidth tree ctrl depth).all
      (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true →
      (secondEmit start workWidth endpointWidth scratchWidth tree ctrl depth).all
        (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true) := by
  induction tree with
  | empty => intros; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | leaf label =>
    intro ctrl depth
    have hp : label - start < workWidth := by
      simp only [Tree.RangeValid] at hv
      omega
    constructor <;> intro h <;>
      simp only [firstEmit, secondEmit, LuoPrefixArithmetic.firstEmit,
        LuoPrefixArithmetic.secondEmit, List.all_append, Bool.and_eq_true] at h ⊢
    · exact ⟨cellAt_wellFormed false hp, h.2⟩
    · exact ⟨h.1, cellAt_wellFormed true hp⟩
  | node bit zero one hz ho =>
    intro ctrl depth
    obtain ⟨hz₁, hz₂⟩ := hz hv.2.1
      (childControl workWidth endpointWidth depth) (depth + 1)
    obtain ⟨ho₁, ho₂⟩ := ho hv.2.2
      (childControl workWidth endpointWidth depth) (depth + 1)
    constructor <;> intro h <;>
      simp only [firstEmit, secondEmit, LuoPrefixArithmetic.firstEmit,
        LuoPrefixArithmetic.secondEmit, List.all_append, Bool.and_eq_true] at h ⊢
    · rcases h with ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩
      exact ⟨⟨⟨⟨⟨ha, hz₁ hb⟩, hc⟩, ho₁ hd⟩, he⟩, hf⟩
    · rcases h with ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩
      exact ⟨⟨⟨⟨⟨ha, hb⟩, ho₂ hc⟩, hd⟩, hz₂ he⟩, hf⟩

theorem cellAt_ccx (backward : Bool) (position workWidth endpointWidth scratchWidth : Nat) :
    (cellAt backward position workWidth endpointWidth scratchWidth).countP RGate.isCcx =
      if backward then 5 else 4 := by
  cases backward <;>
    simp only [cellAt, Bool.false_eq_true, ↓reduceIte, CellPlaced.gates,
      countP_map_gates (RGate.isCcx_map _)]
  · exact BorrowedCell.maj_ccx
  · exact BorrowedCell.uma_ccx

theorem firstEmit_ccx (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl depth : Nat) :
    (firstEmit start workWidth endpointWidth scratchWidth tree ctrl depth).countP RGate.isCcx =
      2 * tree.internal + 4 * tree.leaves := by
  induction tree generalizing ctrl depth with
  | empty => simp [firstEmit, PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | leaf label =>
    simp [firstEmit, cellAt_ccx, RGate.isCcx,
      PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hz ho =>
    simp [firstEmit, negativeAnd, List.countP_cons, hz, ho, RGate.isCcx,
      PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
    omega

theorem secondEmit_ccx (tree : Tree) (start workWidth endpointWidth scratchWidth ctrl depth : Nat) :
    (secondEmit start workWidth endpointWidth scratchWidth tree ctrl depth).countP RGate.isCcx =
      2 * tree.internal + 5 * tree.leaves := by
  induction tree generalizing ctrl depth with
  | empty => simp [secondEmit, PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | leaf label =>
    simp [secondEmit, cellAt_ccx, RGate.isCcx,
      PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
  | node bit zero one hz ho =>
    simp [secondEmit, negativeAnd, List.countP_cons, hz, ho, RGate.isCcx,
      PrunedSelectSwap.Tree.internal, PrunedSelectSwap.Tree.leaves]
    omega

private theorem outer_below (workWidth endpointWidth scratchWidth : Nat) :
    outerWire < cellScratchWire workWidth endpointWidth scratchWidth := by
  simp [outerWire, cellScratchWire, carryWire, scratchOffset, boundaryOffset]

private theorem accumulator_below (workWidth endpointWidth scratchWidth : Nat) :
    accumulatorWire workWidth endpointWidth scratchWidth <
      cellScratchWire workWidth endpointWidth scratchWidth := by
  simp only [accumulatorWire, cellScratchWire]
  omega

private theorem sign_below (workWidth endpointWidth scratchWidth : Nat) (updateSign : Bool) :
    ∀ g ∈ signUpdateGates workWidth endpointWidth scratchWidth updateSign,
      ∀ k ∈ g.wires, k < cellScratchWire workWidth endpointWidth scratchWidth := by
  cases updateSign
  · simp [signUpdateGates]
  · intro g hg k hk
    simp only [signUpdateGates, ↓reduceIte, List.mem_singleton] at hg
    subst g
    simp [RGate.wires] at hk
    rcases hk with rfl | rfl <;>
      simp [signWire, cellScratchWire, carryWire, scratchOffset, boundaryOffset]

theorem addGates_clear {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (updateSign : Bool) (I : Nat) :
    writeField (actGates (addGates tree start workWidth endpointWidth scratchWidth updateSign) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) 1 0 =
      actGates (LuoPrefixArithmetic.addGates tree start workWidth endpointWidth scratchWidth updateSign)
        (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0) := by
  obtain ⟨hf, hb⟩ := emit_clear hv outerWire 0 (by simpa using hd)
    (outer_below workWidth endpointWidth scratchWidth)
  have hc := cx_clear (outer_below workWidth endpointWidth scratchWidth)
    (accumulator_below workWidth endpointWidth scratchWidth)
  simp only [addGates, LuoPrefixArithmetic.addGates, actGates_append]
  rw [hc, hb, clear_below (sign_below workWidth endpointWidth scratchWidth updateSign), hf, hc]

theorem addGates_preserves {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (updateSign : Bool) (I : Nat) :
    (actGates (addGates tree start workWidth endpointWidth scratchWidth updateSign) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  obtain ⟨hf, hb⟩ := emit_preserves hv outerWire 0 (by simpa using hd)
    (outer_below workWidth endpointWidth scratchWidth)
  have hc := cx_preserves (outer_below workWidth endpointWidth scratchWidth)
    (accumulator_below workWidth endpointWidth scratchWidth)
  simp only [addGates, actGates_append]
  rw [hc, hb, preserves_below (sign_below workWidth endpointWidth scratchWidth updateSign), hf, hc]

theorem addGates_wellFormed {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).all
      (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true := by
  have h := LuoPrefixFixed.addGates_wellFormed hv hd updateSign
  obtain ⟨hf, hb⟩ := emit_wellFormed_of_old hv outerWire 0
  simp only [addGates, LuoPrefixArithmetic.addGates, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨h.1.1.1.1, hf h.1.1.1.2⟩, h.1.1.2⟩, hb h.1.2⟩, h.2⟩

theorem addGates_act {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (updateSign : Bool) (I : Nat) :
    actGates (addGates tree start workWidth endpointWidth scratchWidth updateSign) I =
      writeField
        (actGates (LuoPrefixArithmetic.addGates tree start workWidth endpointWidth scratchWidth updateSign)
          (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0))
        (cellScratchWire workWidth endpointWidth scratchWidth) 1
        (bitValue I (cellScratchWire workWidth endpointWidth scratchWidth)) := by
  rw [← addGates_clear hv hd, ← readField_one]
  have hp : readField
      (actGates (addGates tree start workWidth endpointWidth scratchWidth updateSign) I)
      (cellScratchWire workWidth endpointWidth scratchWidth) 1 =
      readField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 := by
    simp only [readField_one, bitValue, addGates_preserves hv hd]
  rw [← hp, writeField_writeField, writeField_read]

theorem subGates_clear {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (I : Nat) :
    writeField (actGates (subGates tree start workWidth endpointWidth scratchWidth) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) 1 0 =
      actGates (LuoPrefixArithmetic.subGates tree start workWidth endpointWidth scratchWidth)
        (writeField I (cellScratchWire workWidth endpointWidth scratchWidth) 1 0) := by
  have hn := actGates_reverse
    (gs := (addGates tree start workWidth endpointWidth scratchWidth false).reverse)
    (by simpa using addGates_wellFormed hv hd false) I
  simp only [List.reverse_reverse] at hn
  have h := addGates_clear hv hd false
    (actGates (subGates tree start workWidth endpointWidth scratchWidth) I)
  rw [subGates, hn] at h
  have h' := congrArg
    (actGates (LuoPrefixArithmetic.addGates tree start workWidth endpointWidth scratchWidth false).reverse) h
  rw [actGates_reverse (LuoPrefixFixed.addGates_wellFormed hv hd false)] at h'
  exact h'.symm

theorem subGates_preserves {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) (I : Nat) :
    (actGates (subGates tree start workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  have hn := actGates_reverse
    (gs := (addGates tree start workWidth endpointWidth scratchWidth false).reverse)
    (by simpa using addGates_wellFormed hv hd false) I
  simp only [List.reverse_reverse] at hn
  have h := addGates_preserves hv hd false
    (actGates (subGates tree start workWidth endpointWidth scratchWidth) I)
  rw [subGates, hn] at h
  exact h.symm

theorem subGates_wellFormed {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hv : tree.RangeValid start workWidth endpointWidth)
    (hd : tree.depth ≤ scratchWidth) :
    (subGates tree start workWidth endpointWidth scratchWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth scratchWidth).width) = true := by
  simpa [subGates] using addGates_wellFormed hv hd false

theorem addGates_ccx (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).countP RGate.isCcx =
      4 * tree.internal + 9 * tree.leaves := by
  cases updateSign <;>
    simp [addGates, signUpdateGates, firstEmit_ccx, secondEmit_ccx, RGate.isCcx] <;> omega

theorem subGates_ccx (tree : Tree) (start workWidth endpointWidth scratchWidth : Nat) :
    (subGates tree start workWidth endpointWidth scratchWidth).countP RGate.isCcx =
      4 * tree.internal + 9 * tree.leaves := by
  simp only [subGates, List.countP_reverse, addGates_ccx]

end VQ.Euclid.BorrowedPrefix
