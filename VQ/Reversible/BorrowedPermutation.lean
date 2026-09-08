import VQ.Reversible.BorrowedControl
import VQ.Reversible.Permutation

namespace VQ.Reversible.BorrowedPermutation

def swap (a b x y scratch : Nat) : List RGate :=
  [.cx y x] ++ BorrowedControl.triple a b x y scratch ++ [.cx y x]

def Valid (a b scratch : Nat) (pair : Nat × Nat) : Prop :=
  a ≠ pair.1 ∧ a ≠ pair.2 ∧ b ≠ pair.1 ∧ b ≠ pair.2 ∧
    scratch ≠ pair.1 ∧ scratch ≠ pair.2 ∧ pair.1 ≠ pair.2

theorem swap_act {a b x y scratch : Nat}
    (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : Valid a b scratch (x, y)) (i : Nat) :
    actGates (swap a b x y scratch) i =
      if i.testBit a && i.testBit b then actGates (swapWires x y) i else i := by
  obtain ⟨hax, hay, hbx, hby, hsx, hsy, hxy⟩ := h
  let pre := RGate.cx y x
  have ha : (pre.act i).testBit a = i.testBit a := by
    apply RGate.testBit_act_of_not_mem
    simp [pre, RGate.wires, hax, hay]
  have hb : (pre.act i).testBit b = i.testBit b := by
    apply RGate.testBit_act_of_not_mem
    simp [pre, RGate.wires, hbx, hby]
  have hcancel : pre.act (pre.act i) = i := by
    apply RGate.act_act (w := x + y + 1)
    simp [pre, RGate.wellFormed, Ne.symm hxy]
    omega
  change pre.act (actGates (BorrowedControl.triple a b x y scratch) (pre.act i)) = _
  rw [BorrowedControl.triple_act has hbs (Ne.symm hsx) hay hby hxy hsy, ha, hb]
  cases ha' : i.testBit a <;> cases hb' : i.testBit b
  · simpa using hcancel
  · simpa using hcancel
  · simpa using hcancel
  · simp only [Bool.and_self, Bool.true_and, ↓reduceIte]
    change pre.act (RGate.act (.cx x y) (pre.act i)) =
      actGates (swapWires x y) i
    rfl

def swaps (a b scratch : Nat) (pairs : List (Nat × Nat)) : List RGate :=
  pairs.flatMap fun pair => swap a b pair.1 pair.2 scratch

def swapsBody (pairs : List (Nat × Nat)) : List RGate :=
  pairs.flatMap fun pair => swapWires pair.1 pair.2

theorem swaps_act {a b scratch : Nat} {pairs : List (Nat × Nat)}
    (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : ∀ pair ∈ pairs, Valid a b scratch pair) (i : Nat) :
    actGates (swaps a b scratch pairs) i =
      if i.testBit a && i.testBit b then actGates (swapsBody pairs) i else i := by
  induction pairs generalizing i with
  | nil => simp [swaps, swapsBody, actGates_nil]
  | cons pair pairs ih =>
      have hp := h pair List.mem_cons_self
      have htail := fun pair' hp' => h pair' (List.mem_cons_of_mem pair hp')
      simp only [swaps, swapsBody, List.flatMap_cons, actGates_append]
      rw [swap_act has hbs hp]
      cases ha : i.testBit a <;> cases hb : i.testBit b
      · simpa [swaps, ha, hb] using ih htail i
      · simpa [swaps, ha, hb] using ih htail i
      · simpa [swaps, ha, hb] using ih htail i
      · have ha' : (actGates (swapWires pair.1 pair.2) i).testBit a = true := by
          rw [testBit_actGates_of_outside]
          · exact ha
          · intro g hg
            simp [swapWires] at hg
            rcases hg with rfl | rfl | rfl <;> simp [RGate.wires, hp.1, hp.2.1]
        have hb' : (actGates (swapWires pair.1 pair.2) i).testBit b = true := by
          rw [testBit_actGates_of_outside]
          · exact hb
          · intro g hg
            simp [swapWires] at hg
            rcases hg with rfl | rfl | rfl <;>
              simp [RGate.wires, hp.2.2.1, hp.2.2.2.1]
        simpa [swaps, swapsBody, ha', hb'] using
          ih htail (actGates (swapWires pair.1 pair.2) i)

theorem swaps_preserves_borrowed {a b scratch : Nat} {pairs : List (Nat × Nat)}
    (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : ∀ pair ∈ pairs, Valid a b scratch pair) (i : Nat) :
    (actGates (swaps a b scratch pairs) i).testBit scratch = i.testBit scratch := by
  rw [swaps_act has hbs h]
  split
  · apply testBit_actGates_of_outside
    intro g hg
    obtain ⟨pair, hp, hg⟩ := List.exists_of_mem_flatMap hg
    have hv := h pair hp
    simp [swapWires] at hg
    rcases hg with rfl | rfl | rfl <;>
      simp [RGate.wires, hv.2.2.2.2.1, hv.2.2.2.2.2.1]
  · rfl

theorem swap_wellFormed {a b x y scratch width : Nat}
    (ha : a < width) (hb : b < width) (hx : x < width)
    (hy : y < width) (hs : scratch < width)
    (hab : a ≠ b) (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : Valid a b scratch (x, y)) :
    (swap a b x y scratch).all (RGate.wellFormed width) = true := by
  obtain ⟨hax, hay, hbx, hby, hsx, hsy, hxy⟩ := h
  simp [swap, BorrowedControl.triple, RGate.wellFormed, ha, hb, hx, hy, hs,
    hab, has, hbs, hsx, hsy, hxy, Ne.symm hxy]

theorem swaps_wellFormed {a b scratch width : Nat} {pairs : List (Nat × Nat)}
    (ha : a < width) (hb : b < width) (hs : scratch < width)
    (hab : a ≠ b) (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : ∀ pair ∈ pairs,
      Valid a b scratch pair ∧ pair.1 < width ∧ pair.2 < width) :
    (swaps a b scratch pairs).all (RGate.wellFormed width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨pair, hp, hg⟩ := List.exists_of_mem_flatMap hg
  obtain ⟨hv, hx, hy⟩ := h pair hp
  exact List.all_eq_true.mp (swap_wellFormed ha hb hx hy hs hab has hbs hv) g hg

theorem swaps_ccx (a b scratch : Nat) (pairs : List (Nat × Nat)) :
    (swaps a b scratch pairs).countP RGate.isCcx = 4 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      simp [swaps, swap, BorrowedControl.triple, List.countP_cons, RGate.isCcx] at *
      omega

theorem swaps_cx (a b scratch : Nat) (pairs : List (Nat × Nat)) :
    (swaps a b scratch pairs).countP RGate.isCx = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      simp [swaps, swap, BorrowedControl.triple, List.countP_cons, RGate.isCx] at *
      omega

end VQ.Reversible.BorrowedPermutation
