import VQ.Reversible.BorrowedPermutation
import VQ.Reversible.BorrowedEquivalence

namespace VQ.Reversible.BorrowedPermutation

def cleanSwap (a b x y scratch : Nat) : List RGate :=
  [.ccx a b scratch] ++ fredkin scratch x y ++ [.ccx a b scratch]

theorem swap_eq_clean {a b x y scratch : Nat}
    (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : Valid a b scratch (x, y)) {I : Nat}
    (hs : I.testBit scratch = false) :
    actGates (swap a b x y scratch) I = actGates (cleanSwap a b x y scratch) I := by
  obtain ⟨hax, hay, hbx, hby, hsx, hsy, hxy⟩ := h
  dsimp only [Prod.fst, Prod.snd] at hax hay hbx hby hsx hsy hxy
  have hcancel (n u v : Nat) : (n ^^^ u ^^^ v) ^^^ u = n ^^^ v := by
    rw [show n ^^^ u ^^^ v = (n ^^^ v) ^^^ u by ac_rfl, Nat.xor_assoc,
      Nat.xor_self, Nat.xor_zero]
  have hcancel₂ (n u v z : Nat) : n ^^^ u ^^^ v ^^^ z ^^^ u = n ^^^ v ^^^ z := by
    rw [show n ^^^ u ^^^ v ^^^ z = n ^^^ (v ^^^ z) ^^^ u by ac_rfl,
      Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.xor_assoc]
  cases ha : I.testBit a <;> cases hb : I.testBit b <;>
    cases hx : I.testBit x <;> cases hy : I.testBit y <;>
    simp [swap, cleanSwap, fredkin, BorrowedControl.triple, actGates, RGate.act,
      ha, hb, hx, hy, hs, RGate.testBit_xor_of_ne has,
      RGate.testBit_xor_of_ne hbs, RGate.testBit_xor_of_ne hax,
      RGate.testBit_xor_of_ne hbx, RGate.testBit_xor_of_ne hay,
      RGate.testBit_xor_of_ne hby, RGate.testBit_xor_of_ne hsx,
      RGate.testBit_xor_of_ne hsy, RGate.testBit_xor_of_ne (Ne.symm hsx),
      RGate.testBit_xor_of_ne (Ne.symm hsy),
      RGate.testBit_xor_of_ne hxy, RGate.testBit_xor_of_ne (Ne.symm hxy),
      RGate.xor_cancel, hcancel, hcancel₂]

theorem swap_equiv {a b x y scratch : Nat}
    (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : Valid a b scratch (x, y)) :
    BorrowedEquivalent scratch (cleanSwap a b x y scratch) (swap a b x y scratch) := by
  have hout : ∀ g ∈ swapWires x y, scratch ∉ g.wires := by
    intro g hg
    simp [swapWires] at hg
    rcases hg with rfl | rfl | rfl <;>
      simp [RGate.wires, h.2.2.2.2.1, h.2.2.2.2.2.1]
  constructor
  · intro I
    have hz : (writeField I scratch 1 0).testBit scratch = false := by
      rw [testBit_writeField_inside (by omega) (by omega)]
      simp
    rw [← swap_eq_clean has hbs h hz, swap_act has hbs h, swap_act has hbs h,
      testBit_writeField_outside (by omega : a < scratch ∨ scratch + 1 ≤ a),
      testBit_writeField_outside (by omega : b < scratch ∨ scratch + 1 ≤ b)]
    split
    · exact ((BorrowedEquivalent.of_avoids hout).projected I)
    · rfl
  · intro I
    rw [swap_act has hbs h]
    split
    · exact testBit_actGates_of_outside hout I
    · rfl

def sharedSwaps (a b scratch : Nat) (pairs : List (Nat × Nat)) : List RGate :=
  [.ccx a b scratch] ++
    pairs.flatMap (fun p => fredkin scratch p.1 p.2) ++ [.ccx a b scratch]

theorem sharedSwaps_equiv {a b scratch : Nat} {pairs : List (Nat × Nat)}
    (hab : a ≠ b) (has : a ≠ scratch) (hbs : b ≠ scratch)
    (h : ∀ p ∈ pairs, Valid a b scratch p) :
    BorrowedEquivalent scratch (sharedSwaps a b scratch pairs)
      (swaps a b scratch pairs) := by
  have hc : (RGate.ccx a b scratch).wellFormed (a + b + scratch + 1) = true := by
    simp [RGate.wellFormed, hab, has, hbs]; omega
  induction pairs with
  | nil =>
      constructor
      · intro I
        simpa [sharedSwaps, swaps, actGates] using
          (RGate.act_act hc (writeField I scratch 1 0)).symm
      · intro I; rfl
  | cons p pairs ih =>
      have ht := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hp := swap_equiv has hbs (h p List.mem_cons_self)
      have he := hp.append ht
      constructor
      · intro I
        change writeField (actGates (swap a b p.1 p.2 scratch ++ swaps a b scratch pairs) I)
          scratch 1 0 = _
        rw [he.projected]
        simp only [cleanSwap, sharedSwaps, List.flatMap_cons, actGates_append,
          actGates_cons, actGates_nil, RGate.act_act hc]
      · exact he.preserved

end VQ.Reversible.BorrowedPermutation
