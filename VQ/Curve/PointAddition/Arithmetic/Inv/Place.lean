import VQ.Curve.PointAddition.Arithmetic.Inv.Add
import VQ.Curve.PointAddition.Arithmetic.Inv.Geom
import VQ.Reversible.Wiring

/-!
# Adder placement

Every arithmetic step applies the Cuccaro adder forward or backward to three
registers at a selected width.  `VQ.Reversible.place` maps component wires to
absolute wires, and `actGates_placed_write` lifts component semantics to the
placed gates.  `addAt` and `subAt` package these operations at absolute offsets.

The adder's layout is `[w, w, 1]`: augend, addend, and one carry wire.  It
leaves the augend alone and overwrites the addend with the wrapped sum, so
subtraction is the same gates reversed.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible

/-- The adder's own layout at width `w`. -/
def addL (w : Nat) : Layout := [w, w, 1]

theorem addL_width (w : Nat) : (addL w).width = 2 * w + 1 := by
  unfold addL; simp only [Layout.width]; omega

theorem addL_size0 (w : Nat) : (addL w).size 0 = w := rfl
theorem addL_size1 (w : Nat) : (addL w).size 1 = w := rfl
theorem addL_size2 (w : Nat) : (addL w).size 2 = 1 := rfl

/-- Three registers of sizes `w`, `w`, and one are pairwise disjoint. -/
theorem disjoint3 {w oa ob oc : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob) :
    Wiring.Disjoint (addL w) [oa, ob, oc] := by
  intro j k hj hk hjk
  simp only [List.length_cons, List.length_nil] at hj hk
  match j, k with
  | 0, 0 => exact absurd rfl hjk
  | 0, 1 => exact hab
  | 0, 2 => exact hac
  | 1, 0 => exact hab.symm
  | 1, 1 => exact absurd rfl hjk
  | 1, 2 => exact hbc
  | 2, 0 => exact hac.symm
  | 2, 1 => exact hbc.symm
  | 2, 2 => exact absurd rfl hjk
  | _ + 3, _ => omega
  | _, _ + 3 => omega

/-- The adder placed on three absolute offsets. -/
def addAt (w oa ob oc : Nat) : List RGate :=
  (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen w).gates.map (RGate.map (place (addL w) [oa, ob, oc]))

/-- Subtraction: the same gates in reverse. -/
def subAt (w oa ob oc : Nat) : List RGate := (addAt w oa ob oc).reverse

/-- Every gate of the adder is well formed at its own width. -/
theorem add_wf (w : Nat) : ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen w).gates, g.wellFormed (addL w).width = true := by
  intro g hg
  have h := VQ.Curve.PointAddition.Arithmetic.Inv.Add.wf w
  have : (addL w).width = (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen w).width := by
    rw [addL_width]; rfl
  rw [this]
  exact (List.all_eq_true.mp h) g hg

/-- The placed adder overwrites the addend with the wrapped sum of the two
operands and the carry wire.  It restores the augend and carry wire, so the
reversed gates implement subtraction.

The carry-in is stated rather than fixed at zero, because the comparison needs
it at one: complementing the augend and adding with a carry of one is
subtraction, and the overflow bit is the comparison. -/
theorem addAt_act_carry {w oa ob oc I a b c : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob)
    (h0 : readField I oa w = a) (h1 : readField I ob w = b)
    (h2 : readField I oc 1 = c) :
    actGates (addAt w oa ob oc) I = writeField I ob w ((a + b + c) % 2 ^ w) := by
  have hd := disjoint3 hab hac hbc
  have hkey :
      actGates (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen w).gates
          (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I)
        = (addL w).write
            (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I) 1
              ((a + b + c) % 2 ^ w) := by
    have hg0 : readField (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I) 0 w = a := by
      have := readField_gatherBits (addL w) [oa, ob, oc] 0 I
        (show 0 < ([oa, ob, oc] : Wiring).length by simp)
      simpa [addL, Layout.offset, Layout.size] using this.trans h0
    have hg1 : readField (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I) w w = b := by
      have := readField_gatherBits (addL w) [oa, ob, oc] 1 I
        (show 1 < ([oa, ob, oc] : Wiring).length by simp)
      simpa [addL, Layout.offset, Layout.size] using this.trans h1
    have hg2 : readField (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I)
        (2 * w) 1 = c := by
      have := readField_gatherBits (addL w) [oa, ob, oc] 2 I
        (show 2 < ([oa, ob, oc] : Wiring).length by simp)
      simpa [addL, Layout.offset, Layout.size, Nat.two_mul] using this.trans h2
    have hbody := VQ.Curve.PointAddition.Arithmetic.Inv.Add.body_act w w 0
      (gatherBits (place (addL w) [oa, ob, oc]) (addL w).width I) (by omega)
    show actGates (VQ.Curve.PointAddition.Arithmetic.Inv.Add.body w 0 w) _ = _
    rw [hbody, VQ.Curve.PointAddition.Arithmetic.Inv.Add.carryWire_zero, ← VQ.Curve.PointAddition.Arithmetic.Inv.Add.readField_one, Nat.add_zero, hg0, hg1, hg2]
    rfl
  have := actGates_placed_write (gs := (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen w).gates) (L := addL w)
    (W := [oa, ob, oc]) (k := 1) hd (by simp [addL]) (by simp [addL]) (add_wf w) hkey
  simpa [addAt, addL, Layout.size] using this

/-- The carry-free case, which is ordinary addition. -/
theorem addAt_act {w oa ob oc I a b : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob)
    (h0 : readField I oa w = a) (h1 : readField I ob w = b)
    (h2 : readField I oc 1 = 0) :
    actGates (addAt w oa ob oc) I = writeField I ob w ((a + b) % 2 ^ w) := by
  simpa using addAt_act_carry hab hac hbc h0 h1 h2

/-- The placed gates are well formed at any width the three registers fit in. -/
theorem addAt_wf {w oa ob oc Wd : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob)
    (ha : oa + w ≤ Wd) (hb : ob + w ≤ Wd) (hc : oc + 1 ≤ Wd) :
    (addAt w oa ob oc).all (RGate.wellFormed Wd) = true := by
  refine wellFormed_placeGates (disjoint3 hab hac hbc) (by simp [addL]) ?_ (add_wf w)
  intro j hj
  simp only [addL, List.length_cons, List.length_nil] at hj
  match j with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hc
  | _ + 3 => omega

/-- The reversed adder subtracts.  The addend comes out `b - a` modulo
`2 ^ w`, written as `b + (2 ^ w - a)` because these are natural numbers. -/
theorem subAt_act {w oa ob oc I a b Wd : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob)
    (hwa : oa + w ≤ Wd) (hwb : ob + w ≤ Wd) (hwc : oc + 1 ≤ Wd)
    (h0 : readField I oa w = a) (h1 : readField I ob w = b)
    (h2 : readField I oc 1 = 0) :
    actGates (subAt w oa ob oc) I = writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w) := by
  have hbw : b < 2 ^ w := by rw [← h1]; exact readField_lt _ _ _
  have haw : a < 2 ^ w := by rw [← h0]; exact readField_lt _ _ _
  -- `J` is the state the forward adder would have to start from.
  have hJ0 : readField (writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w)) oa w = a := by
    rw [readField_writeField_of_disjoint (by omega)]; exact h0
  have hJ1 : readField (writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w)) ob w
      = (b + (2 ^ w - a)) % 2 ^ w :=
    readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos w))
  have hJ2 : readField (writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w)) oc 1 = 0 := by
    rw [readField_writeField_of_disjoint (by omega)]; exact h2
  have hfwd := addAt_act (w := w) hab hac hbc hJ0 hJ1 hJ2
  have harith : (a + (b + (2 ^ w - a)) % 2 ^ w) % 2 ^ w = b := by
    rw [Nat.add_mod_mod]
    have e : a + (b + (2 ^ w - a)) = b + 2 ^ w := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hbw]
  rw [harith] at hfwd
  have hback : writeField (writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w)) ob w b = I := by
    rw [writeField_writeField, ← h1, writeField_read]
  rw [hback] at hfwd
  have := actGates_reverse (w := Wd) (addAt_wf hab hac hbc hwa hwb hwc)
    (writeField I ob w ((b + (2 ^ w - a)) % 2 ^ w))
  rw [hfwd] at this
  exact this

end VQ.Curve.PointAddition.Arithmetic.Inv
