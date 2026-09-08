import VQ.Euclid.RangeZero
import VQ.Reversible.BorrowedControl

namespace VQ.Euclid.BorrowedRangeZero

open Reversible

def maskedNotAnd (range source scratch next target : Nat) : List RGate :=
  [.cx next target] ++ BorrowedControl.triple range source next target scratch

def maskedNotBit (range source target : Nat) : List RGate :=
  [.x target, .ccx range source target]

private theorem triple_write {a b c target scratch : Nat}
    (has : a ≠ scratch) (hbs : b ≠ scratch) (hcs : c ≠ scratch)
    (hat : a ≠ target) (hbt : b ≠ target) (hct : c ≠ target)
    (hst : scratch ≠ target) (i : Nat) :
    actGates (BorrowedControl.triple a b c target scratch) i =
      writeField i target 1
        ((bitValue i target + bitValue i a * bitValue i b * bitValue i c) % 2) := by
  rw [BorrowedControl.triple_act has hbs hcs hat hbt hct hst]
  cases ha : i.testBit a <;> cases hb : i.testBit b <;> cases hc : i.testBit c <;>
    simp only [Bool.and_self, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, bitValue, ha, hb, hc,
      Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  all_goals first
    | exact act_x_write target i
    | apply Eq.symm
      apply write_of_bitValue
      simpa only [bitValue, Nat.mod_mod] using
        Nat.mod_eq_of_lt (bitValue_lt i target)

theorem maskedNotAnd_act {range source scratch next target i : Nat}
    (hrs : range ≠ scratch) (hss : source ≠ scratch) (hns : next ≠ scratch)
    (hrt : range ≠ target) (hst : source ≠ target) (hnt : next ≠ target)
    (hstarget : scratch ≠ target) :
    actGates (maskedNotAnd range source scratch next target) i =
      writeField i target 1 (RangeZero.maskedNotAndValue i range source next target) := by
  rw [maskedNotAnd, actGates_append, actGates_cons, actGates_nil, act_cx_write,
    triple_write hrs hss hns hrt hst hnt hstarget,
    bitValue_write_self, bitValue_write_ne hrt, bitValue_write_ne hst,
    bitValue_write_ne hnt, writeField_writeField]
  apply write_congr
  have hr := bitValue_lt i range
  have hs := bitValue_lt i source
  have hn := bitValue_lt i next
  have ht := bitValue_lt i target
  have hr' : bitValue i range = 0 ∨ bitValue i range = 1 := by omega
  have hs' : bitValue i source = 0 ∨ bitValue i source = 1 := by omega
  rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs' <;>
    simp [RangeZero.maskedNotAndValue, RangeZero.maskedBit, hr', hs']
  all_goals omega

theorem maskedNotBit_act {range source target i : Nat}
    (hrt : range ≠ target) (hst : source ≠ target) :
    actGates (maskedNotBit range source target) i =
      writeField i target 1 (RangeZero.maskedNotBitValue i range source target) := by
  rw [maskedNotBit, actGates_cons, actGates_cons, actGates_nil, act_x_write,
    act_ccx_write, bitValue_write_self, bitValue_write_ne hrt,
    bitValue_write_ne hst, writeField_writeField]
  apply write_congr
  have hr := bitValue_lt i range
  have hs := bitValue_lt i source
  have ht := bitValue_lt i target
  have hr' : bitValue i range = 0 ∨ bitValue i range = 1 := by omega
  have hs' : bitValue i source = 0 ∨ bitValue i source = 1 := by omega
  rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs' <;>
    simp [RangeZero.maskedNotBitValue, RangeZero.maskedBit, hr', hs']
  all_goals omega

theorem maskedNotAnd_preserves_borrowed {range source scratch next target i : Nat}
    (hrs : range ≠ scratch) (hss : source ≠ scratch) (hns : next ≠ scratch)
    (hrt : range ≠ target) (hst : source ≠ target) (hnt : next ≠ target)
    (hstarget : scratch ≠ target) :
    (actGates (maskedNotAnd range source scratch next target) i).testBit scratch =
      i.testBit scratch := by
  rw [maskedNotAnd_act hrs hss hns hrt hst hnt hstarget]
  apply testBit_writeField_outside
  omega

theorem maskedNotAnd_wellFormed {range source scratch next target width : Nat}
    (hr : range < width) (hs : source < width) (hd : scratch < width)
    (hn : next < width) (ht : target < width)
    (hrs : range ≠ source) (hrd : range ≠ scratch) (hsd : source ≠ scratch)
    (hnd : next ≠ scratch) (hnt : next ≠ target) (hdt : scratch ≠ target) :
    (maskedNotAnd range source scratch next target).all (RGate.wellFormed width) = true := by
  simp [maskedNotAnd, BorrowedControl.triple, RGate.wellFormed, hr, hs, hd, hn, ht,
    hrs, hrd, hsd, Ne.symm hnd, hnt, hdt]

theorem maskedNotBit_wellFormed {range source target width : Nat}
    (hr : range < width) (hs : source < width) (ht : target < width)
    (hrs : range ≠ source) (hrt : range ≠ target) (hst : source ≠ target) :
    (maskedNotBit range source target).all (RGate.wellFormed width) = true := by
  simp [maskedNotBit, RGate.wellFormed, hr, hs, ht, hrs, hrt, hst]

theorem maskedNotAnd_ccx (range source scratch next target : Nat) :
    (maskedNotAnd range source scratch next target).countP RGate.isCcx = 4 := rfl

theorem maskedNotBit_ccx (range source target : Nat) :
    (maskedNotBit range source target).countP RGate.isCcx = 1 := rfl

theorem maskedNotAnd_clear {range source scratch next target i : Nat}
    (hrs : range ≠ scratch) (hss : source ≠ scratch) (hns : next ≠ scratch)
    (hrt : range ≠ target) (hst : source ≠ target) (hnt : next ≠ target)
    (hstarget : scratch ≠ target) :
    writeField (actGates (maskedNotAnd range source scratch next target) i) scratch 1 0 =
      actGates (RangeZero.maskedNotAndGates range source scratch next target)
        (writeField i scratch 1 0) := by
  rw [maskedNotAnd_act hrs hss hns hrt hst hnt hstarget,
    RangeZero.maskedNotAndGates_act hrs hrt hss hst hns.symm hstarget hnt
      (by simp [bitValue_write_self])]
  simp only [RangeZero.maskedNotAndValue, RangeZero.maskedBit,
    bitValue_write_ne hrs, bitValue_write_ne hss, bitValue_write_ne hns,
    bitValue_write_ne hstarget.symm]
  exact writeField_comm (by omega)

theorem maskedNotBit_clear {range source scratch target i : Nat}
    (hrs : range ≠ scratch) (hss : source ≠ scratch)
    (hrt : range ≠ target) (hst : source ≠ target) (hstarget : scratch ≠ target) :
    writeField (actGates (maskedNotBit range source target) i) scratch 1 0 =
      actGates (RangeZero.maskedNotBitGates range source scratch target)
        (writeField i scratch 1 0) := by
  rw [maskedNotBit_act hrt hst,
    RangeZero.maskedNotBitGates_act hrs hrt hss hst hstarget
      (by simp [bitValue_write_self])]
  simp only [RangeZero.maskedNotBitValue, RangeZero.maskedBit,
    bitValue_write_ne hrs, bitValue_write_ne hss, bitValue_write_ne hstarget.symm]
  exact writeField_comm (by omega)

theorem maskedNotBit_preserves_borrowed {range source scratch target i : Nat}
    (hrt : range ≠ target) (hst : source ≠ target) (hstarget : scratch ≠ target) :
    (actGates (maskedNotBit range source target) i).testBit scratch = i.testBit scratch := by
  rw [maskedNotBit_act hrt hst]
  exact testBit_writeField_outside (by omega)

end VQ.Euclid.BorrowedRangeZero
