import VQ.Euclid.BorrowedSelector
import VQ.Reversible.Bit
import VQ.Reversible.Wiring

namespace VQ.Euclid.BorrowedSelectorPlaced

open Reversible

def layout : Layout := [9, 1, 6, 1]

def wiring (source flag scratch borrowed : Nat) : Wiring :=
  [source, flag, scratch, borrowed]

def zeroTest (source flag scratch borrowed : Nat) : List RGate :=
  (BorrowedSelector.gates 511 9).map
    (RGate.map (place layout (wiring source flag scratch borrowed)))

theorem zeroTest_act {source flag scratch borrowed i : Nat}
    (hd : Wiring.Disjoint layout (wiring source flag scratch borrowed))
    (hclear : readField i scratch 6 = 0) :
    actGates (zeroTest source flag scratch borrowed) i =
      writeField i flag 1
        ((bitValue i flag + if readField i source 9 = 511 then 1 else 0) % 2) := by
  let W := wiring source flag scratch borrowed
  let gathered := gatherBits (place layout W) layout.width i
  have hscratch : readField gathered 10 6 = 0 := by
    have h := readField_gatherBits layout W 2 i (by simp [W, wiring])
    simpa [gathered, layout, W, wiring, Layout.offset, Layout.size] using
      h.trans hclear
  have hsource : Selector.source 9 gathered = readField i source 9 := by
    have h := readField_gatherBits layout W 0 i (by simp [W, wiring])
    simpa [gathered, layout, W, wiring, Selector.source, Selector.layout,
      Layout.read, Layout.offset, Layout.size] using h
  have hflag : Selector.flag 9 gathered = bitValue i flag := by
    have h := readField_gatherBits layout W 1 i (by simp [W, wiring])
    simpa [gathered, layout, W, wiring, Selector.flag, Selector.layout,
      Layout.read, Layout.offset, Layout.size, readField_one] using h
  have hlocal : actGates (BorrowedSelector.gates 511 9) gathered =
      layout.write gathered 1
        ((bitValue i flag + if readField i source 9 = 511 then 1 else 0) % 2) := by
    rw [BorrowedSelector.nine_bit_zero_test hscratch, Selector.out, hsource, hflag]
    rfl
  exact actGates_placed_write hd (by simp [layout, wiring]) (by simp [layout])
    (fun g hg => List.all_eq_true.mp BorrowedSelector.nine_bit_zero_test_wellFormed g hg)
    hlocal

theorem zeroTest_wellFormed {source flag scratch borrowed width : Nat}
    (hd : Wiring.Disjoint layout (wiring source flag scratch borrowed))
    (hsource : source + 9 ≤ width) (hflag : flag + 1 ≤ width)
    (hscratch : scratch + 6 ≤ width) (hborrowed : borrowed + 1 ≤ width) :
    (zeroTest source flag scratch borrowed).all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates hd (by simp [layout, wiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [layout] at hj; omega
    rcases hj' with rfl | rfl | rfl | rfl <;>
      simp [layout, wiring, Layout.size, hsource, hflag, hscratch, hborrowed]
  · intro g hg
    exact List.all_eq_true.mp BorrowedSelector.nine_bit_zero_test_wellFormed g hg

theorem zeroTest_ccx (source flag scratch borrowed : Nat) :
    (zeroTest source flag scratch borrowed).countP RGate.isCcx = 16 := by
  rw [zeroTest, countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact BorrowedSelector.nine_bit_zero_test_ccx

theorem wiring_disjoint_of_order {source flag scratch borrowed : Nat}
    (hsource : source + 9 ≤ flag) (hflag : flag + 1 ≤ scratch)
    (hscratch : scratch + 6 ≤ borrowed) :
    Wiring.Disjoint layout (wiring source flag scratch borrowed) := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [wiring] at hj; omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by simp [wiring] at hk; omega
  rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl <;>
    simp_all [layout, wiring, Layout.size] <;> omega

theorem quotientLength_disjoint : Wiring.Disjoint layout (wiring 527 559 564 570) := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [wiring] at hj; omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by simp [wiring] at hk; omega
  rcases hj' with rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl <;>
    simp_all [layout, wiring, Layout.size]

theorem quotientLength_act {i : Nat} (hclear : readField i 564 6 = 0) :
    actGates (zeroTest 527 559 564 570) i =
      writeField i 559 1
        ((bitValue i 559 + if readField i 527 9 = 511 then 1 else 0) % 2) :=
  zeroTest_act quotientLength_disjoint hclear

theorem quotientLength_preserves_field {i : Nat}
    (hclear : readField i 564 6 = 0) :
    readField (actGates (zeroTest 527 559 564 570) i) 570 256 =
      readField i 570 256 := by
  rw [quotientLength_act hclear, readField_writeField_of_disjoint (by decide)]

theorem quotientLength_wellFormed :
    (zeroTest 527 559 564 570).all (RGate.wellFormed 571) = true :=
  zeroTest_wellFormed quotientLength_disjoint (by decide) (by decide)
    (by decide) (by decide)

end VQ.Euclid.BorrowedSelectorPlaced
