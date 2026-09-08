import VQ.Euclid.BorrowedPhase
import VQ.Euclid.BorrowedSelectorProjection

namespace VQ.Euclid.BorrowedPhase

open Reversible

private theorem oldTest_eq (source flag : Nat) :
    (Selector.gates 511 9).map (RGate.map
      (place BorrowedSelectorPlaced.layout
        (BorrowedSelectorPlaced.wiring source flag 35 41))) =
      Placed.selectorGates 511 9 source flag 35 := by
  have hm : Selector.masks 511 9 = [] := by decide
  simp [Placed.selectorGates, Selector.circuit, Selector.gates, hm,
    List.range_succ, Selector.conjunction, Selector.scratchOffset, Selector.flagWire,
    BorrowedSelectorPlaced.layout, BorrowedSelectorPlaced.wiring,
    Selector.layout, Placed.selectorWiring, RGate.map, place]

theorem test_projection {source flag : Nat}
    (hs : source + 9 ≤ flag) (hf : flag + 1 ≤ 35) (I : Nat) :
    writeField (actGates (test source flag) I) 41 1 0 =
      actGates (Placed.selectorGates 511 9 source flag 35) (writeField I 41 1 0) := by
  have hinj := place_inj
    (by simp [BorrowedSelectorPlaced.layout, BorrowedSelectorPlaced.wiring])
    (BorrowedSelectorPlaced.wiring_disjoint_of_order hs hf (by decide : 35 + 6 ≤ 41))
  have h := actGates_map_clear_bit hinj
    (List.all_eq_true.mp BorrowedSelector.nine_bit_zero_test_wellFormed)
    (List.all_eq_true.mp BorrowedSelector.zero_test_old_wellFormed)
    (k := 16) (by decide) BorrowedSelector.zero_test_clear I
  rw [oldTest_eq] at h
  exact h

theorem test_borrowed {source flag : Nat}
    (hs : source + 9 ≤ flag) (hf : flag + 1 ≤ 35) (I : Nat) :
    (actGates (test source flag) I).testBit 41 = I.testBit 41 := by
  have hinj := place_inj
    (by simp [BorrowedSelectorPlaced.layout, BorrowedSelectorPlaced.wiring])
    (BorrowedSelectorPlaced.wiring_disjoint_of_order hs hf (by decide : 35 + 6 ≤ 41))
  exact actGates_map_preserves_bit hinj
    (List.all_eq_true.mp BorrowedSelector.nine_bit_zero_test_wellFormed)
    (k := 16) (by decide) BorrowedSelector.zero_test_preserves I

private theorem q_projection (I : Nat) :
    writeField (actGates (test 3 30) I) 41 1 0 =
      actGates (Phase.qSelector 9 9) (writeField I 41 1 0) :=
  test_projection (by decide) (by decide) I

private theorem r_projection (I : Nat) :
    writeField (actGates (test 12 31) I) 41 1 0 =
      actGates (Phase.rPrimeSelector 9 9) (writeField I 41 1 0) :=
  test_projection (by decide) (by decide) I

private theorem shift_projection (I : Nat) :
    writeField (actGates (test 21 32) I) 41 1 0 =
      actGates (Phase.shiftSelector 9 9) (writeField I 41 1 0) :=
  test_projection (by decide) (by decide) I

private theorem logic_below : (Phase.logicGates 9 9).all (RGate.wellFormed 41) = true := by
  decide

private theorem clear_below {gs : List RGate}
    (h : gs.all (RGate.wellFormed 41) = true) (I : Nat) :
    writeField (actGates gs I) 41 1 0 = actGates gs (writeField I 41 1 0) :=
  (actGates_write_of_outside (fun g hg _ hq => Or.inl
    (wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)) I).symm

theorem gates_projection (I : Nat) :
    writeField (actGates gates I) 41 1 0 = actGates (Phase.gates 9 9) (writeField I 41 1 0) := by
  simp only [gates, selectGates, unselectGates, Phase.gates, actGates_append]
  rw [q_projection, r_projection, shift_projection, clear_below logic_below,
    shift_projection, r_projection, q_projection]

theorem gates_borrowed (I : Nat) :
    (actGates gates I).testBit 41 = I.testBit 41 := by
  have hp := testBit_actGates_of_outside (b := 41) (fun g hg =>
    not_mem_wires_of_wellFormed (List.all_eq_true.mp logic_below g hg) (by decide))
  have hq := test_borrowed (source := 3) (flag := 30) (by decide) (by decide)
  have hr := test_borrowed (source := 12) (flag := 31) (by decide) (by decide)
  have hs := test_borrowed (source := 21) (flag := 32) (by decide) (by decide)
  simp only [gates, selectGates, unselectGates, actGates_append]
  rw [hq, hr, hs, hp, hs, hr, hq]

theorem compactGates_projection (I : Nat) :
    writeField (actGates compactGates I) 41 1 0 =
      actGates CompactPhase.gates (writeField I 41 1 0) := by
  have hx : ([.x 20] : List RGate).all (RGate.wellFormed 41) = true := by decide
  simp only [compactGates, CompactPhase.gates, actGates_append]
  rw [clear_below hx, gates_projection, clear_below hx]
  rfl

theorem compactGates_borrowed (I : Nat) :
    (actGates compactGates I).testBit 41 = I.testBit 41 := by
  have hx : ∀ g ∈ [RGate.x 20], 41 ∉ g.wires := by decide
  simp only [compactGates, actGates_append]
  rw [testBit_actGates_of_outside hx, gates_borrowed, testBit_actGates_of_outside hx]

end VQ.Euclid.BorrowedPhase
