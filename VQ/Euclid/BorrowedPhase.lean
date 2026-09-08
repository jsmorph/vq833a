import VQ.Euclid.BorrowedSelectorPlaced
import VQ.Euclid.Phase
import VQ.Euclid.CompactPhase

namespace VQ.Euclid.BorrowedPhase

open Reversible

def test (source flag : Nat) : List RGate :=
  BorrowedSelectorPlaced.zeroTest source flag 35 41

def selectGates : List RGate := test 3 30 ++ test 12 31 ++ test 21 32
def unselectGates : List RGate := test 21 32 ++ test 12 31 ++ test 3 30
def gates : List RGate := selectGates ++ Phase.logicGates 9 9 ++ unselectGates

private theorem test_act {source flag i : Nat}
    (hsource : source + 9 ≤ flag) (hflag : flag + 1 ≤ 35)
    (hclear : readField i 35 6 = 0) :
    actGates (test source flag) i =
      writeField i flag 1
        ((bitValue i flag + Phase.selectorValue 9 source i) % 2) := by
  exact BorrowedSelectorPlaced.zeroTest_act
    (BorrowedSelectorPlaced.wiring_disjoint_of_order hsource hflag (by decide)) hclear

private theorem test_set {source flag i : Nat}
    (hsource : source + 9 ≤ flag) (hflag : flag + 1 ≤ 35)
    (hclear : readField i 35 6 = 0) (hzero : bitValue i flag = 0) :
    actGates (test source flag) i =
      writeField i flag 1 (Phase.selectorValue 9 source i) := by
  rw [test_act hsource hflag hclear, hzero, Nat.zero_add,
    Nat.mod_eq_of_lt (Phase.selectorValue_lt 9 source i)]

private theorem test_clear {source flag i : Nat}
    (hsource : source + 9 ≤ flag) (hflag : flag + 1 ≤ 35)
    (hclear : readField i 35 6 = 0)
    (hvalue : bitValue i flag = Phase.selectorValue 9 source i) :
    actGates (test source flag) i = writeField i flag 1 0 := by
  rw [test_act hsource hflag hclear, hvalue]
  apply write_congr
  have h := Phase.selectorValue_lt 9 source i
  omega

theorem select_act {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hclear : readField i 35 6 = 0) :
    actGates selectGates i = Phase.selected 9 9 i := by
  let j := writeField i 30 1 (Phase.selectorValue 9 3 i)
  let k := writeField j 31 1 (Phase.selectorValue 9 12 j)
  have hjclear : readField j 35 6 = 0 := by
    rw [readField_writeField_of_disjoint (by decide), hclear]
  have hjr : bitValue j 31 = 0 := by
    rw [bitValue_write_ne (by decide), hr]
  have hkclear : readField k 35 6 = 0 := by
    rw [readField_writeField_of_disjoint (by decide), hjclear]
  have hks : bitValue k 32 = 0 := by
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide), hs]
  rw [selectGates, actGates_append, actGates_append,
    test_set (by decide) (by decide) hclear hq]
  change actGates (test 21 32) (actGates (test 12 31) j) = _
  rw [test_set (by decide) (by decide) hjclear hjr]
  change actGates (test 21 32) k = _
  rw [test_set (by decide) (by decide) hkclear hks]
  rfl

theorem unselect_act {i : Nat}
    (hq : bitValue i 30 = Phase.selectorValue 9 3 i)
    (hr : bitValue i 31 = Phase.selectorValue 9 12 i)
    (hs : bitValue i 32 = Phase.selectorValue 9 21 i)
    (hclear : readField i 35 6 = 0) :
    actGates unselectGates i = Phase.cleaned 9 9 i := by
  let j := writeField i 32 1 0
  let k := writeField j 31 1 0
  have hjclear : readField j 35 6 = 0 := by
    rw [readField_writeField_of_disjoint (by decide), hclear]
  have hjr : bitValue j 31 = Phase.selectorValue 9 12 j := by
    rw [bitValue_write_ne (by decide), hr]
    simp only [Phase.selectorValue, j]
    rw [readField_writeField_of_disjoint (by decide)]
  have hkclear : readField k 35 6 = 0 := by
    rw [readField_writeField_of_disjoint (by decide), hjclear]
  have hkq : bitValue k 30 = Phase.selectorValue 9 3 k := by
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide), hq]
    simp only [Phase.selectorValue, k, j]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
  rw [unselectGates, actGates_append, actGates_append,
    test_clear (by decide) (by decide) hclear hs]
  change actGates (test 3 30) (actGates (test 12 31) j) = _
  rw [test_clear (by decide) (by decide) hjclear hjr]
  change actGates (test 3 30) k = _
  rw [test_clear (by decide) (by decide) hkclear hkq]
  rfl

private theorem selected_read {i off width : Nat}
    (h : off + width ≤ 30 ∨ 33 ≤ off) :
    readField (Phase.selected 9 9 i) off width = readField i off width := by
  apply Phase.selected_preserves_field <;>
    norm_num [Phase.zeroQWire, Phase.zeroRPrimeWire, Phase.zeroShiftWire,
      Phase.shiftOffset] <;> omega

private theorem logic_read {i off width : Nat}
    (h : 3 ≤ off ∧ off + width ≤ 33 ∨ 35 ≤ off) :
    readField (Phase.logicOut 9 9 i) off width = readField i off width := by
  apply Phase.logicOut_preserves_field <;>
    norm_num [Phase.phase1Wire, Phase.phase2Wire, Phase.signWire,
      Phase.conditionWire, Phase.temporaryWire, Phase.zeroQWire, Phase.shiftOffset] <;> omega

theorem gates_act {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hclear : readField i 35 6 = 0) :
    actGates gates i = Phase.out 9 9 i := by
  let s := Phase.selected 9 9 i
  let j := Phase.logicOut 9 9 s
  have flags : bitValue s 30 = Phase.selectorValue 9 3 i ∧
      bitValue s 31 = Phase.selectorValue 9 12 i ∧
      bitValue s 32 = Phase.selectorValue 9 21 i := Phase.selected_flags 9 9 i
  have hjq : bitValue j 30 = Phase.selectorValue 9 3 j := by
    rw [← readField_one, logic_read (by decide), readField_one]
    rw [flags.1]
    simp only [Phase.selectorValue, j, s]
    rw [logic_read (by decide), selected_read (by decide)]
  have hjr : bitValue j 31 = Phase.selectorValue 9 12 j := by
    rw [← readField_one, logic_read (by decide), readField_one]
    rw [flags.2.1]
    simp only [Phase.selectorValue, j, s]
    rw [logic_read (by decide), selected_read (by decide)]
  have hjs : bitValue j 32 = Phase.selectorValue 9 21 j := by
    rw [← readField_one, logic_read (by decide), readField_one]
    rw [flags.2.2]
    simp only [Phase.selectorValue, j, s]
    rw [logic_read (by decide), selected_read (by decide)]
  have hjclear : readField j 35 6 = 0 := by
    rw [logic_read (by decide), selected_read (by decide), hclear]
  rw [gates, actGates_append, actGates_append, select_act hq hr hs hclear,
    Phase.logic_act]
  exact unselect_act hjq hjr hjs hjclear

private theorem output_read {i off width : Nat} (h : 35 ≤ off) :
    readField (Phase.out 9 9 i) off width = readField i off width := by
  simp only [Phase.out, Phase.cleaned]
  rw [readField_writeField_of_disjoint (by
        norm_num [Phase.zeroQWire, Phase.shiftOffset]; omega),
    readField_writeField_of_disjoint (by
        norm_num [Phase.zeroRPrimeWire, Phase.zeroQWire, Phase.shiftOffset]; omega),
    readField_writeField_of_disjoint (by
        norm_num [Phase.zeroShiftWire, Phase.zeroQWire, Phase.shiftOffset]; omega),
    logic_read (Or.inr h), selected_read (Or.inr (by omega))]

theorem gates_preserves_borrowed {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hclear : readField i 35 6 = 0) :
    (actGates gates i).testBit 41 = i.testBit 41 := by
  rw [gates_act hq hr hs hclear]
  apply testBit_eq_of_bitValue_eq
  simpa [readField_one] using output_read (i := i) (off := 41) (width := 1) (by decide)

theorem gates_cleans_workspace {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hc : bitValue i 33 = 0) (ht : bitValue i 34 = 0)
    (hclear : readField i 35 6 = 0) :
    let out := actGates gates i
    bitValue out 30 = 0 ∧ bitValue out 31 = 0 ∧ bitValue out 32 = 0 ∧
      bitValue out 33 = 0 ∧ bitValue out 34 = 0 ∧ readField out 35 6 = 0 := by
  have hc' : bitValue (Phase.selected 9 9 i) (Phase.conditionWire 9 9) = 0 := by
    rw [Phase.selected_preserves_bit (by decide) (by decide) (by decide)]
    exact hc
  have ht' : bitValue (Phase.selected 9 9 i) (Phase.temporaryWire 9 9) = 0 := by
    rw [Phase.selected_preserves_bit (by decide) (by decide) (by decide)]
    exact ht
  rcases Phase.logic_bits hc' ht' with ⟨_, _, _, _, _, _, hcond, htemp⟩
  simp only
  rw [gates_act hq hr hs hclear]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Phase.out, Phase.cleaned, Phase.zeroQWire, Phase.shiftOffset,
      bitValue_write_self]
  · simp [Phase.out, Phase.cleaned, Phase.zeroQWire, Phase.zeroRPrimeWire,
      Phase.shiftOffset, bitValue_write_ne, bitValue_write_self]
  · simp [Phase.out, Phase.cleaned, Phase.zeroQWire, Phase.zeroRPrimeWire,
      Phase.zeroShiftWire, Phase.shiftOffset, bitValue_write_ne, bitValue_write_self]
  · simpa [Phase.out, Phase.cleaned, Phase.zeroQWire, Phase.zeroRPrimeWire,
      Phase.zeroShiftWire, Phase.shiftOffset, Phase.conditionWire,
      bitValue_write_ne] using hcond
  · simpa [Phase.out, Phase.cleaned, Phase.zeroQWire, Phase.zeroRPrimeWire,
      Phase.zeroShiftWire, Phase.shiftOffset, Phase.temporaryWire,
      bitValue_write_ne] using htemp
  · rw [output_read (by decide), hclear]

private theorem test_wellFormed {source flag : Nat}
    (hsource : source + 9 ≤ flag) (hflag : flag + 1 ≤ 35) :
    (test source flag).all (RGate.wellFormed 42) = true := by
  apply BorrowedSelectorPlaced.zeroTest_wellFormed
    (BorrowedSelectorPlaced.wiring_disjoint_of_order hsource hflag (by decide))
    (by omega) (by omega) (by decide) (by decide)

theorem gates_wellFormed : gates.all (RGate.wellFormed 42) = true := by
  have hq := test_wellFormed (by decide : 3 + 9 ≤ 30) (by decide : 30 + 1 ≤ 35)
  have hr := test_wellFormed (by decide : 12 + 9 ≤ 31) (by decide : 31 + 1 ≤ 35)
  have hs := test_wellFormed (by decide : 21 + 9 ≤ 32) (by decide : 32 + 1 ≤ 35)
  have hl : (Phase.logicGates 9 9).all (RGate.wellFormed 42) = true := by decide
  simp [gates, selectGates, unselectGates, hq, hr, hs, hl]

theorem gates_ccx : gates.countP RGate.isCcx = 100 := by
  simp [gates, selectGates, unselectGates, List.countP_append, test,
    BorrowedSelectorPlaced.zeroTest_ccx, Phase.logic_ccx]

def compactGates : List RGate := [.x 20] ++ gates ++ [.x 20]

theorem compactGates_act {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hclear : readField i 35 6 = 0) :
    actGates compactGates i =
      CompactPhase.restored (Phase.out 9 9 (CompactPhase.prepared i)) := by
  have hclear' : readField (CompactPhase.prepared i) 35 6 = 0 := by
    rw [CompactPhase.prepared, readField_writeField_of_disjoint (by decide), hclear]
  simp only [compactGates, actGates_append, actGates_cons, actGates_nil]
  have hin : RGate.act (.x 20) i = CompactPhase.prepared i := CompactPhase.prepared_act i
  rw [hin]
  rw [gates_act (CompactPhase.prepared_zeroQ hq)
    (CompactPhase.prepared_zeroRPrime hr) (CompactPhase.prepared_zeroShift hs) hclear']
  exact CompactPhase.restored_act _

theorem compactGates_wellFormed :
    compactGates.all (RGate.wellFormed 42) = true := by
  simp [compactGates, gates_wellFormed, RGate.wellFormed]

theorem compactGates_ccx : compactGates.countP RGate.isCcx = 100 := by
  simp [compactGates, gates_ccx, List.countP_append, RGate.isCcx]

theorem compactGates_preserves_high_field {i : Nat} (width : Nat)
    (hq : bitValue i 30 = 0) (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hclear : readField i 35 6 = 0) :
    readField (actGates compactGates i) 41 width = readField i 41 width := by
  rw [compactGates_act hq hr hs hclear, CompactPhase.restored,
    readField_writeField_of_disjoint (Or.inl (by decide)), output_read (by decide),
    CompactPhase.prepared, readField_writeField_of_disjoint (Or.inl (by decide))]

theorem compactGates_cleans_workspace {i : Nat} (hq : bitValue i 30 = 0)
    (hr : bitValue i 31 = 0) (hs : bitValue i 32 = 0)
    (hc : bitValue i 33 = 0) (ht : bitValue i 34 = 0)
    (hclear : readField i 35 6 = 0) :
    let out := actGates compactGates i
    bitValue out 30 = 0 ∧ bitValue out 31 = 0 ∧ bitValue out 32 = 0 ∧
      bitValue out 33 = 0 ∧ bitValue out 34 = 0 ∧ readField out 35 6 = 0 := by
  have hclear' : readField (CompactPhase.prepared i) 35 6 = 0 := by
    rw [CompactPhase.prepared, readField_writeField_of_disjoint (by decide), hclear]
  have hraw := gates_cleans_workspace (CompactPhase.prepared_zeroQ hq)
    (CompactPhase.prepared_zeroRPrime hr) (CompactPhase.prepared_zeroShift hs)
    (CompactPhase.prepared_condition hc) (CompactPhase.prepared_temporary ht) hclear'
  simp only [compactGates, actGates_append, actGates_cons, actGates_nil]
  have hin : RGate.act (.x 20) i = CompactPhase.prepared i := CompactPhase.prepared_act i
  rw [hin, act_x_write]
  simpa only [bitValue_write_ne (by decide : 30 ≠ 20),
    bitValue_write_ne (by decide : 31 ≠ 20), bitValue_write_ne (by decide : 32 ≠ 20),
    bitValue_write_ne (by decide : 33 ≠ 20), bitValue_write_ne (by decide : 34 ≠ 20),
    readField_writeField_of_disjoint (by decide : 20 + 1 ≤ 35 ∨ 35 + 6 ≤ 20)] using hraw

end VQ.Euclid.BorrowedPhase
