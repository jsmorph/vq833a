import VQ.Euclid.BorrowedPrefix
import VQ.Euclid.CompactCoefficientDirty

namespace VQ.Euclid.BorrowedCoefficient

open Reversible

def count : Nat := 257
def tree := LuoPrefixTree.secp256k1Tree count
def borrowed : Nat := LuoCoefficientPass.cellScratchWire count

def prefixGates (backward : Bool) : List RGate :=
  (if backward then BorrowedPrefix.subGates tree 1 count 9 9
    else BorrowedPrefix.addGates tree 1 count 9 9 true).map
      (RGate.map (place (LuoPrefixArithmetic.layout count 9 9)
        (LuoCoefficientPass.prefixWiring count)))

def gates : List RGate :=
  LuoCoefficientPass.prepareGates count ++
    Step.around CompactCoefficientDirty.subtractControlGates (prefixGates true) ++
    LuoCoefficientPass.signToggleGates ++
    LuoCoefficientPass.addControlGates count ++ prefixGates false ++
    LuoCoefficientPass.addControlGates count ++
    LuoCoefficientPass.restoreGates count

private theorem tree_valid : tree.RangeValid 1 count 9 :=
  (LuoPrefixTree.secp256k1_tree_structure (count := count) (by decide) (by decide)).1

private theorem tree_depth : tree.depth ≤ 9 :=
  (LuoPrefixTree.secp256k1_tree_structure (count := count) (by decide) (by decide)).2.1

theorem prefixGates_clear (backward : Bool) (I : Nat) :
    writeField (actGates (prefixGates backward) I) borrowed 1 0 =
      actGates (if backward then LuoCoefficientPass.prefixSubGates count
        else LuoCoefficientPass.prefixAddGates count) (writeField I borrowed 1 0) := by
  have hinj := place_inj
    (by simp [LuoPrefixArithmetic.layout, LuoCoefficientPass.prefixWiring])
    (LuoCoefficientPass.prefixWiring_disjoint count)
  cases backward
  · exact actGates_map_clear_bit hinj
      (List.all_eq_true.mp (BorrowedPrefix.addGates_wellFormed tree_valid tree_depth true))
      (List.all_eq_true.mp (LuoPrefixFixed.addGates_wellFormed tree_valid tree_depth true))
      (k := LuoPrefixArithmetic.cellScratchWire count 9 9) (by decide)
      (BorrowedPrefix.addGates_clear tree_valid tree_depth true) I
  · exact actGates_map_clear_bit hinj
      (List.all_eq_true.mp (BorrowedPrefix.subGates_wellFormed tree_valid tree_depth))
      (List.all_eq_true.mp (by simpa [LuoPrefixArithmetic.subGates] using
        LuoPrefixFixed.addGates_wellFormed tree_valid tree_depth false))
      (k := LuoPrefixArithmetic.cellScratchWire count 9 9) (by decide)
      (BorrowedPrefix.subGates_clear tree_valid tree_depth) I

theorem prefixGates_preserves (backward : Bool) (I : Nat) :
    (actGates (prefixGates backward) I).testBit borrowed = I.testBit borrowed := by
  have hinj := place_inj
    (by simp [LuoPrefixArithmetic.layout, LuoCoefficientPass.prefixWiring])
    (LuoCoefficientPass.prefixWiring_disjoint count)
  cases backward
  · exact actGates_map_preserves_bit hinj
      (List.all_eq_true.mp (BorrowedPrefix.addGates_wellFormed tree_valid tree_depth true))
      (k := LuoPrefixArithmetic.cellScratchWire count 9 9) (by decide)
      (BorrowedPrefix.addGates_preserves tree_valid tree_depth true) I
  · exact actGates_map_preserves_bit hinj
      (List.all_eq_true.mp (BorrowedPrefix.subGates_wellFormed tree_valid tree_depth))
      (k := LuoPrefixArithmetic.cellScratchWire count 9 9) (by decide)
      (BorrowedPrefix.subGates_preserves tree_valid tree_depth) I

theorem prefixGates_wellFormed (backward : Bool) :
    (prefixGates backward).all (RGate.wellFormed 558) = true := by
  apply wellFormed_placeGates (LuoCoefficientPass.prefixWiring_disjoint count)
    (by simp [LuoPrefixArithmetic.layout, LuoCoefficientPass.prefixWiring])
    (LuoCoefficientPass.prefixWiring_total count)
  cases backward
  · exact List.all_eq_true.mp (BorrowedPrefix.addGates_wellFormed tree_valid tree_depth true)
  · exact List.all_eq_true.mp (BorrowedPrefix.subGates_wellFormed tree_valid tree_depth)

private theorem prepare_below :
    (LuoCoefficientPass.prepareGates count).all (RGate.wellFormed borrowed) = true := by
  decide

private theorem restore_below :
    (LuoCoefficientPass.restoreGates count).all (RGate.wellFormed borrowed) = true := by
  decide

private theorem subtractControl_below :
    CompactCoefficientDirty.subtractControlGates.all (RGate.wellFormed borrowed) = true := by
  decide

private theorem addControl_below :
    (LuoCoefficientPass.addControlGates count).all (RGate.wellFormed borrowed) = true := by
  decide

private theorem sign_below :
    LuoCoefficientPass.signToggleGates.all (RGate.wellFormed borrowed) = true := by
  decide

private theorem clear_below {gs : List RGate}
    (h : gs.all (RGate.wellFormed borrowed) = true) (I : Nat) :
    writeField (actGates gs I) borrowed 1 0 = actGates gs (writeField I borrowed 1 0) :=
  (actGates_write_of_outside (fun g hg _ hq => Or.inl
    (wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)) I).symm

private theorem preserves_below {gs : List RGate}
    (h : gs.all (RGate.wellFormed borrowed) = true) (I : Nat) :
    (actGates gs I).testBit borrowed = I.testBit borrowed :=
  testBit_actGates_of_outside (fun g hg => not_mem_wires_of_wellFormed
    (List.all_eq_true.mp h g hg) (by omega)) I

theorem gates_clear (I : Nat) :
    writeField (actGates gates I) borrowed 1 0 =
      actGates CompactCoefficientDirty.gates (writeField I borrowed 1 0) := by
  have hr : CompactCoefficientDirty.subtractControlGates.reverse.all
      (RGate.wellFormed borrowed) = true := by simpa using subtractControl_below
  simp only [gates, CompactCoefficientDirty.gates, CompactCoefficientDirty.middleGates,
    CompactCoefficientDirty.subtractBlockGates, LuoCoefficientPass.addBlockGates,
    Step.around, actGates_append]
  rw [clear_below restore_below, clear_below addControl_below, prefixGates_clear false,
    clear_below addControl_below, clear_below sign_below, clear_below hr,
    prefixGates_clear true, clear_below subtractControl_below, clear_below prepare_below]
  rfl

theorem gates_preserves (I : Nat) :
    (actGates gates I).testBit borrowed = I.testBit borrowed := by
  have hr : CompactCoefficientDirty.subtractControlGates.reverse.all
      (RGate.wellFormed borrowed) = true := by simpa using subtractControl_below
  simp only [gates, Step.around, actGates_append]
  rw [preserves_below restore_below, preserves_below addControl_below, prefixGates_preserves,
    preserves_below addControl_below, preserves_below sign_below, preserves_below hr,
    prefixGates_preserves, preserves_below subtractControl_below, preserves_below prepare_below]

theorem gates_act (I : Nat) :
    actGates gates I = writeField
      (actGates CompactCoefficientDirty.gates (writeField I borrowed 1 0))
      borrowed 1 (bitValue I borrowed) := by
  rw [← gates_clear, ← readField_one]
  have hp : readField (actGates gates I) borrowed 1 = readField I borrowed 1 := by
    simp only [readField_one, bitValue, gates_preserves]
  rw [← hp, writeField_writeField, writeField_read]

end VQ.Euclid.BorrowedCoefficient
