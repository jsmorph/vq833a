/-
The pruned prefix tree emitted by the current Luo companion source for the
secp256k1 T-side coefficient window.
-/
import VQ.Euclid.LuoPrefixFixed

namespace VQ.Euclid.LuoPrefixTree

open Reversible
open LuoPrefixArithmetic

abbrev Tree := LuoPrefixArithmetic.Tree

def rangeValidB (start workWidth endpointWidth : Nat) : Tree → Bool
  | .empty => true
  | .leaf label => decide (start ≤ label ∧ label < start + workWidth)
  | .node bit zero one =>
      decide (bit < endpointWidth) &&
        rangeValidB start workWidth endpointWidth zero &&
        rangeValidB start workWidth endpointWidth one

theorem rangeValidB_eq_true_iff
    {start workWidth endpointWidth : Nat} {tree : Tree} :
    rangeValidB start workWidth endpointWidth tree = true ↔
      tree.RangeValid start workWidth endpointWidth := by
  induction tree with
  | empty => simp [rangeValidB, LuoPrefixArithmetic.Tree.RangeValid]
  | leaf label => simp [rangeValidB, LuoPrefixArithmetic.Tree.RangeValid]
  | node bit zero one hzero hone =>
      simp [rangeValidB, LuoPrefixArithmetic.Tree.RangeValid, hzero, hone,
        and_assoc]

def sourceTree : Nat → List Nat → Tree
  | _, [] => .empty
  | _, [label] => .leaf label
  | 0, _ :: _ :: _ => .empty
  | bits + 1, labels =>
      let bit := bits
      let zero := labels.filter fun label => !label.testBit bit
      let one := labels.filter fun label => label.testBit bit
      if zero.isEmpty || one.isEmpty then
        sourceTree bits labels
      else
        .node bit (sourceTree bits zero) (sourceTree bits one)

def rangeTree (start count endpointWidth : Nat) : Tree :=
  sourceTree endpointWidth (List.range' start count)

def allocatedDepth (count : Nat) : Nat :=
  if count ≤ 1 then 0
  else if count = 2 then 1
  else Nat.log2 (count - 2) + 2

def sourceScratchWidth (count endpointWidth : Nat) : Nat :=
  max (allocatedDepth count) endpointWidth

def Certificate (start count endpointWidth : Nat) : Prop :=
  let tree := rangeTree start count endpointWidth
  tree.RangeValid start count endpointWidth ∧
    Tree.labels tree = List.range' start count ∧
    tree.depth ≤ allocatedDepth count ∧
    allocatedDepth count ≤ endpointWidth ∧
    tree.leaves = count ∧
    tree.internal + 1 = count ∧
    (List.range' start count).all
      (fun boundary => decide (tree.select boundary = some boundary)) = true

def check (start count endpointWidth : Nat) : Bool :=
  let tree := rangeTree start count endpointWidth
  rangeValidB start count endpointWidth tree &&
    decide (Tree.labels tree = List.range' start count) &&
    decide (tree.depth ≤ allocatedDepth count) &&
    decide (allocatedDepth count ≤ endpointWidth) &&
    decide (tree.leaves = count) &&
    decide (tree.internal + 1 = count) &&
    (List.range' start count).all
      (fun boundary => decide (tree.select boundary = some boundary))

theorem check_eq_true_iff {start count endpointWidth : Nat} :
    check start count endpointWidth = true ↔
      Certificate start count endpointWidth := by
  simp [check, Certificate, rangeValidB_eq_true_iff, and_assoc]

def checkRange (first amount : Nat) : Bool :=
  (List.range' first amount).all fun count => check 1 count 9

theorem certificate_of_checkRange
    {first amount count : Nat}
    (hcheck : checkRange first amount = true)
    (hcount : count ∈ List.range' first amount) :
    Certificate 1 count 9 := by
  have hall : ∀ count ∈ List.range' first amount, check 1 count 9 = true := by
    simpa [checkRange] using List.all_eq_true.mp hcheck
  exact check_eq_true_iff.mp (hall count hcount)

theorem secp256k1_check_001_016 : checkRange 1 16 = true := by
  decide +kernel

theorem secp256k1_check_017_032 : checkRange 17 16 = true := by
  decide +kernel

theorem secp256k1_check_033_048 : checkRange 33 16 = true := by
  decide +kernel

theorem secp256k1_check_049_064 : checkRange 49 16 = true := by
  decide +kernel

theorem secp256k1_check_065_080 : checkRange 65 16 = true := by
  decide +kernel

theorem secp256k1_check_081_096 : checkRange 81 16 = true := by
  decide +kernel

theorem secp256k1_check_097_112 : checkRange 97 16 = true := by
  decide +kernel

theorem secp256k1_check_113_128 : checkRange 113 16 = true := by
  decide +kernel

theorem secp256k1_check_129_144 : checkRange 129 16 = true := by
  decide +kernel

theorem secp256k1_check_145_160 : checkRange 145 16 = true := by
  decide +kernel

theorem secp256k1_check_161_176 : checkRange 161 16 = true := by
  decide +kernel

theorem secp256k1_check_177_192 : checkRange 177 16 = true := by
  decide +kernel

theorem secp256k1_check_193_208 : checkRange 193 16 = true := by
  decide +kernel

theorem secp256k1_check_209_224 : checkRange 209 16 = true := by
  decide +kernel

theorem secp256k1_check_225_240 : checkRange 225 16 = true := by
  decide +kernel

theorem secp256k1_check_257 : check 1 257 9 = true := by
  decide +kernel

theorem secp256k1_check_241_256 : checkRange 241 16 = true := by
  decide +kernel

theorem secp256k1_certificate
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    Certificate 1 count 9 := by
  have hblocks :
      count ≤ 16 ∨
      (17 ≤ count ∧ count ≤ 32) ∨
      (33 ≤ count ∧ count ≤ 48) ∨
      (49 ≤ count ∧ count ≤ 64) ∨
      (65 ≤ count ∧ count ≤ 80) ∨
      (81 ≤ count ∧ count ≤ 96) ∨
      (97 ≤ count ∧ count ≤ 112) ∨
      (113 ≤ count ∧ count ≤ 128) ∨
      (129 ≤ count ∧ count ≤ 144) ∨
      (145 ≤ count ∧ count ≤ 160) ∨
      (161 ≤ count ∧ count ≤ 176) ∨
      (177 ≤ count ∧ count ≤ 192) ∨
      (193 ≤ count ∧ count ≤ 208) ∨
      (209 ≤ count ∧ count ≤ 224) ∨
      (225 ≤ count ∧ count ≤ 240) ∨
      (241 ≤ count ∧ count ≤ 256) ∨ count = 257 := by
    omega
  rcases hblocks with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h
  · apply certificate_of_checkRange secp256k1_check_001_016
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_017_032
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_033_048
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_049_064
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_065_080
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_081_096
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_097_112
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_113_128
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_129_144
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_145_160
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_161_176
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_177_192
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_193_208
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_209_224
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_225_240
    simp
    omega
  · apply certificate_of_checkRange secp256k1_check_241_256
    simp
    omega
  · subst count
    exact check_eq_true_iff.mp secp256k1_check_257

theorem secp256k1_allocatedDepth : allocatedDepth 257 = 9 := by
  decide

def secp256k1Tree (count : Nat) : Tree := rangeTree 1 count 9

def secp256k1ScratchWidth (count : Nat) : Nat := sourceScratchWidth count 9

theorem secp256k1_tree_structure
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    let tree := secp256k1Tree count
    tree.RangeValid 1 count 9 ∧
      tree.depth ≤ 9 ∧
      Tree.labels tree = List.range' 1 count := by
  have certificate := secp256k1_certificate hpositive hcount
  dsimp [Certificate] at certificate
  rcases certificate with
    ⟨hvalid, hlabels, hdepth, _hallocated, _hleaves, _hinternal,
      _hselects⟩
  exact ⟨hvalid, hdepth.trans _hallocated, hlabels⟩

theorem secp256k1_tree_data
    {count boundary : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundary : 1 ≤ boundary ∧ boundary < 1 + count) :
    let tree := secp256k1Tree count
    tree.RangeValid 1 count 9 ∧
      tree.depth ≤ secp256k1ScratchWidth count ∧
      Tree.labels tree = List.range' 1 count ∧
      tree.select boundary = some boundary ∧
      tree.leaves = count ∧
      tree.internal + 1 = count := by
  have certificate := secp256k1_certificate hpositive hcount
  dsimp [Certificate] at certificate
  rcases certificate with
    ⟨hvalid, hlabels, hdepth, hallocated, hleaves, hinternal, hselects⟩
  have hselect : (rangeTree 1 count 9).select boundary = some boundary := by
    have hmember : boundary ∈ List.range' 1 count := by
      simp
      omega
    have hchecked := List.all_eq_true.mp hselects boundary hmember
    simpa using hchecked
  change
    (rangeTree 1 count 9).RangeValid 1 count 9 ∧
      (rangeTree 1 count 9).depth ≤ sourceScratchWidth count 9 ∧
      Tree.labels (rangeTree 1 count 9) = List.range' 1 count ∧
      (rangeTree 1 count 9).select boundary = some boundary ∧
      (rangeTree 1 count 9).leaves = count ∧
      (rangeTree 1 count 9).internal + 1 = count
  exact ⟨hvalid, hdepth.trans (Nat.le_max_left _ _), hlabels, hselect,
    hleaves, hinternal⟩

theorem secp256k1_scratchWidth
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    secp256k1ScratchWidth count = 9 := by
  have certificate := secp256k1_certificate hpositive hcount
  dsimp [Certificate] at certificate
  rcases certificate with
    ⟨_, _, _, hallocated, _, _, _⟩
  simp [secp256k1ScratchWidth, sourceScratchWidth,
    Nat.max_eq_right hallocated]

theorem secp256k1_addGates_wellFormed
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (updateSign : Bool) :
    (addGates (secp256k1Tree count) 1 count 9
      (secp256k1ScratchWidth count) updateSign).all
        (Reversible.RGate.wellFormed
          (layout count 9 (secp256k1ScratchWidth count)).width) = true := by
  have certificate := secp256k1_certificate hpositive hcount
  dsimp [Certificate] at certificate
  rcases certificate with ⟨hvalid, _, hdepth, _, _, _, _⟩
  apply LuoPrefixFixed.addGates_wellFormed hvalid
    (hdepth.trans (Nat.le_max_left _ _)) updateSign

theorem secp256k1_addGates_sign_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary :
      readField I (boundaryOffset count) 9 = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear count 9 0 (secp256k1Tree count).depth I)
    (haccumulator : bitValue I
      (accumulatorWire count 9 (secp256k1ScratchWidth count)) = 0)
    (hcellScratch : I.testBit
      (cellScratchWire count 9 (secp256k1ScratchWidth count)) = false) :
    actGates
        (addGates (secp256k1Tree count) 1 count 9
          (secp256k1ScratchWidth count) true) I =
      writeField
        (writeField I (targetOffset count) boundary
          ((readField I (targetOffset count) boundary +
            readField I sourceOffset boundary +
            bitValue I
              (carryWire count 9 (secp256k1ScratchWidth count))) %
              2 ^ boundary))
        signWire 1
          ((bitValue I signWire +
            (readField I (targetOffset count) boundary +
              readField I sourceOffset boundary +
              bitValue I
                (carryWire count 9 (secp256k1ScratchWidth count))) /
                2 ^ boundary) % 2) := by
  obtain ⟨hvalid, hdepth, hlabels, hselect, _, _⟩ :=
    secp256k1_tree_data hpositive hcount hboundaryRange
  have haction := LuoPrefixFixed.addGates_sign_act hvalid hdepth hlabels
    hselect hboundary houter hscratch haccumulator hcellScratch
  simpa [show boundary - 1 + 1 = boundary by omega] using haction

theorem secp256k1_subGates_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (boundaryOffset count) 9 = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear count 9 0 (secp256k1Tree count).depth I)
    (hcarry : bitValue I
      (carryWire count 9 (secp256k1ScratchWidth count)) = 0)
    (haccumulator : bitValue I
      (accumulatorWire count 9 (secp256k1ScratchWidth count)) = 0)
    (hcellScratch : I.testBit
      (cellScratchWire count 9 (secp256k1ScratchWidth count)) = false) :
    actGates
        (subGates (secp256k1Tree count) 1 count 9
          (secp256k1ScratchWidth count)) I =
      writeField I (targetOffset count) boundary
        (Adder.difference boundary
          (readField I sourceOffset boundary)
          (readField I (targetOffset count) boundary)) := by
  obtain ⟨hvalid, hdepth, hlabels, hselect, _, _⟩ :=
    secp256k1_tree_data hpositive hcount hboundaryRange
  have haction := LuoPrefixFixed.subGates_act hvalid hdepth hlabels hselect
    hboundary houter hscratch hcarry haccumulator hcellScratch
  simpa [show boundary - 1 + 1 = boundary by omega] using haction

theorem secp256k1_addGates_resources
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (updateSign : Bool) :
    (addGates (secp256k1Tree count) 1 count 9
      (secp256k1ScratchWidth count) updateSign).length =
        29 * count - 14 + (if updateSign then 1 else 0) ∧
    (addGates (secp256k1Tree count) 1 count 9
        (secp256k1ScratchWidth count) updateSign).countP
          Reversible.RGate.isCcx = 11 * count - 4 ∧
    (addGates (secp256k1Tree count) 1 count 9
        (secp256k1ScratchWidth count) updateSign).countP
          Reversible.RGate.isCx =
        10 * count - 2 + (if updateSign then 1 else 0) ∧
    (layout count 9 (secp256k1ScratchWidth count)).width = 2 * count + 23 := by
  have certificate := secp256k1_certificate hpositive hcount
  dsimp [Certificate] at certificate
  rcases certificate with
    ⟨_, _, _, _, hleaves, hinternal, _⟩
  have hscratch := secp256k1_scratchWidth hpositive hcount
  have hleaves' : (secp256k1Tree count).leaves = count := by
    simpa [secp256k1Tree] using hleaves
  have hinternal' : (secp256k1Tree count).internal + 1 = count := by
    simpa [secp256k1Tree] using hinternal
  rw [LuoPrefixArithmetic.addGates_length,
    LuoPrefixArithmetic.addGates_ccx, LuoPrefixArithmetic.addGates_cx,
    LuoPrefixArithmetic.layout_width, hleaves', hscratch]
  omega

end VQ.Euclid.LuoPrefixTree
