/-
Fixed-prefix arithmetic for the contiguous circuit extracted from the current
Luo companion source.
-/
import VQ.Euclid.LuoPrefixArithmetic

namespace VQ.Euclid.LuoPrefixFixed

open Reversible
open LuoPrefixArithmetic

def coreLayout : Layout := [1, 1, 1]

def coreWiring
    (position workWidth endpointWidth scratchWidth : Nat) : Wiring :=
  [targetOffset workWidth + position, sourceOffset + position,
    carryWire workWidth endpointWidth scratchWidth]

def coreGates
    (gs : List RGate)
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  gs.map (RGate.map (place coreLayout
    (coreWiring position workWidth endpointWidth scratchWidth)))

def baseMajAt
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.baseMajGates
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def baseUmaAt
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.baseUmaGates
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

def disabledAt
    (position workWidth endpointWidth scratchWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.disabledGates
    (targetOffset workWidth + position) (sourceOffset + position)
    (carryWire workWidth endpointWidth scratchWidth)
    (accumulatorWire workWidth endpointWidth scratchWidth)
    (cellScratchWire workWidth endpointWidth scratchWidth)

theorem baseMajAt_eq_core
    (position workWidth endpointWidth scratchWidth : Nat) :
    baseMajAt position workWidth endpointWidth scratchWidth =
      coreGates Cell.baseMajGates position workWidth endpointWidth scratchWidth := by
  simp [baseMajAt, CellPlaced.gates, coreGates, Cell.baseMajGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

theorem baseUmaAt_eq_core
    (position workWidth endpointWidth scratchWidth : Nat) :
    baseUmaAt position workWidth endpointWidth scratchWidth =
      coreGates Cell.baseUmaGates position workWidth endpointWidth scratchWidth := by
  simp [baseUmaAt, CellPlaced.gates, coreGates, Cell.baseUmaGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

theorem disabledAt_eq_core
    (position workWidth endpointWidth scratchWidth : Nat) :
    disabledAt position workWidth endpointWidth scratchWidth =
      coreGates Cell.disabledGates position workWidth endpointWidth scratchWidth := by
  simp [disabledAt, CellPlaced.gates, coreGates, Cell.disabledGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

theorem cell_disjoint
    {position workWidth endpointWidth scratchWidth : Nat}
    (hposition : position < workWidth) :
    Wiring.Disjoint CellPlaced.layout
      (LuoPrefixArithmetic.cellWiring position workWidth endpointWidth
        scratchWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    simp [LuoPrefixArithmetic.cellWiring, CellPlaced.wiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
    simp [LuoPrefixArithmetic.cellWiring, CellPlaced.wiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
    simp [CellPlaced.layout, LuoPrefixArithmetic.cellWiring,
      CellPlaced.wiring, Layout.size, targetOffset, sourceOffset, carryWire,
      accumulatorWire, cellScratchWire, scratchOffset, boundaryOffset] at * <;>
    omega

theorem core_disjoint
    {position workWidth endpointWidth scratchWidth : Nat}
    (hposition : position < workWidth) :
    Wiring.Disjoint coreLayout
      (coreWiring position workWidth endpointWidth scratchWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [coreWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [coreWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    simp [coreLayout, coreWiring, Layout.size, targetOffset, sourceOffset,
      carryWire, scratchOffset, boundaryOffset] at * <;>
    omega

theorem majAt_reduces
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates
        (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth) I =
      if I.testBit (accumulatorWire workWidth endpointWidth scratchWidth) then
        actGates (baseMajAt position workWidth endpointWidth scratchWidth) I
      else
        actGates (disabledAt position workWidth endpointWidth scratchWidth) I := by
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth scratchWidth) = true
  · rw [if_pos hcontrol]
    exact CellPlaced.maj_enabled (cell_disjoint hposition) hcontrol hscratch
  · rw [if_neg hcontrol]
    exact CellPlaced.maj_control_clear (cell_disjoint hposition)
      (Bool.eq_false_iff.mpr hcontrol) hscratch

theorem umaAt_reduces
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates
        (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth) I =
      if I.testBit (accumulatorWire workWidth endpointWidth scratchWidth) then
        actGates (baseUmaAt position workWidth endpointWidth scratchWidth) I
      else
        actGates (disabledAt position workWidth endpointWidth scratchWidth) I := by
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth scratchWidth) = true
  · rw [if_pos hcontrol]
    exact CellPlaced.uma_enabled (cell_disjoint hposition) hcontrol hscratch
  · rw [if_neg hcontrol]
    exact CellPlaced.uma_control_clear (cell_disjoint hposition)
      (Bool.eq_false_iff.mpr hcontrol) hscratch

theorem baseMajAt_eq_adderMajAt
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    actGates (baseMajAt position workWidth endpointWidth scratchWidth) I =
      actGates
        (Adder.maj (targetOffset workWidth + position)
          (sourceOffset + position)
          (carryWire workWidth endpointWidth scratchWidth)) I := by
  have hp := actGates_placed_congr
    (L := coreLayout)
    (W := coreWiring position workWidth endpointWidth scratchWidth)
    (gs := Cell.baseMajGates)
    (hs := Adder.maj Cell.targetWire Cell.sourceWire Cell.carryWire)
    (core_disjoint hposition) (by simp [coreLayout, coreWiring])
    (by decide) (by decide) I (Cell.baseMaj_eq_adderMaj _)
  simpa [baseMajAt_eq_core, coreGates, Adder.maj, coreLayout, coreWiring,
    place, RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]
    using hp

theorem baseUmaAt_eq_adderUmaAt
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    actGates (baseUmaAt position workWidth endpointWidth scratchWidth) I =
      actGates
        (Adder.uma (sourceOffset + position)
          (targetOffset workWidth + position)
          (carryWire workWidth endpointWidth scratchWidth)) I := by
  have hp := actGates_placed_congr
    (L := coreLayout)
    (W := coreWiring position workWidth endpointWidth scratchWidth)
    (gs := Cell.baseUmaGates)
    (hs := Adder.uma Cell.sourceWire Cell.targetWire Cell.carryWire)
    (core_disjoint hposition) (by simp [coreLayout, coreWiring])
    (by decide) (by decide) I (Cell.baseUma_eq_adderUma _)
  simpa [baseUmaAt_eq_core, coreGates, Adder.uma, coreLayout, coreWiring,
    place, RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]
    using hp

def fixedToggle
    (endpoint position workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  if position = endpoint then
    [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
  else []

def fixedFirstScan
    (left right workWidth endpointWidth scratchWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | position, count + 1 =>
      fixedToggle left position workWidth endpointWidth scratchWidth ++
      LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth ++
      fixedToggle right position workWidth endpointWidth scratchWidth ++
      fixedFirstScan left right workWidth endpointWidth scratchWidth
        (position + 1) count

def fixedSecondScan
    (left right workWidth endpointWidth scratchWidth : Nat) :
    Nat → List RGate
  | 0 => []
  | count + 1 =>
      fixedToggle right count workWidth endpointWidth scratchWidth ++
      LuoPrefixArithmetic.umaAt count workWidth endpointWidth scratchWidth ++
      fixedToggle left count workWidth endpointWidth scratchWidth ++
      fixedSecondScan left right workWidth endpointWidth scratchWidth count

def fixedGates
    (left right workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  fixedFirstScan left right workWidth endpointWidth scratchWidth 0 workWidth ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    fixedSecondScan left right workWidth endpointWidth scratchWidth workWidth

def selectedMajAt
    (left right position workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  if left ≤ position ∧ position ≤ right then
    baseMajAt position workWidth endpointWidth scratchWidth
  else disabledAt position workWidth endpointWidth scratchWidth

def selectedUmaAt
    (left right position workWidth endpointWidth scratchWidth : Nat) :
    List RGate :=
  if left ≤ position ∧ position ≤ right then
    baseUmaAt position workWidth endpointWidth scratchWidth
  else disabledAt position workWidth endpointWidth scratchWidth

def selectedFirstScan
    (left right workWidth endpointWidth scratchWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | position, count + 1 =>
      selectedMajAt left right position workWidth endpointWidth scratchWidth ++
      selectedFirstScan left right workWidth endpointWidth scratchWidth
        (position + 1) count

def selectedSecondScan
    (left right workWidth endpointWidth scratchWidth : Nat) :
    Nat → List RGate
  | 0 => []
  | count + 1 =>
      selectedUmaAt left right count workWidth endpointWidth scratchWidth ++
      selectedSecondScan left right workWidth endpointWidth scratchWidth count

def selectedGates
    (left right workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  selectedFirstScan left right workWidth endpointWidth scratchWidth 0 workWidth ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    selectedSecondScan left right workWidth endpointWidth scratchWidth workWidth

def scanAccumulator (left right position : Nat) : Nat :=
  if left < position ∧ position ≤ right then 1 else 0

theorem scanAccumulator_left {left right position : Nat} (hLR : left ≤ right) :
    (scanAccumulator left right position +
        (if position = left then 1 else 0)) % 2 =
      if left ≤ position ∧ position ≤ right then 1 else 0 := by
  unfold scanAccumulator
  by_cases hbefore : left < position ∧ position ≤ right <;>
    by_cases htoggle : position = left <;>
    by_cases hactive : left ≤ position ∧ position ≤ right <;>
    simp [hbefore, htoggle, hactive] <;>
    omega

theorem scanAccumulator_right {left right position : Nat} (hLR : left ≤ right) :
    ((if left ≤ position ∧ position ≤ right then 1 else 0) +
        (if position = right then 1 else 0)) % 2 =
      scanAccumulator left right (position + 1) := by
  unfold scanAccumulator
  by_cases heq : position = right
  · subst position
    have hleft : left < right + 1 := by omega
    have hright : ¬right + 1 ≤ right := by omega
    simp [hLR, hleft, hright]
  · by_cases hpositionRight : position < right
    · have hpositionLe : position ≤ right := by omega
      have hnextRight : position + 1 ≤ right := by omega
      by_cases hleftPosition : left ≤ position
      · have hnextLeft : left < position + 1 := by omega
        simp [heq, hpositionLe, hleftPosition, hnextLeft, hnextRight]
      · have hnextLeft : ¬left < position + 1 := by omega
        simp [heq, hpositionLe, hleftPosition, hnextLeft, hnextRight]
    · have hrightPosition : right < position := by omega
      have hactive : ¬(left ≤ position ∧ position ≤ right) := by omega
      have hafter : ¬(left < position + 1 ∧ position + 1 ≤ right) := by omega
      simp [heq, hactive, hafter]

theorem scanAccumulator_right_reverse
    {left right position : Nat} (hLR : left ≤ right) :
    (scanAccumulator left right (position + 1) +
        (if position = right then 1 else 0)) % 2 =
      if left ≤ position ∧ position ≤ right then 1 else 0 := by
  have h := scanAccumulator_right (left := left) (right := right)
    (position := position) hLR
  rw [← h]
  have hactive : (if left ≤ position ∧ position ≤ right then 1 else 0) < 2 := by
    by_cases ha : left ≤ position ∧ position ≤ right <;> simp [ha]
  have htoggle : (if position = right then 1 else 0) < 2 := by
    by_cases ht : position = right <;> simp [ht]
  omega

theorem scanAccumulator_left_reverse
    {left right position : Nat} (hLR : left ≤ right) :
    ((if left ≤ position ∧ position ≤ right then 1 else 0) +
        (if position = left then 1 else 0)) % 2 =
      scanAccumulator left right position := by
  have h := scanAccumulator_left (left := left) (right := right)
    (position := position) hLR
  rw [← h]
  have hbefore : scanAccumulator left right position < 2 := by
    unfold scanAccumulator
    by_cases hb : left < position ∧ position ≤ right <;> simp [hb]
  have htoggle : (if position = left then 1 else 0) < 2 := by
    by_cases ht : position = left <;> simp [ht]
  omega

theorem scanAccumulator_width
    {left right workWidth : Nat} (hR : right < workWidth) :
    scanAccumulator left right workWidth = 0 := by
  simp [scanAccumulator]
  omega

theorem scanAccumulator_zero {left right : Nat} :
    scanAccumulator left right 0 = 0 := by
  simp [scanAccumulator]

theorem fixedToggle_act
    {endpoint position workWidth endpointWidth scratchWidth I : Nat} :
    actGates
        (fixedToggle endpoint position workWidth endpointWidth scratchWidth) I =
      writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1
        ((bitValue I
          (accumulatorWire workWidth endpointWidth scratchWidth) +
          if position = endpoint then 1 else 0) % 2) := by
  by_cases heq : position = endpoint
  · simp only [fixedToggle, if_pos heq, actGates_cons, actGates_nil]
    exact act_x_write _ _
  · simp only [fixedToggle, if_neg heq, actGates_nil, Nat.add_zero]
    rw [Nat.mod_eq_of_lt
        (bitValue_lt I (accumulatorWire workWidth endpointWidth scratchWidth)),
      ← readField_one, writeField_read]

theorem coreGates_avoids_accumulator
    {gs : List RGate} {position workWidth endpointWidth scratchWidth : Nat}
    (hposition : position < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    ∀ g ∈ coreGates gs position workWidth endpointWidth scratchWidth,
      ∀ q ∈ g.wires,
        q < accumulatorWire workWidth endpointWidth scratchWidth ∨
          accumulatorWire workWidth endpointWidth scratchWidth + 1 ≤ q := by
  apply placeGates_avoids
      (L := coreLayout)
      (W := coreWiring position workWidth endpointWidth scratchWidth)
  · simp [coreLayout, coreWiring]
  · exact hwf
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
      simp [coreLayout] at hk
      omega
    rcases hk' with rfl | rfl | rfl <;>
      simp [coreLayout, coreWiring, Layout.size, targetOffset, sourceOffset,
        carryWire, accumulatorWire, scratchOffset, boundaryOffset] <;>
      omega

theorem coreGates_writeAccumulator
    {gs : List RGate} {position workWidth endpointWidth scratchWidth I v : Nat}
    (hposition : position < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    actGates (coreGates gs position workWidth endpointWidth scratchWidth)
        (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 v) =
      writeField
        (actGates (coreGates gs position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1 v := by
  exact actGates_write_of_outside
    (coreGates_avoids_accumulator hposition hwf) I

theorem coreGates_preserve_cellScratch
    {gs : List RGate} {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    (actGates (coreGates gs position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  apply testBit_actGates_map_of_outside hwf
  intro q hq
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq' with rfl | rfl | rfl <;>
    simp [coreLayout, coreWiring, place, cellScratchWire,
      carryWire, targetOffset, sourceOffset, scratchOffset, boundaryOffset] <;>
    omega

theorem selectedMajAt_writeAccumulator
    {left right position workWidth endpointWidth scratchWidth I v : Nat}
    (hposition : position < workWidth) :
    actGates
        (selectedMajAt left right position workWidth endpointWidth scratchWidth)
        (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 v) =
      writeField
        (actGates
          (selectedMajAt left right position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1 v := by
  by_cases hselected : left ≤ position ∧ position ≤ right
  · rw [selectedMajAt, if_pos hselected, baseMajAt_eq_core]
    exact coreGates_writeAccumulator hposition (by decide)
  · rw [selectedMajAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_writeAccumulator hposition (by decide)

theorem selectedUmaAt_writeAccumulator
    {left right position workWidth endpointWidth scratchWidth I v : Nat}
    (hposition : position < workWidth) :
    actGates
        (selectedUmaAt left right position workWidth endpointWidth scratchWidth)
        (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 v) =
      writeField
        (actGates
          (selectedUmaAt left right position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1 v := by
  by_cases hselected : left ≤ position ∧ position ≤ right
  · rw [selectedUmaAt, if_pos hselected, baseUmaAt_eq_core]
    exact coreGates_writeAccumulator hposition (by decide)
  · rw [selectedUmaAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_writeAccumulator hposition (by decide)

theorem selectedMajAt_preserves_cellScratch
    {left right position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    (actGates
      (selectedMajAt left right position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  by_cases hselected : left ≤ position ∧ position ≤ right
  · rw [selectedMajAt, if_pos hselected, baseMajAt_eq_core]
    exact coreGates_preserve_cellScratch hposition (by decide)
  · rw [selectedMajAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_preserve_cellScratch hposition (by decide)

theorem selectedUmaAt_preserves_cellScratch
    {left right position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    (actGates
      (selectedUmaAt left right position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  by_cases hselected : left ≤ position ∧ position ≤ right
  · rw [selectedUmaAt, if_pos hselected, baseUmaAt_eq_core]
    exact coreGates_preserve_cellScratch hposition (by decide)
  · rw [selectedUmaAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_preserve_cellScratch hposition (by decide)

theorem selectedFirstScan_writeAccumulator
    {left right workWidth endpointWidth scratchWidth I v : Nat} :
    ∀ count position, position + count ≤ workWidth →
    actGates
        (selectedFirstScan left right workWidth endpointWidth scratchWidth
          position count)
        (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 v) =
      writeField
        (actGates
          (selectedFirstScan left right workWidth endpointWidth scratchWidth
            position count) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1 v := by
  intro count
  induction count generalizing I with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hbound
      simp only [selectedFirstScan, actGates_append]
      rw [selectedMajAt_writeAccumulator (by omega),
        ih (position := position + 1) (by omega)]

theorem selectedSecondScan_writeAccumulator
    {left right workWidth endpointWidth scratchWidth I v : Nat} :
    ∀ count, count ≤ workWidth →
    actGates
        (selectedSecondScan left right workWidth endpointWidth scratchWidth count)
        (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 v) =
      writeField
        (actGates
          (selectedSecondScan left right workWidth endpointWidth scratchWidth count) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1 v := by
  intro count
  induction count generalizing I with
  | zero => intro _; rfl
  | succ count ih =>
      intro hbound
      simp only [selectedSecondScan, actGates_append]
      rw [selectedUmaAt_writeAccumulator (by omega), ih (by omega)]

theorem selectedFirstScan_preserves_cellScratch
    {left right workWidth endpointWidth scratchWidth I : Nat} :
    ∀ count position, position + count ≤ workWidth →
    (actGates
      (selectedFirstScan left right workWidth endpointWidth scratchWidth
        position count) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  intro count
  induction count generalizing I with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hbound
      simp only [selectedFirstScan, actGates_append]
      rw [ih (position := position + 1) (by omega),
        selectedMajAt_preserves_cellScratch (by omega)]

theorem selectedSecondScan_preserves_cellScratch
    {left right workWidth endpointWidth scratchWidth I : Nat} :
    ∀ count, count ≤ workWidth →
    (actGates
      (selectedSecondScan left right workWidth endpointWidth scratchWidth count) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  intro count
  induction count generalizing I with
  | zero => intro _; rfl
  | succ count ih =>
      intro hbound
      simp only [selectedSecondScan, actGates_append]
      rw [ih (by omega), selectedUmaAt_preserves_cellScratch (by omega)]

theorem fixedToggle_preserves_cellScratch
    {endpoint position workWidth endpointWidth scratchWidth I : Nat} :
    (actGates
      (fixedToggle endpoint position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  by_cases heq : position = endpoint
  · simp only [fixedToggle, if_pos heq, actGates_cons, actGates_nil,
      RGate.act]
    rw [RGate.testBit_xor_of_ne]
    simp [cellScratchWire, accumulatorWire]
  · rw [fixedToggle, if_neg heq]
    rfl

theorem majAt_preserves_cellScratch
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    (actGates
      (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
  rw [majAt_reduces hposition hscratch]
  split
  · rw [baseMajAt_eq_core,
      coreGates_preserve_cellScratch hposition (by decide), hscratch]
  · rw [disabledAt_eq_core,
      coreGates_preserve_cellScratch hposition (by decide), hscratch]

theorem umaAt_preserves_cellScratch
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    (actGates
      (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
  rw [umaAt_reduces hposition hscratch]
  split
  · rw [baseUmaAt_eq_core,
      coreGates_preserve_cellScratch hposition (by decide), hscratch]
  · rw [disabledAt_eq_core,
      coreGates_preserve_cellScratch hposition (by decide), hscratch]

theorem fixedFirstStep_act
    {left right position workWidth endpointWidth scratchWidth I : Nat}
    (hLR : left ≤ right)
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false)
    (hacc : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) =
        scanAccumulator left right position) :
    actGates
        (fixedToggle left position workWidth endpointWidth scratchWidth ++
          LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth ++
          fixedToggle right position workWidth endpointWidth scratchWidth) I =
      writeField
        (actGates
          (selectedMajAt left right position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1
        (scanAccumulator left right (position + 1)) := by
  let active := if left ≤ position ∧ position ≤ right then 1 else 0
  let I₁ := actGates
    (fixedToggle left position workWidth endpointWidth scratchWidth) I
  have hI₁ : I₁ = writeField I
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 active := by
    rw [show I₁ = actGates
      (fixedToggle left position workWidth endpointWidth scratchWidth) I from rfl,
      fixedToggle_act, hacc, scanAccumulator_left hLR]
  have hscratchI₁ : I₁.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
    rw [show I₁ = actGates
      (fixedToggle left position workWidth endpointWidth scratchWidth) I from rfl,
      fixedToggle_preserves_cellScratch, hscratch]
  have hcell : actGates
      (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth) I₁ =
    actGates
      (selectedMajAt left right position workWidth endpointWidth scratchWidth) I₁ := by
    rw [majAt_reduces hposition hscratchI₁]
    by_cases hselected : left ≤ position ∧ position ≤ right
    · have htest : I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = true := by
        rw [hI₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [selectedMajAt, hselected]
    · have htest : I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = false := by
        rw [hI₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [selectedMajAt, hselected]
  let I₂ := actGates
    (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth) I₁
  have hI₂ : I₂ = writeField
      (actGates
        (selectedMajAt left right position workWidth endpointWidth scratchWidth) I)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 active := by
    rw [show I₂ = actGates
        (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth) I₁
      from rfl,
      hcell, hI₁, selectedMajAt_writeAccumulator hposition]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ position ∧ position ≤ right <;>
      simp [hselected]
  simp only [actGates_append]
  change actGates
      (fixedToggle right position workWidth endpointWidth scratchWidth) I₂ = _
  rw [fixedToggle_act, hI₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, scanAccumulator_right hLR,
    writeField_writeField]

theorem fixedFirstScan_act
    {left right workWidth endpointWidth scratchWidth I : Nat}
    (hLR : left ≤ right)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    ∀ count position, position + count ≤ workWidth →
    bitValue I (accumulatorWire workWidth endpointWidth scratchWidth) =
      scanAccumulator left right position →
    actGates
        (fixedFirstScan left right workWidth endpointWidth scratchWidth
          position count) I =
      writeField
        (actGates
          (selectedFirstScan left right workWidth endpointWidth scratchWidth
            position count) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1
        (scanAccumulator left right (position + count)) := by
  intro count
  induction count generalizing I with
  | zero =>
      intro position _ hacc
      rw [fixedFirstScan, selectedFirstScan, actGates_nil, Nat.add_zero,
        ← hacc, ← readField_one, writeField_read]
  | succ count ih =>
      intro position hbound hacc
      let stepGates :=
        fixedToggle left position workWidth endpointWidth scratchWidth ++
          LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth ++
          fixedToggle right position workWidth endpointWidth scratchWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (selectedMajAt left right position workWidth endpointWidth scratchWidth) I)
          (accumulatorWire workWidth endpointWidth scratchWidth) 1
          (scanAccumulator left right (position + 1)) := by
        exact fixedFirstStep_act hLR (by omega) hscratch hacc
      have hscratchStep : stepState.testBit
          (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        rw [fixedToggle_preserves_cellScratch,
          majAt_preserves_cellScratch (by omega) (by
            rw [fixedToggle_preserves_cellScratch, hscratch])]
      have hscan : scanAccumulator left right (position + 1) < 2 := by
        unfold scanAccumulator
        by_cases hs : left < position + 1 ∧ position + 1 ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (accumulatorWire workWidth endpointWidth scratchWidth) =
          scanAccumulator left right (position + 1) := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedFirstScan left right workWidth endpointWidth scratchWidth
          position (count + 1) =
          stepGates ++ fixedFirstScan left right workWidth endpointWidth
            scratchWidth (position + 1) count from rfl,
        actGates_append,
        ih hscratchStep (position + 1) (by omega) haccStep,
        hstep,
        selectedFirstScan_writeAccumulator
          (count := count) (position := position + 1) (by omega),
        show selectedFirstScan left right workWidth endpointWidth scratchWidth
            position (count + 1) =
          selectedMajAt left right position workWidth endpointWidth scratchWidth ++
            selectedFirstScan left right workWidth endpointWidth scratchWidth
              (position + 1) count from rfl,
        actGates_append, writeField_writeField]
      congr 2
      omega

theorem fixedSecondStep_act
    {left right position workWidth endpointWidth scratchWidth I : Nat}
    (hLR : left ≤ right)
    (hposition : position < workWidth)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false)
    (hacc : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) =
        scanAccumulator left right (position + 1)) :
    actGates
        (fixedToggle right position workWidth endpointWidth scratchWidth ++
          LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth ++
          fixedToggle left position workWidth endpointWidth scratchWidth) I =
      writeField
        (actGates
          (selectedUmaAt left right position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1
        (scanAccumulator left right position) := by
  let active := if left ≤ position ∧ position ≤ right then 1 else 0
  let I₁ := actGates
    (fixedToggle right position workWidth endpointWidth scratchWidth) I
  have hI₁ : I₁ = writeField I
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 active := by
    rw [show I₁ = actGates
      (fixedToggle right position workWidth endpointWidth scratchWidth) I from rfl,
      fixedToggle_act, hacc, scanAccumulator_right_reverse hLR]
  have hscratchI₁ : I₁.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
    rw [show I₁ = actGates
      (fixedToggle right position workWidth endpointWidth scratchWidth) I from rfl,
      fixedToggle_preserves_cellScratch, hscratch]
  have hcell : actGates
      (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth) I₁ =
    actGates
      (selectedUmaAt left right position workWidth endpointWidth scratchWidth) I₁ := by
    rw [umaAt_reduces hposition hscratchI₁]
    by_cases hselected : left ≤ position ∧ position ≤ right
    · have htest : I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = true := by
        rw [hI₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [selectedUmaAt, hselected]
    · have htest : I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = false := by
        rw [hI₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬I₁.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [selectedUmaAt, hselected]
  let I₂ := actGates
    (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth) I₁
  have hI₂ : I₂ = writeField
      (actGates
        (selectedUmaAt left right position workWidth endpointWidth scratchWidth) I)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 active := by
    rw [show I₂ = actGates
        (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth) I₁
      from rfl,
      hcell, hI₁, selectedUmaAt_writeAccumulator hposition]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ position ∧ position ≤ right <;>
      simp [hselected]
  simp only [actGates_append]
  change actGates
      (fixedToggle left position workWidth endpointWidth scratchWidth) I₂ = _
  rw [fixedToggle_act, hI₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, scanAccumulator_left_reverse hLR,
    writeField_writeField]

theorem fixedSecondScan_act
    {left right workWidth endpointWidth scratchWidth I : Nat}
    (hLR : left ≤ right)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    ∀ count, count ≤ workWidth →
    bitValue I (accumulatorWire workWidth endpointWidth scratchWidth) =
      scanAccumulator left right count →
    actGates
        (fixedSecondScan left right workWidth endpointWidth scratchWidth count) I =
      writeField
        (actGates
          (selectedSecondScan left right workWidth endpointWidth scratchWidth count) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) 1
        (scanAccumulator left right 0) := by
  intro count
  induction count generalizing I with
  | zero =>
      intro _ hacc
      rw [fixedSecondScan, selectedSecondScan, actGates_nil,
        ← hacc, ← readField_one, writeField_read]
  | succ count ih =>
      intro hbound hacc
      let stepGates :=
        fixedToggle right count workWidth endpointWidth scratchWidth ++
          LuoPrefixArithmetic.umaAt count workWidth endpointWidth scratchWidth ++
          fixedToggle left count workWidth endpointWidth scratchWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (selectedUmaAt left right count workWidth endpointWidth scratchWidth) I)
          (accumulatorWire workWidth endpointWidth scratchWidth) 1
          (scanAccumulator left right count) := by
        exact fixedSecondStep_act hLR (by omega) hscratch hacc
      have hscratchStep : stepState.testBit
          (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        rw [fixedToggle_preserves_cellScratch,
          umaAt_preserves_cellScratch (by omega) (by
            rw [fixedToggle_preserves_cellScratch, hscratch])]
      have hscan : scanAccumulator left right count < 2 := by
        unfold scanAccumulator
        by_cases hs : left < count ∧ count ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (accumulatorWire workWidth endpointWidth scratchWidth) =
          scanAccumulator left right count := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedSecondScan left right workWidth endpointWidth scratchWidth
          (count + 1) =
          stepGates ++ fixedSecondScan left right workWidth endpointWidth
            scratchWidth count from rfl,
        actGates_append,
        ih hscratchStep (by omega) haccStep,
        hstep,
        selectedSecondScan_writeAccumulator (count := count) (by omega),
        show selectedSecondScan left right workWidth endpointWidth scratchWidth
            (count + 1) =
          selectedUmaAt left right count workWidth endpointWidth scratchWidth ++
            selectedSecondScan left right workWidth endpointWidth scratchWidth count
          from rfl,
        actGates_append, writeField_writeField]

theorem signUpdateGates_preserves_cellScratch
    {workWidth endpointWidth scratchWidth I : Nat} {updateSign : Bool} :
    (actGates
      (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I).testBit
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth scratchWidth) := by
  cases updateSign with
  | false => rfl
  | true =>
      change (actGates
        [.cx (carryWire workWidth endpointWidth scratchWidth) signWire] I).testBit
          (cellScratchWire workWidth endpointWidth scratchWidth) = _
      apply testBit_actGates_of_outside
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst g
      simp [RGate.wires, cellScratchWire, carryWire,
        signWire, scratchOffset, boundaryOffset]

theorem fixedGates_eq_selected
    {left right workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool}
    (hLR : left ≤ right)
    (hR : right < workWidth)
    (hacc : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates
        (fixedGates left right workWidth endpointWidth scratchWidth updateSign) I =
      actGates
        (selectedGates left right workWidth endpointWidth scratchWidth updateSign) I := by
  let firstSelected :=
    selectedFirstScan left right workWidth endpointWidth scratchWidth 0 workWidth
  have hIclear : writeField I
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 0 = I := by
    rw [show 0 = bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) from hacc.symm,
      ← readField_one, writeField_read]
  have hfirstWrite := selectedFirstScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := I) (v := 0) workWidth 0 (by omega)
  change actGates firstSelected
      (writeField I (accumulatorWire workWidth endpointWidth scratchWidth) 1 0) =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 0 at hfirstWrite
  rw [hIclear] at hfirstWrite
  have hfirst := fixedFirstScan_act hLR hscratch workWidth 0 (by omega) (by
    rw [hacc, scanAccumulator_zero])
  simp only [Nat.zero_add] at hfirst
  change actGates
      (fixedFirstScan left right workWidth endpointWidth scratchWidth 0 workWidth) I =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1
      (scanAccumulator left right workWidth) at hfirst
  rw [scanAccumulator_width hR, ← hfirstWrite] at hfirst
  let I₁ := actGates firstSelected I
  have hI₁acc : bitValue I₁
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
    have hb := congrArg
      (fun J => bitValue J
        (accumulatorWire workWidth endpointWidth scratchWidth)) hfirstWrite
    rw [bitValue_write_self] at hb
    simpa using hb
  have hI₁scratch : I₁.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
    have hp := selectedFirstScan_preserves_cellScratch
      (left := left) (right := right) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
      (I := I) workWidth 0 (by omega)
    simpa [I₁, firstSelected] using hp.trans hscratch
  let I₂ := actGates
    (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I₁
  have hI₂acc : bitValue I₂
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
    rw [show I₂ = actGates
      (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I₁ from rfl,
      signUpdateGates_preserve_bitValue]
    · exact hI₁acc
    · simp [accumulatorWire, carryWire, signWire, scratchOffset,
        boundaryOffset]
  have hI₂scratch : I₂.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
    rw [show I₂ = actGates
      (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I₁ from rfl,
      signUpdateGates_preserves_cellScratch, hI₁scratch]
  let secondSelected :=
    selectedSecondScan left right workWidth endpointWidth scratchWidth workWidth
  have hI₂clear : writeField I₂
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 0 = I₂ := by
    rw [show 0 = bitValue I₂
      (accumulatorWire workWidth endpointWidth scratchWidth) from hI₂acc.symm,
      ← readField_one, writeField_read]
  have hsecondWrite := selectedSecondScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := I₂) (v := 0) workWidth (by omega)
  change actGates secondSelected
      (writeField I₂ (accumulatorWire workWidth endpointWidth scratchWidth) 1 0) =
    writeField (actGates secondSelected I₂)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1 0 at hsecondWrite
  rw [hI₂clear] at hsecondWrite
  have hsecond := fixedSecondScan_act hLR hI₂scratch workWidth (by omega) (by
    rw [hI₂acc, scanAccumulator_width hR])
  change actGates
      (fixedSecondScan left right workWidth endpointWidth scratchWidth workWidth) I₂ =
    writeField (actGates secondSelected I₂)
      (accumulatorWire workWidth endpointWidth scratchWidth) 1
      (scanAccumulator left right 0) at hsecond
  rw [scanAccumulator_zero, ← hsecondWrite] at hsecond
  simp only [fixedGates, selectedGates, actGates_append]
  rw [hfirst]
  change actGates
      (fixedSecondScan left right workWidth endpointWidth scratchWidth workWidth) I₂ = _
  exact hsecond

def disabledForward
    (workWidth endpointWidth scratchWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | position, count + 1 =>
      disabledAt position workWidth endpointWidth scratchWidth ++
      disabledForward workWidth endpointWidth scratchWidth (position + 1) count

def baseMajForward
    (workWidth endpointWidth scratchWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | position, count + 1 =>
      baseMajAt position workWidth endpointWidth scratchWidth ++
      baseMajForward workWidth endpointWidth scratchWidth (position + 1) count

def selectedBackward
    (left right workWidth endpointWidth scratchWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, count + 1 =>
      selectedUmaAt left right (top - 1) workWidth endpointWidth scratchWidth ++
      selectedBackward left right workWidth endpointWidth scratchWidth
        (top - 1) count

def disabledBackward
    (workWidth endpointWidth scratchWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | top, count + 1 =>
      disabledAt (top - 1) workWidth endpointWidth scratchWidth ++
      disabledBackward workWidth endpointWidth scratchWidth (top - 1) count

def baseUmaBackward
    (workWidth endpointWidth scratchWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | top, count + 1 =>
      baseUmaAt (top - 1) workWidth endpointWidth scratchWidth ++
      baseUmaBackward workWidth endpointWidth scratchWidth (top - 1) count

def activeGates
    (left right workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  baseMajForward workWidth endpointWidth scratchWidth left (right - left + 1) ++
    signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
    baseUmaBackward workWidth endpointWidth scratchWidth (right + 1)
      (right - left + 1)

theorem selectedFirstScan_split
    (left right workWidth endpointWidth scratchWidth position a b : Nat) :
    selectedFirstScan left right workWidth endpointWidth scratchWidth
        position (a + b) =
      selectedFirstScan left right workWidth endpointWidth scratchWidth
          position a ++
        selectedFirstScan left right workWidth endpointWidth scratchWidth
          (position + a) b := by
  induction a generalizing position with
  | zero => simp [selectedFirstScan]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [selectedFirstScan]
      rw [ih (position := position + 1), List.append_assoc]
      simp only [show position + 1 + a = position + (a + 1) by omega]

theorem selectedSecondScan_eq_backward
    (left right workWidth endpointWidth scratchWidth : Nat) : ∀ count,
    selectedSecondScan left right workWidth endpointWidth scratchWidth count =
      selectedBackward left right workWidth endpointWidth scratchWidth
        count count := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [selectedSecondScan, selectedBackward, ih]

theorem selectedBackward_split
    (left right workWidth endpointWidth scratchWidth base a b : Nat) :
    selectedBackward left right workWidth endpointWidth scratchWidth
        (base + a + b) (a + b) =
      selectedBackward left right workWidth endpointWidth scratchWidth
          (base + a + b) a ++
        selectedBackward left right workWidth endpointWidth scratchWidth
          (base + b) b := by
  induction a generalizing base with
  | zero => simp [selectedBackward]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega,
        show base + (a + 1) + b = (base + a + b) + 1 by omega]
      simp only [selectedBackward, Nat.add_sub_cancel]
      rw [ih (base := base), List.append_assoc]

theorem selectedFirstScan_inside
    {left right workWidth endpointWidth scratchWidth : Nat} : ∀ count position,
    left ≤ position → position + count ≤ right + 1 →
    selectedFirstScan left right workWidth endpointWidth scratchWidth
        position count =
      baseMajForward workWidth endpointWidth scratchWidth position count := by
  intro count
  induction count with
  | zero => intro position _ _; rfl
  | succ count ih =>
      intro position hleft hright
      have hposition : left ≤ position ∧ position ≤ right := by omega
      simp [selectedFirstScan, selectedMajAt, baseMajForward, hposition,
        ih (position + 1) (by omega) (by omega)]

theorem selectedFirstScan_above
    {left right workWidth endpointWidth scratchWidth : Nat} : ∀ count position,
    right < position →
    selectedFirstScan left right workWidth endpointWidth scratchWidth
        position count =
      disabledForward workWidth endpointWidth scratchWidth position count := by
  intro count
  induction count with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hright
      have hposition : ¬(left ≤ position ∧ position ≤ right) := by omega
      simp [selectedFirstScan, selectedMajAt, disabledForward, hposition,
        ih (position + 1) (by omega)]

theorem selectedBackward_inside
    {left right workWidth endpointWidth scratchWidth : Nat} : ∀ count top,
    count ≤ top → left + count ≤ top → top ≤ right + 1 →
    selectedBackward left right workWidth endpointWidth scratchWidth top count =
      baseUmaBackward workWidth endpointWidth scratchWidth top count := by
  intro count
  induction count with
  | zero => intro top _ _ _; rfl
  | succ count ih =>
      intro top hcount hleft hright
      have htop : 0 < top := by omega
      have hposition : left ≤ top - 1 ∧ top - 1 ≤ right := by omega
      rw [selectedBackward, baseUmaBackward, selectedUmaAt, if_pos hposition,
        ih (top - 1) (by omega) (by omega) (by omega)]

theorem selectedBackward_above
    {left right workWidth endpointWidth scratchWidth : Nat} : ∀ count top,
    count ≤ top → right + count < top →
    selectedBackward left right workWidth endpointWidth scratchWidth top count =
      disabledBackward workWidth endpointWidth scratchWidth top count := by
  intro count
  induction count with
  | zero => intro top _ _; rfl
  | succ count ih =>
      intro top hcount hright
      have htop : 0 < top := by omega
      have hposition : ¬(left ≤ top - 1 ∧ top - 1 ≤ right) := by omega
      rw [selectedBackward, disabledBackward, selectedUmaAt, if_neg hposition,
        ih (top - 1) (by omega) (by omega)]

theorem selectedFirstScan_zero_decompose
    {right workWidth endpointWidth scratchWidth : Nat}
    (hR : right < workWidth) :
    selectedFirstScan 0 right workWidth endpointWidth scratchWidth 0 workWidth =
      baseMajForward workWidth endpointWidth scratchWidth 0 (right + 1) ++
        disabledForward workWidth endpointWidth scratchWidth (right + 1)
          (workWidth - (right + 1)) := by
  let count := right + 1
  let upper := workWidth - count
  have hsum : count + upper = workWidth := by
    dsimp [count, upper]
    omega
  have hsplit := selectedFirstScan_split 0 right workWidth endpointWidth
    scratchWidth 0 count upper
  rw [Nat.zero_add, hsum] at hsplit
  rw [hsplit]
  dsimp [count, upper]
  rw [
    selectedFirstScan_inside (right + 1) 0 (by omega) (by omega),
    selectedFirstScan_above (workWidth - (right + 1)) (right + 1)
      (by omega)]

theorem selectedSecondScan_zero_decompose
    {right workWidth endpointWidth scratchWidth : Nat}
    (hR : right < workWidth) :
    selectedSecondScan 0 right workWidth endpointWidth scratchWidth workWidth =
      disabledBackward workWidth endpointWidth scratchWidth workWidth
          (workWidth - (right + 1)) ++
        baseUmaBackward workWidth endpointWidth scratchWidth (right + 1)
          (right + 1) := by
  let count := right + 1
  let upper := workWidth - count
  have hsum : upper + count = workWidth := by
    dsimp [count, upper]
    omega
  rw [selectedSecondScan_eq_backward]
  have hsplit := selectedBackward_split 0 right workWidth endpointWidth
    scratchWidth 0 upper count
  simp only [Nat.zero_add, hsum] at hsplit
  rw [hsplit]
  dsimp [count, upper]
  rw [
    selectedBackward_above (workWidth - (right + 1)) workWidth
      (by omega) (by omega),
    selectedBackward_inside (right + 1) (right + 1)
      (by omega) (by omega) (by omega)]

theorem disabledAt_eq_pair
    (position workWidth endpointWidth scratchWidth : Nat) :
    disabledAt position workWidth endpointWidth scratchWidth =
      [.cx (carryWire workWidth endpointWidth scratchWidth)
          (targetOffset workWidth + position),
       .cx (carryWire workWidth endpointWidth scratchWidth)
          (sourceOffset + position)] := by
  simp [disabledAt, CellPlaced.gates, Cell.disabledGates,
    CellPlaced.layout, CellPlaced.wiring, place, targetOffset, sourceOffset,
    carryWire, RGate.map, Cell.carryWire, Cell.targetWire, Cell.sourceWire]

theorem disabledAt_involutive
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    actGates (disabledAt position workWidth endpointWidth scratchWidth)
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I) = I := by
  have hp := actGates_placed_congr
    (L := coreLayout)
    (W := coreWiring position workWidth endpointWidth scratchWidth)
    (gs := Cell.disabledGates ++ Cell.disabledGates) (hs := [])
    (core_disjoint hposition) (by simp [coreLayout, coreWiring])
    (by decide) (by simp) I (by
      rw [actGates_append, Cell.disabledGates_act,
        Cell.disabledGates_act, Cell.disabledState_involutive,
        actGates_nil])
  simpa [disabledAt_eq_core, coreGates, List.map_append,
    actGates_append, actGates_nil] using hp

theorem disabledForward_snoc
    (workWidth endpointWidth scratchWidth : Nat) : ∀ count position,
    disabledForward workWidth endpointWidth scratchWidth position (count + 1) =
      disabledForward workWidth endpointWidth scratchWidth position count ++
        disabledAt (position + count) workWidth endpointWidth scratchWidth := by
  intro count
  induction count with
  | zero => intro position; simp [disabledForward]
  | succ count ih =>
      intro position
      change disabledAt position workWidth endpointWidth scratchWidth ++
          disabledForward workWidth endpointWidth scratchWidth
            (position + 1) (count + 1) =
        (disabledAt position workWidth endpointWidth scratchWidth ++
          disabledForward workWidth endpointWidth scratchWidth
            (position + 1) count) ++
          disabledAt (position + (count + 1)) workWidth endpointWidth scratchWidth
      rw [ih (position + 1), List.append_assoc]
      simp only [show position + 1 + count = position + (count + 1) by omega]

theorem disabledForward_backward_cancel
    {position count workWidth endpointWidth scratchWidth I : Nat}
    (hbound : position + count ≤ workWidth) :
    actGates
        (disabledBackward workWidth endpointWidth scratchWidth
          (position + count) count)
        (actGates
          (disabledForward workWidth endpointWidth scratchWidth position count) I) = I := by
  induction count generalizing I with
  | zero => rfl
  | succ count ih =>
      rw [disabledForward_snoc, actGates_append]
      have htop : position + (count + 1) - 1 = position + count := by omega
      rw [show disabledBackward workWidth endpointWidth scratchWidth
          (position + (count + 1)) (count + 1) =
        disabledAt (position + count) workWidth endpointWidth scratchWidth ++
          disabledBackward workWidth endpointWidth scratchWidth
            (position + count) count by
        simp [disabledBackward, htop]]
      simp only [actGates_append]
      rw [disabledAt_involutive (by omega), ih (by omega)]

theorem disabledAt_preserves_carry
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    bitValue
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I)
        (carryWire workWidth endpointWidth scratchWidth) =
      bitValue I (carryWire workWidth endpointWidth scratchWidth) := by
  rw [disabledAt_eq_pair]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [bitValue_write_ne (by
      simp [sourceOffset, carryWire, scratchOffset, boundaryOffset]
      omega),
    bitValue_write_ne (by
      simp [targetOffset, carryWire, scratchOffset, boundaryOffset]
      omega)]

theorem disabledAt_preserves_accumulator
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    bitValue
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth scratchWidth) := by
  rw [disabledAt_eq_pair]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [bitValue_write_ne (by
      simp [sourceOffset, accumulatorWire, carryWire, scratchOffset,
        boundaryOffset]
      omega),
    bitValue_write_ne (by
      simp [targetOffset, accumulatorWire, carryWire, scratchOffset,
        boundaryOffset]
      omega)]

theorem disabledAt_preserves_cellScratch
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    bitValue
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      bitValue I (cellScratchWire workWidth endpointWidth scratchWidth) := by
  rw [disabledAt_eq_pair]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [bitValue_write_ne (by
      simp [sourceOffset, cellScratchWire, carryWire,
        scratchOffset, boundaryOffset]
      omega),
    bitValue_write_ne (by
      simp [targetOffset, cellScratchWire, carryWire,
        scratchOffset, boundaryOffset]
      omega)]

theorem disabledForward_preserves_accumulator
    {position count workWidth endpointWidth scratchWidth I : Nat}
    (hbound : position + count ≤ workWidth) :
    bitValue
        (actGates
          (disabledForward workWidth endpointWidth scratchWidth position count) I)
        (accumulatorWire workWidth endpointWidth scratchWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth scratchWidth) := by
  induction count generalizing position I with
  | zero => rfl
  | succ count ih =>
      simp only [disabledForward, actGates_append]
      rw [ih (by omega), disabledAt_preserves_accumulator (by omega)]

theorem disabledForward_preserves_cellScratch
    {position count workWidth endpointWidth scratchWidth I : Nat}
    (hbound : position + count ≤ workWidth) :
    bitValue
        (actGates
          (disabledForward workWidth endpointWidth scratchWidth position count) I)
        (cellScratchWire workWidth endpointWidth scratchWidth) =
      bitValue I (cellScratchWire workWidth endpointWidth scratchWidth) := by
  induction count generalizing position I with
  | zero => rfl
  | succ count ih =>
      simp only [disabledForward, actGates_append]
      rw [ih (by omega), disabledAt_preserves_cellScratch (by omega)]

theorem firstLabelScan_none_range_act
    {start position count workWidth endpointWidth scratchWidth I : Nat}
    (hbound : position + count ≤ workWidth)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : bitValue I
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0) :
    actGates
        (firstLabelScan start workWidth endpointWidth scratchWidth
          (List.range' (start + position) count) none) I =
      actGates
        (disabledForward workWidth endpointWidth scratchWidth position count) I := by
  induction count generalizing position I with
  | zero => simp [firstLabelScan, disabledForward]
  | succ count ih =>
      have hposition : position < workWidth := by omega
      have hcellTest : I.testBit
          (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
        simpa [bitValue] using hcellScratch
      have haccTest : I.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = false := by
        simpa [bitValue] using haccumulator
      have hmaj := majAt_reduces hposition hcellTest
      rw [if_neg (by simpa using haccTest)] at hmaj
      let J := actGates
        (disabledAt position workWidth endpointWidth scratchWidth) I
      have haccumulatorJ : bitValue J
          (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
        exact (disabledAt_preserves_accumulator hposition).trans haccumulator
      have hcellScratchJ : bitValue J
          (cellScratchWire workWidth endpointWidth scratchWidth) = 0 := by
        exact (disabledAt_preserves_cellScratch hposition).trans hcellScratch
      rw [List.range'_succ, firstLabelScan, if_neg (by simp)]
      simp only [List.append_nil, actGates_append]
      rw [show start + position - start = position by omega, hmaj]
      change actGates
          (firstLabelScan start workWidth endpointWidth scratchWidth
            (List.range' (start + (position + 1)) count) none) J = _
      rw [ih (by omega) haccumulatorJ hcellScratchJ]
      rfl

theorem secondLabelScan_none_range_act
    {start position count workWidth endpointWidth scratchWidth I : Nat}
    (hbound : position + count ≤ workWidth)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : bitValue I
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0) :
    actGates
        (secondLabelScan start workWidth endpointWidth scratchWidth
          (List.range' (start + position) count).reverse none) I =
      actGates
        (disabledBackward workWidth endpointWidth scratchWidth
          (position + count) count) I := by
  induction count generalizing I with
  | zero => simp [secondLabelScan, disabledBackward]
  | succ count ih =>
      have hlast : position + count < workWidth := by omega
      rw [List.range'_1_concat, List.reverse_append,
        secondLabelScan_append]
      simp only [List.reverse_singleton, secondLabelScan]
      rw [if_neg (by simp)]
      simp only [List.nil_append, actGates_append, actGates_nil]
      have hcellTest : I.testBit
          (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
        simpa [bitValue] using hcellScratch
      have haccTest : I.testBit
          (accumulatorWire workWidth endpointWidth scratchWidth) = false := by
        simpa [bitValue] using haccumulator
      have huma := umaAt_reduces hlast hcellTest
      rw [if_neg (by simpa using haccTest)] at huma
      rw [show start + position + count - start = position + count by omega,
        huma]
      let J := actGates
        (disabledAt (position + count) workWidth endpointWidth scratchWidth) I
      have haccumulatorJ : bitValue J
          (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
        exact (disabledAt_preserves_accumulator hlast).trans haccumulator
      have hcellScratchJ : bitValue J
          (cellScratchWire workWidth endpointWidth scratchWidth) = 0 := by
        exact (disabledAt_preserves_cellScratch hlast).trans hcellScratch
      change actGates
          (secondLabelScan start workWidth endpointWidth scratchWidth
            (List.range' (start + position) count).reverse none) J = _
      rw [ih (by omega) haccumulatorJ hcellScratchJ]
      rw [show disabledBackward workWidth endpointWidth scratchWidth
          (position + (count + 1)) (count + 1) =
        disabledAt (position + count) workWidth endpointWidth scratchWidth ++
          disabledBackward workWidth endpointWidth scratchWidth
            (position + count) count by
        simp [disabledBackward]]
      rw [actGates_append]

theorem labelScans_none_cancel
    {start workWidth endpointWidth scratchWidth I : Nat}
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : bitValue I
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0) :
    actGates
        (firstLabelScan start workWidth endpointWidth scratchWidth
            (List.range' start workWidth) none ++
          secondLabelScan start workWidth endpointWidth scratchWidth
            (List.range' start workWidth).reverse none) I = I := by
  rw [actGates_append]
  have hfirst := firstLabelScan_none_range_act
    (start := start) (position := 0) (count := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := I) (by simp)
    haccumulator hcellScratch
  simp only [Nat.add_zero] at hfirst
  rw [hfirst]
  have haccumulator' := disabledForward_preserves_accumulator
    (position := 0) (count := workWidth) (workWidth := workWidth)
    (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) (I := I)
    (by simp)
  have hcellScratch' := disabledForward_preserves_cellScratch
    (position := 0) (count := workWidth) (workWidth := workWidth)
    (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) (I := I)
    (by simp)
  have hsecond := secondLabelScan_none_range_act
    (start := start) (position := 0) (count := workWidth)
    (workWidth := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := actGates
      (disabledForward workWidth endpointWidth scratchWidth 0 workWidth) I)
    (by simp)
    (haccumulator'.trans haccumulator)
    (hcellScratch'.trans hcellScratch)
  simp only [Nat.add_zero, Nat.zero_add] at hsecond
  rw [hsecond]
  simpa only [Nat.zero_add] using
    (disabledForward_backward_cancel
      (position := 0) (count := workWidth) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
      (I := I) (by simp))

theorem addGates_outerClear_act
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 0)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : bitValue I
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth false) I = I := by
  rw [LuoPrefixArithmetic.addGates_outerClear_act_flat
      hvalid hdepth hboundary houter hscratch,
    flatFirst_eq_firstLabelScan (by rw [hlabels]; exact List.nodup_range'),
    flatSecond_eq_secondLabelScan (by rw [hlabels]; exact List.nodup_range')]
  simp only [hlabels]
  exact labelScans_none_cancel haccumulator hcellScratch

theorem disabledAt_sign_comm
    {position workWidth endpointWidth scratchWidth I : Nat}
    (hposition : position < workWidth) :
    actGates
        [.cx (carryWire workWidth endpointWidth scratchWidth) signWire]
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I) =
      actGates (disabledAt position workWidth endpointWidth scratchWidth)
        (actGates
          [.cx (carryWire workWidth endpointWidth scratchWidth) signWire] I) := by
  have hout : ∀ g ∈ disabledAt position workWidth endpointWidth scratchWidth,
      ∀ q ∈ g.wires, q < signWire ∨ signWire + 1 ≤ q := by
    rw [disabledAt_eq_pair]
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      simp [RGate.wires] at hq <;>
      rcases hq with rfl | rfl <;>
      simp [targetOffset, sourceOffset, carryWire, signWire, scratchOffset,
        boundaryOffset] <;>
      omega
  have hsign : bitValue
      (actGates (disabledAt position workWidth endpointWidth scratchWidth) I)
        signWire = bitValue I signWire := by
    rw [← readField_one, readField_actGates_of_outside hout I, readField_one]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [disabledAt_preserves_carry hposition, hsign,
    actGates_write_of_outside hout]

theorem disabledAt_signUpdate_comm
    {position workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool} (hposition : position < workWidth) :
    actGates (signUpdateGates workWidth endpointWidth scratchWidth updateSign)
        (actGates (disabledAt position workWidth endpointWidth scratchWidth) I) =
      actGates (disabledAt position workWidth endpointWidth scratchWidth)
        (actGates
          (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I) := by
  cases updateSign with
  | false => rfl
  | true => exact disabledAt_sign_comm hposition

theorem disabledBackward_signUpdate_comm
    {count top workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool}
    (hcount : count ≤ top) (htop : top ≤ workWidth) :
    actGates (signUpdateGates workWidth endpointWidth scratchWidth updateSign)
        (actGates
          (disabledBackward workWidth endpointWidth scratchWidth top count) I) =
      actGates (disabledBackward workWidth endpointWidth scratchWidth top count)
        (actGates
          (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I) := by
  induction count generalizing top I with
  | zero => rfl
  | succ count ih =>
      have htopPositive : 0 < top := by omega
      simp only [disabledBackward, actGates_append]
      rw [ih (top := top - 1)
          (I := actGates
            (disabledAt (top - 1) workWidth endpointWidth scratchWidth) I)
          (by omega) (by omega),
        disabledAt_signUpdate_comm (by omega)]

theorem disabled_signUpdate_sandwich
    {position count workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool}
    (hbound : position + count ≤ workWidth) :
    actGates
        (disabledForward workWidth endpointWidth scratchWidth position count ++
          signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
          disabledBackward workWidth endpointWidth scratchWidth
            (position + count) count) I =
      actGates
        (signUpdateGates workWidth endpointWidth scratchWidth updateSign) I := by
  simp only [actGates_append]
  rw [← disabledBackward_signUpdate_comm
      (count := count) (top := position + count)
      (I := actGates
        (disabledForward workWidth endpointWidth scratchWidth position count) I)
      (by omega) hbound,
    disabledForward_backward_cancel hbound]

theorem addGates_outerClear_sign_act
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 0)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I)
    (hcarry : bitValue I
      (carryWire workWidth endpointWidth scratchWidth) = 0)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : bitValue I
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth true) I = I := by
  rw [LuoPrefixArithmetic.addGates_outerClear_act_flat_sign
      hvalid hdepth hboundary houter hscratch,
    flatFirst_eq_firstLabelScan (by rw [hlabels]; exact List.nodup_range'),
    flatSecond_eq_secondLabelScan (by rw [hlabels]; exact List.nodup_range')]
  simp only [Bool.false_eq_true, if_false, hlabels, actGates_append]
  have hfirst := firstLabelScan_none_range_act
    (start := start) (position := 0) (count := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := I) (by simp) haccumulator hcellScratch
  simp only [Nat.add_zero] at hfirst
  rw [hfirst]
  let J₁ := actGates
    (disabledForward workWidth endpointWidth scratchWidth 0 workWidth) I
  have haccumulatorJ₁ : bitValue J₁
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
    exact (disabledForward_preserves_accumulator
      (position := 0) (count := workWidth) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
      (I := I) (by simp)).trans haccumulator
  have hcellScratchJ₁ : bitValue J₁
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0 := by
    exact (disabledForward_preserves_cellScratch
      (position := 0) (count := workWidth) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
      (I := I) (by simp)).trans hcellScratch
  let J₂ := actGates
    (signUpdateGates workWidth endpointWidth scratchWidth true) J₁
  have haccumulatorJ₂ : bitValue J₂
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
    have hne : accumulatorWire workWidth endpointWidth scratchWidth ≠ signWire := by
      simp [accumulatorWire, carryWire, scratchOffset, boundaryOffset, signWire]
    exact (signUpdateGates_preserve_bitValue
      (workWidth := workWidth) (endpointWidth := endpointWidth)
      (scratchWidth := scratchWidth)
      (q := accumulatorWire workWidth endpointWidth scratchWidth)
      (I := J₁) (updateSign := true) hne).trans haccumulatorJ₁
  have hcellScratchJ₂ : bitValue J₂
      (cellScratchWire workWidth endpointWidth scratchWidth) = 0 := by
    have hne : cellScratchWire workWidth endpointWidth scratchWidth ≠ signWire := by
      simp [cellScratchWire, carryWire, scratchOffset, boundaryOffset, signWire]
    exact (signUpdateGates_preserve_bitValue
      (workWidth := workWidth) (endpointWidth := endpointWidth)
      (scratchWidth := scratchWidth)
      (q := cellScratchWire workWidth endpointWidth scratchWidth)
      (I := J₁) (updateSign := true) hne).trans hcellScratchJ₁
  have hsecond := secondLabelScan_none_range_act
    (start := start) (position := 0) (count := workWidth)
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) (I := J₂) (by simp)
    haccumulatorJ₂ hcellScratchJ₂
  simp only [Nat.add_zero, Nat.zero_add] at hsecond
  rw [show actGates
      (signUpdateGates workWidth endpointWidth scratchWidth true) J₁ = J₂ by rfl,
    hsecond]
  have hsandwich := disabled_signUpdate_sandwich
    (position := 0) (count := workWidth) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (I := I) (updateSign := true) (by simp)
  simp only [actGates_append, Nat.zero_add] at hsandwich
  rw [hsandwich]
  simpa [signUpdateGates] using cx_off hcarry

theorem selectedGates_zero_eq_active
    {right workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool}
    (hR : right < workWidth) :
    actGates
        (selectedGates 0 right workWidth endpointWidth scratchWidth updateSign) I =
      actGates
        (activeGates 0 right workWidth endpointWidth scratchWidth updateSign) I := by
  let count := right + 1
  let upper := workWidth - count
  let maj := baseMajForward workWidth endpointWidth scratchWidth 0 count
  let disabledFirst :=
    disabledForward workWidth endpointWidth scratchWidth count upper
  let sign := signUpdateGates workWidth endpointWidth scratchWidth updateSign
  let disabledSecond :=
    disabledBackward workWidth endpointWidth scratchWidth workWidth upper
  let uma := baseUmaBackward workWidth endpointWidth scratchWidth count count
  have hfirst := selectedFirstScan_zero_decompose
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth) hR
  have hsecond := selectedSecondScan_zero_decompose
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth) hR
  change selectedFirstScan 0 right workWidth endpointWidth scratchWidth 0 workWidth =
    maj ++ disabledFirst at hfirst
  change selectedSecondScan 0 right workWidth endpointWidth scratchWidth workWidth =
    disabledSecond ++ uma at hsecond
  have htop : count + upper = workWidth := by
    dsimp [count, upper]
    omega
  have hsandwich := disabled_signUpdate_sandwich
    (position := count) (count := upper) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (scratchWidth := scratchWidth)
    (updateSign := updateSign) (I := actGates maj I) (by
      dsimp [count, upper]
      omega)
  rw [htop] at hsandwich
  change actGates (disabledFirst ++ sign ++ disabledSecond)
      (actGates maj I) = actGates sign (actGates maj I) at hsandwich
  simp only [actGates_append] at hsandwich
  simp only [selectedGates, hfirst, hsecond, actGates_append]
  rw [hsandwich]
  simp [activeGates, count, maj, sign, uma, actGates_append]

def arithmeticLayout (width : Nat) : Layout := [width, width, 1, 1]

def arithmeticWiring
    (workWidth endpointWidth scratchWidth : Nat) : Wiring :=
  [targetOffset workWidth, sourceOffset,
    carryWire workWidth endpointWidth scratchWidth, signWire]

def idealGates
    (right workWidth endpointWidth scratchWidth : Nat)
    (updateSign : Bool) : List RGate :=
  let width := right + 1
  let mapGate := RGate.map
    (place (arithmeticLayout width)
      (arithmeticWiring workWidth endpointWidth scratchWidth))
  if updateSign then
    (Serial.carryGates width).map mapGate
  else
    (Serial.body width 0 width).map mapGate

def adderMajForward
    (workWidth endpointWidth scratchWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | position, count + 1 =>
      Adder.maj (targetOffset workWidth + position) (sourceOffset + position)
          (carryWire workWidth endpointWidth scratchWidth) ++
        adderMajForward workWidth endpointWidth scratchWidth
          (position + 1) count

def adderUmaBackward
    (workWidth endpointWidth scratchWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, count + 1 =>
      Adder.uma (sourceOffset + top - 1) (targetOffset workWidth + top - 1)
          (carryWire workWidth endpointWidth scratchWidth) ++
        adderUmaBackward workWidth endpointWidth scratchWidth (top - 1) count

theorem arithmeticLayout_width (width : Nat) :
    (arithmeticLayout width).width = 2 * width + 2 := by
  simp [arithmeticLayout, Layout.width]
  omega

theorem arithmetic_disjoint
    {right workWidth endpointWidth scratchWidth : Nat}
    (hR : right < workWidth) :
    Wiring.Disjoint (arithmeticLayout (right + 1))
      (arithmeticWiring workWidth endpointWidth scratchWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
    simp [arithmeticWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
    simp [arithmeticWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl <;>
    simp [arithmeticLayout, arithmeticWiring, Layout.size, targetOffset,
      sourceOffset, carryWire, signWire, scratchOffset, boundaryOffset] at * <;>
    omega

theorem place_arithmetic_target
    {width workWidth endpointWidth scratchWidth position : Nat}
    (hposition : position < width) :
    place (arithmeticLayout width)
        (arithmeticWiring workWidth endpointWidth scratchWidth) position =
      targetOffset workWidth + position := by
  simp [arithmeticLayout, arithmeticWiring, place, hposition]

theorem place_arithmetic_source
    {width workWidth endpointWidth scratchWidth position : Nat}
    (hposition : position < width) :
    place (arithmeticLayout width)
        (arithmeticWiring workWidth endpointWidth scratchWidth)
        (width + position) =
      sourceOffset + position := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show width + position - width = position by omega,
    if_pos hposition]

theorem place_arithmetic_carry
    (width workWidth endpointWidth scratchWidth : Nat) :
    place (arithmeticLayout width)
        (arithmeticWiring workWidth endpointWidth scratchWidth) (2 * width) =
      carryWire workWidth endpointWidth scratchWidth := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show 2 * width - width = width by omega,
    if_neg (by omega), Nat.sub_self, if_pos (by omega)]
  simp

theorem place_arithmetic_sign
    (width workWidth endpointWidth scratchWidth : Nat) :
    place (arithmeticLayout width)
        (arithmeticWiring workWidth endpointWidth scratchWidth)
        (2 * width + 1) = signWire := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show 2 * width + 1 - width = width + 1 by omega,
    if_neg (by omega), show width + 1 - width = 1 by omega,
    if_neg (by omega), Nat.sub_self, if_pos (by omega)]
  simp

theorem map_serial_maj
    {width workWidth endpointWidth scratchWidth position : Nat}
    (hposition : position < width) :
    (Adder.maj position (width + position) (2 * width)).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring workWidth endpointWidth scratchWidth))) =
      Adder.maj (targetOffset workWidth + position) (sourceOffset + position)
        (carryWire workWidth endpointWidth scratchWidth) := by
  simp only [Adder.maj, List.map_cons, List.map_nil, RGate.map]
  rw [place_arithmetic_carry, place_arithmetic_source hposition,
    place_arithmetic_target hposition]

theorem map_serial_uma
    {width workWidth endpointWidth scratchWidth position : Nat}
    (hposition : position < width) :
    (Adder.uma (width + position) position (2 * width)).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring workWidth endpointWidth scratchWidth))) =
      Adder.uma (sourceOffset + position) (targetOffset workWidth + position)
        (carryWire workWidth endpointWidth scratchWidth) := by
  simp only [Adder.uma, List.map_cons, List.map_nil, RGate.map]
  rw [place_arithmetic_carry, place_arithmetic_source hposition,
    place_arithmetic_target hposition]

theorem adderUmaBackward_snoc
    (workWidth endpointWidth scratchWidth : Nat) : ∀ count top,
    count + 1 ≤ top →
    adderUmaBackward workWidth endpointWidth scratchWidth top (count + 1) =
      adderUmaBackward workWidth endpointWidth scratchWidth top count ++
        Adder.uma (sourceOffset + (top - (count + 1)))
          (targetOffset workWidth + (top - (count + 1)))
          (carryWire workWidth endpointWidth scratchWidth) := by
  intro count
  induction count with
  | zero =>
      intro top htop
      simp [adderUmaBackward]
      congr 4 <;> omega
  | succ count ih =>
      intro top htop
      change Adder.uma (sourceOffset + top - 1)
          (targetOffset workWidth + top - 1)
          (carryWire workWidth endpointWidth scratchWidth) ++
          adderUmaBackward workWidth endpointWidth scratchWidth
            (top - 1) (count + 1) =
        (Adder.uma (sourceOffset + top - 1)
            (targetOffset workWidth + top - 1)
            (carryWire workWidth endpointWidth scratchWidth) ++
          adderUmaBackward workWidth endpointWidth scratchWidth
            (top - 1) count) ++
        Adder.uma (sourceOffset + (top - (count + 1 + 1)))
          (targetOffset workWidth + (top - (count + 1 + 1)))
          (carryWire workWidth endpointWidth scratchWidth)
      rw [ih (top - 1) (by omega), List.append_assoc]
      simp only [show top - 1 - (count + 1) =
        top - (count + 1 + 1) by omega]

theorem map_serial_majChain
    {width workWidth endpointWidth scratchWidth : Nat} : ∀ count position,
    position + count ≤ width →
    (Serial.majChain width position count).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring workWidth endpointWidth scratchWidth))) =
      adderMajForward workWidth endpointWidth scratchWidth position count := by
  intro count
  induction count with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hbound
      simp only [Serial.majChain, List.map_append, adderMajForward]
      rw [map_serial_maj (by omega), ih (position + 1) (by omega)]

theorem map_serial_umaChain
    {width workWidth endpointWidth scratchWidth : Nat} : ∀ count position,
    position + count ≤ width →
    (Serial.umaChain width position count).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring workWidth endpointWidth scratchWidth))) =
      adderUmaBackward workWidth endpointWidth scratchWidth
        (position + count) count := by
  intro count
  induction count with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hbound
      simp only [Serial.umaChain, List.map_append]
      rw [ih (position + 1) (by omega), map_serial_uma (by omega),
        adderUmaBackward_snoc workWidth endpointWidth scratchWidth count
          (position + (count + 1)) (by omega)]
      simp only [
        show position + 1 + count = position + (count + 1) by omega,
        show position + (count + 1) - (count + 1) = position by omega]

theorem idealGates_eq_adderGates
    {right workWidth endpointWidth scratchWidth : Nat}
    {updateSign : Bool} :
    idealGates right workWidth endpointWidth scratchWidth updateSign =
      adderMajForward workWidth endpointWidth scratchWidth 0 (right + 1) ++
      signUpdateGates workWidth endpointWidth scratchWidth updateSign ++
      adderUmaBackward workWidth endpointWidth scratchWidth (right + 1)
        (right + 1) := by
  cases updateSign with
  | false =>
      simp only [idealGates, Bool.false_eq_true, ↓reduceIte,
        Serial.body_eq_chains, List.map_append, signUpdateGates]
      rw [map_serial_majChain (right + 1) 0 (by omega),
        map_serial_umaChain (right + 1) 0 (by omega)]
      simp
  | true =>
      simp only [idealGates, ↓reduceIte, Serial.carryGates,
        List.map_append, List.map_cons, List.map_nil, RGate.map,
        signUpdateGates]
      rw [map_serial_majChain (right + 1) 0 (by omega),
        map_serial_umaChain (right + 1) 0 (by omega),
        place_arithmetic_carry,
        show Serial.signWire (right + 1) = 2 * (right + 1) + 1 by rfl,
        place_arithmetic_sign]
      simp

theorem baseMajForward_eq_adderMajForward
    {workWidth endpointWidth scratchWidth I : Nat} : ∀ count position,
    position + count ≤ workWidth →
    actGates
        (baseMajForward workWidth endpointWidth scratchWidth position count) I =
      actGates
        (adderMajForward workWidth endpointWidth scratchWidth position count) I := by
  intro count
  induction count generalizing I with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hbound
      simp only [baseMajForward, adderMajForward, actGates_append]
      rw [baseMajAt_eq_adderMajAt (by omega),
        ih (position := position + 1) (by omega)]

theorem baseUmaBackward_eq_adderUmaBackward
    {workWidth endpointWidth scratchWidth I : Nat} : ∀ count top,
    count ≤ top → top ≤ workWidth →
    actGates
        (baseUmaBackward workWidth endpointWidth scratchWidth top count) I =
      actGates
        (adderUmaBackward workWidth endpointWidth scratchWidth top count) I := by
  intro count
  induction count generalizing I with
  | zero => intro top _ _; rfl
  | succ count ih =>
      intro top hcount htop
      simp only [baseUmaBackward, adderUmaBackward, actGates_append]
      have htopPositive : 0 < top := by omega
      rw [baseUmaAt_eq_adderUmaAt (position := top - 1) (by omega)]
      change actGates
          (baseUmaBackward workWidth endpointWidth scratchWidth
            (top - 1) count)
          (actGates
            (Adder.uma (sourceOffset + (top - 1))
              (targetOffset workWidth + (top - 1))
              (carryWire workWidth endpointWidth scratchWidth)) I) = _
      rw [ih (top := top - 1) (by omega) (by omega)]
      congr 4 <;> omega

theorem activeGates_zero_eq_ideal
    {right workWidth endpointWidth scratchWidth I : Nat}
    {updateSign : Bool} (hR : right < workWidth) :
    actGates
        (activeGates 0 right workWidth endpointWidth scratchWidth updateSign) I =
      actGates
        (idealGates right workWidth endpointWidth scratchWidth updateSign) I := by
  rw [idealGates_eq_adderGates]
  simp only [activeGates, Nat.sub_zero, actGates_append]
  rw [baseMajForward_eq_adderMajForward
      (count := right + 1) (position := 0) (by omega)]
  let middle := actGates
    (signUpdateGates workWidth endpointWidth scratchWidth updateSign)
    (actGates
      (adderMajForward workWidth endpointWidth scratchWidth 0 (right + 1)) I)
  change actGates
      (baseUmaBackward workWidth endpointWidth scratchWidth
        (right + 1) (right + 1)) middle =
    actGates
      (adderUmaBackward workWidth endpointWidth scratchWidth
        (right + 1) (right + 1)) middle
  exact baseUmaBackward_eq_adderUmaBackward
    (count := right + 1) (top := right + 1) (by omega) (by omega)

theorem idealGates_sign_act
    {right workWidth endpointWidth scratchWidth I : Nat}
    (hR : right < workWidth) :
    actGates (idealGates right workWidth endpointWidth scratchWidth true) I =
      writeField
        (writeField I (targetOffset workWidth) (right + 1)
          ((readField I (targetOffset workWidth) (right + 1) +
            readField I sourceOffset (right + 1) +
            bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
              2 ^ (right + 1)))
        signWire 1
          ((bitValue I signWire +
            (readField I (targetOffset workWidth) (right + 1) +
              readField I sourceOffset (right + 1) +
              bitValue I (carryWire workWidth endpointWidth scratchWidth)) /
                2 ^ (right + 1)) % 2) := by
  let width := right + 1
  let L := arithmeticLayout width
  let W := arithmeticWiring workWidth endpointWidth scratchWidth
  let gathered := gatherBits (place L W) L.width I
  have hwidth : 0 < width := by
    dsimp [width]
    omega
  have hTarget : readField gathered 0 width =
      readField I (targetOffset workWidth) width := by
    have hr := readField_gatherBits L W 0 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I sourceOffset width := by
    have hr := readField_gatherBits L W 1 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (carryWire workWidth endpointWidth scratchWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  have hSign : bitValue gathered (Serial.signWire width) =
      bitValue I signWire := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 3 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Serial.signWire, Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega] using hr
  change actGates
      ((Serial.carryGates width).map (RGate.map (place L W))) I = _
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 3)
      (v₁ := (readField I (targetOffset workWidth) width +
        readField I sourceOffset width +
        bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
          2 ^ width)
      (v₂ := (bitValue I signWire +
        (readField I (targetOffset workWidth) width +
          readField I sourceOffset width +
          bitValue I (carryWire workWidth endpointWidth scratchWidth)) /
            2 ^ width) % 2)
      (arithmetic_disjoint hR)
      (by simp [L, W, arithmeticLayout, arithmeticWiring])
      (by simp [L, arithmeticLayout])
      (by simp [L, arithmeticLayout])
      (by decide)
  · intro g hg
    rw [show Layout.width L = 2 * width + 2 by
      simp [L, arithmeticLayout_width]]
    exact RCircuit.wellFormed_mem
      (Serial.carryCircuit_wellFormed width) hg
  · have hlocal := Serial.carryGates_act
      (width := width) (i := gathered) hwidth
    rw [hlocal, hTarget, hSource, hCarry, hSign]
    simp [gathered, L, arithmeticLayout, Layout.write, Layout.offset,
      Layout.size, Serial.signWire,
      show width + (width + 1) = 2 * width + 1 by omega]

theorem idealGates_noSign_act
    {right workWidth endpointWidth scratchWidth I : Nat}
    (hR : right < workWidth) :
    actGates (idealGates right workWidth endpointWidth scratchWidth false) I =
      writeField I (targetOffset workWidth) (right + 1)
        ((readField I (targetOffset workWidth) (right + 1) +
          readField I sourceOffset (right + 1) +
          bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
            2 ^ (right + 1)) := by
  let width := right + 1
  let L := arithmeticLayout width
  let W := arithmeticWiring workWidth endpointWidth scratchWidth
  let gathered := gatherBits (place L W) L.width I
  have hTarget : readField gathered 0 width =
      readField I (targetOffset workWidth) width := by
    have hr := readField_gatherBits L W 0 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I sourceOffset width := by
    have hr := readField_gatherBits L W 1 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (carryWire workWidth endpointWidth scratchWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  change actGates
      ((Serial.body width 0 width).map (RGate.map (place L W))) I = _
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := (readField I (targetOffset workWidth) width +
        readField I sourceOffset width +
        bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
          2 ^ width)
      (arithmetic_disjoint hR)
      (by simp [L, W, arithmeticLayout, arithmeticWiring])
      (by simp [L, arithmeticLayout])
  · intro g hg
    rw [show Layout.width L = 2 * width + 2 by
      simp [L, arithmeticLayout_width]]
    exact RGate.wellFormed_mono (by simp [Serial.circuit])
      (RCircuit.wellFormed_mem (Serial.circuit_wellFormed width) hg)
  · have hlocal := Serial.body_act width width 0 gathered (by omega)
    rw [hlocal, hTarget, hSource, hCarry]
    simp [gathered, L, arithmeticLayout, Layout.write, Layout.offset,
      Layout.size]

theorem activeGates_zero_sign_act
    {right workWidth endpointWidth scratchWidth I : Nat}
    (hR : right < workWidth) :
    actGates (activeGates 0 right workWidth endpointWidth scratchWidth true) I =
      writeField
        (writeField I (targetOffset workWidth) (right + 1)
          ((readField I (targetOffset workWidth) (right + 1) +
            readField I sourceOffset (right + 1) +
            bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
              2 ^ (right + 1)))
        signWire 1
          ((bitValue I signWire +
            (readField I (targetOffset workWidth) (right + 1) +
              readField I sourceOffset (right + 1) +
              bitValue I (carryWire workWidth endpointWidth scratchWidth)) /
                2 ^ (right + 1)) % 2) := by
  rw [activeGates_zero_eq_ideal hR, idealGates_sign_act hR]

theorem activeGates_zero_noSign_act
    {right workWidth endpointWidth scratchWidth I : Nat}
    (hR : right < workWidth) :
    actGates (activeGates 0 right workWidth endpointWidth scratchWidth false) I =
      writeField I (targetOffset workWidth) (right + 1)
        ((readField I (targetOffset workWidth) (right + 1) +
          readField I sourceOffset (right + 1) +
          bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
            2 ^ (right + 1)) := by
  rw [activeGates_zero_eq_ideal hR, idealGates_noSign_act hR]

theorem labelToggle_eq_fixed
    {start boundary position workWidth endpointWidth scratchWidth : Nat}
    (hstart : start ≤ boundary) :
    (if some boundary = some (start + position) then
        [.x (accumulatorWire workWidth endpointWidth scratchWidth)]
      else []) =
      fixedToggle (boundary - start) position workWidth endpointWidth
        scratchWidth := by
  simp only [Option.some.injEq]
  by_cases hselected : boundary = start + position
  · rw [if_pos hselected]
    unfold fixedToggle
    rw [if_pos (by omega)]
  · rw [if_neg hselected]
    unfold fixedToggle
    rw [if_neg (by
      intro hposition
      apply hselected
      omega)]

theorem firstLabelScan_tail_eq_fixed
    {start boundary workWidth endpointWidth scratchWidth : Nat}
    (hstart : start ≤ boundary) : ∀ count position,
    0 < position →
    firstLabelScan start workWidth endpointWidth scratchWidth
        (List.range' (start + position) count) (some boundary) =
      fixedFirstScan 0 (boundary - start) workWidth endpointWidth scratchWidth
        position count := by
  intro count
  induction count with
  | zero => intro position _; rfl
  | succ count ih =>
      intro position hposition
      simp only [List.range'_succ, firstLabelScan, fixedFirstScan]
      have hleft :
          fixedToggle 0 position workWidth endpointWidth scratchWidth = [] := by
        simp [fixedToggle]
        omega
      rw [hleft]
      have htail := ih (position + 1) (by omega)
      rw [show start + position + 1 = start + (position + 1) by omega,
        htail, show start + position - start = position by omega]
      rw [labelToggle_eq_fixed hstart]
      simp only [List.nil_append, List.append_assoc]

theorem firstLabelScan_range_eq_fixed
    {start boundary workWidth endpointWidth scratchWidth count : Nat}
    (hstart : start ≤ boundary) :
    [.x (accumulatorWire workWidth endpointWidth scratchWidth)] ++
        firstLabelScan start workWidth endpointWidth scratchWidth
          (List.range' start (count + 1)) (some boundary) =
      fixedFirstScan 0 (boundary - start) workWidth endpointWidth scratchWidth
        0 (count + 1) := by
  simp only [List.range'_succ, firstLabelScan, fixedFirstScan]
  have htail := firstLabelScan_tail_eq_fixed
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) hstart count 1 (by omega)
  rw [htail, show start - start = 0 by omega]
  rw [show start = start + 0 by omega, labelToggle_eq_fixed hstart]
  simp [fixedToggle, List.append_assoc]

theorem secondLabelScan_reverse_eq_fixed
    {start boundary workWidth endpointWidth scratchWidth : Nat}
    (hstart : start ≤ boundary) : ∀ count,
    secondLabelScan start workWidth endpointWidth scratchWidth
        (List.range' start (count + 1)).reverse (some boundary) ++
        [.x (accumulatorWire workWidth endpointWidth scratchWidth)] =
      fixedSecondScan 0 (boundary - start) workWidth endpointWidth scratchWidth
        (count + 1) := by
  intro count
  induction count with
  | zero =>
      simp only [List.range'_succ, List.range'_zero, List.reverse_singleton,
        secondLabelScan, fixedSecondScan, Nat.zero_add]
      rw [show start = start + 0 by omega, labelToggle_eq_fixed hstart]
      simp [fixedToggle, List.append_assoc]
  | succ count ih =>
      rw [List.range'_1_concat, List.reverse_append,
        secondLabelScan_append]
      simp only [List.reverse_singleton, secondLabelScan]
      rw [show fixedSecondScan 0 (boundary - start) workWidth endpointWidth
          scratchWidth (count + 2) =
        fixedToggle (boundary - start) (count + 1) workWidth endpointWidth
            scratchWidth ++
          LuoPrefixArithmetic.umaAt (count + 1) workWidth endpointWidth
            scratchWidth ++
          fixedToggle 0 (count + 1) workWidth endpointWidth scratchWidth ++
          fixedSecondScan 0 (boundary - start) workWidth endpointWidth
            scratchWidth (count + 1) by rfl]
      have hleft : fixedToggle 0 (count + 1) workWidth endpointWidth
          scratchWidth = [] := by
        simp [fixedToggle]
      rw [hleft]
      have hlabel : start + (count + 1) - start = count + 1 := by omega
      rw [hlabel]
      rw [labelToggle_eq_fixed hstart]
      rw [List.append_assoc, ih]

theorem contiguousAddGates_eq_fixedGates
    {start workWidth endpointWidth scratchWidth boundary : Nat}
    {updateSign : Bool}
    (hstart : start ≤ boundary)
    (hboundary : boundary < start + workWidth) :
    contiguousAddGates start workWidth endpointWidth scratchWidth boundary
        updateSign =
      fixedGates 0 (boundary - start) workWidth endpointWidth scratchWidth
        updateSign := by
  have hpositive : 0 < workWidth := by omega
  obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : workWidth ≠ 0)
  have hfirst := firstLabelScan_range_eq_fixed
    (workWidth := count + 1) (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) (count := count) hstart
  have hsecond := secondLabelScan_reverse_eq_fixed
    (workWidth := count + 1) (endpointWidth := endpointWidth)
    (scratchWidth := scratchWidth) hstart count
  simp only [contiguousAddGates, fixedGates]
  calc
    [.x (accumulatorWire (count + 1) endpointWidth scratchWidth)] ++
          firstLabelScan start (count + 1) endpointWidth scratchWidth
            (List.range' start (count + 1)) (some boundary) ++
          signUpdateGates (count + 1) endpointWidth scratchWidth updateSign ++
          secondLabelScan start (count + 1) endpointWidth scratchWidth
            (List.range' start (count + 1)).reverse (some boundary) ++
          [.x (accumulatorWire (count + 1) endpointWidth scratchWidth)] =
        ([.x (accumulatorWire (count + 1) endpointWidth scratchWidth)] ++
          firstLabelScan start (count + 1) endpointWidth scratchWidth
            (List.range' start (count + 1)) (some boundary)) ++
          signUpdateGates (count + 1) endpointWidth scratchWidth updateSign ++
          (secondLabelScan start (count + 1) endpointWidth scratchWidth
            (List.range' start (count + 1)).reverse (some boundary) ++
            [.x (accumulatorWire (count + 1) endpointWidth scratchWidth)]) := by
          simp [List.append_assoc]
    _ = fixedFirstScan 0 (boundary - start) (count + 1) endpointWidth
          scratchWidth 0 (count + 1) ++
          signUpdateGates (count + 1) endpointWidth scratchWidth updateSign ++
          fixedSecondScan 0 (boundary - start) (count + 1) endpointWidth
            scratchWidth (count + 1) := by
          rw [hfirst, hsecond]

theorem selected_boundary_range
    {tree : Tree} {start workWidth boundary : Nat}
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary) :
    start ≤ boundary ∧ boundary < start + workWidth := by
  have hmem := Tree.select_mem_labels hselect
  rw [hlabels] at hmem
  simpa using hmem

theorem addGates_sign_act
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth true) I =
      writeField
        (writeField I (targetOffset workWidth) (boundary - start + 1)
          ((readField I (targetOffset workWidth) (boundary - start + 1) +
            readField I sourceOffset (boundary - start + 1) +
            bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
              2 ^ (boundary - start + 1)))
        signWire 1
          ((bitValue I signWire +
            (readField I (targetOffset workWidth) (boundary - start + 1) +
              readField I sourceOffset (boundary - start + 1) +
              bitValue I (carryWire workWidth endpointWidth scratchWidth)) /
                2 ^ (boundary - start + 1)) % 2) := by
  obtain ⟨hstart, hboundaryRange⟩ :=
    selected_boundary_range hlabels hselect
  have hright : boundary - start < workWidth := by omega
  rw [addGates_act_contiguous hvalid hdepth hlabels hselect hboundary houter
      hscratch,
    contiguousAddGates_eq_fixedGates hstart hboundaryRange,
    fixedGates_eq_selected (by omega) hright haccumulator hcellScratch,
    selectedGates_zero_eq_active hright,
    activeGates_zero_sign_act hright]

theorem addGates_noSign_act
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates
        (addGates tree start workWidth endpointWidth scratchWidth false) I =
      writeField I (targetOffset workWidth) (boundary - start + 1)
        ((readField I (targetOffset workWidth) (boundary - start + 1) +
          readField I sourceOffset (boundary - start + 1) +
          bitValue I (carryWire workWidth endpointWidth scratchWidth)) %
            2 ^ (boundary - start + 1)) := by
  obtain ⟨hstart, hboundaryRange⟩ :=
    selected_boundary_range hlabels hselect
  have hright : boundary - start < workWidth := by omega
  rw [addGates_act_contiguous hvalid hdepth hlabels hselect hboundary houter
      hscratch,
    contiguousAddGates_eq_fixedGates hstart hboundaryRange,
    fixedGates_eq_selected (by omega) hright haccumulator hcellScratch,
    selectedGates_zero_eq_active hright,
    activeGates_zero_noSign_act hright]

theorem majAt_wellFormed
    {position workWidth endpointWidth scratchWidth : Nat}
    (hposition : position < workWidth) :
    (LuoPrefixArithmetic.majAt position workWidth endpointWidth scratchWidth).all
      (RGate.wellFormed
        (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width) =
      true := by
  apply wellFormed_placeGates (cell_disjoint hposition)
    (by simp [CellPlaced.layout, LuoPrefixArithmetic.cellWiring,
      CellPlaced.wiring])
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [CellPlaced.layout] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      simp [LuoPrefixArithmetic.cellWiring, CellPlaced.wiring,
        CellPlaced.layout, Layout.size, LuoPrefixArithmetic.layout_width,
        targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, scratchOffset, boundaryOffset] <;>
      omega
  · exact CellPlaced.component_wellFormed CellPlaced.maj_wellFormed

theorem umaAt_wellFormed
    {position workWidth endpointWidth scratchWidth : Nat}
    (hposition : position < workWidth) :
    (LuoPrefixArithmetic.umaAt position workWidth endpointWidth scratchWidth).all
      (RGate.wellFormed
        (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width) =
      true := by
  apply wellFormed_placeGates (cell_disjoint hposition)
    (by simp [CellPlaced.layout, LuoPrefixArithmetic.cellWiring,
      CellPlaced.wiring])
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [CellPlaced.layout] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      simp [LuoPrefixArithmetic.cellWiring, CellPlaced.wiring,
        CellPlaced.layout, Layout.size, LuoPrefixArithmetic.layout_width,
        targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, scratchOffset, boundaryOffset] <;>
      omega
  · exact CellPlaced.component_wellFormed CellPlaced.uma_wellFormed

private theorem emits_wellFormed
    {tree : Tree}
    {start workWidth endpointWidth scratchWidth ctrl scratchDepth : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : scratchDepth + tree.depth ≤ scratchWidth)
    (hcontrolTotal : ctrl <
      (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width)
    (hcontrolKind :
      ctrl = outerWire ∨
        scratchOffset workWidth endpointWidth ≤ ctrl ∧
          ctrl < scratchOffset workWidth endpointWidth + scratchDepth) :
    (firstEmit start workWidth endpointWidth scratchWidth tree ctrl
        scratchDepth).all
        (RGate.wellFormed
          (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width) =
      true ∧
    (secondEmit start workWidth endpointWidth scratchWidth tree ctrl
        scratchDepth).all
        (RGate.wellFormed
          (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width) =
      true := by
  induction tree generalizing ctrl scratchDepth with
  | empty => exact ⟨rfl, rfl⟩
  | leaf label =>
      rcases hvalid with ⟨hstart, hlabel⟩
      have hposition : label - start < workWidth := by omega
      have hcellMaj := majAt_wellFormed
        (endpointWidth := endpointWidth) (scratchWidth := scratchWidth) hposition
      have hcellUma := umaAt_wellFormed
        (endpointWidth := endpointWidth) (scratchWidth := scratchWidth) hposition
      have haccumulatorTotal :
          accumulatorWire workWidth endpointWidth scratchWidth <
            (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width := by
        rw [LuoPrefixArithmetic.layout_width]
        simp [accumulatorWire, carryWire, scratchOffset, boundaryOffset]
        omega
      have hcontrolAccumulator :
          ctrl ≠ accumulatorWire workWidth endpointWidth scratchWidth := by
        rcases hcontrolKind with rfl | hscratch
        · simp [outerWire, accumulatorWire, carryWire, scratchOffset,
            boundaryOffset]
        · simp [accumulatorWire, carryWire] at *
          omega
      have htoggle :
          ([.cx ctrl (accumulatorWire workWidth endpointWidth scratchWidth)] :
            List RGate).all
            (RGate.wellFormed
              (LuoPrefixArithmetic.layout workWidth endpointWidth
                scratchWidth).width) = true := by
        simp only [List.all_cons, List.all_nil, Bool.and_true, RGate.wellFormed,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hcontrolTotal, haccumulatorTotal⟩, hcontrolAccumulator⟩
      simp only [firstEmit, secondEmit, List.all_append, hcellMaj, hcellUma,
        htoggle, Bool.and_self]
      exact ⟨True.intro, True.intro⟩
  | node bit zero one hzero hone =>
      rcases hvalid with ⟨hbit, hzvalid, hovalid⟩
      have hzdepth : scratchDepth + 1 + zero.depth ≤ scratchWidth := by
        have hzle :
            scratchDepth + (zero.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_left zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤
              scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hzle.trans hnode
      have hodepth : scratchDepth + 1 + one.depth ≤ scratchWidth := by
        have hole :
            scratchDepth + (one.depth + 1) ≤
              scratchDepth + (Nat.max zero.depth one.depth + 1) :=
          Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.le_max_right zero.depth one.depth)) _
        have hnode :
            scratchDepth + (Nat.max zero.depth one.depth + 1) ≤
              scratchWidth := by
          simpa [PrunedSelectSwap.Tree.depth] using hdepth
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hole.trans hnode
      have hscratchDepth : scratchDepth < scratchWidth := by
        simp only [PrunedSelectSwap.Tree.depth] at hdepth
        omega
      let selector := boundaryOffset workWidth + bit
      let child := childControl workWidth endpointWidth scratchDepth
      let compute := negativeAnd ctrl selector child
      have hselectorTotal : selector <
          (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width := by
        rw [LuoPrefixArithmetic.layout_width]
        simp [selector, boundaryOffset]
        omega
      have hchildTotal : child <
          (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width := by
        rw [LuoPrefixArithmetic.layout_width]
        simp [child, childControl, scratchOffset, boundaryOffset]
        omega
      have hctrlSelector : ctrl ≠ selector := by
        rcases hcontrolKind with rfl | hscratch
        · simp [outerWire, selector, boundaryOffset]
          omega
        · simp [selector, scratchOffset] at *
          omega
      have hselectorChild : selector ≠ child := by
        simp [selector, child, childControl, scratchOffset]
        omega
      have hctrlChild : ctrl ≠ child := by
        rcases hcontrolKind with rfl | hscratch
        · simp [outerWire, child, childControl, scratchOffset,
            boundaryOffset]
          omega
        · simp [child, childControl] at *
          omega
      have hcompute : compute.all
          (RGate.wellFormed
            (LuoPrefixArithmetic.layout workWidth endpointWidth
              scratchWidth).width) = true := by
        simp [compute, negativeAnd, RGate.wellFormed, hselectorTotal,
          hcontrolTotal, hchildTotal, hctrlSelector, hselectorChild,
          hctrlChild]
      have hcx : ([.cx ctrl child] : List RGate).all
          (RGate.wellFormed
            (LuoPrefixArithmetic.layout workWidth endpointWidth
              scratchWidth).width) = true := by
        simp only [List.all_cons, List.all_nil, Bool.and_true, RGate.wellFormed,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hcontrolTotal, hchildTotal⟩, hctrlChild⟩
      have hchildKind :
          child = outerWire ∨
            scratchOffset workWidth endpointWidth ≤ child ∧
              child < scratchOffset workWidth endpointWidth +
                (scratchDepth + 1) := by
        right
        simp [child, childControl]
      have hz := hzero hzvalid hzdepth hchildTotal hchildKind
      have ho := hone hovalid hodepth hchildTotal hchildKind
      have hcomputeReverse : compute.reverse.all
          (RGate.wellFormed
            (LuoPrefixArithmetic.layout workWidth endpointWidth
              scratchWidth).width) = true := by
        simpa using hcompute
      constructor
      · change (compute ++
            firstEmit start workWidth endpointWidth scratchWidth zero child
              (scratchDepth + 1) ++
            [RGate.cx ctrl child] ++
            firstEmit start workWidth endpointWidth scratchWidth one child
              (scratchDepth + 1) ++
            [RGate.cx ctrl child] ++ compute.reverse).all _ = true
        simp only [List.all_append, hcompute, hz.1, hcx, ho.1,
          hcomputeReverse, Bool.and_self]
      · change (compute ++ [RGate.cx ctrl child] ++
            secondEmit start workWidth endpointWidth scratchWidth one child
              (scratchDepth + 1) ++
            [RGate.cx ctrl child] ++
            secondEmit start workWidth endpointWidth scratchWidth zero child
              (scratchDepth + 1) ++ compute.reverse).all _ = true
        simp only [List.all_append, hcompute, hcx, ho.2, hz.2,
          hcomputeReverse, Bool.and_self]

theorem addGates_wellFormed
    {tree : Tree} {start workWidth endpointWidth scratchWidth : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (updateSign : Bool) :
    (addGates tree start workWidth endpointWidth scratchWidth updateSign).all
      (RGate.wellFormed
        (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width) =
      true := by
  have houterTotal : outerWire <
      (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width := by
    rw [LuoPrefixArithmetic.layout_width]
    simp [outerWire]
  have haccumulatorTotal :
      accumulatorWire workWidth endpointWidth scratchWidth <
        (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width := by
    rw [LuoPrefixArithmetic.layout_width]
    simp [accumulatorWire, carryWire, scratchOffset, boundaryOffset]
    omega
  have houterAccumulator :
      outerWire ≠ accumulatorWire workWidth endpointWidth scratchWidth := by
    simp [outerWire, accumulatorWire, carryWire, scratchOffset, boundaryOffset]
  have htoggle :
      ([.cx outerWire
        (accumulatorWire workWidth endpointWidth scratchWidth)] : List RGate).all
        (RGate.wellFormed
          (LuoPrefixArithmetic.layout workWidth endpointWidth
            scratchWidth).width) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, RGate.wellFormed,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨houterTotal, haccumulatorTotal⟩, houterAccumulator⟩
  have hemits := emits_wellFormed
    (ctrl := outerWire) (scratchDepth := 0) hvalid
    (by simpa using hdepth) houterTotal (Or.inl rfl)
  have hsign :
      (signUpdateGates workWidth endpointWidth scratchWidth updateSign).all
        (RGate.wellFormed
          (LuoPrefixArithmetic.layout workWidth endpointWidth
            scratchWidth).width) = true := by
    cases updateSign with
    | false => rfl
    | true =>
        have hcarryTotal :
            carryWire workWidth endpointWidth scratchWidth <
              (LuoPrefixArithmetic.layout workWidth endpointWidth
                scratchWidth).width := by
          rw [LuoPrefixArithmetic.layout_width]
          simp [carryWire, scratchOffset, boundaryOffset]
          omega
        have hsignTotal : signWire <
            (LuoPrefixArithmetic.layout workWidth endpointWidth
              scratchWidth).width := by
          rw [LuoPrefixArithmetic.layout_width]
          simp [signWire]
        have hcarrySign :
            carryWire workWidth endpointWidth scratchWidth ≠ signWire := by
          simp [carryWire, signWire, scratchOffset, boundaryOffset]
          omega
        change ([.cx (carryWire workWidth endpointWidth scratchWidth)
          signWire] : List RGate).all _ = true
        simp only [List.all_cons, List.all_nil, Bool.and_true,
          RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hcarryTotal, hsignTotal⟩, hcarrySign⟩
  simp only [addGates, List.all_append, htoggle, hemits.1, hsign, hemits.2,
    Bool.and_self]

theorem subGates_act
    {tree : Tree} {start workWidth endpointWidth scratchWidth boundary I : Nat}
    (hvalid : tree.RangeValid start workWidth endpointWidth)
    (hdepth : tree.depth ≤ scratchWidth)
    (hlabels : Tree.labels tree = List.range' start workWidth)
    (hselect : tree.select boundary = some boundary)
    (hboundary :
      readField I (boundaryOffset workWidth) endpointWidth = boundary)
    (houter : bitValue I outerWire = 1)
    (hscratch : scratchClear workWidth endpointWidth 0 tree.depth I)
    (hcarry : bitValue I
      (carryWire workWidth endpointWidth scratchWidth) = 0)
    (haccumulator : bitValue I
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0)
    (hcellScratch : I.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false) :
    actGates (subGates tree start workWidth endpointWidth scratchWidth) I =
      writeField I (targetOffset workWidth) (boundary - start + 1)
        (Adder.difference (boundary - start + 1)
          (readField I sourceOffset (boundary - start + 1))
          (readField I (targetOffset workWidth) (boundary - start + 1))) := by
  obtain ⟨hstart, hboundaryRange⟩ := selected_boundary_range hlabels hselect
  let width := boundary - start + 1
  let target := targetOffset workWidth
  let source := sourceOffset
  let a := readField I source width
  let b := readField I target width
  let x := Adder.difference width a b
  let J := writeField I target width x
  have hwidth : width ≤ workWidth := by
    dsimp [width]
    omega
  have hSourceTarget : source + width ≤ target := by
    dsimp [source, target]
    simp [sourceOffset, targetOffset]
    omega
  have hTargetBoundary : target + width ≤ boundaryOffset workWidth := by
    dsimp [target]
    simp [targetOffset, boundaryOffset]
    omega
  have ha : a < 2 ^ width := readField_lt I source width
  have hb : b < 2 ^ width := readField_lt I target width
  have hspec : (a + x) % 2 ^ width = b := by
    simpa [x, Adder.difference] using
      (Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).1
  have hx : x < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)
  have hJTarget : readField J target width = x := by
    simp only [J]
    rw [readField_writeField_self hx]
  have hJSource : readField J source width = a := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inr hSourceTarget)]
  have hJBoundary :
      readField J (boundaryOffset workWidth) endpointWidth = boundary := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inl hTargetBoundary), hboundary]
  have hJOuter : bitValue J outerWire = 1 := by
    simp only [J]
    rw [bitValue_write_out (Or.inl (by
        dsimp [target]
        simp [outerWire, targetOffset]
        omega)), houter]
  have hJCarry : bitValue J
      (carryWire workWidth endpointWidth scratchWidth) = 0 := by
    simp only [J]
    rw [bitValue_write_out (Or.inr (by
        dsimp [target]
        simp [targetOffset, carryWire, scratchOffset, boundaryOffset]
        omega)), hcarry]
  have hJAccumulator : bitValue J
      (accumulatorWire workWidth endpointWidth scratchWidth) = 0 := by
    simp only [J]
    rw [bitValue_write_out (Or.inr (by
        dsimp [target]
        simp [targetOffset, accumulatorWire, carryWire, scratchOffset,
          boundaryOffset]
        omega)), haccumulator]
  have hJCellScratch : J.testBit
      (cellScratchWire workWidth endpointWidth scratchWidth) = false := by
    simp only [J]
    rw [testBit_writeField_outside (Or.inr (by
        dsimp [target]
        simp [targetOffset, cellScratchWire, carryWire, scratchOffset,
          boundaryOffset]
        omega)), hcellScratch]
  have hJScratch : scratchClear workWidth endpointWidth 0 tree.depth J := by
    intro k hk
    simp only [J]
    rw [bitValue_write_out (Or.inr (by
        dsimp [target]
        simp [targetOffset, scratchOffset, boundaryOffset]
        omega))]
    exact hscratch k hk
  have hrestore : writeField J target width b = I := by
    simp only [J]
    rw [writeField_writeField, show b = readField I target width from rfl,
      writeField_read]
  have hforward := addGates_noSign_act
    (I := J) hvalid hdepth hlabels hselect hJBoundary hJOuter hJScratch
      hJAccumulator hJCellScratch
  rw [show targetOffset workWidth = target by rfl,
    show boundary - start + 1 = width by rfl,
    show sourceOffset = source by rfl,
    hJTarget, hJSource, hJCarry] at hforward
  simp only [Nat.add_zero] at hforward
  rw [Nat.add_comm x a, hspec, hrestore] at hforward
  have hinverse := actGates_reverse
    (w := (LuoPrefixArithmetic.layout workWidth endpointWidth scratchWidth).width)
    (addGates_wellFormed hvalid hdepth false) J
  change actGates
      (subGates tree start workWidth endpointWidth scratchWidth)
      (actGates
        (addGates tree start workWidth endpointWidth scratchWidth false) J) = J
    at hinverse
  rw [hforward] at hinverse
  simpa [J, x, a, b, target, source, width] using hinverse

end VQ.Euclid.LuoPrefixFixed
