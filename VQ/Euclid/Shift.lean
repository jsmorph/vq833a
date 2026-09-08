/-
The physical shift schedule used on the shared second work register.

The two controls are the conditions already computed by the surrounding step:
`plus` enables one left position shift and one encoded-length increment, while
`minus` enables two right position shifts and two encoded-length decrements.
The circuit keeps both controls and restores the increment scratch field.
-/
import VQ.Euclid.Increment
import VQ.Reversible.Permutation
import VQ.Reversible.Wiring
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace Shift

open Reversible

def layout (workWidth shiftWidth : Nat) : Layout :=
  [shiftWidth, 1, shiftWidth, workWidth, 1]

def positionOffset : Nat := 0

def plusWire (shiftWidth : Nat) : Nat := shiftWidth

def scratchOffset (shiftWidth : Nat) : Nat := shiftWidth + 1

def workOffset (shiftWidth : Nat) : Nat := 2 * shiftWidth + 1

def minusWire (workWidth shiftWidth : Nat) : Nat :=
  workOffset shiftWidth + workWidth

def minusWiring (workWidth shiftWidth : Nat) : Wiring :=
  [positionOffset, minusWire workWidth shiftWidth, scratchOffset shiftWidth]

def placedDecrement (workWidth shiftWidth : Nat) : List RGate :=
  (Increment.circuit shiftWidth).reverse.gates.map
    (RGate.map (place (Increment.layout shiftWidth)
      (minusWiring workWidth shiftWidth)))

def gates (workWidth shiftWidth : Nat) : List RGate :=
  rotateRightControlled (plusWire shiftWidth) (workOffset shiftWidth) workWidth ++
    (Increment.circuit shiftWidth).gates ++
    rotateLeftControlled (minusWire workWidth shiftWidth)
      (workOffset shiftWidth) workWidth ++
    placedDecrement workWidth shiftWidth ++
    rotateLeftControlled (minusWire workWidth shiftWidth)
      (workOffset shiftWidth) workWidth ++
    placedDecrement workWidth shiftWidth

def circuit (workWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout workWidth shiftWidth).width,
    gates := gates workWidth shiftWidth }

def position (shiftWidth i : Nat) : Nat :=
  readField i positionOffset shiftWidth

def work (workWidth shiftWidth i : Nat) : Nat :=
  readField i (workOffset shiftWidth) workWidth

def scratch (shiftWidth i : Nat) : Nat :=
  readField i (scratchOffset shiftWidth) shiftWidth

def rotateRightOut (workWidth shiftWidth control i : Nat) : Nat :=
  if bitValue i control = 1 then
    writeField i (workOffset shiftWidth) workWidth
      (rotateRightValue workWidth (work workWidth shiftWidth i))
  else i

def rotateLeftOut (workWidth shiftWidth control i : Nat) : Nat :=
  if bitValue i control = 1 then
    writeField i (workOffset shiftWidth) workWidth
      (rotateLeftValue workWidth (work workWidth shiftWidth i))
  else i

def incrementOut (shiftWidth control i : Nat) : Nat :=
  writeField i positionOffset shiftWidth
    ((position shiftWidth i + bitValue i control) % 2 ^ shiftWidth)

def decrementOut (shiftWidth control i : Nat) : Nat :=
  writeField i positionOffset shiftWidth
    ((position shiftWidth i + 2 ^ shiftWidth - bitValue i control) %
      2 ^ shiftWidth)

def out (workWidth shiftWidth i : Nat) : Nat :=
  let i := rotateRightOut workWidth shiftWidth (plusWire shiftWidth) i
  let i := incrementOut shiftWidth (plusWire shiftWidth) i
  let i := rotateLeftOut workWidth shiftWidth
    (minusWire workWidth shiftWidth) i
  let i := decrementOut shiftWidth (minusWire workWidth shiftWidth) i
  let i := rotateLeftOut workWidth shiftWidth
    (minusWire workWidth shiftWidth) i
  decrementOut shiftWidth (minusWire workWidth shiftWidth) i

theorem out_increment
    {workWidth shiftWidth i : Nat}
    (hplus : bitValue i (plusWire shiftWidth) = 1)
    (hminus : bitValue i (minusWire workWidth shiftWidth) = 0) :
    position shiftWidth (out workWidth shiftWidth i) =
        (position shiftWidth i + 1) % 2 ^ shiftWidth ∧
      work workWidth shiftWidth (out workWidth shiftWidth i) =
        rotateRightValue workWidth (work workWidth shiftWidth i) := by
  let workValue := rotateRightValue workWidth (work workWidth shiftWidth i)
  let positionValue := (position shiftWidth i + 1) % 2 ^ shiftWidth
  let i₁ := writeField i (workOffset shiftWidth) workWidth workValue
  let i₂ := writeField i₁ positionOffset shiftWidth positionValue
  have hi₁ : rotateRightOut workWidth shiftWidth (plusWire shiftWidth) i = i₁ := by
    simp [rotateRightOut, hplus, i₁, workValue, work]
  have hi₁plus : bitValue i₁ (plusWire shiftWidth) = 1 := by
    dsimp [i₁]
    rw [bitValue_write_out (Or.inl (by
      simp [plusWire, workOffset]
      omega)), hplus]
  have hi₁position : position shiftWidth i₁ = position shiftWidth i := by
    dsimp [i₁]
    rw [position, readField_writeField_of_disjoint (Or.inr (by
      simp [positionOffset, workOffset]
      omega))]
    rfl
  have hi₂ : incrementOut shiftWidth (plusWire shiftWidth) i₁ = i₂ := by
    simp [incrementOut, hi₁plus, hi₁position, i₂, positionValue]
  have hi₂minus : bitValue i₂ (minusWire workWidth shiftWidth) = 0 := by
    dsimp [i₂]
    rw [bitValue_write_out (Or.inr (by
      simp [minusWire, positionOffset, workOffset]
      omega))]
    dsimp [i₁]
    rw [bitValue_write_out (Or.inr (by
      simp [minusWire])), hminus]
  have hleft :
      rotateLeftOut workWidth shiftWidth
        (minusWire workWidth shiftWidth) i₂ = i₂ := by
    simp [rotateLeftOut, hi₂minus]
  have hdecrement :
      decrementOut shiftWidth (minusWire workWidth shiftWidth) i₂ = i₂ := by
    simp only [decrementOut, hi₂minus, Nat.sub_zero, position,
      Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (readField_lt _ _ _), writeField_read]
  have hout : out workWidth shiftWidth i = i₂ := by
    simp only [out, hi₁, hi₂, hleft, hdecrement]
  rw [hout]
  constructor
  · dsimp [i₂]
    rw [position, readField_writeField_self
      (Nat.mod_lt _ (Nat.two_pow_pos shiftWidth))]
  · dsimp [i₂]
    rw [work, readField_writeField_of_disjoint (Or.inl (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₁]
    rw [readField_writeField_self
        (rotateRightValue_lt workWidth (work workWidth shiftWidth i))]

theorem out_decrement
    {workWidth shiftWidth i : Nat}
    (hplus : bitValue i (plusWire shiftWidth) = 1)
    (hminus : bitValue i (minusWire workWidth shiftWidth) = 1) :
    position shiftWidth (out workWidth shiftWidth i) =
        (position shiftWidth i + 2 ^ shiftWidth - 1) % 2 ^ shiftWidth ∧
      work workWidth shiftWidth (out workWidth shiftWidth i) =
        rotateLeftValue workWidth (work workWidth shiftWidth i) := by
  let rightValue := rotateRightValue workWidth (work workWidth shiftWidth i)
  let incremented := (position shiftWidth i + 1) % 2 ^ shiftWidth
  let i₁ := writeField i (workOffset shiftWidth) workWidth rightValue
  let i₂ := writeField i₁ positionOffset shiftWidth incremented
  let restoredWork := rotateLeftValue workWidth rightValue
  let i₃ := writeField i₂ (workOffset shiftWidth) workWidth restoredWork
  let restoredPosition :=
    (incremented + 2 ^ shiftWidth - 1) % 2 ^ shiftWidth
  let i₄ := writeField i₃ positionOffset shiftWidth restoredPosition
  let leftValue := rotateLeftValue workWidth restoredWork
  let i₅ := writeField i₄ (workOffset shiftWidth) workWidth leftValue
  let decremented :=
    (restoredPosition + 2 ^ shiftWidth - 1) % 2 ^ shiftWidth
  let i₆ := writeField i₅ positionOffset shiftWidth decremented
  have hi₁ : rotateRightOut workWidth shiftWidth (plusWire shiftWidth) i = i₁ := by
    simp [rotateRightOut, hplus, i₁, rightValue, work]
  have hi₁plus : bitValue i₁ (plusWire shiftWidth) = 1 := by
    dsimp [i₁]
    rw [bitValue_write_out (Or.inl (by
      simp [plusWire, workOffset]
      omega)), hplus]
  have hi₁position : position shiftWidth i₁ = position shiftWidth i := by
    dsimp [i₁]
    rw [position, readField_writeField_of_disjoint (Or.inr (by
      simp [positionOffset, workOffset]
      omega))]
    rfl
  have hi₂ : incrementOut shiftWidth (plusWire shiftWidth) i₁ = i₂ := by
    simp [incrementOut, hi₁plus, hi₁position, i₂, incremented]
  have hi₂minus : bitValue i₂ (minusWire workWidth shiftWidth) = 1 := by
    dsimp [i₂]
    rw [bitValue_write_out (Or.inr (by
      simp [minusWire, positionOffset, workOffset]
      omega))]
    dsimp [i₁]
    rw [bitValue_write_out (Or.inr (by simp [minusWire])), hminus]
  have hi₂work : work workWidth shiftWidth i₂ = rightValue := by
    dsimp [i₂]
    rw [work, readField_writeField_of_disjoint (Or.inl (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₁]
    exact readField_writeField_self
      (rotateRightValue_lt workWidth (work workWidth shiftWidth i))
  have hi₃ : rotateLeftOut workWidth shiftWidth
      (minusWire workWidth shiftWidth) i₂ = i₃ := by
    simp [rotateLeftOut, hi₂minus, i₃, restoredWork, hi₂work]
  have hi₃minus : bitValue i₃ (minusWire workWidth shiftWidth) = 1 := by
    dsimp [i₃]
    rw [bitValue_write_out (Or.inr (by simp [minusWire])), hi₂minus]
  have hi₃position : position shiftWidth i₃ = incremented := by
    dsimp [i₃]
    rw [position, readField_writeField_of_disjoint (Or.inr (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₂]
    exact readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos shiftWidth))
  have hi₄ : decrementOut shiftWidth
      (minusWire workWidth shiftWidth) i₃ = i₄ := by
    simp [decrementOut, hi₃minus, hi₃position, i₄,
      restoredPosition]
  have hi₄minus : bitValue i₄ (minusWire workWidth shiftWidth) = 1 := by
    dsimp [i₄]
    rw [bitValue_write_out (Or.inr (by
      simp [minusWire, positionOffset, workOffset]
      omega)), hi₃minus]
  have hi₄work : work workWidth shiftWidth i₄ = restoredWork := by
    dsimp [i₄]
    rw [work, readField_writeField_of_disjoint (Or.inl (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₃]
    exact readField_writeField_self
      (rotateLeftValue_lt workWidth rightValue)
  have hi₅ : rotateLeftOut workWidth shiftWidth
      (minusWire workWidth shiftWidth) i₄ = i₅ := by
    simp [rotateLeftOut, hi₄minus, i₅, leftValue, hi₄work]
  have hi₅minus : bitValue i₅ (minusWire workWidth shiftWidth) = 1 := by
    dsimp [i₅]
    rw [bitValue_write_out (Or.inr (by simp [minusWire])), hi₄minus]
  have hi₅position : position shiftWidth i₅ = restoredPosition := by
    dsimp [i₅]
    rw [position, readField_writeField_of_disjoint (Or.inr (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₄]
    exact readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos shiftWidth))
  have hi₆ : decrementOut shiftWidth
      (minusWire workWidth shiftWidth) i₅ = i₆ := by
    simp [decrementOut, hi₅minus, hi₅position, i₆, decremented]
  have hrestoredPosition : restoredPosition = position shiftWidth i := by
    have hposition : position shiftWidth i < 2 ^ shiftWidth :=
      readField_lt i positionOffset shiftWidth
    have hpower := Nat.two_pow_pos shiftWidth
    by_cases hlt : position shiftWidth i + 1 < 2 ^ shiftWidth
    · have hincremented : incremented = position shiftWidth i + 1 := by
        exact Nat.mod_eq_of_lt hlt
      dsimp [restoredPosition]
      rw [hincremented]
      have heq : position shiftWidth i + 1 + 2 ^ shiftWidth - 1 =
          position shiftWidth i + 2 ^ shiftWidth := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hposition]
    · have heq : position shiftWidth i + 1 = 2 ^ shiftWidth := by omega
      have hincremented : incremented = 0 := by
        dsimp [incremented]
        rw [heq, Nat.mod_self]
      dsimp [restoredPosition]
      rw [hincremented]
      have hpositionEq : position shiftWidth i = 2 ^ shiftWidth - 1 := by
        omega
      rw [hpositionEq]
      simp only [Nat.zero_add]
      apply Nat.mod_eq_of_lt
      omega
  have hrestoredWork : restoredWork = work workWidth shiftWidth i := by
    exact rotateLeft_right_value
      (readField_lt i (workOffset shiftWidth) workWidth)
  have hout : out workWidth shiftWidth i = i₆ := by
    simp only [out, hi₁, hi₂, hi₃, hi₄, hi₅, hi₆]
  rw [hout]
  constructor
  · dsimp [i₆]
    rw [position, readField_writeField_self
      (Nat.mod_lt _ (Nat.two_pow_pos shiftWidth))]
    rw [hrestoredPosition]
  · dsimp [i₆]
    rw [work, readField_writeField_of_disjoint (Or.inl (by
      simp [positionOffset, workOffset]
      omega))]
    dsimp [i₅]
    rw [readField_writeField_self (rotateLeftValue_lt workWidth restoredWork),
      hrestoredWork]

theorem minusWiring_disjoint (workWidth shiftWidth : Nat) :
    Wiring.Disjoint (Increment.layout shiftWidth)
      (minusWiring workWidth shiftWidth) := by
  intro j k hj hk hne
  simp [minusWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [minusWiring, Increment.layout, Layout.size, minusWire,
      workOffset, scratchOffset, positionOffset] <;> omega

theorem minusWiring_bound (workWidth shiftWidth : Nat) :
    ∀ j, j < (Increment.layout shiftWidth).length →
      (minusWiring workWidth shiftWidth).getD j 0 +
          (Increment.layout shiftWidth).size j ≤
        (layout workWidth shiftWidth).width := by
  intro j hj
  simp [Increment.layout] at hj
  interval_cases j <;>
    simp_all [minusWiring, Increment.layout, layout, Layout.size, Layout.width,
      minusWire, workOffset, scratchOffset, positionOffset] <;> omega

theorem scratch_rotateRightOut (workWidth shiftWidth control i : Nat) :
    scratch shiftWidth (rotateRightOut workWidth shiftWidth control i) =
      scratch shiftWidth i := by
  unfold rotateRightOut
  split
  · unfold scratch
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [workOffset, scratchOffset]
      omega))]
  · rfl

theorem scratch_rotateLeftOut (workWidth shiftWidth control i : Nat) :
    scratch shiftWidth (rotateLeftOut workWidth shiftWidth control i) =
      scratch shiftWidth i := by
  unfold rotateLeftOut
  split
  · unfold scratch
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [workOffset, scratchOffset]
      omega))]
  · rfl

theorem scratch_incrementOut (shiftWidth control i : Nat) :
    scratch shiftWidth (incrementOut shiftWidth control i) = scratch shiftWidth i := by
  unfold scratch incrementOut positionOffset
  rw [readField_writeField_of_disjoint (Or.inl (by
    simp [scratchOffset]))]

theorem scratch_decrementOut (shiftWidth control i : Nat) :
    scratch shiftWidth (decrementOut shiftWidth control i) = scratch shiftWidth i := by
  unfold scratch decrementOut positionOffset
  rw [readField_writeField_of_disjoint (Or.inl (by
    simp [scratchOffset]))]

theorem rotateRight_act {workWidth shiftWidth control i : Nat}
    (hc : control < workOffset shiftWidth ∨
      workOffset shiftWidth + workWidth ≤ control) :
    actGates (rotateRightControlled control (workOffset shiftWidth) workWidth) i =
      rotateRightOut workWidth shiftWidth control i := by
  rcases (show bitValue i control = 0 ∨ bitValue i control = 1 by
    have := bitValue_lt i control
    omega) with hcontrol | hcontrol
  · rw [rotateRightControlled_off workWidth (workOffset shiftWidth) i hc hcontrol]
    simp [rotateRightOut, hcontrol]
  · rw [rotateRightControlled_on workWidth (workOffset shiftWidth) i hc hcontrol]
    simp [rotateRightOut, hcontrol, work]

theorem rotateLeft_act {workWidth shiftWidth control i : Nat}
    (hc : control < workOffset shiftWidth ∨
      workOffset shiftWidth + workWidth ≤ control) :
    actGates (rotateLeftControlled control (workOffset shiftWidth) workWidth) i =
      rotateLeftOut workWidth shiftWidth control i := by
  rcases (show bitValue i control = 0 ∨ bitValue i control = 1 by
    have := bitValue_lt i control
    omega) with hcontrol | hcontrol
  · rw [rotateLeftControlled_off workWidth (workOffset shiftWidth) i hc hcontrol]
    simp [rotateLeftOut, hcontrol]
  · rw [rotateLeftControlled_on workWidth (workOffset shiftWidth) i hc hcontrol]
    simp [rotateLeftOut, hcontrol, work]

theorem increment_act {shiftWidth i : Nat} (hscratch : scratch shiftWidth i = 0) :
    actGates (Increment.circuit shiftWidth).gates i =
      incrementOut shiftWidth (plusWire shiftWidth) i := by
  have hs : Increment.scratch shiftWidth i = 0 := by
    simpa [Increment.scratch, Increment.layout, Layout.read, Layout.offset,
      Layout.size, scratch, scratchOffset] using hscratch
  simpa [act, incrementOut, position, positionOffset, plusWire,
    Increment.data, Increment.controlWire, Increment.layout, Layout.read,
    Layout.offset, Layout.size] using Increment.act_circuit hs

theorem decrement_minus_act {workWidth shiftWidth i : Nat}
    (hscratch : scratch shiftWidth i = 0) :
    actGates (placedDecrement workWidth shiftWidth) i =
      decrementOut shiftWidth (minusWire workWidth shiftWidth) i := by
  let L := Increment.layout shiftWidth
  let W := minusWiring workWidth shiftWidth
  let gathered := gatherBits (place L W) L.width i
  have hscratchGathered : Increment.scratch shiftWidth gathered = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    simp only [gathered]
    rw [readField_gatherBits L W 2 i (by simp [W, minusWiring])]
    simpa [L, W, Increment.layout, Layout.size, minusWiring, scratch,
      scratchOffset] using hscratch
  have hlocal := Increment.act_reverse_circuit hscratchGathered
  have hdata : Increment.data shiftWidth gathered = position shiftWidth i := by
    change readField gathered (L.offset 0) (L.size 0) = position shiftWidth i
    simp only [gathered]
    rw [readField_gatherBits L W 0 i (by simp [W, minusWiring])]
    simp [L, W, Increment.layout, Layout.size, minusWiring, position,
      positionOffset]
  have hcontrol : bitValue gathered (Increment.controlWire shiftWidth) =
      bitValue i (minusWire workWidth shiftWidth) := by
    rw [← readField_one]
    change readField gathered (L.offset 1) (L.size 1) = _
    simp only [gathered]
    rw [readField_gatherBits L W 1 i (by simp [W, minusWiring])]
    simp [L, W, Increment.layout, Layout.size, minusWiring, readField_one]
  have hwrite : actGates (Increment.circuit shiftWidth).reverse.gates gathered =
      L.write gathered 0
        ((position shiftWidth i + 2 ^ shiftWidth -
          bitValue i (minusWire workWidth shiftWidth)) % 2 ^ shiftWidth) := by
    change act (Increment.circuit shiftWidth).reverse gathered = _
    rw [hlocal]
    simp only [Increment.decrementValue, hdata, hcontrol]
    rfl
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (minusWiring_disjoint workWidth shiftWidth)
      (by simp [L, W, Increment.layout, minusWiring])
      (by simp [L, Increment.layout])
      (fun g hg => RCircuit.wellFormed_mem
        (RCircuit.wellFormed_reverse (Increment.circuit_wellFormed shiftWidth)) hg)
      hwrite

theorem increment_wellFormed (workWidth shiftWidth : Nat) :
    (Increment.circuit shiftWidth).gates.all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
      (w := (Increment.circuit shiftWidth).width)
  · rw [Increment.width_exact]
    simp [layout, Layout.width]
    omega
  · exact RCircuit.wellFormed_mem (Increment.circuit_wellFormed shiftWidth) hg

theorem placedDecrement_wellFormed (workWidth shiftWidth : Nat) :
    (placedDecrement workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  exact wellFormed_placeGates
    (minusWiring_disjoint workWidth shiftWidth)
    (by simp [Increment.layout, minusWiring])
    (minusWiring_bound workWidth shiftWidth)
    (fun g hg => RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse (Increment.circuit_wellFormed shiftWidth)) hg)

theorem circuit_wellFormed (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).wellFormed = true := by
  have hr := rotateRightControlled_wellFormed
    (control := plusWire shiftWidth)
    (total := (layout workWidth shiftWidth).width)
    workWidth (workOffset shiftWidth)
    (Or.inl (by simp [plusWire, workOffset]; omega))
    (by simp [plusWire, layout, Layout.width])
    (by simp [workOffset, layout, Layout.width]; omega)
  have hl := rotateLeftControlled_wellFormed
    (control := minusWire workWidth shiftWidth)
    (total := (layout workWidth shiftWidth).width)
    workWidth (workOffset shiftWidth)
    (Or.inr (by simp [minusWire]))
    (by simp [minusWire, layout, Layout.width, workOffset]; omega)
    (by simp [workOffset, layout, Layout.width]; omega)
  simp only [circuit, RCircuit.wellFormed, gates, List.all_append,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hr, increment_wellFormed workWidth shiftWidth⟩, hl⟩,
    placedDecrement_wellFormed workWidth shiftWidth⟩, hl⟩,
    placedDecrement_wellFormed workWidth shiftWidth⟩

theorem placedDecrement_length (workWidth shiftWidth : Nat) :
    (placedDecrement workWidth shiftWidth).length =
      Increment.lengthCost shiftWidth := by
  simp [placedDecrement, Increment.circuit_length]

theorem placedDecrement_ccx (workWidth shiftWidth : Nat) :
    (placedDecrement workWidth shiftWidth).countP RGate.isCcx =
      Increment.ccxCost shiftWidth := by
  rw [placedDecrement,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  change (Increment.circuit shiftWidth).gates.reverse.countP RGate.isCcx = _
  rw [List.countP_reverse, Increment.circuit_ccx]

theorem placedDecrement_cx (workWidth shiftWidth : Nat) :
    (placedDecrement workWidth shiftWidth).countP RGate.isCx =
      Increment.cxCost shiftWidth := by
  rw [placedDecrement,
    countP_map_gates (fun g => RGate.isCx_map _ g)]
  change (Increment.circuit shiftWidth).gates.reverse.countP RGate.isCx = _
  rw [List.countP_reverse, Increment.circuit_cx]

theorem circuit_length (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).gates.length =
      9 * (workWidth - 1) + 3 * Increment.lengthCost shiftWidth := by
  simp only [circuit, gates, List.length_append,
    rotateRightControlled_length, rotateLeftControlled_length,
    Increment.circuit_length, placedDecrement_length]
  omega

theorem circuit_ccx (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).gates.countP RGate.isCcx =
      3 * (workWidth - 1) + 3 * Increment.ccxCost shiftWidth := by
  simp only [circuit, gates, List.countP_append,
    rotateRightControlled_ccx, rotateLeftControlled_ccx,
    Increment.circuit_ccx, placedDecrement_ccx]
  omega

theorem circuit_cx (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).gates.countP RGate.isCx =
      6 * (workWidth - 1) + 3 * Increment.cxCost shiftWidth := by
  simp only [circuit, gates, List.countP_append,
    rotateRightControlled_cx, rotateLeftControlled_cx,
    Increment.circuit_cx, placedDecrement_cx]
  omega

theorem act_circuit {workWidth shiftWidth i : Nat}
    (hscratch : scratch shiftWidth i = 0) :
    act (circuit workWidth shiftWidth) i = out workWidth shiftWidth i := by
  let i1 := rotateRightOut workWidth shiftWidth (plusWire shiftWidth) i
  let i2 := incrementOut shiftWidth (plusWire shiftWidth) i1
  let i3 := rotateLeftOut workWidth shiftWidth
    (minusWire workWidth shiftWidth) i2
  let i4 := decrementOut shiftWidth (minusWire workWidth shiftWidth) i3
  let i5 := rotateLeftOut workWidth shiftWidth
    (minusWire workWidth shiftWidth) i4
  have hs1 : scratch shiftWidth i1 = 0 := by
    simp only [i1, scratch_rotateRightOut, hscratch]
  have hs2 : scratch shiftWidth i2 = 0 := by
    simp only [i2, scratch_incrementOut, hs1]
  have hs3 : scratch shiftWidth i3 = 0 := by
    simp only [i3, scratch_rotateLeftOut, hs2]
  have hs4 : scratch shiftWidth i4 = 0 := by
    simp only [i4, scratch_decrementOut, hs3]
  have hs5 : scratch shiftWidth i5 = 0 := by
    simp only [i5, scratch_rotateLeftOut, hs4]
  simp only [circuit, gates, act, actGates_append]
  rw [rotateRight_act (workWidth := workWidth) (shiftWidth := shiftWidth)
    (control := plusWire shiftWidth) (i := i)
    (Or.inl (by simp [plusWire, workOffset]; omega))]
  change actGates _ (actGates _ (actGates _ (actGates _ (actGates _ i1)))) = _
  rw [increment_act hs1]
  change actGates _ (actGates _ (actGates _ (actGates _ i2))) = _
  rw [rotateLeft_act (workWidth := workWidth) (shiftWidth := shiftWidth)
    (control := minusWire workWidth shiftWidth) (i := i2)
    (Or.inr (by simp [minusWire]))]
  change actGates _ (actGates _ (actGates _ i3)) = _
  rw [decrement_minus_act hs3]
  change actGates _ (actGates _ i4) = _
  rw [rotateLeft_act (workWidth := workWidth) (shiftWidth := shiftWidth)
    (control := minusWire workWidth shiftWidth) (i := i4)
    (Or.inr (by simp [minusWire]))]
  change actGates _ i5 = _
  rw [decrement_minus_act hs5]
  rfl

theorem rotateRightOut_testBit_outside
    {workWidth shiftWidth control i b : Nat}
    (h : b < workOffset shiftWidth ∨
      workOffset shiftWidth + workWidth ≤ b) :
    (rotateRightOut workWidth shiftWidth control i).testBit b = i.testBit b := by
  unfold rotateRightOut
  split
  · exact testBit_writeField_outside h
  · rfl

theorem rotateLeftOut_testBit_outside
    {workWidth shiftWidth control i b : Nat}
    (h : b < workOffset shiftWidth ∨
      workOffset shiftWidth + workWidth ≤ b) :
    (rotateLeftOut workWidth shiftWidth control i).testBit b = i.testBit b := by
  unfold rotateLeftOut
  split
  · exact testBit_writeField_outside h
  · rfl

theorem incrementOut_testBit_outside
    {shiftWidth control i b : Nat} (h : shiftWidth ≤ b) :
    (incrementOut shiftWidth control i).testBit b = i.testBit b := by
  exact testBit_writeField_outside (Or.inr (by simpa [positionOffset]))

theorem decrementOut_testBit_outside
    {shiftWidth control i b : Nat} (h : shiftWidth ≤ b) :
    (decrementOut shiftWidth control i).testBit b = i.testBit b := by
  exact testBit_writeField_outside (Or.inr (by simpa [positionOffset]))

theorem out_testBit_outside
    {workWidth shiftWidth i b : Nat}
    (hposition : shiftWidth ≤ b)
    (hwork : b < workOffset shiftWidth ∨
      workOffset shiftWidth + workWidth ≤ b) :
    (out workWidth shiftWidth i).testBit b = i.testBit b := by
  simp only [out]
  rw [decrementOut_testBit_outside hposition,
    rotateLeftOut_testBit_outside hwork,
    decrementOut_testBit_outside hposition,
    rotateLeftOut_testBit_outside hwork,
    incrementOut_testBit_outside hposition,
    rotateRightOut_testBit_outside hwork]

theorem out_eq_writeFields (workWidth shiftWidth i : Nat) :
    out workWidth shiftWidth i =
      writeField
        (writeField i positionOffset shiftWidth
          (position shiftWidth (out workWidth shiftWidth i)))
        (workOffset shiftWidth) workWidth
        (work workWidth shiftWidth (out workWidth shiftWidth i)) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hposition : b < shiftWidth
  · rw [testBit_writeField_outside (Or.inl (by
      simp [workOffset]
      omega)),
      testBit_writeField_inside (by simp [positionOffset]) (by
        simp [positionOffset]
        omega)]
    have hread := testBit_readField
      (out workWidth shiftWidth i) positionOffset shiftWidth b
    simp [positionOffset, hposition] at hread
    exact hread.symm
  · by_cases hwork :
        workOffset shiftWidth ≤ b ∧
          b < workOffset shiftWidth + workWidth
    · rw [testBit_writeField_inside hwork.1 hwork.2]
      have hread := testBit_readField (out workWidth shiftWidth i)
        (workOffset shiftWidth) workWidth (b - workOffset shiftWidth)
      have hindex : workOffset shiftWidth + (b - workOffset shiftWidth) = b := by
        omega
      simp [show b - workOffset shiftWidth < workWidth by omega,
        hindex] at hread
      exact hread.symm
    · have hpositionOutside : shiftWidth ≤ b := by omega
      have hworkOutside : b < workOffset shiftWidth ∨
          workOffset shiftWidth + workWidth ≤ b := by omega
      rw [testBit_writeField_outside hworkOutside,
        testBit_writeField_outside (Or.inr (by
          simpa [positionOffset] using hpositionOutside)),
        out_testBit_outside hpositionOutside hworkOutside]

end Shift
end Euclid
end VQ
