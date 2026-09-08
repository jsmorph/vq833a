/-
Borrowed-epoch terminal counter used by the Luo version 2 companion circuit.
-/
import VQ.Euclid.Increment
import VQ.Euclid.Placed
import Mathlib.Tactic.IntervalCases

namespace VQ.Euclid.TerminalEpoch

open Reversible

def layout (shiftWidth : Nat) : Layout := [shiftWidth, 1, shiftWidth, 1, 1]

def lowOffset : Nat := 0
def controlWire (shiftWidth : Nat) : Nat := shiftWidth
def scratchOffset (shiftWidth : Nat) : Nat := shiftWidth + 1
def wrappedWire (shiftWidth : Nat) : Nat := 2 * shiftWidth + 1
def epochWire (shiftWidth : Nat) : Nat := 2 * shiftWidth + 2

def incrementGates (shiftWidth : Nat) : List RGate :=
  (Increment.circuit shiftWidth).gates

def zeroGates (shiftWidth : Nat) : List RGate :=
  Placed.selectorGates 0 shiftWidth lowOffset
    (wrappedWire shiftWidth) (scratchOffset shiftWidth)

def gates (shiftWidth : Nat) : List RGate :=
  incrementGates shiftWidth ++
    zeroGates shiftWidth ++
    [.ccx (controlWire shiftWidth) (wrappedWire shiftWidth)
      (epochWire shiftWidth)] ++
    zeroGates shiftWidth

def circuit (shiftWidth : Nat) : RCircuit :=
  { width := (layout shiftWidth).width, gates := gates shiftWidth }

def nextLow (shiftWidth i : Nat) : Nat :=
  (readField i lowOffset shiftWidth + bitValue i (controlWire shiftWidth)) %
    2 ^ shiftWidth

def wrapped (shiftWidth i : Nat) : Nat :=
  if nextLow shiftWidth i = 0 then 1 else 0

def nextEpoch (shiftWidth i : Nat) : Nat :=
  (bitValue i (epochWire shiftWidth) +
    bitValue i (controlWire shiftWidth) * wrapped shiftWidth i) % 2

def out (shiftWidth i : Nat) : Nat :=
  writeField
    (writeField
      (writeField i lowOffset shiftWidth (nextLow shiftWidth i))
      (wrappedWire shiftWidth) 1 0)
    (epochWire shiftWidth) 1 (nextEpoch shiftWidth i)

theorem selectorWiring_disjoint {shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    Wiring.Disjoint (Selector.layout shiftWidth)
      (Placed.selectorWiring lowOffset (wrappedWire shiftWidth)
        (scratchOffset shiftWidth)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Selector.layout, Layout.size, Placed.selectorWiring, lowOffset,
      wrappedWire, scratchOffset] <;> omega

theorem increment_act
    {shiftWidth i : Nat}
    (hscratch : readField i (scratchOffset shiftWidth) shiftWidth = 0) :
    actGates (incrementGates shiftWidth) i =
      writeField i lowOffset shiftWidth (nextLow shiftWidth i) := by
  have hlocal : Increment.scratch shiftWidth i = 0 := by
    simpa [Increment.scratch, Increment.layout, Layout.read, Layout.offset,
      Layout.size, scratchOffset] using hscratch
  simpa [incrementGates, Increment.circuit, act, Increment.data,
    Increment.layout, Layout.read, Layout.offset, Layout.size, nextLow,
    lowOffset, controlWire, Increment.controlWire] using
    Increment.act_circuit hlocal

theorem zero_act
    {shiftWidth i : Nat}
    (hshift : 0 < shiftWidth)
    (hscratch : readField i (scratchOffset shiftWidth) shiftWidth = 0) :
    actGates (zeroGates shiftWidth) i =
      writeField i (wrappedWire shiftWidth) 1
        ((bitValue i (wrappedWire shiftWidth) +
          if readField i lowOffset shiftWidth = 0 then 1 else 0) % 2) := by
  have hlocal := Placed.selector_act
    (value := 0) (width := shiftWidth) (source := lowOffset)
    (flag := wrappedWire shiftWidth) (scratch := scratchOffset shiftWidth)
    (i := i) (selectorWiring_disjoint hshift) hscratch
  rw [Nat.zero_mod] at hlocal
  simpa only [zeroGates] using hlocal

theorem incrementGates_wellFormed (shiftWidth : Nat) :
    (incrementGates shiftWidth).all
      (RGate.wellFormed (layout shiftWidth).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono (w := (Increment.layout shiftWidth).width)
  · simp [Increment.layout, layout, Layout.width]
  · exact RCircuit.wellFormed_mem (Increment.circuit_wellFormed shiftWidth)
      (by simpa [incrementGates] using hg)

theorem selectorWiring_bound (shiftWidth : Nat) :
    ∀ j, j < (Selector.layout shiftWidth).length →
      (Placed.selectorWiring lowOffset (wrappedWire shiftWidth)
          (scratchOffset shiftWidth)).getD j 0 +
        (Selector.layout shiftWidth).size j ≤ (layout shiftWidth).width := by
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp [Placed.selectorWiring, Selector.layout, Layout.size, layout,
      Layout.width, lowOffset, wrappedWire, scratchOffset] <;> omega

theorem zeroGates_wellFormed
    {shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (zeroGates shiftWidth).all
      (RGate.wellFormed (layout shiftWidth).width) = true := by
  exact Placed.selector_wellFormed
    (selectorWiring_disjoint hshift) (selectorWiring_bound shiftWidth)

theorem gates_wellFormed
    {shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (gates shiftWidth).all
      (RGate.wellFormed (layout shiftWidth).width) = true := by
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨incrementGates_wellFormed shiftWidth,
    zeroGates_wellFormed hshift⟩, ?_⟩, zeroGates_wellFormed hshift⟩
  simp [RGate.wellFormed, layout, Layout.width, controlWire, wrappedWire,
    epochWire]
  omega

theorem circuit_wellFormed
    {shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (circuit shiftWidth).wellFormed = true := by
  exact gates_wellFormed hshift

theorem gates_act
    {shiftWidth i : Nat}
    (hshift : 0 < shiftWidth)
    (hscratch : readField i (scratchOffset shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i (wrappedWire shiftWidth) = 0) :
    actGates (gates shiftWidth) i = out shiftWidth i := by
  let J := writeField i lowOffset shiftWidth (nextLow shiftWidth i)
  let K := writeField J (wrappedWire shiftWidth) 1 (wrapped shiftWidth i)
  let L := writeField K (epochWire shiftWidth) 1 (nextEpoch shiftWidth i)
  have hnextLow : nextLow shiftWidth i < 2 ^ shiftWidth := by
    exact Nat.mod_lt _ (Nat.two_pow_pos shiftWidth)
  have hwrappedFit : wrapped shiftWidth i < 2 := by
    unfold wrapped
    split <;> omega
  have hJ := increment_act hscratch
  have hJscratch : readField J (scratchOffset shiftWidth) shiftWidth = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lowOffset, scratchOffset]))]
    exact hscratch
  have hJlow : readField J lowOffset shiftWidth = nextLow shiftWidth i := by
    simp [J, readField_writeField_self, hnextLow]
  have hJwrapped : bitValue J (wrappedWire shiftWidth) = 0 := by
    simp only [J]
    rw [bitValue_write_out (Or.inr (by
      simp [lowOffset, wrappedWire]; omega))]
    exact hwrapped
  have hzeroFirst := zero_act hshift hJscratch
  have hzeroFirst' : actGates (zeroGates shiftWidth) J = K := by
    rw [hzeroFirst, hJlow, hJwrapped]
    simp only [Nat.zero_add, K, wrapped]
    split <;> simp
  have hKcontrol : bitValue K (controlWire shiftWidth) =
      bitValue i (controlWire shiftWidth) := by
    simp only [K, J]
    rw [bitValue_write_out (Or.inl (by
      simp [controlWire, wrappedWire]; omega)),
      bitValue_write_out (Or.inr (by
        simp [lowOffset, controlWire]))]
  have hKwrapped : bitValue K (wrappedWire shiftWidth) = wrapped shiftWidth i := by
    simp [K, bitValue_write_self, Nat.mod_eq_of_lt hwrappedFit]
  have hKepoch : bitValue K (epochWire shiftWidth) =
      bitValue i (epochWire shiftWidth) := by
    simp only [K, J]
    rw [bitValue_write_out (Or.inr (by
      simp [wrappedWire, epochWire])),
      bitValue_write_out (Or.inr (by
        simp [lowOffset, epochWire]; omega))]
  have hccx : actGates
      [.ccx (controlWire shiftWidth) (wrappedWire shiftWidth)
        (epochWire shiftWidth)] K = L := by
    rw [actGates_cons, actGates_nil, act_ccx_write,
      hKcontrol, hKwrapped, hKepoch]
    rfl
  have hLscratch : readField L (scratchOffset shiftWidth) shiftWidth = 0 := by
    simp only [L, K, J]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [scratchOffset, epochWire]; omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [scratchOffset, wrappedWire]; omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lowOffset, scratchOffset]))]
    exact hscratch
  have hLlow : readField L lowOffset shiftWidth = nextLow shiftWidth i := by
    simp only [L, K, J]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lowOffset, epochWire]; omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [lowOffset, wrappedWire]; omega)),
      readField_writeField_self]
    exact hnextLow
  have hLwrapped : bitValue L (wrappedWire shiftWidth) = wrapped shiftWidth i := by
    simp only [L]
    rw [bitValue_write_out (Or.inl (by
      simp [wrappedWire, epochWire]))]
    exact hKwrapped
  have hzeroSecond := zero_act hshift hLscratch
  have hzeroSecond' : actGates (zeroGates shiftWidth) L =
      writeField L (wrappedWire shiftWidth) 1 0 := by
    rw [hzeroSecond, hLlow, hLwrapped]
    simp only [wrapped]
    split <;> simp
  simp only [gates, actGates_append]
  rw [hJ, hzeroFirst', hccx, hzeroSecond']
  simp only [L, K, J, out]
  rw [writeField_comm (Or.inr (by
    simp [wrappedWire, epochWire])), writeField_writeField]

end VQ.Euclid.TerminalEpoch
