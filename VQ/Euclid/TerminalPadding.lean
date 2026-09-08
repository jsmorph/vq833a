/-
Borrowed-epoch terminal padding with the controlled work-register rotation.
-/
import VQ.Euclid.TerminalEpoch
import VQ.Reversible.Permutation

namespace VQ.Euclid.TerminalPadding

open Reversible

def layout (workWidth shiftWidth : Nat) : Layout :=
  [workWidth, shiftWidth, 1, shiftWidth, 1, 1]

def workOffset : Nat := 0
def lowOffset (workWidth : Nat) : Nat := workWidth
def controlWire (workWidth shiftWidth : Nat) : Nat := workWidth + shiftWidth
def scratchOffset (workWidth shiftWidth : Nat) : Nat :=
  workWidth + shiftWidth + 1
def wrappedWire (workWidth shiftWidth : Nat) : Nat :=
  workWidth + 2 * shiftWidth + 1
def epochWire (workWidth shiftWidth : Nat) : Nat :=
  workWidth + 2 * shiftWidth + 2

def epochWiring (workWidth shiftWidth : Nat) : Wiring :=
  [lowOffset workWidth, controlWire workWidth shiftWidth,
    scratchOffset workWidth shiftWidth, wrappedWire workWidth shiftWidth,
    epochWire workWidth shiftWidth]

def rotationGates (workWidth shiftWidth : Nat) : List RGate :=
  rotateRightControlled (controlWire workWidth shiftWidth) workOffset workWidth

def epochGates (workWidth shiftWidth : Nat) : List RGate :=
  (TerminalEpoch.gates shiftWidth).map
    (RGate.map (place (TerminalEpoch.layout shiftWidth)
      (epochWiring workWidth shiftWidth)))

def gates (workWidth shiftWidth : Nat) : List RGate :=
  rotationGates workWidth shiftWidth ++ epochGates workWidth shiftWidth

def circuit (workWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout workWidth shiftWidth).width,
    gates := gates workWidth shiftWidth }

def nextLow (workWidth shiftWidth i : Nat) : Nat :=
  (readField i (lowOffset workWidth) shiftWidth +
    bitValue i (controlWire workWidth shiftWidth)) % 2 ^ shiftWidth

def wrapped (workWidth shiftWidth i : Nat) : Nat :=
  if nextLow workWidth shiftWidth i = 0 then 1 else 0

def nextEpoch (workWidth shiftWidth i : Nat) : Nat :=
  (bitValue i (epochWire workWidth shiftWidth) +
    bitValue i (controlWire workWidth shiftWidth) *
      wrapped workWidth shiftWidth i) % 2

def out (workWidth shiftWidth i : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField i workOffset workWidth
          (rotateRightValue workWidth (readField i workOffset workWidth)))
        (lowOffset workWidth) shiftWidth (nextLow workWidth shiftWidth i))
      (wrappedWire workWidth shiftWidth) 1 0)
    (epochWire workWidth shiftWidth) 1 (nextEpoch workWidth shiftWidth i)

theorem epochWiring_disjoint {workWidth shiftWidth : Nat}
    (hshift : 0 < shiftWidth) :
    Wiring.Disjoint (TerminalEpoch.layout shiftWidth)
      (epochWiring workWidth shiftWidth) := by
  intro j k hj hk hne
  simp [epochWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [TerminalEpoch.layout, Layout.size, epochWiring, lowOffset,
      controlWire, scratchOffset, wrappedWire, epochWire] <;> omega

theorem epochWiring_bound (workWidth shiftWidth : Nat) :
    ∀ j, j < (TerminalEpoch.layout shiftWidth).length →
      (epochWiring workWidth shiftWidth).getD j 0 +
        (TerminalEpoch.layout shiftWidth).size j ≤
          (layout workWidth shiftWidth).width := by
  intro j hj
  simp [TerminalEpoch.layout] at hj
  interval_cases j <;>
    simp [epochWiring, TerminalEpoch.layout, Layout.size, layout, Layout.width,
      lowOffset, controlWire, scratchOffset, wrappedWire, epochWire] <;> omega

theorem epochGates_wellFormed
    {workWidth shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (epochGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  exact wellFormed_placeGates (epochWiring_disjoint hshift)
    (by simp [TerminalEpoch.layout, epochWiring])
    (epochWiring_bound workWidth shiftWidth)
    (fun g hg => List.all_eq_true.mp (TerminalEpoch.gates_wellFormed hshift) g hg)

theorem epochGates_act
    {workWidth shiftWidth i : Nat}
    (hshift : 0 < shiftWidth)
    (hscratch : readField i (scratchOffset workWidth shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i (wrappedWire workWidth shiftWidth) = 0) :
    actGates (epochGates workWidth shiftWidth) i =
      writeField
        (writeField
          (writeField i (lowOffset workWidth) shiftWidth
            (nextLow workWidth shiftWidth i))
          (wrappedWire workWidth shiftWidth) 1 0)
        (epochWire workWidth shiftWidth) 1
          (nextEpoch workWidth shiftWidth i) := by
  let L := TerminalEpoch.layout shiftWidth
  let W := epochWiring workWidth shiftWidth
  let gathered := gatherBits (place L W) L.width i
  have hlocalScratch :
      readField gathered (TerminalEpoch.scratchOffset shiftWidth) shiftWidth = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    rw [readField_gatherBits L W 2 i (by simp [W, epochWiring])]
    simpa [L, W, TerminalEpoch.layout, Layout.size, epochWiring,
      scratchOffset] using hscratch
  have hlocalWrapped :
      bitValue gathered (TerminalEpoch.wrappedWire shiftWidth) = 0 := by
    rw [← readField_one]
    have hoff : TerminalEpoch.wrappedWire shiftWidth = L.offset 3 := by
      simp [L, TerminalEpoch.layout, Layout.offset, TerminalEpoch.wrappedWire,
        two_mul]
      omega
    have hsize : 1 = L.size 3 := by
      simp [L, TerminalEpoch.layout, Layout.size]
    rw [hoff, hsize]
    rw [readField_gatherBits L W 3 i (by simp [W, epochWiring])]
    simpa [L, W, TerminalEpoch.layout, Layout.size, epochWiring,
      wrappedWire, readField_one] using hwrapped
  have hlocalLow :
      readField gathered TerminalEpoch.lowOffset shiftWidth =
        readField i (lowOffset workWidth) shiftWidth := by
    change readField gathered (L.offset 0) (L.size 0) = _
    rw [readField_gatherBits L W 0 i (by simp [W, epochWiring])]
    simp [L, W, TerminalEpoch.layout, Layout.size, epochWiring, lowOffset]
  have hlocalControl :
      bitValue gathered (TerminalEpoch.controlWire shiftWidth) =
        bitValue i (controlWire workWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    change readField gathered (L.offset 1) (L.size 1) = _
    rw [readField_gatherBits L W 1 i (by simp [W, epochWiring])]
    simp [L, W, TerminalEpoch.layout, Layout.size, epochWiring, controlWire]
  have hlocalEpoch :
      bitValue gathered (TerminalEpoch.epochWire shiftWidth) =
        bitValue i (epochWire workWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    have hoff : TerminalEpoch.epochWire shiftWidth = L.offset 4 := by
      simp [L, TerminalEpoch.layout, Layout.offset, TerminalEpoch.epochWire,
        two_mul]
      omega
    have hsize : 1 = L.size 4 := by
      simp [L, TerminalEpoch.layout, Layout.size]
    rw [hoff, hsize]
    rw [readField_gatherBits L W 4 i (by simp [W, epochWiring])]
    simp [L, W, TerminalEpoch.layout, Layout.size, epochWiring, epochWire]
  have hnextLow : TerminalEpoch.nextLow shiftWidth gathered =
      nextLow workWidth shiftWidth i := by
    simp [TerminalEpoch.nextLow, nextLow, hlocalLow, hlocalControl]
  have hlocalWrap : TerminalEpoch.wrapped shiftWidth gathered =
      wrapped workWidth shiftWidth i := by
    simp [TerminalEpoch.wrapped, wrapped, hnextLow]
  have hnextEpoch : TerminalEpoch.nextEpoch shiftWidth gathered =
      nextEpoch workWidth shiftWidth i := by
    simp [TerminalEpoch.nextEpoch, nextEpoch, hlocalEpoch, hlocalControl,
      hlocalWrap]
  have hlocal :
      actGates (TerminalEpoch.gates shiftWidth) gathered =
        L.write
          (L.write
            (L.write gathered 0 (nextLow workWidth shiftWidth i))
            3 0)
          4 (nextEpoch workWidth shiftWidth i) := by
    rw [TerminalEpoch.gates_act hshift hlocalScratch hlocalWrapped]
    simp [TerminalEpoch.out, L, TerminalEpoch.layout, Layout.write,
      Layout.offset, Layout.size, TerminalEpoch.lowOffset,
      TerminalEpoch.wrappedWire, TerminalEpoch.epochWire, hnextLow,
      hnextEpoch, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hplaced := actGates_placed_write₃
    (L := L) (W := W) (k₁ := 0) (k₂ := 3) (k₃ := 4)
    (v₁ := nextLow workWidth shiftWidth i) (v₂ := 0)
    (v₃ := nextEpoch workWidth shiftWidth i) (I := i)
    (epochWiring_disjoint hshift)
    (by simp [L, W, TerminalEpoch.layout, epochWiring])
    (by simp [L, TerminalEpoch.layout])
    (by simp [L, TerminalEpoch.layout])
    (by simp [L, TerminalEpoch.layout])
    (by omega) (by omega) (by omega)
    (fun g hg => List.all_eq_true.mp (TerminalEpoch.gates_wellFormed hshift) g hg)
    hlocal
  simpa [epochGates, L, W, epochWiring, TerminalEpoch.layout, Layout.size,
    lowOffset, wrappedWire, epochWire] using hplaced

theorem rotationGates_act_on
    {workWidth shiftWidth i : Nat}
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 1) :
    actGates (rotationGates workWidth shiftWidth) i =
      writeField i workOffset workWidth
        (rotateRightValue workWidth (readField i workOffset workWidth)) := by
  exact rotateRightControlled_on workWidth workOffset i
    (Or.inr (by simp [workOffset, controlWire])) hcontrol

theorem gates_act
    {workWidth shiftWidth i : Nat}
    (hshift : 0 < shiftWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 1)
    (hscratch : readField i (scratchOffset workWidth shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i (wrappedWire workWidth shiftWidth) = 0) :
    actGates (gates workWidth shiftWidth) i = out workWidth shiftWidth i := by
  let j := writeField i workOffset workWidth
    (rotateRightValue workWidth (readField i workOffset workWidth))
  have hjScratch :
      readField j (scratchOffset workWidth shiftWidth) shiftWidth = 0 := by
    simp only [j]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [workOffset, scratchOffset]; omega))]
    exact hscratch
  have hjWrapped : bitValue j (wrappedWire workWidth shiftWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_out (Or.inr (by
      simp [workOffset, wrappedWire]; omega))]
    exact hwrapped
  have hjLow : readField j (lowOffset workWidth) shiftWidth =
      readField i (lowOffset workWidth) shiftWidth := by
    simp only [j]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [workOffset, lowOffset]))]
  have hjControl : bitValue j (controlWire workWidth shiftWidth) =
      bitValue i (controlWire workWidth shiftWidth) := by
    simp only [j]
    rw [bitValue_write_out (Or.inr (by
      simp [workOffset, controlWire]))]
  have hjEpoch : bitValue j (epochWire workWidth shiftWidth) =
      bitValue i (epochWire workWidth shiftWidth) := by
    simp only [j]
    rw [bitValue_write_out (Or.inr (by
      simp [workOffset, epochWire]; omega))]
  have hjNextLow : nextLow workWidth shiftWidth j =
      nextLow workWidth shiftWidth i := by
    simp [nextLow, hjLow, hjControl]
  have hjWrappedValue : wrapped workWidth shiftWidth j =
      wrapped workWidth shiftWidth i := by
    simp [wrapped, hjNextLow]
  have hjNextEpoch : nextEpoch workWidth shiftWidth j =
      nextEpoch workWidth shiftWidth i := by
    simp [nextEpoch, hjEpoch, hjControl, hjWrappedValue]
  simp only [gates, actGates_append]
  rw [rotationGates_act_on hcontrol]
  change actGates (epochGates workWidth shiftWidth) j = _
  rw [epochGates_act hshift hjScratch hjWrapped]
  simp [out, j, hjNextLow, hjNextEpoch]

theorem gates_identity_control_off
    {workWidth shiftWidth i : Nat}
    (hshift : 0 < shiftWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i (wrappedWire workWidth shiftWidth) = 0) :
    actGates (gates workWidth shiftWidth) i = i := by
  simp only [gates, actGates_append]
  rw [show actGates (rotationGates workWidth shiftWidth) i = i from
    rotateRightControlled_off workWidth workOffset i
      (Or.inr (by simp [workOffset, controlWire])) hcontrol,
    epochGates_act hshift hscratch hwrapped]
  simp only [nextLow, nextEpoch, hcontrol, zero_mul, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (readField_lt i (lowOffset workWidth) shiftWidth)]
  rw [writeField_read]
  have hclearWrapped :
      writeField i (wrappedWire workWidth shiftWidth) 1 0 = i :=
    write_of_bitValue (by simpa using hwrapped.symm)
  rw [hclearWrapped,
    Nat.mod_eq_of_lt (bitValue_lt i (epochWire workWidth shiftWidth)),
    ← readField_one, writeField_read]

theorem rotationGates_wellFormed (workWidth shiftWidth : Nat) :
    (rotationGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  apply rotateRightControlled_wellFormed
  · exact Or.inr (by simp [workOffset, controlWire])
  · simp [controlWire, layout, Layout.width]
  · simp [workOffset, layout, Layout.width]

theorem gates_wellFormed
    {workWidth shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (gates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  simp [gates, rotationGates_wellFormed,
    epochGates_wellFormed hshift, List.all_append]

theorem circuit_wellFormed
    {workWidth shiftWidth : Nat} (hshift : 0 < shiftWidth) :
    (circuit workWidth shiftWidth).wellFormed = true := by
  exact gates_wellFormed hshift

theorem reverse_gates_cancel
    {workWidth shiftWidth i : Nat} (hshift : 0 < shiftWidth) :
    actGates (gates workWidth shiftWidth).reverse
      (actGates (gates workWidth shiftWidth) i) = i := by
  exact actGates_reverse (gates_wellFormed hshift) i

end VQ.Euclid.TerminalPadding
