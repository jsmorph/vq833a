/-
The Figure 11 arithmetic cells placed on arbitrary disjoint wires.
-/
import VQ.Euclid.Cell
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace CellPlaced

open Reversible

def layout : Layout := [1, 1, 1, 1, 1]

def wiring (target source carry control scratch : Nat) : Wiring :=
  [target, source, carry, control, scratch]

def gates (gs : List RGate) (target source carry control scratch : Nat) :
    List RGate :=
  gs.map (RGate.map (place layout
    (wiring target source carry control scratch)))

theorem layout_width : layout.width = 5 := rfl

theorem gathered_bit {target source carry control scratch I k : Nat}
    (hk : k < 5) :
    bitValue
        (gatherBits
          (place layout (wiring target source carry control scratch))
          layout.width I)
        k =
      bitValue I ((wiring target source carry control scratch).getD k 0) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits layout
    (wiring target source carry control scratch) k I (by simp [wiring]; omega)
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
    simpa [layout, Layout.offset, Layout.size] using h

theorem component_wellFormed {gs : List RGate}
    (h : gs.all (RGate.wellFormed 5) = true) :
    ∀ g ∈ gs, g.wellFormed layout.width = true := by
  intro g hg
  exact List.all_eq_true.mp h g hg

theorem baseMaj_wellFormed :
    Cell.baseMajGates.all (RGate.wellFormed 5) = true := by
  decide

theorem baseUma_wellFormed :
    Cell.baseUmaGates.all (RGate.wellFormed 5) = true := by
  decide

theorem maj_wellFormed :
    Cell.majGates.all (RGate.wellFormed 5) = true := by
  have h := Cell.maj_wellFormed
  change Cell.majGates.all (RGate.wellFormed 5) = true at h
  exact h

theorem uma_wellFormed :
    Cell.umaGates.all (RGate.wellFormed 5) = true := by
  have h := Cell.uma_wellFormed
  change Cell.umaGates.all (RGate.wellFormed 5) = true at h
  exact h

theorem disabled_wellFormed :
    Cell.disabledGates.all (RGate.wellFormed 5) = true := by
  decide

theorem maj_enabled {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout
      (wiring target source carry control scratch))
    (hcontrol : I.testBit control = true)
    (hscratch : I.testBit scratch = false) :
    actGates (gates Cell.majGates target source carry control scratch) I =
      actGates (gates Cell.baseMajGates target source carry control scratch) I := by
  let W := wiring target source carry control scratch
  let gathered := gatherBits (place layout W) layout.width I
  have hcValue : bitValue gathered Cell.controlWire = bitValue I control := by
    simpa [gathered, W, wiring, Cell.controlWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 3) (by omega))
  have hsValue : bitValue gathered Cell.scratchWire = bitValue I scratch := by
    simpa [gathered, W, wiring, Cell.scratchWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 4) (by omega))
  have hc : gathered.testBit Cell.controlWire = true := by
    simpa [bitValue, hcontrol] using hcValue
  have hs : gathered.testBit Cell.scratchWire = false := by
    simpa [bitValue, hscratch] using hsValue
  apply actGates_placed_congr hd (by simp [layout, wiring])
    (component_wellFormed maj_wellFormed)
    (component_wellFormed baseMaj_wellFormed) I
  have hlocal := Cell.maj_enabled (i := gathered) hc hs
  change actGates Cell.majGates gathered =
    actGates Cell.baseMajGates gathered at hlocal
  exact hlocal

theorem uma_enabled {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout
      (wiring target source carry control scratch))
    (hcontrol : I.testBit control = true)
    (hscratch : I.testBit scratch = false) :
    actGates (gates Cell.umaGates target source carry control scratch) I =
      actGates (gates Cell.baseUmaGates target source carry control scratch) I := by
  let W := wiring target source carry control scratch
  let gathered := gatherBits (place layout W) layout.width I
  have hcValue : bitValue gathered Cell.controlWire = bitValue I control := by
    simpa [gathered, W, wiring, Cell.controlWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 3) (by omega))
  have hsValue : bitValue gathered Cell.scratchWire = bitValue I scratch := by
    simpa [gathered, W, wiring, Cell.scratchWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 4) (by omega))
  have hc : gathered.testBit Cell.controlWire = true := by
    simpa [bitValue, hcontrol] using hcValue
  have hs : gathered.testBit Cell.scratchWire = false := by
    simpa [bitValue, hscratch] using hsValue
  apply actGates_placed_congr hd (by simp [layout, wiring])
    (component_wellFormed uma_wellFormed)
    (component_wellFormed baseUma_wellFormed) I
  have hlocal := Cell.uma_enabled (i := gathered) hc hs
  change actGates Cell.umaGates gathered =
    actGates Cell.baseUmaGates gathered at hlocal
  exact hlocal

theorem maj_control_clear {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout
      (wiring target source carry control scratch))
    (hcontrol : I.testBit control = false)
    (hscratch : I.testBit scratch = false) :
    actGates (gates Cell.majGates target source carry control scratch) I =
      actGates (gates Cell.disabledGates target source carry control scratch) I := by
  let W := wiring target source carry control scratch
  let gathered := gatherBits (place layout W) layout.width I
  have hcValue : bitValue gathered Cell.controlWire = bitValue I control := by
    simpa [gathered, W, wiring, Cell.controlWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 3) (by omega))
  have hsValue : bitValue gathered Cell.scratchWire = bitValue I scratch := by
    simpa [gathered, W, wiring, Cell.scratchWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 4) (by omega))
  have hc : gathered.testBit Cell.controlWire = false := by
    simpa [bitValue, hcontrol] using hcValue
  have hs : gathered.testBit Cell.scratchWire = false := by
    simpa [bitValue, hscratch] using hsValue
  apply actGates_placed_congr hd (by simp [layout, wiring])
    (component_wellFormed maj_wellFormed)
    (component_wellFormed disabled_wellFormed) I
  have hm := Cell.maj_control_clear (i := gathered) hc hs
  change actGates Cell.majGates gathered = Cell.disabledState gathered at hm
  rw [hm, Cell.disabledGates_act]

theorem uma_control_clear {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout
      (wiring target source carry control scratch))
    (hcontrol : I.testBit control = false)
    (hscratch : I.testBit scratch = false) :
    actGates (gates Cell.umaGates target source carry control scratch) I =
      actGates (gates Cell.disabledGates target source carry control scratch) I := by
  let W := wiring target source carry control scratch
  let gathered := gatherBits (place layout W) layout.width I
  have hcValue : bitValue gathered Cell.controlWire = bitValue I control := by
    simpa [gathered, W, wiring, Cell.controlWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 3) (by omega))
  have hsValue : bitValue gathered Cell.scratchWire = bitValue I scratch := by
    simpa [gathered, W, wiring, Cell.scratchWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 4) (by omega))
  have hc : gathered.testBit Cell.controlWire = false := by
    simpa [bitValue, hcontrol] using hcValue
  have hs : gathered.testBit Cell.scratchWire = false := by
    simpa [bitValue, hscratch] using hsValue
  apply actGates_placed_congr hd (by simp [layout, wiring])
    (component_wellFormed uma_wellFormed)
    (component_wellFormed disabled_wellFormed) I
  have hu := Cell.uma_control_clear (i := gathered) hc hs
  change actGates Cell.umaGates gathered = Cell.disabledState gathered at hu
  rw [hu, Cell.disabledGates_act]

theorem maj_uma_control_clear {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout
      (wiring target source carry control scratch))
    (hcontrol : I.testBit control = false)
    (hscratch : I.testBit scratch = false) :
    actGates (gates Cell.majGates target source carry control scratch) I =
      actGates (gates Cell.umaGates target source carry control scratch) I := by
  let W := wiring target source carry control scratch
  let gathered := gatherBits (place layout W) layout.width I
  have hcValue : bitValue gathered Cell.controlWire = bitValue I control := by
    simpa [gathered, W, wiring, Cell.controlWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 3) (by omega))
  have hsValue : bitValue gathered Cell.scratchWire = bitValue I scratch := by
    simpa [gathered, W, wiring, Cell.scratchWire] using
      (gathered_bit (target := target) (source := source) (carry := carry)
        (control := control) (scratch := scratch) (I := I) (k := 4) (by omega))
  have hc : gathered.testBit Cell.controlWire = false := by
    simpa [bitValue, hcontrol] using hcValue
  have hs : gathered.testBit Cell.scratchWire = false := by
    simpa [bitValue, hscratch] using hsValue
  apply actGates_placed_congr hd (by simp [layout, wiring])
    (component_wellFormed maj_wellFormed)
    (component_wellFormed uma_wellFormed) I
  have hm := Cell.maj_control_clear (i := gathered) hc hs
  have hu := Cell.uma_control_clear (i := gathered) hc hs
  change actGates Cell.majGates gathered = Cell.disabledState gathered at hm
  change actGates Cell.umaGates gathered = Cell.disabledState gathered at hu
  rw [hm, hu]

end CellPlaced
end Euclid
end VQ
