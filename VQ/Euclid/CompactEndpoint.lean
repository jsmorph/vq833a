/-
Endpoint equality with compact conjunction workspace.
-/
import VQ.Euclid.CompactSelector
import VQ.Euclid.Placed

namespace VQ
namespace Euclid
namespace CompactEndpoint

open Reversible

def layout (width : Nat) : Layout := [width, 1, 1, 1, width - 2]

def outerWire (width : Nat) : Nat := width
def accumulatorWire (width : Nat) : Nat := width + 1
def flagWire (width : Nat) : Nat := width + 2
def scratchWire (width : Nat) : Nat := width + 3

def selectorWiring (width : Nat) : Wiring :=
  [0, flagWire width, scratchWire width]

def selectorGates (value width : Nat) : List RGate :=
  (CompactSelector.circuit value width).gates.map
    (RGate.map (place (CompactSelector.layout width) (selectorWiring width)))

def gates (value width : Nat) : List RGate :=
  selectorGates value width ++
    [.ccx (outerWire width) (flagWire width) (accumulatorWire width)] ++
  selectorGates value width

def circuit (value width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates value width }

def selected (value width i : Nat) : Nat :=
  if i.testBit (outerWire width) &&
      decide (readField i 0 width = value % 2 ^ width) then 1 else 0

theorem layout_width {width : Nat} (hwidth : 2 ≤ width) :
    (layout width).width = 2 * width + 1 := by
  simp [layout, Layout.width]
  omega

theorem selector_disjoint {width : Nat} (hwidth : 2 ≤ width) :
    Wiring.Disjoint (CompactSelector.layout width) (selectorWiring width) := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp [selectorWiring] at hj
    omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
    simp [selectorWiring] at hk
    omega
  rcases hj' with rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl <;>
    simp [selectorWiring, CompactSelector.layout, Layout.size, flagWire,
      scratchWire] at * <;> omega

theorem selector_action {value width i : Nat}
    (hwidth : 2 ≤ width)
    (hscratch : readField i (scratchWire width) (width - 2) = 0) :
    actGates (selectorGates value width) i =
      writeField i (flagWire width) 1
        ((bitValue i (flagWire width) +
          if readField i 0 width = value % 2 ^ width then 1 else 0) % 2) := by
  let L := CompactSelector.layout width
  let W := selectorWiring width
  let gathered := gatherBits (place L W) L.width i
  have hscratchGathered : CompactSelector.scratch width gathered = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    simp only [gathered]
    rw [readField_gatherBits L W 2 i (by simp [W, selectorWiring])]
    simpa [L, W, CompactSelector.layout, Layout.size, selectorWiring] using hscratch
  have hsource : CompactSelector.source width gathered = readField i 0 width := by
    change readField gathered (L.offset 0) (L.size 0) = readField i 0 width
    simp only [gathered]
    rw [readField_gatherBits L W 0 i (by simp [W, selectorWiring])]
    simp [L, W, CompactSelector.layout, Layout.size, selectorWiring]
  have hflag : CompactSelector.flag width gathered = bitValue i (flagWire width) := by
    change readField gathered (L.offset 1) (L.size 1) =
      bitValue i (flagWire width)
    simp only [gathered]
    rw [readField_gatherBits L W 1 i (by simp [W, selectorWiring])]
    simp [L, W, CompactSelector.layout, Layout.size, selectorWiring,
      readField_one]
  have hlocal : actGates (CompactSelector.circuit value width).gates gathered =
      L.write gathered 1
        ((bitValue i (flagWire width) +
          if readField i 0 width = value % 2 ^ width then 1 else 0) % 2) := by
    change actGates (CompactSelector.gates value width) gathered = _
    rw [CompactSelector.gates_act hwidth (gatherBits_lt _ _ _) hscratchGathered]
    change L.write gathered 1
      ((CompactSelector.flag width gathered +
        if CompactSelector.source width gathered = value % 2 ^ width then 1 else 0) % 2) = _
    rw [hsource, hflag]
  exact actGates_placed_write (selector_disjoint hwidth)
    (by simp [CompactSelector.layout, selectorWiring])
    (by simp [CompactSelector.layout])
    (fun g hg => RCircuit.wellFormed_mem
      (CompactSelector.circuit_wellFormed value hwidth) hg)
    hlocal

theorem selector_wellFormed (value : Nat) {width : Nat} (hwidth : 2 ≤ width) :
    (selectorGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  exact wellFormed_placeGates (selector_disjoint hwidth)
    (by simp [CompactSelector.layout, selectorWiring])
    (by
      intro j hj
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
        simp [CompactSelector.layout] at hj
        omega
      rcases hj' with rfl | rfl | rfl <;>
        simp [selectorWiring, CompactSelector.layout, Layout.size,
          layout_width hwidth, flagWire, scratchWire] <;> omega)
    (fun g hg => RCircuit.wellFormed_mem
      (CompactSelector.circuit_wellFormed value hwidth) hg)

theorem circuit_wellFormed (value : Nat) {width : Nat} (hwidth : 2 ≤ width) :
    (circuit value width).wellFormed = true := by
  change (gates value width).all
    (RGate.wellFormed (layout width).width) = true
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨selector_wellFormed value hwidth, ?_⟩,
    selector_wellFormed value hwidth⟩
  rw [layout_width hwidth]
  simp [RGate.wellFormed, outerWire, flagWire, accumulatorWire]
  omega

theorem gates_length_le (value width : Nat) :
    (gates value width).length ≤ 8 * width + 3 := by
  simp only [gates, List.length_append, List.length_cons, List.length_nil,
    selectorGates, CompactSelector.circuit, List.length_map]
  have h := CompactSelector.gates_length_le value width
  omega

theorem gates_ccx_le (value width : Nat) :
    (gates value width).countP RGate.isCcx ≤ 4 * width + 1 := by
  simp only [gates, List.countP_append, List.countP_cons, List.countP_nil,
    RGate.isCcx, if_true, selectorGates, CompactSelector.circuit]
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)]
  have h := CompactSelector.gates_ccx_le value width
  omega

theorem gates_act {value width i : Nat}
    (hwidth : 2 ≤ width)
    (hflag : bitValue i (flagWire width) = 0)
    (hscratch : readField i (scratchWire width) (width - 2) = 0) :
    actGates (gates value width) i =
      writeField i (accumulatorWire width) 1
        ((bitValue i (accumulatorWire width) + selected value width i) % 2) := by
  let e := if readField i 0 width = value % 2 ^ width then 1 else 0
  let j := writeField i (flagWire width) 1 e
  let k := writeField j (accumulatorWire width) 1
    ((bitValue i (accumulatorWire width) +
      bitValue i (outerWire width) * e) % 2)
  have he : e < 2 := by simp [e]; split <;> omega
  have hj : actGates (selectorGates value width) i = j := by
    rw [selector_action hwidth hscratch]
    simp only [j, e, hflag, Nat.zero_add]
    rw [Nat.mod_eq_of_lt he]
  have hjOuter : bitValue j (outerWire width) = bitValue i (outerWire width) := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_ne (by simp [flagWire, outerWire])]
  have hjFlag : bitValue j (flagWire width) = e := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_self, Nat.mod_eq_of_lt he]
  have hjAcc : bitValue j (accumulatorWire width) =
      bitValue i (accumulatorWire width) := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_ne (by simp [flagWire, accumulatorWire])]
  have hmiddle :
      RGate.act (.ccx (outerWire width) (flagWire width)
        (accumulatorWire width)) j = k := by
    rw [act_ccx_write, hjOuter, hjFlag, hjAcc]
  have hkScratch : readField k (scratchWire width) (width - 2) = 0 := by
    simp only [k, j]
    rw [readField_writeField_of_disjoint (by simp [accumulatorWire, scratchWire]),
      readField_writeField_of_disjoint (by simp [flagWire, scratchWire]),
      hscratch]
  have hkEndpoint : readField k 0 width = readField i 0 width := by
    simp only [k, j]
    rw [readField_writeField_of_disjoint (by simp [accumulatorWire]),
      readField_writeField_of_disjoint (by simp [flagWire])]
  have hkFlag : bitValue k (flagWire width) = e := by
    simp only [k]
    rw [bitValue_write_ne (by simp [flagWire, accumulatorWire]), hjFlag]
  have hlast := selector_action (value := value) (i := k) hwidth hkScratch
  rw [gates, actGates_append, actGates_append, hj]
  change actGates (selectorGates value width)
    (RGate.act (.ccx (outerWire width) (flagWire width)
      (accumulatorWire width)) j) = _
  rw [hmiddle, hlast, hkEndpoint, hkFlag]
  have he2 : (e + e) % 2 = 0 := by simp [e]; split <;> omega
  rw [he2]
  simp only [k, j]
  rw [writeField_comm
      (i := writeField i (flagWire width) 1 e)
      (o₁ := accumulatorWire width) (n₁ := 1)
      (v := (bitValue i (accumulatorWire width) +
        bitValue i (outerWire width) * e) % 2)
      (o₂ := flagWire width) (n₂ := 1) (u := 0)
      (by simp [accumulatorWire, flagWire]),
    writeField_writeField]
  have hrestore : writeField i (flagWire width) 1 0 = i := by
    exact write_of_bitValue (by omega)
  rw [hrestore]
  apply write_congr
  simp only [selected, e]
  by_cases ho : i.testBit (outerWire width)
  · simp [ho, bitValue]
  · have hof : i.testBit (outerWire width) = false := Bool.eq_false_iff.mpr ho
    simp [hof, bitValue]

end CompactEndpoint
end Euclid
end VQ
