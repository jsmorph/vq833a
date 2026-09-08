/-
Placement of a compact equality selector on arbitrary register fields.
-/
import VQ.Euclid.CompactSelector
import VQ.Euclid.Placed

namespace VQ
namespace Euclid
namespace CompactPlaced

open Reversible

def selectorWiring (source flag scratch : Nat) : Wiring :=
  [source, flag, scratch]

def selectorGates (value width source flag scratch : Nat) : List RGate :=
  (CompactSelector.circuit value width).gates.map
    (RGate.map (place (CompactSelector.layout width)
      (selectorWiring source flag scratch)))

theorem selector_act {value width source flag scratch i : Nat}
    (hwidth : 2 ≤ width)
    (hd : Wiring.Disjoint (CompactSelector.layout width)
      (selectorWiring source flag scratch))
    (hscratch : readField i scratch (width - 2) = 0) :
    actGates (selectorGates value width source flag scratch) i =
      writeField i flag 1
        ((bitValue i flag +
          if readField i source width = value % 2 ^ width then 1 else 0) % 2) := by
  let L := CompactSelector.layout width
  let W := selectorWiring source flag scratch
  let gathered := gatherBits (place L W) L.width i
  have hscratchGathered : CompactSelector.scratch width gathered = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    simp only [gathered]
    rw [readField_gatherBits L W 2 i (by simp [W, selectorWiring])]
    simpa [L, W, CompactSelector.layout, Layout.size, selectorWiring] using hscratch
  have hsource : CompactSelector.source width gathered = readField i source width := by
    change readField gathered (L.offset 0) (L.size 0) = readField i source width
    simp only [gathered]
    rw [readField_gatherBits L W 0 i (by simp [W, selectorWiring])]
    simp [L, W, CompactSelector.layout, Layout.size, selectorWiring]
  have hflag : CompactSelector.flag width gathered = bitValue i flag := by
    change readField gathered (L.offset 1) (L.size 1) = bitValue i flag
    simp only [gathered]
    rw [readField_gatherBits L W 1 i (by simp [W, selectorWiring])]
    simp [L, W, CompactSelector.layout, Layout.size, selectorWiring,
      readField_one]
  have hlocal : actGates (CompactSelector.circuit value width).gates gathered =
      L.write gathered 1
        ((bitValue i flag +
          if readField i source width = value % 2 ^ width then 1 else 0) % 2) := by
    change actGates (CompactSelector.gates value width) gathered = _
    rw [CompactSelector.gates_act hwidth (gatherBits_lt _ _ _) hscratchGathered]
    change L.write gathered 1
      ((CompactSelector.flag width gathered +
        if CompactSelector.source width gathered = value % 2 ^ width then 1 else 0) % 2) = _
    rw [hsource, hflag]
  exact actGates_placed_write hd
    (by simp [CompactSelector.layout, selectorWiring])
    (by simp [CompactSelector.layout])
    (fun g hg => RCircuit.wellFormed_mem
      (CompactSelector.circuit_wellFormed value hwidth) hg)
    hlocal

theorem selector_wellFormed {value width source flag scratch total : Nat}
    (hwidth : 2 ≤ width)
    (hd : Wiring.Disjoint (CompactSelector.layout width)
      (selectorWiring source flag scratch))
    (hbound : ∀ j, j < (CompactSelector.layout width).length →
      (selectorWiring source flag scratch).getD j 0 +
          (CompactSelector.layout width).size j ≤ total) :
    (selectorGates value width source flag scratch).all
      (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd
    (by simp [CompactSelector.layout, selectorWiring]) hbound
    (fun g hg => RCircuit.wellFormed_mem
      (CompactSelector.circuit_wellFormed value hwidth) hg)

theorem selector_length (value width source flag scratch : Nat) :
    (selectorGates value width source flag scratch).length =
      (CompactSelector.circuit value width).gates.length := by
  simp [selectorGates]

theorem selector_ccx (value width source flag scratch : Nat) :
    (selectorGates value width source flag scratch).countP RGate.isCcx =
      (CompactSelector.circuit value width).gates.countP RGate.isCcx := by
  rw [selectorGates, countP_map_gates (fun g => RGate.isCcx_map _ g)]

end CompactPlaced
end Euclid
end VQ
