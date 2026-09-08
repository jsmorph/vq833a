/-
Placement lemmas for Euclidean-step components whose local fields occupy
arbitrary disjoint blocks of a larger register.
-/
import VQ.Euclid.Selector
import VQ.Reversible.Bit
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace Placed

open Reversible

def selectorWiring (source flag scratch : Nat) : Wiring :=
  [source, flag, scratch]

def selectorGates (value width source flag scratch : Nat) : List RGate :=
  (Selector.circuit value width).gates.map
    (RGate.map (place (Selector.layout width)
      (selectorWiring source flag scratch)))

theorem selector_act {value width source flag scratch i : Nat}
    (hd : Wiring.Disjoint (Selector.layout width)
      (selectorWiring source flag scratch))
    (hscratch : readField i scratch width = 0) :
    actGates (selectorGates value width source flag scratch) i =
      writeField i flag 1
        ((bitValue i flag +
          if readField i source width = value % 2 ^ width then 1 else 0) % 2) := by
  let L := Selector.layout width
  let W := selectorWiring source flag scratch
  let gathered := gatherBits (place L W) L.width i
  have hscratchGathered : Selector.scratch width gathered = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    simp only [gathered]
    rw [readField_gatherBits L W 2 i (by simp [W, selectorWiring])]
    simpa [L, W, Selector.layout, Layout.size, selectorWiring] using hscratch
  have hsource : Selector.source width gathered = readField i source width := by
    change readField gathered (L.offset 0) (L.size 0) = readField i source width
    simp only [gathered]
    rw [readField_gatherBits L W 0 i (by simp [W, selectorWiring])]
    simp [L, W, Selector.layout, Layout.size, selectorWiring]
  have hflag : Selector.flag width gathered = bitValue i flag := by
    change readField gathered (L.offset 1) (L.size 1) = bitValue i flag
    simp only [gathered]
    rw [readField_gatherBits L W 1 i (by simp [W, selectorWiring])]
    simp [L, W, Selector.layout, Layout.size, selectorWiring, readField_one]
  have hlocal : actGates (Selector.circuit value width).gates gathered =
      L.write gathered 1
        ((bitValue i flag +
          if readField i source width = value % 2 ^ width then 1 else 0) % 2) := by
    change act (Selector.circuit value width) gathered = _
    rw [Selector.act_circuit hscratchGathered]
    simp only [Selector.out, hsource, hflag]
    rfl
  exact actGates_placed_write hd (by simp [Selector.layout, selectorWiring])
    (by simp [Selector.layout])
    (fun g hg => RCircuit.wellFormed_mem (Selector.circuit_wellFormed value width) hg)
    hlocal

theorem selector_wellFormed {value width source flag scratch total : Nat}
    (hd : Wiring.Disjoint (Selector.layout width)
      (selectorWiring source flag scratch))
    (hbound : ∀ j, j < (Selector.layout width).length →
      (selectorWiring source flag scratch).getD j 0 +
          (Selector.layout width).size j ≤ total) :
    (selectorGates value width source flag scratch).all
      (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd
    (by simp [Selector.layout, selectorWiring]) hbound
    (fun g hg => RCircuit.wellFormed_mem (Selector.circuit_wellFormed value width) hg)

theorem selector_length (value width source flag scratch : Nat) :
    (selectorGates value width source flag scratch).length =
      (Selector.circuit value width).gates.length := by
  simp [selectorGates]

theorem selector_ccx (value width source flag scratch : Nat) :
    (selectorGates value width source flag scratch).countP RGate.isCcx =
      (Selector.circuit value width).gates.countP RGate.isCcx := by
  rw [selectorGates, countP_map_gates (fun g => RGate.isCcx_map _ g)]

theorem selector_cx (value width source flag scratch : Nat) :
    (selectorGates value width source flag scratch).countP RGate.isCx =
      (Selector.circuit value width).gates.countP RGate.isCx := by
  rw [selectorGates, countP_map_gates (fun g => RGate.isCx_map _ g)]

end Placed
end Euclid
end VQ
