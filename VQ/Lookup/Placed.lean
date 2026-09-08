import VQ.Lookup.Spec
import VQ.Reversible.Wiring

namespace VQ.Lookup

open Reversible

def placedWiring (addressOffset outputOffset workspaceOffset : Nat) : Wiring :=
  [addressOffset, outputOffset, workspaceOffset]

def placedGates (addressWidth outputWidth workspaceWidth : Nat)
    (addressOffset outputOffset workspaceOffset : Nat) (r : RCircuit) :
    List RGate :=
  r.gates.map (RGate.map (place
    (layout addressWidth outputWidth workspaceWidth)
    (placedWiring addressOffset outputOffset workspaceOffset)))

theorem placedGates_act
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {addressOffset outputOffset workspaceOffset I : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    (hdis : Wiring.Disjoint
      (layout addressWidth outputWidth workspaceWidth)
      (placedWiring addressOffset outputOffset workspaceOffset))
    (hworkspace : readField I workspaceOffset workspaceWidth = 0) :
    actGates
        (placedGates addressWidth outputWidth workspaceWidth
          addressOffset outputOffset workspaceOffset r) I =
      writeField I outputOffset outputWidth
        (readField I outputOffset outputWidth ^^^
          value table outputWidth
            (readField I addressOffset addressWidth)) := by
  let L := layout addressWidth outputWidth workspaceWidth
  let W := placedWiring addressOffset outputOffset workspaceOffset
  let J := gatherBits (place L W) L.width I
  have haddress : address addressWidth outputWidth workspaceWidth J =
      readField I addressOffset addressWidth := by
    change L.read J 0 = _
    rw [read_gatherBits L W 0 I (by simp [W, placedWiring])]
    rfl
  have houtput : output addressWidth outputWidth workspaceWidth J =
      readField I outputOffset outputWidth := by
    change L.read J 1 = _
    rw [read_gatherBits L W 1 I (by simp [W, placedWiring])]
    rfl
  have hworkspaceLocal :
      workspace addressWidth outputWidth workspaceWidth J = 0 := by
    change L.read J 2 = 0
    rw [read_gatherBits L W 2 I (by simp [W, placedWiring])]
    exact hworkspace
  have hwf : ∀ g ∈ r.gates, g.wellFormed L.width = true := by
    have h := hspec.2.1
    rw [RCircuit.wellFormed, hspec.1] at h
    exact List.all_eq_true.mp h
  have hlocal : actGates r.gates J =
      L.write J 1
        (readField I outputOffset outputWidth ^^^
          value table outputWidth
            (readField I addressOffset addressWidth)) := by
    have h := hspec.2.2 J hworkspaceLocal
    change actGates r.gates J = _ at h
    rw [h]
    simp only [xorOutput, houtput, haddress]
    rfl
  have hplaced := actGates_placed_write
    (L := L) (W := W) (gs := r.gates) (k := 1) (I := I)
    hdis (by simp [L, W, layout, placedWiring])
    (by simp [L, layout]) hwf hlocal
  simpa [placedGates, L, W, placedWiring, layout, Layout.size] using hplaced

theorem placedGates_wellFormed
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {addressOffset outputOffset workspaceOffset totalWidth : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    (hdis : Wiring.Disjoint
      (layout addressWidth outputWidth workspaceWidth)
      (placedWiring addressOffset outputOffset workspaceOffset))
    (hbound : ∀ j, j < (layout addressWidth outputWidth workspaceWidth).length →
      (placedWiring addressOffset outputOffset workspaceOffset).getD j 0 +
          (layout addressWidth outputWidth workspaceWidth).size j ≤ totalWidth) :
    (placedGates addressWidth outputWidth workspaceWidth
      addressOffset outputOffset workspaceOffset r).all
        (RGate.wellFormed totalWidth) = true := by
  have hwf : ∀ g ∈ r.gates,
      g.wellFormed (layout addressWidth outputWidth workspaceWidth).width = true := by
    have h := hspec.2.1
    rw [RCircuit.wellFormed, hspec.1] at h
    exact List.all_eq_true.mp h
  exact wellFormed_placeGates hdis
    (by simp [layout, placedWiring]) hbound hwf

theorem placedGates_reverse_act
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {addressOffset outputOffset workspaceOffset totalWidth I : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    (hdis : Wiring.Disjoint
      (layout addressWidth outputWidth workspaceWidth)
      (placedWiring addressOffset outputOffset workspaceOffset))
    (hbound : ∀ j, j < (layout addressWidth outputWidth workspaceWidth).length →
      (placedWiring addressOffset outputOffset workspaceOffset).getD j 0 +
          (layout addressWidth outputWidth workspaceWidth).size j ≤ totalWidth)
    (hworkspace : readField I workspaceOffset workspaceWidth = 0) :
    actGates
        (placedGates addressWidth outputWidth workspaceWidth
          addressOffset outputOffset workspaceOffset r).reverse
        (writeField I outputOffset outputWidth
          (readField I outputOffset outputWidth ^^^
            value table outputWidth
              (readField I addressOffset addressWidth))) = I := by
  rw [← placedGates_act hspec hdis hworkspace]
  exact actGates_reverse
    (placedGates_wellFormed hspec hdis hbound) I

end VQ.Lookup
