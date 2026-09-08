import VQ.Curve.PackedAffineInputProduct
import VQ.Curve.SevenCarryCompactProduct

namespace VQ.Curve.NarrowPackedInputProduct

open Reversible

def sourceGates : List RGate :=
  SevenCarryCompactProduct.sourceGates.map
    (RGate.map (place PackedAffineInputProduct.localLayout PackedAffineInputProduct.wiring))

def gates : List RGate := sourceGates.map (RGate.map (RemoveBorrowedBit.lower 570))

def circuit : RCircuit := { width := 832, gates }

theorem sourceGates_wellFormed : sourceGates.all (RGate.wellFormed 827) = true := by
  apply wellFormed_placeGates PackedAffineInputProduct.wiring_disjoint
    PackedAffineInputProduct.wiring_length PackedAffineInputProduct.wiring_bound_core
  intro g hg
  rw [PackedAffineInputProduct.localLayout_width,
    PackedReversibleSecp256k1CompactProduct.width_eq]
  exact List.all_eq_true.mp SevenCarryCompactProduct.sourceGates_wellFormed g hg

private theorem place_avoids : ∀ k, k < 815 → k ≠ 561 →
    place PackedAffineInputProduct.localLayout PackedAffineInputProduct.wiring k ≠ 570 := by
  native_decide

theorem sourceGates_avoids : ∀ g ∈ sourceGates, 570 ∉ g.wires := by
  intro g hg hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map] at hq
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hq
  exact place_avoids k
    (wire_lt_of_wellFormed (List.all_eq_true.mp
      SevenCarryCompactProduct.sourceGates_wellFormed s hs) hk)
    (fun h => SevenCarryCompactProduct.sourceGates_avoids s hs (h ▸ hk)) he

theorem gates_wellFormed : gates.all (RGate.wellFormed 826) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide) sourceGates_wellFormed sourceGates_avoids

theorem gates_equiv : RemoveBorrowedBit.Equivalent 570 sourceGates gates :=
  RemoveBorrowedBit.gates_equivalent sourceGates_avoids

end VQ.Curve.NarrowPackedInputProduct

