import VQ.Curve.PackedAffineTerminalProduct
import VQ.Curve.SevenCarryCompactProduct

namespace VQ.Curve.NarrowPackedTerminalProduct

open Reversible

def sourceGates : List RGate :=
  SevenCarryCompactProduct.sourceGates.map
    (RGate.map (place PackedAffineTerminalProduct.localLayout PackedAffineTerminalProduct.wiring))

def gates : List RGate := sourceGates.map (RGate.map (RemoveBorrowedBit.lower 570))

def circuit : RCircuit := { width := 832, gates }

theorem sourceGates_wellFormed : sourceGates.all (RGate.wellFormed 827) = true := by
  apply wellFormed_placeGates PackedAffineTerminalProduct.wiring_disjoint
    PackedAffineTerminalProduct.wiring_length PackedAffineTerminalProduct.wiring_bound_core
  intro g hg
  rw [PackedAffineTerminalProduct.localLayout_width,
    PackedReversibleSecp256k1CompactProduct.width_eq]
  exact List.all_eq_true.mp SevenCarryCompactProduct.sourceGates_wellFormed g hg

private theorem place_avoids : ∀ k, k < 815 → k ≠ 561 →
    place PackedAffineTerminalProduct.localLayout PackedAffineTerminalProduct.wiring k ≠ 570 := by
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

def workspaceMaskGates : List RGate :=
  PackedAffineTerminalProduct.workspaceMaskGates.map (RGate.map (RemoveBorrowedBit.lower 570))

def terminalGates : List RGate := workspaceMaskGates ++ gates ++ workspaceMaskGates.reverse

def terminalCircuit : RCircuit := { width := 832, gates := terminalGates }

theorem workspaceMask_avoids :
    ∀ g ∈ PackedAffineTerminalProduct.workspaceMaskGates, 570 ∉ g.wires := by
  have h : PackedAffineTerminalProduct.workspaceMaskGates.all
      (fun g => decide (570 ∉ g.wires)) = true := by native_decide
  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)

theorem workspaceMask_wellFormed : workspaceMaskGates.all (RGate.wellFormed 826) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide)
    PackedAffineTerminalProduct.workspaceMaskGates_wellFormed_core workspaceMask_avoids

theorem terminalGates_wellFormed : terminalGates.all (RGate.wellFormed 826) = true := by
  simp only [terminalGates, List.all_append, List.all_reverse,
    workspaceMask_wellFormed, gates_wellFormed, Bool.and_self]

end VQ.Curve.NarrowPackedTerminalProduct

