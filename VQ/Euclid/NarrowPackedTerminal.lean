import VQ.Euclid.BorrowedTerminalEndpoint
import VQ.Euclid.PackedTerminalEndpoint
import VQ.Reversible.RemoveBorrowedBit

namespace VQ.Euclid.NarrowPackedTerminal

open Reversible PackedTerminalEndpoint

def oldPreparation : List RGate :=
  (LuoTerminalEndpoint.preparationGates 259 9 256 8).map
    (RGate.map (place endpointLayout endpointWiring))

def preparationGates : List RGate :=
  BorrowedTerminalEndpoint.preparationGates.map
    (RGate.map (place endpointLayout endpointWiring))

def oldCopy : List RGate :=
  (LuoTerminalEndpoint.copyGates 259 9 256).map
    (RGate.map (place endpointLayout endpointWiring))

def copyGates : List RGate := oldCopy.map (RGate.map (RemoveBorrowedBit.lower 570))

def signGates : List RGate :=
  PackedTerminalEndpoint.signGates.map (RGate.map (RemoveBorrowedBit.lower 570))

def gates : List RGate := preparationGates ++ copyGates ++ preparationGates.reverse ++ signGates

theorem oldSource : PackedTerminalEndpoint.gates =
    oldPreparation ++ oldCopy ++ oldPreparation.reverse ++ PackedTerminalEndpoint.signGates := by
  simp only [PackedTerminalEndpoint.gates, endpointGates, LuoTerminalEndpoint.gates,
    List.map_append, List.map_reverse, oldPreparation, oldCopy]

theorem oldPreparation_below : oldPreparation.all (RGate.wellFormed 571) = true := by native_decide

theorem preparationGates_below : preparationGates.all (RGate.wellFormed 571) = true := by native_decide

theorem preparationGates_borrowed : BorrowedEquivalent 570 oldPreparation preparationGates :=
  BorrowedTerminalEndpoint.preparationGates_equiv.map (place_inj (by decide) endpointWiring_disjoint)
    (List.all_eq_true.mp (LuoTerminalEndpoint.preparationGates_wellFormed (by decide : 0 < 259)
      (by decide : 2 ≤ 9) (by decide : 8 ≤ TerminalCanonicalization.counterWidth 9)))
    (List.all_eq_true.mp BorrowedTerminalEndpoint.preparationGates_wellFormed) (by decide)

theorem preparationGates_equiv : RemoveBorrowedBit.Equivalent 570 oldPreparation preparationGates :=
  RemoveBorrowedBit.borrowed_core preparationGates_borrowed oldPreparation_below preparationGates_below

private theorem copy_avoids : oldCopy.all (fun g => decide (570 ∉ g.wires)) = true := by native_decide

private theorem sign_avoids :
    PackedTerminalEndpoint.signGates.all (fun g => decide (570 ∉ g.wires)) = true := by native_decide

theorem copyGates_equiv : RemoveBorrowedBit.Equivalent 570 oldCopy copyGates :=
  RemoveBorrowedBit.gates_equivalent
    (fun g hg => of_decide_eq_true (List.all_eq_true.mp copy_avoids g hg))

theorem signGates_equiv :
    RemoveBorrowedBit.Equivalent 570 PackedTerminalEndpoint.signGates signGates :=
  RemoveBorrowedBit.gates_equivalent
    (fun g hg => of_decide_eq_true (List.all_eq_true.mp sign_avoids g hg))

theorem gates_equiv : RemoveBorrowedBit.Equivalent 570 PackedTerminalEndpoint.gates gates := by
  rw [oldSource]
  exact RemoveBorrowedBit.append
    (RemoveBorrowedBit.append (RemoveBorrowedBit.append preparationGates_equiv copyGates_equiv)
      (RemoveBorrowedBit.reverse preparationGates_equiv oldPreparation_below preparationGates_below))
    signGates_equiv

theorem copyGates_wellFormed : copyGates.all (RGate.wellFormed 826) = true := by
  have hc : oldCopy.all (RGate.wellFormed 827) = true := by native_decide
  exact RemoveBorrowedBit.gates_wellFormed (by decide) hc
    (fun g hg => of_decide_eq_true (List.all_eq_true.mp copy_avoids g hg))

theorem signGates_wellFormed : signGates.all (RGate.wellFormed 826) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide) PackedTerminalEndpoint.signGates_wellFormed
    (fun g hg => of_decide_eq_true (List.all_eq_true.mp sign_avoids g hg))

theorem gates_wellFormed : gates.all (RGate.wellFormed 826) = true := by
  have hp : preparationGates.all (RGate.wellFormed 826) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp preparationGates_below g hg))
  simp only [gates, List.all_append, List.all_reverse, hp,
    copyGates_wellFormed, signGates_wellFormed, Bool.and_self]

theorem preparationGates_ccx : preparationGates.countP RGate.isCcx =
    oldPreparation.countP RGate.isCcx + 7720 := by
  simp only [preparationGates, oldPreparation, countP_map_gates (RGate.isCcx_map _),
    BorrowedTerminalEndpoint.preparationGates_ccx]

theorem gates_ccx : gates.countP RGate.isCcx =
    PackedTerminalEndpoint.gates.countP RGate.isCcx + 15440 := by
  rw [oldSource]
  simp only [gates, List.countP_append, List.countP_reverse, preparationGates_ccx,
    copyGates, signGates, countP_map_gates (RGate.isCcx_map _)]
  omega

end VQ.Euclid.NarrowPackedTerminal
