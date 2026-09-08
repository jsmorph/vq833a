import VQ.Euclid.BorrowedTerminalCanonicalization
import VQ.Euclid.LuoTerminalEndpoint

namespace VQ.Euclid.BorrowedTerminalEndpoint

open Reversible

def preparationGates : List RGate :=
  LuoTerminalEndpoint.flagGates 259 9 256 8 ++
    BorrowedTerminalCanonicalization.gates ++ LuoTerminalEndpoint.compressionGates 259 9 ++
    LuoTerminalEndpoint.flagGates 259 9 256 8

def gates : List RGate :=
  preparationGates ++ LuoTerminalEndpoint.copyGates 259 9 256 ++ preparationGates.reverse

private theorem flag_avoids :
    (LuoTerminalEndpoint.flagGates 259 9 256 8).all (fun g => decide (280 ∉ g.wires)) = true := by
  native_decide

private theorem compression_avoids :
    (LuoTerminalEndpoint.compressionGates 259 9).all (fun g => decide (280 ∉ g.wires)) = true := by
  native_decide

private theorem copy_avoids :
    (LuoTerminalEndpoint.copyGates 259 9 256).all (fun g => decide (280 ∉ g.wires)) = true := by
  native_decide

private theorem unchanged {gs : List RGate}
    (h : gs.all (fun g => decide (280 ∉ g.wires)) = true) : BorrowedEquivalent 280 gs gs :=
  BorrowedEquivalent.of_avoids (fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg))

theorem preparationGates_equiv :
    BorrowedEquivalent 280 (LuoTerminalEndpoint.preparationGates 259 9 256 8) preparationGates :=
  (((unchanged flag_avoids).append BorrowedTerminalCanonicalization.gates_equiv).append
    (unchanged compression_avoids)).append (unchanged flag_avoids)

theorem preparationGates_wellFormed : preparationGates.all (RGate.wellFormed 546) = true := by
  have hf : (LuoTerminalEndpoint.flagGates 259 9 256 8).all (RGate.wellFormed 546) = true :=
    LuoTerminalEndpoint.flagGates_wellFormed (by decide)
  have hc : (LuoTerminalEndpoint.compressionGates 259 9).all (RGate.wellFormed 546) = true :=
    LuoTerminalEndpoint.compressionGates_wellFormed (outputWidth := 256) (lengthWidth := 8) (by decide)
  have hn : BorrowedTerminalCanonicalization.gates.all (RGate.wellFormed 546) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp BorrowedTerminalCanonicalization.gates_wellFormed g hg))
  simp only [preparationGates, List.all_append, hf, hc, hn, Bool.and_self]

theorem preparationGates_reverse_equiv :
    BorrowedEquivalent 280 (LuoTerminalEndpoint.preparationGates 259 9 256 8).reverse
      preparationGates.reverse :=
  preparationGates_equiv.reverse
    (LuoTerminalEndpoint.preparationGates_wellFormed (by decide : 0 < 259)
      (by decide : 2 ≤ 9) (by decide : 8 ≤ TerminalCanonicalization.counterWidth 9))
    preparationGates_wellFormed

theorem gates_equiv : BorrowedEquivalent 280 (LuoTerminalEndpoint.gates 259 9 256 8) gates :=
  (preparationGates_equiv.append (unchanged copy_avoids)).append preparationGates_reverse_equiv

theorem gates_wellFormed : gates.all (RGate.wellFormed 546) = true := by
  have hc : (LuoTerminalEndpoint.copyGates 259 9 256).all (RGate.wellFormed 546) = true :=
    LuoTerminalEndpoint.copyGates_wellFormed (lengthWidth := 8) (by decide)
  simp only [gates, List.all_append, List.all_reverse, preparationGates_wellFormed, hc, Bool.and_self]

theorem gates_reverse_equiv :
    BorrowedEquivalent 280 (LuoTerminalEndpoint.gates 259 9 256 8).reverse gates.reverse :=
  gates_equiv.reverse
    (LuoTerminalEndpoint.gates_wellFormed (by decide : 0 < 259)
      (by decide : 2 ≤ 9) (by decide : 256 ≤ 259)
      (by decide : 8 ≤ TerminalCanonicalization.counterWidth 9)) gates_wellFormed

theorem rotationSwapCount : LuoSelectionPermutation.sourceRotationSwapCount 259 10 = 2580 := by
  native_decide

theorem canonicalizationGates_ccx : BorrowedTerminalCanonicalization.gates.countP RGate.isCcx =
    (LuoTerminalCanonicalization.gates 259 9).countP RGate.isCcx + 7720 := by
  have h := BorrowedTerminalCanonicalization.gates_ccx
  rw [rotationSwapCount] at h
  omega

theorem preparationGates_ccx : preparationGates.countP RGate.isCcx =
    (LuoTerminalEndpoint.preparationGates 259 9 256 8).countP RGate.isCcx + 7720 := by
  simp only [preparationGates, LuoTerminalEndpoint.preparationGates, List.countP_append,
    canonicalizationGates_ccx]
  omega

theorem gates_ccx : gates.countP RGate.isCcx =
    (LuoTerminalEndpoint.gates 259 9 256 8).countP RGate.isCcx + 15440 := by
  simp only [gates, LuoTerminalEndpoint.gates, List.countP_append, List.countP_reverse,
    preparationGates_ccx]
  omega

end VQ.Euclid.BorrowedTerminalEndpoint
