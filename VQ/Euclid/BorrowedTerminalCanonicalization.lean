import VQ.Euclid.LuoTerminalCanonicalization
import VQ.Reversible.BorrowedPermutationProjection

namespace VQ.Euclid.BorrowedTerminalCanonicalization

open Reversible LuoSelectionPermutation

def rotationBlock (j : Nat) : List RGate :=
  BorrowedPermutation.swaps 281 (259 + j) 280
    (selectionSwaps 259 (barrelAmount 259 j))

def rotationGates : Nat → List RGate
  | 0 => []
  | count + 1 => rotationGates count ++ rotationBlock count

def gates : List RGate :=
  TerminalCanonicalization.decodeGates 259 9 ++ rotationGates 10 ++
    (TerminalCanonicalization.decodeGates 259 9).reverse

private theorem valid {j : Nat} (hj : j < 10) :
    ∀ p ∈ selectionSwaps 259 (barrelAmount 259 j), BorrowedPermutation.Valid 281 (259 + j) 280 p := by
  intro p hp
  obtain ⟨hx, hy, hxy⟩ := selectionSwaps_valid (by decide : 0 < 259) p hp
  unfold BorrowedPermutation.Valid
  omega

theorem rotationBlock_equiv {j : Nat} (hj : j < 10) :
    BorrowedEquivalent 280
      (jointControlledSwaps 281 (259 + j) 280 0
        (selectionSwaps 259 (barrelAmount 259 j))) (rotationBlock j) := by
  have h := BorrowedPermutation.sharedSwaps_equiv (by omega) (by decide) (by omega) (valid hj)
  simpa only [jointControlledSwaps, jointCompute, controlledSwaps,
    BorrowedPermutation.sharedSwaps, List.reverse_singleton, Nat.zero_add, rotationBlock] using h

theorem rotationGates_equiv {count : Nat} (hc : count ≤ 10) :
    BorrowedEquivalent 280 (sourceRotationGates 281 259 280 0 259 count) (rotationGates count) := by
  induction count with
  | zero => exact BorrowedEquivalent.nil _
  | succ count ih => exact (ih (by omega)).append (rotationBlock_equiv (by omega))

private theorem decode_below :
    (TerminalCanonicalization.decodeGates 259 9).all (RGate.wellFormed 280) = true :=
  TerminalCanonicalization.decodeGates_wellFormed 259 9

theorem gates_equiv : BorrowedEquivalent 280 (LuoTerminalCanonicalization.gates 259 9) gates := by
  have hd := BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp decode_below g hg) hq)
  exact (hd.append (rotationGates_equiv (by decide))).append (hd.reverse decode_below decode_below)

theorem rotationBlock_wellFormed {j : Nat} (hj : j < 10) :
    (rotationBlock j).all (RGate.wellFormed 282) = true := by
  apply BorrowedPermutation.swaps_wellFormed (by decide) (by omega) (by decide)
    (by omega) (by decide) (by omega)
  intro p hp
  obtain ⟨hx, hy, _⟩ := selectionSwaps_valid (by decide : 0 < 259) p hp
  exact ⟨valid hj p hp, by omega, by omega⟩

theorem rotationGates_wellFormed {count : Nat} (hc : count ≤ 10) :
    (rotationGates count).all (RGate.wellFormed 282) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [rotationGates, List.all_append, Bool.and_eq_true]
    exact ⟨ih (by omega), rotationBlock_wellFormed (by omega)⟩

theorem gates_wellFormed : gates.all (RGate.wellFormed 282) = true := by
  have hd : (TerminalCanonicalization.decodeGates 259 9).all (RGate.wellFormed 282) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp decode_below g hg))
  simp only [gates, List.all_append, List.all_reverse, hd,
    rotationGates_wellFormed (by decide : 10 ≤ 10), Bool.and_self]

theorem gates_reverse_equiv :
    BorrowedEquivalent 280 (LuoTerminalCanonicalization.gates 259 9).reverse gates.reverse :=
  gates_equiv.reverse (LuoTerminalCanonicalization.gates_wellFormed (by decide : 0 < 259))
    gates_wellFormed

theorem rotationGates_ccx (count : Nat) :
    (rotationGates count).countP RGate.isCcx = 4 * sourceRotationSwapCount 259 count := by
  induction count with
  | zero => simp [rotationGates, sourceRotationSwapCount]
  | succ count ih =>
    simp only [rotationGates, rotationBlock, List.countP_append, BorrowedPermutation.swaps_ccx,
      sourceRotationSwapCount_succ, ih]
    omega

theorem gates_ccx : gates.countP RGate.isCcx + 20 =
    (LuoTerminalCanonicalization.gates 259 9).countP RGate.isCcx +
      3 * sourceRotationSwapCount 259 10 := by
  simp only [gates, LuoTerminalCanonicalization.gates, List.countP_append, List.countP_reverse,
    LuoTerminalCanonicalization.rotationGates, sourceRotationGates_ccx, rotationGates_ccx,
    TerminalCanonicalization.counterWidth]
  norm_num only
  omega

end VQ.Euclid.BorrowedTerminalCanonicalization
