import VQ.Euclid.PackedInputPreparation
import VQ.Euclid.BorrowedPackedRoundResources
import VQ.Curve.Field

namespace VQ.Euclid.BorrowedPreparedSchedule

open Reversible

def gates : List RGate :=
  PackedInputPreparation.gates Curve.p ++ BorrowedPackedRound.roundsGates 1620

theorem preparation_below :
    (PackedInputPreparation.gates Curve.p).all (RGate.wellFormed 570) = true := by native_decide

theorem preparation_equiv :
    BorrowedEquivalent 570 (PackedInputPreparation.gates Curve.p) (PackedInputPreparation.gates Curve.p) :=
  BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp preparation_below g hg) hq)

theorem gates_equiv :
    BorrowedEquivalent 570
      (PackedInputPreparation.gates Curve.p ++ LuoWindowedOwnership.roundsGates 1620) gates :=
  preparation_equiv.append (BorrowedPackedRound.roundsGates_equiv (by decide))

theorem gates_wellFormed : gates.all (RGate.wellFormed 571) = true := by
  have hp : (PackedInputPreparation.gates Curve.p).all (RGate.wellFormed 571) = true :=
    PackedInputPreparation.gates_wellFormed Curve.p
  simp only [gates, List.all_append, hp,
    BorrowedPackedRound.roundsGates_wellFormed (by decide : 1620 ≤ 1620),
    Bool.and_self]

theorem gates_reverse_equiv :
    BorrowedEquivalent 570
      (PackedInputPreparation.gates Curve.p ++ LuoWindowedOwnership.roundsGates 1620).reverse
      gates.reverse := by
  apply gates_equiv.reverse (w := 571) (v := 571) _ gates_wellFormed
  have hp : (PackedInputPreparation.gates Curve.p).all (RGate.wellFormed 571) = true :=
    PackedInputPreparation.gates_wellFormed Curve.p
  have hr : (LuoWindowedOwnership.roundsGates 1620).all (RGate.wellFormed 571) = true :=
    LuoWindowedOwnership.roundsGates_wellFormed (by decide)
  simp only [List.all_append, hp, hr, Bool.and_self]

theorem gates_ccx : gates.countP RGate.isCcx =
    (PackedInputPreparation.gates Curve.p ++ LuoWindowedOwnership.roundsGates 1620).countP
      RGate.isCcx + 7341124 := by
  simp only [gates, List.countP_append, BorrowedPackedRound.fullSchedule_ccx]
  omega

end VQ.Euclid.BorrowedPreparedSchedule
