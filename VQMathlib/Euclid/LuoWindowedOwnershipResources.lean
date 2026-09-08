import VQMathlib.Euclid.LuoWindowedOwnershipCircuitResources

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

theorem roundsGatesFrom_ccx (first rounds : Nat) :
    (roundsGatesFrom first rounds).countP RGate.isCcx =
      ((List.range' first rounds).map roundToffoli).sum :=
  roundsGatesFrom_countP_of RGate.isCcx roundToffoli roundGates_ccx
    first rounds

theorem range'_one_eq_map_succ (count : Nat) :
    List.range' 1 count = (List.range count).map (fun index => index + 1) := by
  rw [show 1 = 0 + 1 by rfl, List.range'_succ_left,
    ← List.range_eq_range']

theorem roundsGates_ccx (rounds : Nat) :
    (roundsGates rounds).countP RGate.isCcx =
      ((List.range rounds).map (fun index => roundToffoli (index + 1))).sum := by
  rw [roundsGates, roundsGatesFrom_ccx, range'_one_eq_map_succ,
    List.map_map]
  rfl

end VQMathlib.LuoSchedule.WindowedOwnership
