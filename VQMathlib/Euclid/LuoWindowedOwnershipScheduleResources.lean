import VQMathlib.Euclid.LuoWindowedOwnershipFixedResources
import VQMathlib.Euclid.LuoOwnershipCost

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

def roundToffoli (step : Nat) : Nat :=
  roundFixedToffoli + windowedOwnershipToffoli step

theorem roundToffoliSchedule_eq (rounds : Nat) :
    ((List.range rounds).map (fun index => roundToffoli (index + 1))).sum =
      rounds * roundFixedToffoli +
        ((List.range rounds).map (fun index =>
          windowedOwnershipToffoli (index + 1))).sum := by
  simpa only [roundToffoli, List.length_range] using
    sum_map_add_left roundFixedToffoli
      (fun index => windowedOwnershipToffoli (index + 1))
      (List.range rounds)

theorem roundScheduleToffoli_eq :
    1620 * roundFixedToffoli + windowedOwnershipScheduleToffoli =
      267092220 := by
  rw [roundFixedToffoli_eq, windowedOwnershipScheduleToffoli_eq]

end VQMathlib.LuoSchedule.WindowedOwnership
