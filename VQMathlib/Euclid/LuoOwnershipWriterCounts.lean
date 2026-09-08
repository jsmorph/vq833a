import VQ.Euclid.LuoOwnershipWindows
import VQMathlib.Euclid.LengthWriterBitCounts

namespace VQMathlib.LuoSchedule.OwnershipWriterCounts

open VQ VQ.Euclid VQ.Reversible
open VQ.Euclid.LuoWindowedOwnership
open VQMathlib.Euclid.LengthWriterCounts
open VQMathlib.Euclid.LengthWriterBitCounts

def upperCount (step : Nat) : Nat :=
  2 * dirtyCountFormula (ownershipUpperWorkWidth step) +
    2 * (68 * ownershipUpperWorkWidth step - 4)

def lowerCount (step : Nat) : Nat :=
  2 * dirtyCountFormula (ownershipLowerWorkWidth step) +
    2 * (68 * ownershipLowerWorkWidth step - 4)

theorem upperCount_eq (step : Nat) :
    (LengthWriter.upperGates 1 (ownershipUpperWorkWidth step) 9).countP
      RGate.isCcx = upperCount step := by
  rw [upperGates_ccx, upper_dirtyCount_eq
    (show ownershipUpperWorkWidth step ≤ 259 by
      unfold ownershipUpperWorkWidth
      omega)]
  rfl

theorem lowerCount_eq (step : Nat) :
    (LengthWriter.lowerGates 256 (ownershipLowerSource step + 1)
      (ownershipLowerWorkWidth step) 9).countP RGate.isCcx = lowerCount step := by
  rw [lowerGates_ccx]
  simp only [ownershipLowerWorkWidth, lower_dirtyCount_eq, lowerCount]

set_option maxRecDepth 8192 in
theorem schedule_eq :
    ((List.range 1620).map (fun index =>
      512 + (2 * upperCount (index + 1) + 2 * lowerCount (index + 1)))).sum =
        141696120 := by
  decide +kernel

end VQMathlib.LuoSchedule.OwnershipWriterCounts
