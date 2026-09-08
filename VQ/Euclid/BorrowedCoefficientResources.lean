import VQ.Euclid.BorrowedCoefficient

namespace VQ.Euclid.BorrowedCoefficient

open Reversible

theorem gates_wellFormed : gates.all (RGate.wellFormed 558) = true := by
  native_decide

theorem gates_ccx : gates.countP RGate.isCcx =
    CompactCoefficientDirty.gates.countP RGate.isCcx + 1028 := by
  native_decide

theorem gates_reverse_clear (I : Nat) :
    writeField (actGates gates.reverse I) borrowed 1 0 =
      actGates CompactCoefficientDirty.gates.reverse (writeField I borrowed 1 0) :=
  actGates_reverse_clear_bit gates_wellFormed CompactCoefficientDirty.circuit_wellFormed gates_clear I

theorem gates_reverse_preserves (I : Nat) :
    (actGates gates.reverse I).testBit borrowed = I.testBit borrowed :=
  actGates_reverse_preserves_bit gates_wellFormed gates_preserves I

theorem gates_reverse_act (I : Nat) :
    actGates gates.reverse I = writeField
      (actGates CompactCoefficientDirty.gates.reverse (writeField I borrowed 1 0))
      borrowed 1 (bitValue I borrowed) :=
  eq_write_of_clear_bit (gates_reverse_clear I) (gates_reverse_preserves I)

end VQ.Euclid.BorrowedCoefficient
