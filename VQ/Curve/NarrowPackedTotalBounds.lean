import VQ.Curve.NarrowPackedArithmeticBounds

namespace VQ.Curve.NarrowPackedRetainedMultiplication

open Reversible
open NarrowPackedRetainedDivision (gateOps lowerGates)

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level) : program.wellFormed level = true := by
  have hp : (lowerGates PackedFieldInversion.prepareGates).all (RGate.wellFormed 832) = true :=
    NarrowPackedOperands.wellFormed NarrowPackedOperands.prepare PackedFieldInversion.prepareGates_wellFormed
  have hr : (lowerGates PackedFieldInversion.restoreGates).all (RGate.wellFormed 832) = true :=
    NarrowPackedOperands.wellFormed NarrowPackedOperands.restore PackedFieldInversion.restoreGates_wellFormed
  change Program.opsWellFormed level 832 0 256 totalMultiplicationOps = true
  simp only [totalMultiplicationOps, gateOps, Program.opsWellFormed_append,
    Lookup3.gateOps_wellFormed hl NarrowPackedRetainedDivision.numeratorMove_wellFormed,
    Lookup3.gateOps_wellFormed hl hp, selectedMultiplication_wellFormed hl,
    Lookup3.gateOps_wellFormed hl hr,
    Lookup3.gateOps_wellFormed hl NarrowPackedRetainedDivision.quotientMove_wellFormed,
    Bool.and_self]

end VQ.Curve.NarrowPackedRetainedMultiplication
