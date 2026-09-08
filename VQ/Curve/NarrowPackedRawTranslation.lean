import VQ.Curve.NarrowPackedTotalBounds

namespace VQ.Curve.NarrowPackedRawTranslation

open Reversible
open NarrowPackedRetainedDivision (gateOps lowerGates)

def ops (ax ay : Nat) : List Op :=
  gateOps (lowerGates (PackedAffineConstantAddition.unconditionalGates (Curve.neg ax))) ++
    gateOps (lowerGates (PackedAffineSecondConstantSubtraction.gates ay)) ++
    NarrowPackedRetainedDivision.totalDivisionOps ++
    gateOps (lowerGates PackedAffineSquareSubtract.gates) ++
    gateOps (lowerGates (PackedAffineConstantAddition.gates (Curve.mul 3 ax))) ++
    NarrowPackedRetainedMultiplication.totalMultiplicationOps ++
    gateOps (lowerGates PackedAffineNegation.gates) ++
    gateOps (lowerGates (PackedAffineConstantAddition.unconditionalGates ax)) ++
    gateOps (lowerGates (PackedAffineSecondConstantSubtraction.gates ay))

def program (ax ay : Nat) : Program := { width := 832, cbits := 256, ops := ops ax ay }

theorem unconditionalAddition_wellFormed (constant : Nat) :
    (lowerGates (PackedAffineConstantAddition.unconditionalGates constant)).all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed (NarrowPackedOperands.unconditionalAdd constant)
    (PackedAffineConstantAddition.unconditionalGates_wellFormed constant)

theorem secondSubtraction_wellFormed (constant : Nat) :
    (lowerGates (PackedAffineSecondConstantSubtraction.gates constant)).all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed (NarrowPackedOperands.secondSubtract constant)
    (PackedAffineSecondConstantSubtraction.gates_wellFormed constant)

theorem squareSubtraction_wellFormed :
    (lowerGates PackedAffineSquareSubtract.gates).all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed NarrowPackedOperands.squareSubtract PackedAffineSquareSubtract.gates_wellFormed

theorem controlledAddition_wellFormed (constant : Nat) :
    (lowerGates (PackedAffineConstantAddition.gates constant)).all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed (NarrowPackedOperands.constantAdd constant)
    (PackedAffineConstantAddition.gates_wellFormed constant)

theorem negation_wellFormed :
    (lowerGates PackedAffineNegation.gates).all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed NarrowPackedOperands.negation PackedAffineNegation.gates_wellFormed

theorem program_wellFormed {level ax ay : Nat} (hl : 3 ≤ level) :
    (program ax ay).wellFormed level = true := by
  have hd := NarrowPackedRetainedDivision.program_wellFormed hl
  have hm := NarrowPackedRetainedMultiplication.program_wellFormed hl
  change Program.opsWellFormed level 832 0 256 NarrowPackedRetainedDivision.totalDivisionOps = true at hd
  change Program.opsWellFormed level 832 0 256 NarrowPackedRetainedMultiplication.totalMultiplicationOps = true at hm
  change Program.opsWellFormed level 832 0 256 (ops ax ay) = true
  simp only [ops, gateOps, Program.opsWellFormed_append,
    Lookup3.gateOps_wellFormed hl (unconditionalAddition_wellFormed _),
    Lookup3.gateOps_wellFormed hl (secondSubtraction_wellFormed _), hd,
    Lookup3.gateOps_wellFormed hl squareSubtraction_wellFormed,
    Lookup3.gateOps_wellFormed hl (controlledAddition_wellFormed _), hm,
    Lookup3.gateOps_wellFormed hl negation_wellFormed, Bool.and_self]

end VQ.Curve.NarrowPackedRawTranslation
