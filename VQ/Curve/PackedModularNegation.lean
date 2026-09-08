import VQ.Curve.PackedModularAddition

namespace VQ.Curve.PackedModularNegation

open Reversible Semantics
open VQ.Curve.PackedModularProduct

def complementGates (wordWidth : Nat) : List RGate :=
  constantXorGates (2 ^ wordWidth - 1) 0 wordWidth

def complementOps (wordWidth : Nat) : List Op :=
  gateOps (complementGates wordWidth)

def negationOps (modulus wordWidth : Nat) : List Op :=
  complementOps wordWidth ++ constantAddOps (modulus + 1) wordWidth

def program (modulus wordWidth : Nat) : Program :=
  { width := adderWidth wordWidth
    cbits := wordWidth - 1
    ops := negationOps modulus wordWidth }

theorem complementGates_wellFormed {wordWidth : Nat} :
    (complementGates wordWidth).all
      (RGate.wellFormed (adderWidth wordWidth)) = true := by
  exact constantXorGates_wellFormed (by simp [adderWidth]; omega)

theorem complementOps_wellFormed
    {level wordWidth : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level (adderWidth wordWidth) 0 (wordWidth - 1)
      (complementOps wordWidth) = true := by
  simpa [complementOps, gateOps] using Lookup3.gateOps_wellFormed
    (iw := 0) (cw := wordWidth - 1) hl
      (complementGates_wellFormed (wordWidth := wordWidth))

theorem negationOps_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    Program.opsWellFormed level (adderWidth wordWidth) 0 (wordWidth - 1)
      (negationOps modulus wordWidth) = true := by
  rw [negationOps, Program.opsWellFormed_append,
    complementOps_wellFormed hl, constantAddOps_wellFormed hl hwidth]
  rfl

theorem program_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    (program modulus wordWidth).wellFormed level = true := by
  exact negationOps_wellFormed hl hwidth

end VQ.Curve.PackedModularNegation
