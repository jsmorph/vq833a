import VQMathlib.Curve.FixedBaseScalarMultiplication.Circuit

namespace VQ.Tests.TwoScalarMultiplication

open VQ.Reversible
open FixedBaseScalarMultiplication

def secondScalarOffset (tableP : List Nat) : Nat :=
  scalarOffset + tableP.length

def twoScalarGates (tableP tableQ : List Nat) : List RGate :=
  scalarGatesAux scalarOffset tableP ++
    scalarGatesAux (secondScalarOffset tableP) tableQ

def twoScalarCircuit (tableP tableQ : List Nat) : RCircuit :=
  { width := scalarOffset + tableP.length + tableQ.length
    gates := twoScalarGates tableP tableQ }

def twoFixedBaseCircuit (widthP widthQ pointP pointQ : Nat) : RCircuit :=
  twoScalarCircuit (powerTable widthP pointP) (powerTable widthQ pointQ)

theorem twoScalarCircuit_gates (tableP tableQ : List Nat) :
    (twoScalarCircuit tableP tableQ).gates = twoScalarGates tableP tableQ := rfl

theorem twoScalarCircuit_width (tableP tableQ : List Nat) :
    (twoScalarCircuit tableP tableQ).width =
      scalarOffset + tableP.length + tableQ.length := rfl

theorem scalarFields_adjacent (tableP : List Nat) :
    scalarOffset + tableP.length = secondScalarOffset tableP := rfl

theorem scalarFields_end_at_width (tableP tableQ : List Nat) :
    secondScalarOffset tableP + tableQ.length =
      (twoScalarCircuit tableP tableQ).width := by
  simp [secondScalarOffset, twoScalarCircuit_width]

theorem twoFixedBaseCircuit_width (widthP widthQ pointP pointQ : Nat) :
    (twoFixedBaseCircuit widthP widthQ pointP pointQ).width =
      scalarOffset + widthP + widthQ := by
  simp [twoFixedBaseCircuit, twoScalarCircuit_width, powerTable_length]

theorem twoScalarCircuit_wf (tableP tableQ : List Nat) :
    (twoScalarCircuit tableP tableQ).wellFormed = true := by
  simp only [RCircuit.wellFormed, twoScalarCircuit, twoScalarGates,
    List.all_append, Bool.and_eq_true]
  constructor
  · apply scalarGatesAux_wf (Nat.le_refl scalarOffset)
    omega
  · apply scalarGatesAux_wf
    · simp [secondScalarOffset]
    · simp [secondScalarOffset]

theorem twoFixedBaseCircuit_wf (widthP widthQ pointP pointQ : Nat) :
    (twoFixedBaseCircuit widthP widthQ pointP pointQ).wellFormed = true :=
  twoScalarCircuit_wf _ _

end VQ.Tests.TwoScalarMultiplication
