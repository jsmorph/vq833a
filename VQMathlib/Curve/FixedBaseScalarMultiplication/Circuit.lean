import VQMathlib.Curve.FixedBaseScalarMultiplication.Math
import VQMathlib.Curve.GroupTotalPointAddition.Control
import VQ.Reversible.Constant

namespace VQ.Tests.FixedBaseScalarMultiplication

open VQ VQ.Reversible
open VQ.Curve.PointAddition.Runtime
open GroupTotalPointAddition

def scalarControl : Nat := groupPointAddWidth

def scalarDecomposition : Nat := groupPointAddWidth + 1

def scalarOffset : Nat := groupPointAddWidth + 2

def offsetLoad (point : Nat) : List RGate :=
  constantXorGates point context pointWidth

def scalarStepGates (scalarWire point : Nat) : List RGate :=
  offsetLoad point ++ [.cx scalarWire scalarControl] ++
    controlledGroupCircuit.gates ++ [.cx scalarWire scalarControl] ++
    offsetLoad point

def scalarGatesAux : Nat → List Nat → List RGate
  | _, [] => []
  | scalarWire, point :: rest =>
      scalarStepGates scalarWire point ++ scalarGatesAux (scalarWire + 1) rest

def scalarGates (table : List Nat) : List RGate :=
  scalarGatesAux scalarOffset table

def scalarCircuit (table : List Nat) : RCircuit :=
  { width := scalarOffset + table.length, gates := scalarGates table }

def fixedBaseCircuit (width point : Nat) : RCircuit :=
  scalarCircuit (powerTable width point)

theorem scalarCircuit_gates (table : List Nat) :
    (scalarCircuit table).gates = scalarGates table := rfl

theorem scalarCircuit_width (table : List Nat) :
    (scalarCircuit table).width = scalarOffset + table.length := rfl

theorem powerTable_length (width point : Nat) :
    (powerTable width point).length = width := by
  induction width generalizing point with
  | zero => rfl
  | succ width ih => simp [powerTable, ih]

theorem fixedBaseCircuit_width (width point : Nat) :
    (fixedBaseCircuit width point).width = scalarOffset + width := by
  simp [fixedBaseCircuit, scalarCircuit_width, powerTable_length]

theorem offsetLoad_wf {point total : Nat} (htotal : groupPointAddWidth + 2 ≤ total) :
    (offsetLoad point).all (RGate.wellFormed total) = true := by
  apply constantXorGates_wellFormed
  exact Nat.le_trans (by decide : context + pointWidth ≤ groupPointAddWidth + 2) htotal

theorem controlledGroupGates_wf {total : Nat}
    (htotal : groupPointAddWidth + 2 ≤ total) :
    controlledGroupCircuit.gates.all (RGate.wellFormed total) = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  exact RGate.wellFormed_mono htotal
    (RCircuit.wellFormed_mem controlledGroupCircuit_wf hgate)

theorem scalarStepGates_wf {scalarWire point total : Nat}
    (hscalar : scalarOffset ≤ scalarWire) (hbound : scalarWire < total) :
    (scalarStepGates scalarWire point).all (RGate.wellFormed total) = true := by
  change groupPointAddWidth + 2 ≤ scalarWire at hscalar
  have htotal : groupPointAddWidth + 2 ≤ total := by
    exact Nat.le_trans hscalar (Nat.le_of_lt hbound)
  simp only [scalarStepGates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨offsetLoad_wf htotal, ?_⟩, controlledGroupGates_wf htotal⟩, ?_⟩,
    offsetLoad_wf htotal⟩
  · simp [RGate.wellFormed, scalarControl]
    omega
  · simp [RGate.wellFormed, scalarControl]
    omega

theorem scalarGatesAux_wf {scalarWire total : Nat} {table : List Nat}
    (hscalar : scalarOffset ≤ scalarWire)
    (hbound : scalarWire + table.length ≤ total) :
    (scalarGatesAux scalarWire table).all (RGate.wellFormed total) = true := by
  induction table generalizing scalarWire with
  | nil => rfl
  | cons point rest ih =>
      rw [scalarGatesAux, List.all_append, Bool.and_eq_true]
      constructor
      · apply scalarStepGates_wf hscalar
        simp only [List.length_cons] at hbound
        omega
      · apply ih (by omega)
        simp only [List.length_cons] at hbound
        omega

theorem scalarCircuit_wf (table : List Nat) :
    (scalarCircuit table).wellFormed = true := by
  exact scalarGatesAux_wf (Nat.le_refl scalarOffset) (Nat.le_refl _)

theorem fixedBaseCircuit_wf (width point : Nat) :
    (fixedBaseCircuit width point).wellFormed = true :=
  scalarCircuit_wf (powerTable width point)

end VQ.Tests.FixedBaseScalarMultiplication
