import VQ.Curve.PackedAffineSquare
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineSquareSubtract

open Reversible

def targetOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def sourceOffset : Nat := PackedAffineLayout.inverseOffset

def localLayout : Layout :=
  [256, 1, 256, 1, 1, 1, 1, 1, 1, 33, 1, 1, 8]

def wiring : Wiring :=
  [targetOffset, targetOffset + 256,
    sourceOffset, Euclid.PackedStepLayout.workTwoOffset + 256,
    Euclid.PackedStepLayout.workTwoOffset + 257,
    Euclid.PackedStepLayout.workTwoOffset + 258,
    targetOffset + 257, targetOffset + 258,
    Euclid.PackedStepLayout.lengthTOffset,
    Euclid.PackedStepLayout.lengthTOffset + 1,
    Euclid.PackedStepLayout.shiftOffset + 7,
    Euclid.PackedStepLayout.shiftOffset + 8,
    Euclid.PackedStepLayout.phaseOneWire]

def addGates : List RGate :=
  PackedReversibleSecp256k1Arithmetic.modularAddGates.map
    (RGate.map (place localLayout wiring))

def controlToggleGates : List RGate :=
  [.cx PackedAffineLayout.controlWire Euclid.PackedStepLayout.lengthTOffset]

def subtractGates : List RGate :=
  controlToggleGates ++ addGates.reverse ++ controlToggleGates

def gates : List RGate :=
  PackedAffineSquare.gates ++ subtractGates ++
    PackedAffineSquare.gates.reverse

def circuit : RCircuit := { width := PackedAffineLayout.width, gates }

theorem localLayout_width : localLayout.width =
    PackedReversibleSecp256k1Arithmetic.width := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size,
      targetOffset, sourceOffset, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.workTwoOffset,
      Euclid.PackedStepLayout.lengthTOffset,
      Euclid.PackedStepLayout.shiftOffset,
      Euclid.PackedStepLayout.phaseOneWire,
      PackedAffineLayout.inverseOffset,
      Euclid.PackedTerminalEndpoint.outputOffset,
      Euclid.PackedStepLayout.width, Euclid.PackedStepLayout.layout,
      Euclid.PackedStepLayout.workWidth,
      Euclid.PackedStepLayout.lengthWidth,
      Euclid.PackedStepLayout.remainderLengthWidth,
      Euclid.PackedStepLayout.poolWidth, Layout.width]

theorem wiring_length : localLayout.length ≤ wiring.length := by
  decide

theorem wiring_bound : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤ PackedAffineLayout.width := by
  decide +kernel

theorem addGates_wellFormed :
    addGates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply wellFormed_placeGates wiring_disjoint wiring_length wiring_bound
  intro gate hgate
  rw [localLayout_width]
  exact List.all_eq_true.mp
    PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed gate hgate

theorem controlToggleGates_wellFormed :
    controlToggleGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  decide +kernel

theorem subtractGates_wellFormed :
    subtractGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [subtractGates, controlToggleGates_wellFormed, addGates_wellFormed]

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [gates, PackedAffineSquare.gates_wellFormed,
    subtractGates_wellFormed]

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed

end VQ.Curve.PackedAffineSquareSubtract
