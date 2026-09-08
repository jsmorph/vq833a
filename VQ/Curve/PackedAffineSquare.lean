import VQ.Curve.PackedAffineLayout
import VQ.Curve.PackedReversibleSecp256k1Square
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineSquare

open Reversible

def targetOffset : Nat := PackedAffineLayout.inverseOffset

def sourceOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def localLayout : Layout :=
  [256, 1, 256, 1, 1, 1, 1, 1, 1, 33, 1, 1, 8]

def wiring : Wiring :=
  [targetOffset, Euclid.PackedStepLayout.workOneOffset + 256,
    sourceOffset, sourceOffset + 256, sourceOffset + 257,
    sourceOffset + 258, Euclid.PackedStepLayout.workOneOffset + 257,
    Euclid.PackedStepLayout.workOneOffset + 258,
    Euclid.PackedStepLayout.lengthTOffset,
    Euclid.PackedStepLayout.lengthTOffset + 1,
    Euclid.PackedStepLayout.shiftOffset + 7,
    Euclid.PackedStepLayout.shiftOffset + 8,
    Euclid.PackedStepLayout.phaseOneWire]

def gates : List RGate :=
  PackedReversibleSecp256k1Square.gates.map
    (RGate.map (place localLayout wiring))

def circuit : RCircuit := { width := PackedAffineLayout.width, gates }

theorem localLayout_width : localLayout.width =
    PackedReversibleSecp256k1Square.width := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size, targetOffset, sourceOffset,
      Euclid.PackedStepLayout.workOneOffset,
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

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply wellFormed_placeGates wiring_disjoint wiring_length wiring_bound
  intro gate hgate
  rw [localLayout_width]
  exact List.all_eq_true.mp
    PackedReversibleSecp256k1Square.gates_wellFormed gate hgate

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed

end VQ.Curve.PackedAffineSquare
