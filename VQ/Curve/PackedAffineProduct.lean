import VQ.Curve.PackedAffineLayout
import VQ.Curve.PackedReversibleSecp256k1Arithmetic
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineProduct

open Reversible

def targetOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def sourceOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def multiplierOffset : Nat := PackedAffineLayout.inverseOffset

def localLayout : Layout :=
  [256, 1, 256, 1, 1, 1, 1, 1, 1, 33, 1, 1, 8, 256]

def wiring : Wiring :=
  [targetOffset, targetOffset + 256,
    sourceOffset, sourceOffset + 256, sourceOffset + 257,
    sourceOffset + 258, targetOffset + 257, targetOffset + 258,
    Euclid.PackedStepLayout.lengthTOffset,
    Euclid.PackedStepLayout.lengthTOffset + 1,
    Euclid.PackedStepLayout.shiftOffset + 7,
    Euclid.PackedStepLayout.shiftOffset + 8,
    Euclid.PackedStepLayout.phaseOneWire,
    multiplierOffset]

def gates : List RGate :=
  PackedReversibleSecp256k1Arithmetic.modularProductGates.map
    (RGate.map (place localLayout wiring))

def circuit : RCircuit := { width := PackedAffineLayout.width, gates }

def coreCircuit : RCircuit :=
  { width := PackedAffineLayout.auxiliaryOffset, gates }

theorem localLayout_width : localLayout.width =
    PackedReversibleSecp256k1Arithmetic.productWidth := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size, targetOffset, sourceOffset,
      multiplierOffset, Euclid.PackedStepLayout.workOneOffset,
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

theorem wiring_bound_core : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤
      PackedAffineLayout.auxiliaryOffset := by
  decide +kernel

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply wellFormed_placeGates wiring_disjoint wiring_length wiring_bound
  intro gate hgate
  rw [localLayout_width]
  exact List.all_eq_true.mp
    PackedReversibleSecp256k1Arithmetic.modularProductGates_wellFormed
      gate hgate

theorem gates_wellFormed_core :
    gates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  apply wellFormed_placeGates wiring_disjoint wiring_length wiring_bound_core
  intro gate hgate
  rw [localLayout_width]
  exact List.all_eq_true.mp
    PackedReversibleSecp256k1Arithmetic.modularProductGates_wellFormed
      gate hgate

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed

theorem coreCircuit_wellFormed : coreCircuit.wellFormed = true := by
  simpa only [coreCircuit, RCircuit.wellFormed] using gates_wellFormed_core

end VQ.Curve.PackedAffineProduct
