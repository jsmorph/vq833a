import VQ.Curve.PackedAffineConstantAddition
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineSecondConstantSubtraction

open Reversible

def targetOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def sourceOffset : Nat := PackedAffineLayout.inverseOffset

def localLayout : Layout :=
  [256, 1, 256, 1, 1, 1, 1, 1, 1, 33, 1, 1, 8]

def wiring : Wiring :=
  [targetOffset, targetOffset + 256,
    sourceOffset, Euclid.PackedStepLayout.workOneOffset + 256,
    targetOffset + 257, targetOffset + 258,
    Euclid.PackedStepLayout.workOneOffset + 257,
    Euclid.PackedStepLayout.workOneOffset + 258,
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

def loadGates (constant : Nat) : List RGate :=
  constantXorGates constant sourceOffset 256

def subtractGates : List RGate :=
  controlToggleGates ++ addGates.reverse ++ controlToggleGates

def gates (constant : Nat) : List RGate :=
  loadGates constant ++ subtractGates ++ (loadGates constant).reverse

def circuit (constant : Nat) : RCircuit :=
  { width := PackedAffineLayout.width, gates := gates constant }

theorem localLayout_width : localLayout.width =
    PackedReversibleSecp256k1Arithmetic.width := by
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

theorem loadGates_wellFormed (constant : Nat) :
    (loadGates constant).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  exact constantXorGates_wellFormed (by decide)

theorem loadGates_avoid_target (constant : Nat) :
    ∀ gate ∈ loadGates constant, ∀ q ∈ gate.wires,
      q < targetOffset ∨ targetOffset + 256 ≤ q := by
  intro gate hgate q hq
  have hwire := constantXorGates_wires gate hgate q hq
  right
  exact Nat.le_trans (by decide +kernel) hwire.1

theorem subtractGates_wellFormed :
    subtractGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [subtractGates, controlToggleGates_wellFormed,
    addGates_wellFormed]

theorem gates_wellFormed (constant : Nat) :
    (gates constant).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [gates, loadGates_wellFormed, subtractGates_wellFormed]

theorem circuit_wellFormed (constant : Nat) :
    (circuit constant).wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed constant

end VQ.Curve.PackedAffineSecondConstantSubtraction
