import VQ.Curve.PackedAffineSquareSubtract

namespace VQ.Curve.PackedAffineConstantAddition

open Reversible

def loadGates (constant : Nat) : List RGate :=
  constantXorGates constant PackedAffineLayout.inverseOffset 256

def controlledAddGates : List RGate :=
  PackedAffineSquareSubtract.controlToggleGates ++
    PackedAffineSquareSubtract.addGates ++
    PackedAffineSquareSubtract.controlToggleGates

def unconditionalControlGates : List RGate :=
  [.x VQ.Euclid.PackedStepLayout.lengthTOffset]

def unconditionalAddGates : List RGate :=
  unconditionalControlGates ++
    PackedAffineSquareSubtract.addGates ++
    unconditionalControlGates

def gates (constant : Nat) : List RGate :=
  loadGates constant ++ controlledAddGates ++ (loadGates constant).reverse

def unconditionalGates (constant : Nat) : List RGate :=
  loadGates constant ++ unconditionalAddGates ++ (loadGates constant).reverse

def circuit (constant : Nat) : RCircuit :=
  { width := PackedAffineLayout.width, gates := gates constant }

theorem loadGates_wellFormed (constant : Nat) :
    (loadGates constant).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  exact constantXorGates_wellFormed (by decide)

theorem loadGates_avoid_target (constant : Nat) :
    ∀ gate ∈ loadGates constant, ∀ q ∈ gate.wires,
      q < PackedAffineSquareSubtract.targetOffset ∨
        PackedAffineSquareSubtract.targetOffset + 256 ≤ q := by
  intro gate hgate q hq
  have hwire := constantXorGates_wires gate hgate q hq
  right
  exact Nat.le_trans (by decide +kernel) hwire.1

theorem controlledAddGates_wellFormed :
    controlledAddGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [controlledAddGates,
    PackedAffineSquareSubtract.controlToggleGates_wellFormed,
    PackedAffineSquareSubtract.addGates_wellFormed]

theorem unconditionalControlGates_wellFormed :
    unconditionalControlGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  decide +kernel

theorem unconditionalAddGates_wellFormed :
    unconditionalAddGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [unconditionalAddGates, unconditionalControlGates_wellFormed,
    PackedAffineSquareSubtract.addGates_wellFormed]

theorem gates_wellFormed (constant : Nat) :
    (gates constant).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [gates, loadGates_wellFormed, controlledAddGates_wellFormed]

theorem unconditionalGates_wellFormed (constant : Nat) :
    (unconditionalGates constant).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [unconditionalGates, loadGates_wellFormed,
    unconditionalAddGates_wellFormed]

theorem circuit_wellFormed (constant : Nat) :
    (circuit constant).wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed constant

end VQ.Curve.PackedAffineConstantAddition
