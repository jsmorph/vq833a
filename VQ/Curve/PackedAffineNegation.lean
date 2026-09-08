import VQ.Curve.PackedAffineConstantAddition
import VQ.Curve.PointAddition.Arithmetic.Neg
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineNegation

open Reversible

def targetOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def localLayout : Layout := [256, 1, 1, 256, 1, 1]

def wiring : Wiring :=
  [targetOffset, targetOffset + 256, targetOffset + 257,
    PackedAffineLayout.inverseOffset, PackedAffineLayout.controlWire,
    PackedAffineLayout.equalityWire]

def gates : List RGate :=
  (control (PointAddition.Arithmetic.Neg.gen 256)).gates.map
    (RGate.map (place localLayout wiring))

def circuit : RCircuit := { width := PackedAffineLayout.width, gates }

theorem localLayout_width : localLayout.width =
    (control (PointAddition.Arithmetic.Neg.gen 256)).width := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  have hinverse : PackedAffineLayout.inverseOffset = 571 := by
    decide +kernel
  have hcontrol : PackedAffineLayout.controlWire = 827 := by
    decide +kernel
  have hequality : PackedAffineLayout.equalityWire = 832 := by
    decide +kernel
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size, targetOffset,
      Euclid.PackedStepLayout.workOneOffset]

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
  exact RCircuit.wellFormed_mem
    (control_wellFormed (PointAddition.Arithmetic.Neg.wf 256)) hgate

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed

end VQ.Curve.PackedAffineNegation
