import VQ.Curve.PackedAffineLayout
import VQ.Curve.PackedReversibleSecp256k1CompactProduct
import VQ.Reversible.Constant
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineTerminalProduct

open Reversible

def targetOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def sourceOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def multiplierOffset : Nat := PackedAffineLayout.inverseOffset

def localLayout : Layout :=
  [256, 1, 256, 1, 1, 1, 1, 1, 1, 9, 9, 8, 2, 5, 1, 1, 8, 253]

def wiring : Wiring :=
  [targetOffset, multiplierOffset, sourceOffset, multiplierOffset + 1,
    sourceOffset + 256, multiplierOffset + 2, sourceOffset + 257,
    sourceOffset + 258, targetOffset + 256,
    Euclid.PackedStepLayout.lengthTOffset,
    Euclid.PackedStepLayout.lengthQOffset,
    Euclid.PackedStepLayout.lengthRPrimeOffset,
    Euclid.PackedStepLayout.phaseOneWire,
    Euclid.PackedStepLayout.poolOffset,
    targetOffset + 257, targetOffset + 258,
    Euclid.PackedStepLayout.poolOffset + 5, multiplierOffset + 3]

def gates : List RGate :=
  PackedReversibleSecp256k1CompactProduct.gates.map
    (RGate.map (place localLayout wiring))

def circuit : RCircuit := { width := PackedAffineLayout.width, gates }

def workspaceMaskGates : List RGate :=
  constantXorGates 255 Euclid.PackedStepLayout.lengthTOffset 9 ++
    constantXorGates 511 Euclid.PackedStepLayout.lengthQOffset 9 ++
    constantXorGates 255 Euclid.PackedStepLayout.lengthRPrimeOffset 8 ++
    constantXorGates 4 (targetOffset + 256) 3

def terminalGates : List RGate :=
  workspaceMaskGates ++ gates ++ workspaceMaskGates.reverse

def terminalCircuit : RCircuit :=
  { width := PackedAffineLayout.width, gates := terminalGates }

theorem localLayout_width : localLayout.width =
    PackedReversibleSecp256k1CompactProduct.width := by
  decide +kernel

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size, targetOffset, sourceOffset,
      multiplierOffset, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.workTwoOffset,
      Euclid.PackedStepLayout.lengthTOffset,
      Euclid.PackedStepLayout.lengthQOffset,
      Euclid.PackedStepLayout.lengthRPrimeOffset,
      Euclid.PackedStepLayout.phaseOneWire,
      Euclid.PackedStepLayout.poolOffset,
      PackedAffineLayout.inverseOffset,
      Euclid.PackedTerminalEndpoint.outputOffset,
      Euclid.PackedStepLayout.width, Euclid.PackedStepLayout.layout,
      Euclid.PackedStepLayout.workWidth,
      Euclid.PackedStepLayout.lengthWidth,
      Euclid.PackedStepLayout.remainderLengthWidth,
      Euclid.PackedStepLayout.poolWidth, Layout.width]

theorem wiring_length : localLayout.length ≤ wiring.length := by decide

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
    PackedReversibleSecp256k1CompactProduct.gates_wellFormed gate hgate

theorem gates_wellFormed_core :
    gates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  apply wellFormed_placeGates wiring_disjoint wiring_length wiring_bound_core
  intro gate hgate
  rw [localLayout_width]
  exact List.all_eq_true.mp
    PackedReversibleSecp256k1CompactProduct.gates_wellFormed gate hgate

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simpa only [circuit, RCircuit.wellFormed] using gates_wellFormed

theorem workspaceMaskGates_wellFormed :
    workspaceMaskGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [workspaceMaskGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨constantXorGates_wellFormed (by decide),
    constantXorGates_wellFormed (by decide)⟩,
    constantXorGates_wellFormed (by decide)⟩,
    constantXorGates_wellFormed (by decide)⟩

theorem workspaceMaskGates_wellFormed_core :
    workspaceMaskGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [workspaceMaskGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨constantXorGates_wellFormed (by decide),
    constantXorGates_wellFormed (by decide)⟩,
    constantXorGates_wellFormed (by decide)⟩,
    constantXorGates_wellFormed (by decide)⟩

theorem terminalGates_wellFormed :
    terminalGates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [terminalGates, workspaceMaskGates_wellFormed, gates_wellFormed]

theorem terminalGates_wellFormed_core :
    terminalGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp [terminalGates, workspaceMaskGates_wellFormed_core,
    gates_wellFormed_core]

theorem terminalCircuit_wellFormed : terminalCircuit.wellFormed = true := by
  simpa only [terminalCircuit, RCircuit.wellFormed] using
    terminalGates_wellFormed

theorem workspaceMaskGates_avoids_target :
    ∀ gate ∈ workspaceMaskGates, ∀ q ∈ gate.wires,
      q < targetOffset ∨ targetOffset + 256 ≤ q := by
  intro gate hgate q hq
  simp only [workspaceMaskGates, List.mem_append] at hgate
  rcases hgate with ((hgate | hgate) | hgate) | hgate
  · have hwire := constantXorGates_wires gate hgate q hq
    right
    simp [targetOffset, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.lengthTOffset] at hwire ⊢
    omega
  · have hwire := constantXorGates_wires gate hgate q hq
    right
    simp [targetOffset, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.lengthQOffset] at hwire ⊢
    omega
  · have hwire := constantXorGates_wires gate hgate q hq
    right
    simp [targetOffset, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.lengthRPrimeOffset] at hwire ⊢
    omega
  · have hwire := constantXorGates_wires gate hgate q hq
    right
    simp [targetOffset, Euclid.PackedStepLayout.workOneOffset] at hwire ⊢
    omega

end VQ.Curve.PackedAffineTerminalProduct
