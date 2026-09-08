import VQ.Euclid.PackedInputPreparation
import VQ.Euclid.LuoWindowedOwnershipSchedule

namespace VQ.Curve.PackedAffineLayout

open Reversible

def layout : Layout :=
  [VQ.Euclid.PackedStepLayout.width, 256, 1, 4, 1]

def euclidOffset : Nat := 0

def inverseOffset : Nat := VQ.Euclid.PackedTerminalEndpoint.outputOffset

def controlWire : Nat := VQ.Euclid.PackedTerminalEndpoint.width

def exceptionalOffset : Nat := controlWire + 1

def zeroFactorWire : Nat := exceptionalOffset + 4

def equalityWire : Nat := zeroFactorWire

def auxiliaryOffset : Nat := controlWire

def auxiliaryWidth : Nat := 6

def width : Nat := layout.width

def inverterCircuit : RCircuit :=
  { width := width,
    gates := VQ.Euclid.LuoWindowedOwnership.inverterGates }

def fieldInverterGates (p : Nat) : List RGate :=
  VQ.Euclid.PackedInputPreparation.gates p ++
    inverterCircuit.gates ++
    (VQ.Euclid.PackedInputPreparation.gates p).reverse

def fieldInverterCircuit (p : Nat) : RCircuit :=
  { width := width, gates := fieldInverterGates p }

theorem layout_width : width = 833 := by decide

theorem auxiliary_end : auxiliaryOffset + auxiliaryWidth = width := by decide

theorem inverterGates_wellFormed :
    inverterCircuit.wellFormed = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := VQ.Euclid.PackedTerminalEndpoint.width)
  · decide
  · exact List.all_eq_true.mp
      VQ.Euclid.LuoWindowedOwnership.inverterGates_wellFormed g hg

theorem inverterGates_avoid_auxiliary :
    ∀ g ∈ inverterCircuit.gates, ∀ q ∈ g.wires,
      q < auxiliaryOffset ∨ auxiliaryOffset + auxiliaryWidth ≤ q := by
  intro g hg q hq
  left
  have hwellFormed := List.all_eq_true.mp
    VQ.Euclid.LuoWindowedOwnership.inverterGates_wellFormed g hg
  exact wire_lt_of_wellFormed hwellFormed hq

theorem inputPreparationGates_wellFormed (p : Nat) :
    (VQ.Euclid.PackedInputPreparation.gates p).all
      (RGate.wellFormed width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := VQ.Euclid.PackedStepLayout.width)
  · decide
  · exact List.all_eq_true.mp
      (VQ.Euclid.PackedInputPreparation.gates_wellFormed p) g hg

theorem inputPreparationGates_avoid_inverse (p : Nat) :
    ∀ g ∈ VQ.Euclid.PackedInputPreparation.gates p, ∀ q ∈ g.wires,
      q < inverseOffset ∨ inverseOffset + 256 ≤ q := by
  intro g hg q hq
  left
  have hwellFormed := List.all_eq_true.mp
    (VQ.Euclid.PackedInputPreparation.gates_wellFormed p) g hg
  exact wire_lt_of_wellFormed hwellFormed hq

theorem roundsGates_avoid_inverse :
    ∀ g ∈ VQ.Euclid.LuoWindowedOwnership.roundsGates 1620, ∀ q ∈ g.wires,
      q < inverseOffset ∨ inverseOffset + 256 ≤ q := by
  intro g hg q hq
  left
  exact wire_lt_of_wellFormed
    (List.all_eq_true.mp
      (VQ.Euclid.LuoWindowedOwnership.roundsGates_wellFormed
        (by decide : 1620 ≤ 1620)) g hg) hq

theorem fieldInverterGates_wellFormed (p : Nat) :
    (fieldInverterCircuit p).wellFormed = true := by
  have hinverter : inverterCircuit.gates.all
      (RGate.wellFormed width) = true := by
    exact inverterGates_wellFormed
  simp only [RCircuit.wellFormed, fieldInverterCircuit,
    fieldInverterGates, List.all_append, List.all_reverse,
    Bool.and_eq_true]
  exact ⟨⟨inputPreparationGates_wellFormed p, hinverter⟩,
    inputPreparationGates_wellFormed p⟩

theorem fieldInverterGates_avoid_auxiliary (p : Nat) :
    ∀ g ∈ (fieldInverterCircuit p).gates, ∀ q ∈ g.wires,
      q < auxiliaryOffset ∨ auxiliaryOffset + auxiliaryWidth ≤ q := by
  intro g hg q hq
  have hgm : g ∈ fieldInverterGates p := by
    simpa only [fieldInverterCircuit] using hg
  rw [fieldInverterGates] at hgm
  rcases List.mem_append.mp hgm with hleft | hprep
  · rcases List.mem_append.mp hleft with hprep | hinverter
    · left
      have hwellFormed := List.all_eq_true.mp
        (VQ.Euclid.PackedInputPreparation.gates_wellFormed p) g
          hprep
      exact (wire_lt_of_wellFormed hwellFormed hq).trans (by decide)
    · exact inverterGates_avoid_auxiliary g hinverter q hq
  · left
    have hwellFormed := List.all_eq_true.mp
      (VQ.Euclid.PackedInputPreparation.gates_wellFormed p) g
        (List.mem_reverse.mp hprep)
    exact (wire_lt_of_wellFormed hwellFormed hq).trans (by decide)

end VQ.Curve.PackedAffineLayout
