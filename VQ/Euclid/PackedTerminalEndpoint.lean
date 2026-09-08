import VQ.Euclid.LuoTerminalEndpoint
import VQ.Euclid.PackedStepLayout
import VQ.Euclid.PackedTerminalEpoch
import VQ.Euclid.SignCorrection

namespace VQ.Euclid.PackedTerminalEndpoint

open Reversible

def outputOffset : Nat := PackedStepLayout.width

def width : Nat := outputOffset + 256

def endpointLayout : Layout := [259, 9, 1, 10, 1, 1, 1, 256, 8]

def endpointWiring : Wiring :=
  [PackedStepLayout.workTwoOffset, PackedStepLayout.shiftOffset,
    PackedStepLayout.extensionWire, PackedStepLayout.poolOffset + 1,
    PackedStepLayout.poolOffset + 11, PackedStepLayout.poolOffset + 12,
    PackedStepLayout.poolOffset, outputOffset,
    PackedStepLayout.lengthRPrimeOffset]

def endpointGates : List RGate :=
  (LuoTerminalEndpoint.gates 259 9 256 8).map
    (RGate.map (place endpointLayout endpointWiring))

def signLayout : Layout := SignCorrection.controlledLayout 256

def signWiring : Wiring :=
  [PackedStepLayout.workOneOffset, outputOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.iterationWire,
    PackedStepLayout.poolOffset + 1]

def signGates : List RGate :=
  (SignCorrection.negativeControlledGates 256).map
    (RGate.map (place signLayout signWiring))

def gates : List RGate := endpointGates ++ signGates

def circuit : RCircuit := { width := width, gates := gates }

def inverterGates : List RGate :=
  VQ.Euclid.PackedTerminalEpoch.roundsGates 1620 ++ gates ++
    (VQ.Euclid.PackedTerminalEpoch.roundsGates 1620).reverse

def inverterCircuit : RCircuit := { width := width, gates := inverterGates }

theorem endpointLayout_width : endpointLayout.width = 546 := by decide

theorem endpointWiring_disjoint :
    Wiring.Disjoint endpointLayout endpointWiring := by
  intro j k hj hk hne
  simp [endpointWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [endpointLayout, endpointWiring, Layout.size,
      PackedStepLayout.workTwoOffset, PackedStepLayout.shiftOffset,
      PackedStepLayout.extensionWire, PackedStepLayout.poolOffset,
      PackedStepLayout.lengthRPrimeOffset, outputOffset,
      PackedStepLayout.width, PackedStepLayout.layout,
      PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
      PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
      Layout.width]

theorem endpointWiring_bound : ∀ j, j < endpointLayout.length →
    endpointWiring.getD j 0 + endpointLayout.size j ≤ width := by
  decide +kernel

theorem endpointGates_wellFormed :
    endpointGates.all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates endpointWiring_disjoint (by decide)
    endpointWiring_bound
  intro g hg
  rw [endpointLayout_width]
  exact List.all_eq_true.mp
    (LuoTerminalEndpoint.gates_wellFormed
      (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
      (lengthWidth := 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [TerminalCanonicalization.counterWidth])) g hg

theorem signWiring_disjoint : Wiring.Disjoint signLayout signWiring := by
  intro j k hj hk hne
  simp [signWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [signLayout, SignCorrection.controlledLayout, signWiring,
      Layout.size, PackedStepLayout.workOneOffset,
      PackedStepLayout.poolOffset, PackedStepLayout.iterationWire,
      outputOffset, PackedStepLayout.width, PackedStepLayout.layout,
      PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
      PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
      Layout.width]

theorem signWiring_bound : ∀ j, j < signLayout.length →
    signWiring.getD j 0 + signLayout.size j ≤ width := by
  native_decide

theorem signGates_wellFormed :
    signGates.all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates signWiring_disjoint (by decide)
    signWiring_bound
  intro g hg
  exact List.all_eq_true.mp
    (SignCorrection.negativeControlledGates_wellFormed 256) g hg

theorem gates_wellFormed :
    gates.all (RGate.wellFormed width) = true := by
  simp [gates, endpointGates_wellFormed, signGates_wellFormed]

theorem circuit_wellFormed : circuit.wellFormed = true := gates_wellFormed

theorem circuit_width : circuit.width = 827 := by
  decide

theorem roundsGates_wellFormed (rounds : Nat) :
    (VQ.Euclid.PackedTerminalEpoch.roundsGates rounds).all
      (RGate.wellFormed width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := PackedStepLayout.width)
  · rw [PackedStepLayout.layout_width]
    native_decide
  · exact List.all_eq_true.mp
      (VQ.Euclid.PackedTerminalEpoch.roundsGates_wellFormed rounds) g hg

theorem roundsGates_avoids_output (rounds : Nat) :
    ∀ g ∈ VQ.Euclid.PackedTerminalEpoch.roundsGates rounds,
      ∀ q ∈ g.wires,
        q < outputOffset ∨ outputOffset + 256 ≤ q := by
  intro g hg q hq
  left
  have hgwf := List.all_eq_true.mp
    (VQ.Euclid.PackedTerminalEpoch.roundsGates_wellFormed rounds) g hg
  have hqWidth := wire_lt_of_wellFormed hgwf hq
  simpa [outputOffset] using hqWidth

theorem inverterGates_wellFormed :
    inverterGates.all (RGate.wellFormed width) = true := by
  simp [inverterGates, roundsGates_wellFormed, gates_wellFormed,
    List.all_reverse]

theorem inverterCircuit_wellFormed :
    inverterCircuit.wellFormed = true := inverterGates_wellFormed

theorem inverterCircuit_width : inverterCircuit.width = 827 := by
  decide

end VQ.Euclid.PackedTerminalEndpoint
