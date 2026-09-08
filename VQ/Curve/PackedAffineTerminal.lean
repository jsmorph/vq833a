import VQ.Curve.PackedAffineLayout
import VQ.Euclid.PackedTerminalEndpoint

namespace VQ.Curve.PackedAffineTerminal

open Reversible

def preparationGates : List RGate :=
  (Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8).map
    (RGate.map (place Euclid.PackedTerminalEndpoint.endpointLayout
      Euclid.PackedTerminalEndpoint.endpointWiring))

def signLayout : Layout := Euclid.SignCorrection.controlledLayout 256

def signWiring : Wiring :=
  [Euclid.PackedStepLayout.workOneOffset,
    Euclid.PackedStepLayout.workTwoOffset,
    Euclid.PackedStepLayout.phaseOneWire,
    Euclid.PackedStepLayout.iterationWire,
    Euclid.PackedStepLayout.phaseTwoWire]

def signGates : List RGate :=
  (Euclid.SignCorrection.negativeControlledGates 256).map
    (RGate.map (place signLayout signWiring))

def gates : List RGate := preparationGates ++ signGates

theorem preparationGates_wellFormed :
    preparationGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply wellFormed_placeGates
    Euclid.PackedTerminalEndpoint.endpointWiring_disjoint (by decide)
  · intro j hj
    exact (Euclid.PackedTerminalEndpoint.endpointWiring_bound j hj).trans
      (by decide)
  · intro g hg
    rw [Euclid.PackedTerminalEndpoint.endpointLayout_width]
    exact List.all_eq_true.mp
      (Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [Euclid.TerminalCanonicalization.counterWidth])) g hg

theorem preparationGates_wellFormed_core :
    preparationGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  apply wellFormed_placeGates
    Euclid.PackedTerminalEndpoint.endpointWiring_disjoint (by decide)
  · intro j hj
    exact (Euclid.PackedTerminalEndpoint.endpointWiring_bound j hj).trans
      (by decide)
  · intro g hg
    rw [Euclid.PackedTerminalEndpoint.endpointLayout_width]
    exact List.all_eq_true.mp
      (Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [Euclid.TerminalCanonicalization.counterWidth])) g hg

theorem signWiring_disjoint : Wiring.Disjoint signLayout signWiring := by
  intro j k hj hk hne
  simp [signWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [signLayout, Euclid.SignCorrection.controlledLayout,
      signWiring, Layout.size, Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.workTwoOffset,
      Euclid.PackedStepLayout.phaseOneWire,
      Euclid.PackedStepLayout.phaseTwoWire,
      Euclid.PackedStepLayout.iterationWire]

theorem signWiring_bound : ∀ j, j < signLayout.length →
    signWiring.getD j 0 + signLayout.size j ≤ PackedAffineLayout.width := by
  decide +kernel

theorem signWiring_bound_core : ∀ j, j < signLayout.length →
    signWiring.getD j 0 + signLayout.size j ≤
      PackedAffineLayout.auxiliaryOffset := by
  decide +kernel

theorem signGates_wellFormed :
    signGates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply wellFormed_placeGates signWiring_disjoint (by decide) signWiring_bound
  intro g hg
  exact List.all_eq_true.mp
    (Euclid.SignCorrection.negativeControlledGates_wellFormed 256) g hg

theorem signGates_wellFormed_core :
    signGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  apply wellFormed_placeGates signWiring_disjoint (by decide)
    signWiring_bound_core
  intro g hg
  exact List.all_eq_true.mp
    (Euclid.SignCorrection.negativeControlledGates_wellFormed 256) g hg

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [gates, preparationGates_wellFormed, signGates_wellFormed]

theorem gates_wellFormed_core :
    gates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp [gates, preparationGates_wellFormed_core,
    signGates_wellFormed_core]

theorem preparationGates_avoids_inverse :
    ∀ g ∈ preparationGates, ∀ q ∈ g.wires,
      q < PackedAffineLayout.inverseOffset ∨
        PackedAffineLayout.inverseOffset + 256 ≤ q := by
  intro g hg q hq
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  left
  have hlocalWf := List.all_eq_true.mp
    (Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
      (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
      (lengthWidth := 8) (by norm_num) (by norm_num)
      (by norm_num [Euclid.TerminalCanonicalization.counterWidth])) g' hg'
  have hlt := wire_lt_of_wellFormed hlocalWf hq'
  have havoid :=
    Euclid.LuoTerminalEndpoint.preparationGates_avoids_output
      (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
      (lengthWidth := 8) (by norm_num)
      (by norm_num [Euclid.TerminalCanonicalization.counterWidth])
      g' hg' q' hq'
  obtain ⟨j, b, hj, hb, rfl⟩ :=
    exists_field Euclid.PackedTerminalEndpoint.endpointLayout q' hlt
  have hjne : j ≠ 7 := by
    intro heq
    subst j
    rcases havoid with hbefore | hafter
    · simp [Euclid.PackedTerminalEndpoint.endpointLayout, Layout.offset,
        Euclid.LuoTerminalEndpoint.outputOffset,
        Euclid.LuoTerminalExtraction.outputOffset,
        Euclid.LuoTerminalCanonicalization.width,
        Euclid.LuoTerminalCanonicalization.outerWire,
        Euclid.LuoTerminalCanonicalization.jointWire,
        Euclid.TerminalCanonicalization.carryWire,
        Euclid.TerminalCanonicalization.counterWidth] at hbefore
    · simp [Euclid.PackedTerminalEndpoint.endpointLayout, Layout.offset,
        Layout.size, Euclid.LuoTerminalEndpoint.outputOffset,
        Euclid.LuoTerminalExtraction.outputOffset,
        Euclid.LuoTerminalCanonicalization.width,
        Euclid.LuoTerminalCanonicalization.outerWire,
        Euclid.LuoTerminalCanonicalization.jointWire,
        Euclid.TerminalCanonicalization.carryWire,
        Euclid.TerminalCanonicalization.counterWidth] at hafter hb
      omega
  have hj' : j < 9 := by
    simpa [Euclid.PackedTerminalEndpoint.endpointLayout] using hj
  rw [place_field Euclid.PackedTerminalEndpoint.endpointLayout
    Euclid.PackedTerminalEndpoint.endpointWiring j b
      (by simpa [Euclid.PackedTerminalEndpoint.endpointWiring] using hj') hb]
  interval_cases j <;>
    simp_all [Euclid.PackedTerminalEndpoint.endpointLayout,
      Euclid.PackedTerminalEndpoint.endpointWiring, Layout.size,
      PackedAffineLayout.inverseOffset,
      Euclid.PackedTerminalEndpoint.outputOffset,
      Euclid.PackedStepLayout.workTwoOffset,
      Euclid.PackedStepLayout.shiftOffset,
      Euclid.PackedStepLayout.extensionWire,
      Euclid.PackedStepLayout.poolOffset,
      Euclid.PackedStepLayout.lengthRPrimeOffset,
      Euclid.PackedStepLayout.width, Euclid.PackedStepLayout.layout,
      Euclid.PackedStepLayout.workWidth,
      Euclid.PackedStepLayout.lengthWidth,
      Euclid.PackedStepLayout.remainderLengthWidth,
      Euclid.PackedStepLayout.poolWidth, Layout.width] <;> omega

theorem signGates_avoids_inverse :
    ∀ g ∈ signGates, ∀ q ∈ g.wires,
      q < PackedAffineLayout.inverseOffset ∨
        PackedAffineLayout.inverseOffset + 256 ≤ q := by
  have havoids := placeGates_avoids
    (L := signLayout) (W := signWiring)
    (gs := Euclid.SignCorrection.negativeControlledGates 256)
    (lo := PackedAffineLayout.inverseOffset)
    (hi := PackedAffineLayout.inverseOffset + 256)
    (by decide)
    (fun g hg => List.all_eq_true.mp
      (Euclid.SignCorrection.negativeControlledGates_wellFormed 256) g hg)
    (by decide +kernel)
  simpa [signGates] using havoids

theorem gates_avoids_inverse :
    ∀ g ∈ gates, ∀ q ∈ g.wires,
      q < PackedAffineLayout.inverseOffset ∨
        PackedAffineLayout.inverseOffset + 256 ≤ q := by
  intro g hg q hq
  rw [gates, List.mem_append] at hg
  rcases hg with hpreparation | hsign
  · exact preparationGates_avoids_inverse g hpreparation q hq
  · exact signGates_avoids_inverse g hsign q hq

theorem reverseGates_wellFormed :
    gates.reverse.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  simpa [List.all_reverse] using gates_wellFormed

theorem reverseGates_wellFormed_core :
    gates.reverse.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simpa [List.all_reverse] using gates_wellFormed_core

end VQ.Curve.PackedAffineTerminal
