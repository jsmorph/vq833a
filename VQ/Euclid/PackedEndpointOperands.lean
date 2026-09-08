import VQ.Euclid.PackedStepLayout

namespace VQ.Euclid.PackedEndpointOperands

open VQ.Reversible

set_option maxRecDepth 4096

theorem remainderPrepare_avoids_poolHead :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset ∨
        PackedStepLayout.poolOffset + 1 ≤ q := by
  decide +kernel

theorem remainderPrepare_avoids_poolTail :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset + 11 ∨
        PackedStepLayout.poolOffset + 13 ≤ q := by
  decide +kernel

theorem remainderPrepare_avoids_workOne :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  decide +kernel

theorem remainderPrepare_avoids_sign :
    ∀ g ∈ PackedStepLayout.remainderPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨
        PackedStepLayout.signWire + 1 ≤ q := by
  decide +kernel

theorem swapPrepare_avoids_poolHead :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset ∨
        PackedStepLayout.poolOffset + 1 ≤ q := by
  decide +kernel

theorem swapPrepare_avoids_poolTail :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.poolOffset + 11 ∨
        PackedStepLayout.poolOffset + 13 ≤ q := by
  decide +kernel

theorem swapPrepare_avoids_workOne :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workOneOffset ∨
        PackedStepLayout.workOneOffset + 259 ≤ q := by
  decide +kernel

theorem swapPrepare_avoids_sign :
    ∀ g ∈ PackedStepLayout.swapPrepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨
        PackedStepLayout.signWire + 1 ≤ q := by
  decide +kernel

end VQ.Euclid.PackedEndpointOperands
