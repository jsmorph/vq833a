import VQ.Euclid.PackedOwnership

namespace VQ.Euclid.PackedOwnershipOperands

open VQ.Reversible

set_option maxRecDepth 4096

theorem prepareGates_avoids_sign :
    ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.signWire ∨
        PackedStepLayout.signWire + 1 ≤ q := by
  decide +kernel

theorem prepareGates_avoids_phaseTwo :
    ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.phaseTwoWire ∨
        PackedStepLayout.phaseTwoWire + 1 ≤ q := by
  decide +kernel

theorem prepareGates_avoids_extension :
    ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.extensionWire ∨
        PackedStepLayout.extensionWire + 1 ≤ q := by
  decide +kernel

end VQ.Euclid.PackedOwnershipOperands
