/-
Physical placement of the compact secp256k1 Euclidean-step components.
-/
import VQ.Euclid.CompactCoefficientDirty
import VQ.Euclid.CompactIntervalVariants
import VQ.Euclid.CompactPhase
import VQ.Euclid.CompactSelectSwap
import VQ.Euclid.PackedEndpointPreparation
import VQ.Euclid.Shift
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace PackedStepLayout

open Reversible

def workWidth : Nat := 259
def lengthWidth : Nat := 9
def remainderLengthWidth : Nat := 8
def poolWidth : Nat := 13

def workOneOffset : Nat := 0
def workTwoOffset : Nat := 259
def lengthTOffset : Nat := 518
def lengthQOffset : Nat := 527
def lengthRPrimeOffset : Nat := 536
def extensionWire : Nat := 544
def shiftOffset : Nat := 545
def phaseOneWire : Nat := 554
def phaseTwoWire : Nat := 555
def iterationWire : Nat := 556
def signWire : Nat := 557
def poolOffset : Nat := 558

def layout : Layout :=
  [workWidth, workWidth, lengthWidth, lengthWidth, remainderLengthWidth, 1,
    lengthWidth, 1, 1, 1, 1, poolWidth]

def width : Nat := layout.width

theorem layout_width : width = 571 := by
  decide

def intervalLayout : Layout :=
  [259, 259, 9, 9, 1, 1, 1, 1, 1, 1, 7, 1]

def intervalWiring : Wiring :=
  [workOneOffset, workTwoOffset, lengthTOffset, shiftOffset,
    poolOffset, signWire, poolOffset + 1, poolOffset + 2,
    poolOffset + 3, poolOffset + 4, poolOffset + 5, poolOffset + 12]

def remainderIntervalWiring : Wiring :=
  [workTwoOffset, workOneOffset, lengthTOffset, shiftOffset,
    poolOffset, signWire, poolOffset + 1, poolOffset + 2,
    poolOffset + 3, poolOffset + 4, poolOffset + 5, poolOffset + 12]

def selectSwapLayout : Layout :=
  [259, 259, 9, 9, 1, 1, 1, 1, 1, 1, 6]

def selectSwapWiring : Wiring :=
  [workOneOffset, workTwoOffset, lengthTOffset, lengthQOffset,
    poolOffset, signWire, poolOffset + 1, poolOffset + 2,
    poolOffset + 3, poolOffset + 4, poolOffset + 5]

def coefficientLayout : Layout :=
  [1, 1, 1, 257, 257, 9, 8, 1, 9, 1, 1, 9, 1, 1, 1]

def coefficientWiring : Wiring :=
  [phaseOneWire, phaseTwoWire, signWire, workOneOffset, workTwoOffset,
    lengthTOffset, lengthRPrimeOffset, extensionWire, shiftOffset,
    poolOffset, iterationWire, poolOffset + 1, poolOffset + 10,
    poolOffset + 11, poolOffset + 12]

def phaseLayout : Layout := CompactPhase.layout

def phaseWiring : Wiring :=
  [phaseOneWire, phaseTwoWire, signWire, lengthQOffset,
    lengthRPrimeOffset, extensionWire, shiftOffset, poolOffset + 1,
    poolOffset + 2, poolOffset + 3, poolOffset + 4, poolOffset + 5,
    poolOffset + 6]

def endpointLayout : Layout := PackedEndpointPreparation.layout

def endpointWiring : Wiring :=
  [lengthTOffset, lengthQOffset, shiftOffset, poolOffset + 1, poolOffset + 10]

def shiftLayout : Layout := Shift.layout workWidth lengthWidth

def shiftWiring : Wiring :=
  [shiftOffset, poolOffset, poolOffset + 1, workTwoOffset, poolOffset + 10]

def quotientLayout : Layout := Increment.layout lengthWidth

def quotientWiring : Wiring :=
  [lengthQOffset, poolOffset, poolOffset + 1]

def placed (L : Layout) (W : Wiring) (gs : List RGate) : List RGate :=
  gs.map (RGate.map (place L W))

def intervalGates : List RGate :=
  placed intervalLayout intervalWiring CompactInterval.circuit.gates

def intervalNoSignGates : List RGate :=
  placed intervalLayout intervalWiring
    CompactIntervalVariants.noSignCircuit.gates

def remainderIntervalGates : List RGate :=
  placed intervalLayout remainderIntervalWiring
    CompactIntervalVariants.bigEndianCircuit.gates

def remainderIntervalReverseGates : List RGate :=
  placed intervalLayout remainderIntervalWiring
    CompactIntervalVariants.bigEndianReverseCircuit.gates

def remainderIntervalNoSignGates : List RGate :=
  placed intervalLayout remainderIntervalWiring
    CompactIntervalVariants.bigEndianNoSignCircuit.gates

def selectSwapGates : List RGate :=
  placed selectSwapLayout selectSwapWiring CompactSelectSwap.circuit.gates

def coefficientGates : List RGate :=
  placed coefficientLayout coefficientWiring CompactCoefficientDirty.gates

def phaseGates : List RGate :=
  placed phaseLayout phaseWiring CompactPhase.gates

def remainderPrepareGates : List RGate :=
  placed endpointLayout endpointWiring
    PackedEndpointPreparation.remainderPrepare

def remainderCleanupGates : List RGate := remainderPrepareGates.reverse

def swapPrepareGates : List RGate :=
  placed endpointLayout endpointWiring PackedEndpointPreparation.swapPrepare

def swapCleanupGates : List RGate := swapPrepareGates.reverse

def shiftGates : List RGate :=
  placed shiftLayout shiftWiring (Shift.gates workWidth lengthWidth)

def quotientIncrementGates : List RGate :=
  placed quotientLayout quotientWiring (Increment.circuit lengthWidth).gates

def quotientDecrementGates : List RGate := quotientIncrementGates.reverse

theorem intervalLayout_width : intervalLayout.width = 550 := by decide
theorem selectSwapLayout_width : selectSwapLayout.width = 548 := by decide
theorem coefficientLayout_width : coefficientLayout.width = 558 := by decide
theorem phaseLayout_width : phaseLayout.width = 42 := by decide
theorem endpointLayout_width : endpointLayout.width = 37 := by decide
theorem shiftLayout_width : shiftLayout.width = 279 := by decide
theorem quotientLayout_width : quotientLayout.width = 19 := by decide

theorem interval_disjoint : Wiring.Disjoint intervalLayout intervalWiring := by
  intro j k hj hk hne
  simp [intervalWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [intervalLayout, intervalWiring, Layout.size, workOneOffset,
      workTwoOffset, lengthTOffset, shiftOffset, poolOffset, signWire]

theorem remainderInterval_disjoint :
    Wiring.Disjoint intervalLayout remainderIntervalWiring := by
  intro j k hj hk hne
  simp [remainderIntervalWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [intervalLayout, remainderIntervalWiring, Layout.size,
      workOneOffset, workTwoOffset, lengthTOffset, shiftOffset, poolOffset,
      signWire]

theorem selectSwap_disjoint :
    Wiring.Disjoint selectSwapLayout selectSwapWiring := by
  intro j k hj hk hne
  simp [selectSwapWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [selectSwapLayout, selectSwapWiring, Layout.size,
      workOneOffset, workTwoOffset, lengthTOffset, lengthQOffset,
      poolOffset, signWire]

theorem coefficient_disjoint :
    Wiring.Disjoint coefficientLayout coefficientWiring := by
  intro j k hj hk hne
  simp [coefficientWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [coefficientLayout, coefficientWiring, Layout.size,
      phaseOneWire, phaseTwoWire, signWire, workOneOffset, workTwoOffset,
      lengthTOffset, lengthRPrimeOffset, extensionWire, poolOffset, shiftOffset,
      iterationWire]

theorem phase_disjoint : Wiring.Disjoint phaseLayout phaseWiring := by
  intro j k hj hk hne
  simp [phaseWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [phaseLayout, CompactPhase.layout, phaseWiring, Layout.size,
      phaseOneWire, phaseTwoWire, signWire, lengthQOffset,
      lengthRPrimeOffset, extensionWire, poolOffset, shiftOffset]

theorem endpoint_disjoint : Wiring.Disjoint endpointLayout endpointWiring := by
  intro j k hj hk hne
  simp [endpointWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [endpointLayout, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.width, endpointWiring, Layout.size,
      lengthTOffset, lengthQOffset, shiftOffset, poolOffset]

theorem shift_disjoint : Wiring.Disjoint shiftLayout shiftWiring := by
  intro j k hj hk hne
  simp [shiftWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [shiftLayout, Shift.layout, shiftWiring, Layout.size, shiftOffset,
      poolOffset, workTwoOffset, workWidth, lengthWidth]

theorem quotient_disjoint : Wiring.Disjoint quotientLayout quotientWiring := by
  intro j k hj hk hne
  simp [quotientWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [quotientLayout, Increment.layout, quotientWiring, Layout.size,
      lengthQOffset, poolOffset, lengthWidth]

theorem interval_bound : ∀ j, j < intervalLayout.length →
    intervalWiring.getD j 0 + intervalLayout.size j ≤ width := by
  native_decide

set_option maxRecDepth 4096 in
theorem remainderInterval_bound : ∀ j, j < intervalLayout.length →
    remainderIntervalWiring.getD j 0 + intervalLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem selectSwap_bound : ∀ j, j < selectSwapLayout.length →
    selectSwapWiring.getD j 0 + selectSwapLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem coefficient_bound : ∀ j, j < coefficientLayout.length →
    coefficientWiring.getD j 0 + coefficientLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem phase_bound : ∀ j, j < phaseLayout.length →
    phaseWiring.getD j 0 + phaseLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem endpoint_bound : ∀ j, j < endpointLayout.length →
    endpointWiring.getD j 0 + endpointLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shift_bound : ∀ j, j < shiftLayout.length →
    shiftWiring.getD j 0 + shiftLayout.size j ≤ width := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem quotient_bound : ∀ j, j < quotientLayout.length →
    quotientWiring.getD j 0 + quotientLayout.size j ≤ width := by
  decide +kernel

theorem placedWellFormed
    {L : Layout} {W : Wiring} {r : RCircuit}
    (hd : Wiring.Disjoint L W)
    (hlen : L.length ≤ W.length)
    (hbound : ∀ j, j < L.length → W.getD j 0 + L.size j ≤ width)
    (hwidth : r.width = L.width)
    (hwf : r.wellFormed = true) :
    (placed L W r.gates).all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates hd hlen hbound
  intro g hg
  have h := RCircuit.wellFormed_mem hwf hg
  rwa [hwidth] at h

theorem interval_wellFormed :
    intervalGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed interval_disjoint (by decide) interval_bound (by
      change CompactInterval.width = intervalLayout.width
      rw [CompactInterval.width_eq, intervalLayout_width])
    CompactInterval.circuit_wellFormed

theorem intervalNoSign_wellFormed :
    intervalNoSignGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed interval_disjoint (by decide) interval_bound (by
      change CompactInterval.width = intervalLayout.width
      rw [CompactInterval.width_eq, intervalLayout_width])
    CompactIntervalVariants.noSignCircuit_wellFormed

theorem remainderInterval_wellFormed :
    remainderIntervalGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed remainderInterval_disjoint (by decide)
    remainderInterval_bound (by
      change CompactInterval.width = intervalLayout.width
      rw [CompactInterval.width_eq, intervalLayout_width])
    CompactIntervalVariants.bigEndianCircuit_wellFormed

theorem remainderIntervalReverse_wellFormed :
    remainderIntervalReverseGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed remainderInterval_disjoint (by decide)
    remainderInterval_bound (by
      change CompactInterval.width = intervalLayout.width
      rw [CompactInterval.width_eq, intervalLayout_width])
    CompactIntervalVariants.bigEndianReverseCircuit_wellFormed

theorem remainderIntervalNoSign_wellFormed :
    remainderIntervalNoSignGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed remainderInterval_disjoint (by decide)
    remainderInterval_bound (by
      change CompactInterval.width = intervalLayout.width
      rw [CompactInterval.width_eq, intervalLayout_width])
    CompactIntervalVariants.bigEndianNoSignCircuit_wellFormed

theorem selectSwap_wellFormed :
    selectSwapGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed selectSwap_disjoint (by decide) selectSwap_bound (by
      change CompactSelectSwap.width = selectSwapLayout.width
      rw [selectSwapLayout_width]
      decide)
    CompactSelectSwap.circuit_wellFormed

theorem coefficient_wellFormed :
    coefficientGates.all (RGate.wellFormed width) = true := by
  unfold coefficientGates placed
  apply wellFormed_placeGates coefficient_disjoint (by decide)
    coefficient_bound
  intro g hg
  have h := RCircuit.wellFormed_mem
    CompactCoefficientDirty.circuit_wellFormed hg
  change g.wellFormed CompactCoefficientDirty.layout.width = true at h
  change g.wellFormed coefficientLayout.width = true
  rw [coefficientLayout_width]
  simpa [CompactCoefficientDirty.layout, CompactCoefficientPass.layout_width]
    using h

theorem phase_wellFormed :
    phaseGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed phase_disjoint (by decide) phase_bound (by
      change CompactPhase.layout.width = phaseLayout.width
      rfl)
    CompactPhase.circuit_wellFormed

theorem remainderPrepare_wellFormed :
    remainderPrepareGates.all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates endpoint_disjoint (by decide) endpoint_bound
  intro g hg
  have h := List.all_eq_true.mp
    PackedEndpointPreparation.remainderPrepare_wellFormed g hg
  simpa [endpointLayout] using h

theorem swapPrepare_wellFormed :
    swapPrepareGates.all (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates endpoint_disjoint (by decide) endpoint_bound
  intro g hg
  have h := List.all_eq_true.mp
    PackedEndpointPreparation.swapPrepare_wellFormed g hg
  simpa [endpointLayout] using h

set_option maxRecDepth 100000 in
theorem shift_wellFormed :
    shiftGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed shift_disjoint (by decide) shift_bound (by
      change (Shift.layout workWidth lengthWidth).width = shiftLayout.width
      rfl)
    (Shift.circuit_wellFormed workWidth lengthWidth)

theorem quotientIncrement_wellFormed :
    quotientIncrementGates.all (RGate.wellFormed width) = true := by
  exact placedWellFormed quotient_disjoint (by decide) quotient_bound (by
      change (Increment.layout lengthWidth).width = quotientLayout.width
      rfl)
    (Increment.circuit_wellFormed lengthWidth)

theorem endpoint_uncompute (I : Nat) :
    actGates remainderCleanupGates (actGates remainderPrepareGates I) = I := by
  exact actGates_reverse remainderPrepare_wellFormed I

theorem swapEndpoint_uncompute (I : Nat) :
    actGates swapCleanupGates (actGates swapPrepareGates I) = I := by
  exact actGates_reverse swapPrepare_wellFormed I

end PackedStepLayout
end Euclid
end VQ
