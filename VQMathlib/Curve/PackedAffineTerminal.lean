import VQ.Curve.PackedAffineTerminal
import VQMathlib.Euclid.PackedTerminalEndpoint

namespace VQMathlib.Curve.PackedAffineTerminal

open VQ
open VQ.Euclid
open VQ.Reversible
open VQMathlib.Euclid.LuoActiveWindows

private def preparationInput (I : Nat) : Nat :=
  gatherBits
    (place VQ.Euclid.PackedTerminalEndpoint.endpointLayout
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout.width I

private theorem preparationInput_field (j I : Nat)
    (hj : j < VQ.Euclid.PackedTerminalEndpoint.endpointWiring.length) :
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout.read
        (preparationInput I) j =
      readField I
        (VQ.Euclid.PackedTerminalEndpoint.endpointWiring.getD j 0)
        (VQ.Euclid.PackedTerminalEndpoint.endpointLayout.size j) := by
  exact read_gatherBits
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring j I hj

private theorem preparationInput_work (I : Nat) :
    readField (preparationInput I)
        TerminalCanonicalization.workOffset 259 =
      readField I PackedStepLayout.workTwoOffset 259 := by
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.workOffset, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 0 I (by decide)

private theorem preparationInput_low (I : Nat) :
    readField (preparationInput I)
        (TerminalCanonicalization.counterOffset 259) 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.counterOffset, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 1 I (by decide)

private theorem preparationInput_epoch (I : Nat) :
    bitValue (preparationInput I)
        (TerminalCanonicalization.epochWire 259 9) =
      bitValue I PackedStepLayout.extensionWire := by
  rw [← readField_one, ← readField_one]
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.epochWire,
    TerminalCanonicalization.counterOffset, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 2 I (by decide)

private theorem preparationInput_scratch (I : Nat) :
    readField (preparationInput I)
        (TerminalCanonicalization.scratchOffset 259 9) 10 =
      readField I (PackedStepLayout.poolOffset + 1) 10 := by
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.scratchOffset,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 3 I (by decide)

private theorem preparationInput_carry (I : Nat) :
    bitValue (preparationInput I)
        (TerminalCanonicalization.carryWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 11) := by
  rw [← readField_one, ← readField_one]
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 4 I (by decide)

private theorem preparationInput_joint (I : Nat) :
    bitValue (preparationInput I)
        (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 12) := by
  rw [← readField_one, ← readField_one]
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 5 I (by decide)

private theorem preparationInput_outer (I : Nat) :
    bitValue (preparationInput I)
        (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalCanonicalization.outerWire,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 6 I (by decide)

private theorem preparationInput_length (I : Nat) :
    readField (preparationInput I)
        (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
      readField I PackedStepLayout.lengthRPrimeOffset 8 := by
  simpa [preparationInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset,
    VQ.Euclid.LuoTerminalExtraction.width,
    VQ.Euclid.LuoTerminalExtraction.outputOffset,
    VQ.Euclid.LuoTerminalCanonicalization.width,
    VQ.Euclid.LuoTerminalCanonicalization.outerWire,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using preparationInput_field 8 I (by decide)

theorem preparationGates_read_workTwo
    {s : State} {depth : Nat}
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (htPrimeFit : s.tPrime < 2 ^ 259) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.preparationGates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        PackedStepLayout.workTwoOffset 259 = s.tPrime := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let J := preparationInput I
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 :=
    VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_pool
  have hscratch : readField J
      (TerminalCanonicalization.scratchOffset 259 9) 10 = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_scratch]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hcarry : bitValue J
      (TerminalCanonicalization.carryWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_carry,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hjoint : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_joint,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have houter : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_outer,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hlength : readField J
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
        2 ^ 8 - 1 := by
    rw [show J = preparationInput I by rfl, preparationInput_length]
    exact VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_length
      hterminal
  have hdecoded : TerminalCanonicalization.decodedCounter 259 9 J = depth := by
    apply VQMathlib.Euclid.LuoTerminalCanonicalization.circuit_decodedCounter_eq
      hfit
    · rw [show J = preparationInput I by rfl, preparationInput_low]
      exact VQMathlib.Euclid.PackedTerminalEpoch.read_shift hshiftZero hfit
    · rw [show J = preparationInput I by rfl, preparationInput_epoch]
      exact VQMathlib.Euclid.PackedTerminalEpoch.read_extension hshiftZero hfit
  have hwork : readField J TerminalCanonicalization.workOffset 259 =
      rotatePositionsLeft 259 depth s.tPrime := by
    rw [show J = preparationInput I by rfl, preparationInput_work]
    rw [← VQMathlib.Euclid.PackedTerminalEndpoint.terminal_encodeWork2Raw
      hterminal]
    exact VQMathlib.Euclid.PackedTerminalEpoch.read_workTwo
      (depth := depth) hshiftZero
  have hlocal : readField
      (actGates
        (VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8) J)
      TerminalCanonicalization.workOffset 259 = s.tPrime := by
    exact VQ.Euclid.LuoTerminalEndpoint.preparationGates_read_work
      (by norm_num) (by norm_num [TerminalCanonicalization.counterWidth])
      hscratch hcarry hjoint houter hlength hdecoded hwork htPrimeFit
  have hplaced := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 0) (q := 0) (len := 259) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.workOffset, J, preparationInput] using
      hplaced.trans hlocal

theorem preparationGates_workspace
    {s : State} {depth : Nat}
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (htPrimeFit : s.tPrime < 2 ^ 259) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.preparationGates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        PackedStepLayout.poolOffset 13 = 0 ∧
      readField
        (actGates VQ.Curve.PackedAffineTerminal.preparationGates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        PackedStepLayout.lengthRPrimeOffset 8 = 255 := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let J := preparationInput I
  let R := actGates
    (VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8) J
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 :=
    VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_pool
  have hscratch : readField J
      (TerminalCanonicalization.scratchOffset 259 9) 10 = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_scratch]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hcarry : bitValue J
      (TerminalCanonicalization.carryWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_carry,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hjoint : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_joint,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have houter : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) = 0 := by
    rw [show J = preparationInput I by rfl, preparationInput_outer,
      ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hlength : readField J
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
        2 ^ 8 - 1 := by
    rw [show J = preparationInput I by rfl, preparationInput_length]
    exact VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_length
      hterminal
  have hdecoded : TerminalCanonicalization.decodedCounter 259 9 J = depth := by
    apply VQMathlib.Euclid.LuoTerminalCanonicalization.circuit_decodedCounter_eq
      hfit
    · rw [show J = preparationInput I by rfl, preparationInput_low]
      exact VQMathlib.Euclid.PackedTerminalEpoch.read_shift hshiftZero hfit
    · rw [show J = preparationInput I by rfl, preparationInput_epoch]
      exact VQMathlib.Euclid.PackedTerminalEpoch.read_extension hshiftZero hfit
  have hwork : readField J TerminalCanonicalization.workOffset 259 =
      rotatePositionsLeft 259 depth s.tPrime := by
    rw [show J = preparationInput I by rfl, preparationInput_work]
    rw [← VQMathlib.Euclid.PackedTerminalEndpoint.terminal_encodeWork2Raw
      hterminal]
    exact VQMathlib.Euclid.PackedTerminalEpoch.read_workTwo
      (depth := depth) hshiftZero
  have hlocal := VQ.Euclid.LuoTerminalEndpoint.preparationGates_workspace_clear
    (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
    (lengthWidth := 8) (shift := depth) (raw := s.tPrime) (i := J)
    (by norm_num) (by norm_num)
    (by norm_num [TerminalCanonicalization.counterWidth])
    hscratch hcarry hjoint houter hlength hdecoded hwork htPrimeFit
  have hscratchR : readField R
      (TerminalCanonicalization.scratchOffset 259 9) 10 = 0 := hlocal.1
  have hcarryR : bitValue R
      (TerminalCanonicalization.carryWire 259 9) = 0 := hlocal.2.1
  have hjointR : bitValue R
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) = 0 :=
    hlocal.2.2.1
  have houterR : bitValue R
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) = 0 :=
    hlocal.2.2.2.1
  have hlengthR : readField R
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
        255 := by
    norm_num at hlocal
    exact hlocal.2.2.2.2
  have hplacedScratch := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 3) (q := 0) (len := 10) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  have hplacedCarry := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 4) (q := 0) (len := 1) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  have hplacedJoint := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 5) (q := 0) (len := 1) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  have hplacedOuter := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 6) (q := 0) (len := 1) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  have hplacedLength := readField_actGates_placed
    (gs := VQ.Euclid.LuoTerminalEndpoint.preparationGates 259 9 256 8)
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    (k := 8) (q := 0) (len := 8) (I := I)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg)
    (by decide)
  have hphysicalScratch : readField
      (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
      (PackedStepLayout.poolOffset + 1) 10 = 0 := by
    simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
      TerminalCanonicalization.scratchOffset,
      TerminalCanonicalization.counterWidth, R, J, preparationInput,
      Layout.offset, Layout.size] using hplacedScratch.trans hscratchR
  have hphysicalCarry : bitValue
      (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
      (PackedStepLayout.poolOffset + 11) = 0 := by
    rw [← readField_one]
    simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth, R, J, preparationInput,
      Layout.offset, Layout.size, readField_one] using
        hplacedCarry.trans (show readField R
          (TerminalCanonicalization.carryWire 259 9) 1 = 0 by
            rw [readField_one]
            exact hcarryR)
  have hphysicalJoint : bitValue
      (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
      (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
      VQ.Euclid.LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth, R, J, preparationInput,
      Layout.offset, Layout.size, readField_one] using
        hplacedJoint.trans (show readField R
          (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) 1 = 0 by
            rw [readField_one]
            exact hjointR)
  have hphysicalOuter : bitValue
      (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
      PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
      VQ.Euclid.LuoTerminalCanonicalization.outerWire,
      VQ.Euclid.LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth, R, J, preparationInput,
      Layout.offset, Layout.size, readField_one] using
        hplacedOuter.trans (show readField R
          (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) 1 = 0 by
            rw [readField_one]
            exact houterR)
  have hphysicalLength : readField
      (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
      PackedStepLayout.lengthRPrimeOffset 8 = 255 := by
    simpa [VQ.Curve.PackedAffineTerminal.preparationGates,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
      VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset,
      VQ.Euclid.LuoTerminalExtraction.width,
      VQ.Euclid.LuoTerminalExtraction.outputOffset,
      VQ.Euclid.LuoTerminalCanonicalization.width,
      VQ.Euclid.LuoTerminalCanonicalization.outerWire,
      VQ.Euclid.LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth, R, J, preparationInput,
      Layout.offset, Layout.size] using hplacedLength.trans hlengthR
  constructor
  · rw [show 13 = 1 + 12 by omega, readField_split,
      show 12 = 10 + 2 by omega, readField_split,
      show 2 = 1 + 1 by omega, readField_split]
    exact ⟨by simpa [readField_one] using hphysicalOuter,
      hphysicalScratch, by simpa [readField_one] using hphysicalCarry,
      by simpa [readField_one] using hphysicalJoint⟩
  · exact hphysicalLength

theorem preparationGates_readField_of_outside
    {off len I : Nat}
    (houtside : ∀ j,
      j < VQ.Euclid.PackedTerminalEndpoint.endpointLayout.length →
        VQ.Euclid.PackedTerminalEndpoint.endpointWiring.getD j 0 +
            VQ.Euclid.PackedTerminalEndpoint.endpointLayout.size j ≤ off ∨
          off + len ≤
            VQ.Euclid.PackedTerminalEndpoint.endpointWiring.getD j 0) :
    readField (actGates VQ.Curve.PackedAffineTerminal.preparationGates I)
        off len = readField I off len := by
  apply readField_actGates_map_of_outside
    (w := VQ.Euclid.PackedTerminalEndpoint.endpointLayout.width)
  · intro g hg
    exact List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.preparationGates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg
  · exact place_avoids (by decide) houtside

private def signInput (I : Nat) : Nat :=
  gatherBits
    (place VQ.Curve.PackedAffineTerminal.signLayout
      VQ.Curve.PackedAffineTerminal.signWiring)
    VQ.Curve.PackedAffineTerminal.signLayout.width I

private theorem signInput_field (j I : Nat)
    (hj : j < VQ.Curve.PackedAffineTerminal.signWiring.length) :
    VQ.Curve.PackedAffineTerminal.signLayout.read (signInput I) j =
      readField I
        (VQ.Curve.PackedAffineTerminal.signWiring.getD j 0)
        (VQ.Curve.PackedAffineTerminal.signLayout.size j) := by
  exact read_gatherBits VQ.Curve.PackedAffineTerminal.signLayout
    VQ.Curve.PackedAffineTerminal.signWiring j I hj

private theorem signInput_source (I : Nat) :
    readField (signInput I) SignCorrection.sourceOffset 256 =
      readField I PackedStepLayout.workOneOffset 256 := by
  simpa [signInput, VQ.Curve.PackedAffineTerminal.signLayout,
    VQ.Curve.PackedAffineTerminal.signWiring,
    SignCorrection.controlledLayout, SignCorrection.sourceOffset,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 0 I (by decide)

private theorem signInput_target (I : Nat) :
    readField (signInput I) (SignCorrection.targetOffset 256) 256 =
      readField I PackedStepLayout.workTwoOffset 256 := by
  simpa [signInput, VQ.Curve.PackedAffineTerminal.signLayout,
    VQ.Curve.PackedAffineTerminal.signWiring,
    SignCorrection.controlledLayout, SignCorrection.targetOffset,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 1 I (by decide)

private theorem signInput_carry (I : Nat) :
    bitValue (signInput I) (SignCorrection.carryWire 256) =
      bitValue I PackedStepLayout.phaseOneWire := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Curve.PackedAffineTerminal.signLayout,
    VQ.Curve.PackedAffineTerminal.signWiring,
    SignCorrection.controlledLayout, SignCorrection.carryWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 2 I (by decide)

private theorem signInput_control (I : Nat) :
    bitValue (signInput I) (SignCorrection.controlWire 256) =
      bitValue I PackedStepLayout.iterationWire := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Curve.PackedAffineTerminal.signLayout,
    VQ.Curve.PackedAffineTerminal.signWiring,
    SignCorrection.controlledLayout, SignCorrection.controlWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 3 I (by decide)

private theorem signInput_scratch (I : Nat) :
    bitValue (signInput I) (SignCorrection.controlScratchWire 256) =
      bitValue I PackedStepLayout.phaseTwoWire := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Curve.PackedAffineTerminal.signLayout,
    VQ.Curve.PackedAffineTerminal.signWiring,
    SignCorrection.controlledLayout, SignCorrection.controlScratchWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 4 I (by decide)

theorem signGates_act {I : Nat}
    (hcarry : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hscratch : I.testBit PackedStepLayout.phaseTwoWire = false) :
    actGates VQ.Curve.PackedAffineTerminal.signGates I =
      if bitValue I PackedStepLayout.iterationWire = 0 then
        writeField I PackedStepLayout.workTwoOffset 256
          ((readField I PackedStepLayout.workOneOffset 256 + 2 ^ 256 -
            readField I PackedStepLayout.workTwoOffset 256) % 2 ^ 256)
      else I := by
  let J := signInput I
  have hcarryJ : bitValue J (SignCorrection.carryWire 256) = 0 := by
    rw [show J = signInput I by rfl, signInput_carry]
    exact hcarry
  have hscratchJ :
      J.testBit (SignCorrection.controlScratchWire 256) = false := by
    have hvalue : bitValue J
        (SignCorrection.controlScratchWire 256) = 0 := by
      rw [show J = signInput I by rfl, signInput_scratch]
      simp [bitValue, hscratch]
    cases hbit : J.testBit (SignCorrection.controlScratchWire 256) <;>
      simp_all [bitValue]
  have hlocal := SignCorrection.negativeControlledGates_act
    (width := 256) (i := J) (by norm_num) hcarryJ hscratchJ
  rw [show J = signInput I by rfl, signInput_source, signInput_target,
    signInput_control] at hlocal
  by_cases hiter : bitValue I PackedStepLayout.iterationWire = 0
  · rw [if_pos hiter]
    rw [if_pos hiter] at hlocal
    apply actGates_placed_write
      (L := VQ.Curve.PackedAffineTerminal.signLayout)
      (W := VQ.Curve.PackedAffineTerminal.signWiring) (k := 1)
      VQ.Curve.PackedAffineTerminal.signWiring_disjoint
      (by decide) (by decide)
    · intro g hg
      exact List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed 256) g hg
    · simpa [J, signInput, VQ.Curve.PackedAffineTerminal.signLayout,
        VQ.Curve.PackedAffineTerminal.signWiring,
        SignCorrection.controlledLayout, SignCorrection.targetOffset,
        Layout.write, Layout.offset, Layout.size] using hlocal
  · rw [if_neg hiter]
    rw [if_neg hiter] at hlocal
    have hplaced := actGates_placed_congr (hs := [])
      VQ.Curve.PackedAffineTerminal.signWiring_disjoint
      (by decide)
      (fun g hg => List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed 256) g hg)
      (by simp) I
      (by simpa only [J, signInput, actGates_nil] using hlocal)
    simpa [VQ.Curve.PackedAffineTerminal.signGates, actGates_nil] using
      hplaced

theorem gates_act_terminalEncoding
    {p : Nat} {s : State} {depth : Nat}
    (hpacked : Packed 256 9 9 s)
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    actGates VQ.Curve.PackedAffineTerminal.gates
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) =
      writeField
        (actGates VQ.Curve.PackedAffineTerminal.preparationGates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        PackedStepLayout.workTwoOffset 256
        (VQ.Euclid.decodedInverse p s) := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let P := actGates VQ.Curve.PackedAffineTerminal.preparationGates I
  have htPrimeFit : s.tPrime < 2 ^ 256 := htPrimeLt.trans hpFit
  have hworkWide : readField P PackedStepLayout.workTwoOffset 259 =
      s.tPrime := by
    exact preparationGates_read_workTwo hterminal hshiftZero hfit
      (htPrimeFit.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  have hwork : readField P PackedStepLayout.workTwoOffset 256 =
      s.tPrime := by
    calc
      readField P PackedStepLayout.workTwoOffset 256 =
          readField
            (readField P PackedStepLayout.workTwoOffset 259) 0 256 := by
        symm
        simpa using
          (readField_readField
            (i := P) (D := PackedStepLayout.workTwoOffset)
            (off := 0) (len := 256) (W := 259) (by omega))
      _ = readField s.tPrime 0 256 := by rw [hworkWide]
      _ = s.tPrime := by
        rw [readField_zero, Nat.mod_eq_of_lt htPrimeFit]
  have hsource : readField P PackedStepLayout.workOneOffset 256 = p := by
    rw [show P = actGates VQ.Curve.PackedAffineTerminal.preparationGates I by
      rfl, preparationGates_readField_of_outside (by decide +kernel)]
    exact VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_source
      hpacked hterminal hgcd hrelation hpFit
  have hiter : bitValue P PackedStepLayout.iterationWire =
      boolValue s.iter := by
    rw [← readField_one]
    rw [show P = actGates VQ.Curve.PackedAffineTerminal.preparationGates I by
      rfl, preparationGates_readField_of_outside (by decide +kernel),
      readField_one]
    exact VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_iteration
  have hphaseOne : bitValue P PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one]
    rw [show P = actGates VQ.Curve.PackedAffineTerminal.preparationGates I by
      rfl, preparationGates_readField_of_outside (by decide +kernel)]
    rw [show I =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth by rfl,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseOne,
      hterminal.2.2.2.2.1]
    rfl
  have hphaseTwoValue : bitValue P PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one]
    rw [show P = actGates VQ.Curve.PackedAffineTerminal.preparationGates I by
      rfl, preparationGates_readField_of_outside (by decide +kernel)]
    rw [show I =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth by rfl,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseTwo,
      hterminal.2.2.2.2.2.1]
    rfl
  have hphaseTwo : P.testBit PackedStepLayout.phaseTwoWire = false := by
    cases hbit : P.testBit PackedStepLayout.phaseTwoWire <;>
      simp_all [bitValue]
  have hPdef :
      actGates VQ.Curve.PackedAffineTerminal.preparationGates
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) = P :=
    rfl
  have hsign := signGates_act hphaseOne hphaseTwo
  rw [hsource, hwork, hiter] at hsign
  rw [VQ.Curve.PackedAffineTerminal.gates, actGates_append]
  change actGates VQ.Curve.PackedAffineTerminal.signGates P = _
  rw [hsign, VQ.Euclid.TerminalCircuit.decodedInverse_eq_branch
    htPrimePos htPrimeLt]
  cases hiteration : s.iter with
  | false =>
      simp only [boolValue, Bool.false_eq_true, if_false]
      have heq : p + 2 ^ 256 - s.tPrime =
          2 ^ 256 + (p - s.tPrime) := by omega
      have hdiffFit : p - s.tPrime < 2 ^ 256 := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hdiffFit]
      simp only [if_true]
      rfl
  | true =>
      simp only [boolValue, Nat.one_ne_zero, if_false, if_true]
      rw [hPdef]
      rw [← hwork]
      rw [writeField_read]

theorem reverseGates_act_write_inverse (I value : Nat) :
    actGates VQ.Curve.PackedAffineTerminal.gates.reverse
        (writeField
          (actGates VQ.Curve.PackedAffineTerminal.gates I)
          VQ.Curve.PackedAffineLayout.inverseOffset 256 value) =
      writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 value := by
  have hreverseOutside :
      ∀ g ∈ VQ.Curve.PackedAffineTerminal.gates.reverse,
        ∀ q ∈ g.wires,
          q < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ q :=
    fun g hg => VQ.Curve.PackedAffineTerminal.gates_avoids_inverse
      g (List.mem_reverse.mp hg)
  rw [actGates_write_of_outside hreverseOutside,
    actGates_reverse VQ.Curve.PackedAffineTerminal.gates_wellFormed]

end VQMathlib.Curve.PackedAffineTerminal
