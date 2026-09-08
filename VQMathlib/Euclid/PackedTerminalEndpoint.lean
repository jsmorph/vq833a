import VQ.Euclid.PackedTerminalEndpoint
import VQ.Euclid.InputPreparation
import VQMathlib.Euclid.LuoTerminalEndpoint
import VQMathlib.Euclid.PackedTerminalEpoch

namespace VQMathlib.Euclid.PackedTerminalEndpoint

open VQ
open VQ.Euclid
open VQ.Reversible
open LuoActiveWindows

private def endpointInput (I : Nat) : Nat :=
  gatherBits
    (place VQ.Euclid.PackedTerminalEndpoint.endpointLayout
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring)
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout.width I

private theorem endpointInput_field (j I : Nat)
    (hj : j < VQ.Euclid.PackedTerminalEndpoint.endpointWiring.length) :
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout.read
        (endpointInput I) j =
      readField I
        (VQ.Euclid.PackedTerminalEndpoint.endpointWiring.getD j 0)
        (VQ.Euclid.PackedTerminalEndpoint.endpointLayout.size j) := by
  exact read_gatherBits
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring j I hj

private theorem endpointInput_work (I : Nat) :
    readField (endpointInput I) TerminalCanonicalization.workOffset 259 =
      readField I PackedStepLayout.workTwoOffset 259 := by
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.workOffset, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 0 I (by decide)

private theorem endpointInput_low (I : Nat) :
    readField (endpointInput I)
        (TerminalCanonicalization.counterOffset 259) 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.counterOffset, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 1 I (by decide)

private theorem endpointInput_epoch (I : Nat) :
    bitValue (endpointInput I)
        (TerminalCanonicalization.epochWire 259 9) =
      bitValue I PackedStepLayout.extensionWire := by
  rw [← readField_one, ← readField_one]
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.epochWire,
    TerminalCanonicalization.counterOffset, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 2 I (by decide)

private theorem endpointInput_scratch (I : Nat) :
    readField (endpointInput I)
        (TerminalCanonicalization.scratchOffset 259 9) 10 =
      readField I (PackedStepLayout.poolOffset + 1) 10 := by
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.scratchOffset,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 3 I (by decide)

private theorem endpointInput_carry (I : Nat) :
    bitValue (endpointInput I)
        (TerminalCanonicalization.carryWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 11) := by
  rw [← readField_one, ← readField_one]
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 4 I (by decide)

private theorem endpointInput_joint (I : Nat) :
    bitValue (endpointInput I)
        (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 12) := by
  rw [← readField_one, ← readField_one]
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 5 I (by decide)

private theorem endpointInput_outer (I : Nat) :
    bitValue (endpointInput I)
        (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalCanonicalization.outerWire,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 6 I (by decide)

private theorem endpointInput_output (I : Nat) :
    readField (endpointInput I)
        (VQ.Euclid.LuoTerminalEndpoint.outputOffset 259 9) 256 =
      readField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 := by
  simpa [endpointInput,
    VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring,
    VQ.Euclid.LuoTerminalEndpoint.outputOffset,
    VQ.Euclid.LuoTerminalExtraction.outputOffset,
    VQ.Euclid.LuoTerminalCanonicalization.width,
    VQ.Euclid.LuoTerminalCanonicalization.outerWire,
    VQ.Euclid.LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire,
    TerminalCanonicalization.counterWidth, Layout.read, Layout.offset,
    Layout.size] using endpointInput_field 7 I (by decide)

private theorem endpointInput_length (I : Nat) :
    readField (endpointInput I)
        (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
      readField I PackedStepLayout.lengthRPrimeOffset 8 := by
  simpa [endpointInput,
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
    Layout.size] using endpointInput_field 8 I (by decide)

theorem endpointGates_act_of_clear
    {depth raw I : Nat}
    (hfit : depth < 2 ^ (9 + 1))
    (hlow : readField I PackedStepLayout.shiftOffset 9 =
      terminalLow 9 depth)
    (hepoch : bitValue I PackedStepLayout.extensionWire =
      terminalEpoch 9 depth)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 10 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 11) = 0)
    (hjoint : bitValue I (PackedStepLayout.poolOffset + 12) = 0)
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (hterminalLength :
      readField I PackedStepLayout.lengthRPrimeOffset 8 = 2 ^ 8 - 1)
    (hwork : readField I PackedStepLayout.workTwoOffset 259 =
      rotatePositionsLeft 259 depth raw)
    (hraw : raw < 2 ^ 259)
    (houtput : readField I
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 = 0) :
    actGates VQ.Euclid.PackedTerminalEndpoint.endpointGates I =
      writeField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
        (readField raw 0 256) := by
  let J := endpointInput I
  have hlocalLow : readField J
      (TerminalCanonicalization.counterOffset 259) 9 =
        terminalLow 9 depth := by
    rw [show J = endpointInput I by rfl, endpointInput_low]
    exact hlow
  have hlocalEpoch : bitValue J
      (TerminalCanonicalization.epochWire 259 9) =
        terminalEpoch 9 depth := by
    rw [show J = endpointInput I by rfl, endpointInput_epoch]
    exact hepoch
  have hlocalScratch : readField J
      (TerminalCanonicalization.scratchOffset 259 9) 10 = 0 := by
    rw [show J = endpointInput I by rfl, endpointInput_scratch]
    exact hscratch
  have hlocalCarry : bitValue J
      (TerminalCanonicalization.carryWire 259 9) = 0 := by
    rw [show J = endpointInput I by rfl, endpointInput_carry]
    exact hcarry
  have hlocalJoint : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire 259 9) = 0 := by
    rw [show J = endpointInput I by rfl, endpointInput_joint]
    exact hjoint
  have hlocalOuter : bitValue J
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire 259 9) = 0 := by
    rw [show J = endpointInput I by rfl, endpointInput_outer]
    exact houter
  have hlocalLength : readField J
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset 259 9 256) 8 =
        2 ^ 8 - 1 := by
    rw [show J = endpointInput I by rfl, endpointInput_length]
    exact hterminalLength
  have hlocalWork : readField J
      TerminalCanonicalization.workOffset 259 =
        rotatePositionsLeft 259 depth raw := by
    rw [show J = endpointInput I by rfl, endpointInput_work]
    exact hwork
  have hlocalOutput : readField J
      (VQ.Euclid.LuoTerminalEndpoint.outputOffset 259 9) 256 = 0 := by
    rw [show J = endpointInput I by rfl, endpointInput_output]
    exact houtput
  have hlocal :=
    VQMathlib.Euclid.LuoTerminalEndpoint.source_terminal_endpoint_gates_act_of_clear
      (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
      (lengthWidth := 8) (depth := depth) (raw := raw) (i := J)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [TerminalCanonicalization.counterWidth]) hfit
      hlocalLow hlocalEpoch hlocalScratch hlocalCarry hlocalJoint hlocalOuter
      hlocalLength hlocalWork hraw hlocalOutput
  apply actGates_placed_write
    (L := VQ.Euclid.PackedTerminalEndpoint.endpointLayout)
    (W := VQ.Euclid.PackedTerminalEndpoint.endpointWiring) (k := 7)
    VQ.Euclid.PackedTerminalEndpoint.endpointWiring_disjoint
    (by decide) (by decide)
  · intro g hg
    rw [VQ.Euclid.PackedTerminalEndpoint.endpointLayout_width]
    exact List.all_eq_true.mp
      (VQ.Euclid.LuoTerminalEndpoint.gates_wellFormed
        (workWidth := 259) (shiftWidth := 9) (outputWidth := 256)
        (lengthWidth := 8) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [TerminalCanonicalization.counterWidth])) g hg
  · simpa [J, endpointInput,
      VQ.Euclid.PackedTerminalEndpoint.endpointLayout,
      VQ.Euclid.PackedTerminalEndpoint.endpointWiring, Layout.write,
      Layout.offset, Layout.size,
      VQ.Euclid.LuoTerminalEndpoint.outputOffset,
      VQ.Euclid.LuoTerminalExtraction.outputOffset,
      VQ.Euclid.LuoTerminalCanonicalization.width,
      VQ.Euclid.LuoTerminalCanonicalization.outerWire,
      VQ.Euclid.LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] using hlocal

theorem terminalEncoding_pool {s : State} {depth : Nat} :
    readField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        PackedStepLayout.poolOffset 13 = 0 := by
  rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
    (by decide) (by decide) (by decide) (by decide)]
  exact PackedState.read_pool s

theorem terminalEncoding_length
    {s : State} {depth : Nat} (hterminal : Terminal s) :
    readField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        PackedStepLayout.lengthRPrimeOffset 8 = 2 ^ 8 - 1 := by
  rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
    (by decide) (by decide) (by decide) (by decide),
    PackedState.read_lengthRPrime, hterminal.2.1]
  decide +kernel

theorem terminal_encodeWork2Raw
    {s : State} (hterminal : Terminal s) :
    encodeWork2Raw 256 s = s.tPrime := by
  simp [encodeWork2Raw, hterminal.1, hterminal.2.1, reverseBits]

private theorem terminalEncoding_output_clear {s : State} {depth : Nat} :
    readField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 = 0 := by
  rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
    (by decide) (by decide) (by decide) (by decide)]
  exact VQ.Euclid.InputPreparation.readField_zero_above
    (PackedState.encoded_lt s) (by
      rw [VQ.Euclid.PackedTerminalEndpoint.outputOffset,
        PackedStepLayout.layout_width])

theorem endpointGates_act_terminalEncoding
    {s : State} {depth : Nat}
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (htPrimeFit : s.tPrime < 2 ^ 256) :
    actGates VQ.Euclid.PackedTerminalEndpoint.endpointGates
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) =
      writeField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 s.tPrime := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    exact terminalEncoding_pool (s := s) (depth := depth)
  have hpool10 : readField I (PackedStepLayout.poolOffset + 1) 10 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hpoolBit (offset : Nat)
      (hlow : PackedStepLayout.poolOffset ≤ offset)
      (hhigh : offset + 1 ≤ PackedStepLayout.poolOffset + 13) :
      bitValue I offset = 0 := by
    rw [← readField_one]
    exact readField_sub_zero hlow hhigh hpool
  have hlength : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      2 ^ 8 - 1 := by
    exact terminalEncoding_length (s := s) (depth := depth) hterminal
  have hrawEq : encodeWork2Raw 256 s = s.tPrime :=
    terminal_encodeWork2Raw hterminal
  have hrawFit : s.tPrime < 2 ^ 259 :=
    htPrimeFit.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have houtput : readField I
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 = 0 := by
    exact terminalEncoding_output_clear (s := s) (depth := depth)
  have hwork : readField I PackedStepLayout.workTwoOffset 259 =
      rotatePositionsLeft 259 depth s.tPrime := by
    rw [← hrawEq]
    exact VQMathlib.Euclid.PackedTerminalEpoch.read_workTwo
      (depth := depth) hshiftZero
  have hact := endpointGates_act_of_clear
    (I := I) (raw := s.tPrime) hfit
    (VQMathlib.Euclid.PackedTerminalEpoch.read_shift hshiftZero hfit)
    (VQMathlib.Euclid.PackedTerminalEpoch.read_extension hshiftZero hfit)
    hpool10
    (hpoolBit (PackedStepLayout.poolOffset + 11) (by omega) (by omega))
    (hpoolBit (PackedStepLayout.poolOffset + 12) (by omega) (by omega))
    (hpoolBit PackedStepLayout.poolOffset (by omega) (by omega))
    hlength hwork hrawFit houtput
  rw [readField_zero, Nat.mod_eq_of_lt htPrimeFit] at hact
  exact hact

private def signInput (I : Nat) : Nat :=
  gatherBits
    (place VQ.Euclid.PackedTerminalEndpoint.signLayout
      VQ.Euclid.PackedTerminalEndpoint.signWiring)
    VQ.Euclid.PackedTerminalEndpoint.signLayout.width I

private theorem signInput_field (j I : Nat)
    (hj : j < VQ.Euclid.PackedTerminalEndpoint.signWiring.length) :
    VQ.Euclid.PackedTerminalEndpoint.signLayout.read (signInput I) j =
      readField I
        (VQ.Euclid.PackedTerminalEndpoint.signWiring.getD j 0)
        (VQ.Euclid.PackedTerminalEndpoint.signLayout.size j) := by
  exact read_gatherBits
    VQ.Euclid.PackedTerminalEndpoint.signLayout
    VQ.Euclid.PackedTerminalEndpoint.signWiring j I hj

private theorem signInput_source (I : Nat) :
    readField (signInput I) SignCorrection.sourceOffset 256 =
      readField I PackedStepLayout.workOneOffset 256 := by
  simpa [signInput, VQ.Euclid.PackedTerminalEndpoint.signLayout,
    VQ.Euclid.PackedTerminalEndpoint.signWiring,
    SignCorrection.controlledLayout, SignCorrection.sourceOffset,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 0 I (by decide)

private theorem signInput_target (I : Nat) :
    readField (signInput I) (SignCorrection.targetOffset 256) 256 =
      readField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 := by
  simpa [signInput, VQ.Euclid.PackedTerminalEndpoint.signLayout,
    VQ.Euclid.PackedTerminalEndpoint.signWiring,
    SignCorrection.controlledLayout, SignCorrection.targetOffset,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 1 I (by decide)

private theorem signInput_carry (I : Nat) :
    bitValue (signInput I) (SignCorrection.carryWire 256) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Euclid.PackedTerminalEndpoint.signLayout,
    VQ.Euclid.PackedTerminalEndpoint.signWiring,
    SignCorrection.controlledLayout, SignCorrection.carryWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 2 I (by decide)

private theorem signInput_control (I : Nat) :
    bitValue (signInput I) (SignCorrection.controlWire 256) =
      bitValue I PackedStepLayout.iterationWire := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Euclid.PackedTerminalEndpoint.signLayout,
    VQ.Euclid.PackedTerminalEndpoint.signWiring,
    SignCorrection.controlledLayout, SignCorrection.controlWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 3 I (by decide)

private theorem signInput_scratch (I : Nat) :
    bitValue (signInput I) (SignCorrection.controlScratchWire 256) =
      bitValue I (PackedStepLayout.poolOffset + 1) := by
  rw [← readField_one, ← readField_one]
  simpa [signInput, VQ.Euclid.PackedTerminalEndpoint.signLayout,
    VQ.Euclid.PackedTerminalEndpoint.signWiring,
    SignCorrection.controlledLayout, SignCorrection.controlScratchWire,
    Layout.read, Layout.offset, Layout.size] using
      signInput_field 4 I (by decide)

theorem signGates_act {I : Nat}
    (hcarry : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : I.testBit (PackedStepLayout.poolOffset + 1) = false) :
    actGates VQ.Euclid.PackedTerminalEndpoint.signGates I =
      if bitValue I PackedStepLayout.iterationWire = 0 then
        writeField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
          ((readField I PackedStepLayout.workOneOffset 256 + 2 ^ 256 -
            readField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256) %
            2 ^ 256)
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
      (L := VQ.Euclid.PackedTerminalEndpoint.signLayout)
      (W := VQ.Euclid.PackedTerminalEndpoint.signWiring) (k := 1)
      VQ.Euclid.PackedTerminalEndpoint.signWiring_disjoint
      (by decide) (by decide)
    · intro g hg
      exact List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed 256) g hg
    · simpa [J, signInput,
        VQ.Euclid.PackedTerminalEndpoint.signLayout,
        VQ.Euclid.PackedTerminalEndpoint.signWiring,
        SignCorrection.controlledLayout, SignCorrection.targetOffset,
        Layout.write, Layout.offset, Layout.size] using hlocal
  · rw [if_neg hiter]
    rw [if_neg hiter] at hlocal
    have hplaced := actGates_placed_congr (hs := [])
      VQ.Euclid.PackedTerminalEndpoint.signWiring_disjoint
      (by decide)
      (fun g hg => List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed 256) g hg)
      (by simp) I
      (by simpa only [J, signInput, actGates_nil] using hlocal)
    simpa [VQ.Euclid.PackedTerminalEndpoint.signGates, actGates_nil] using
      hplaced

theorem terminalEncoding_iteration {s : State} {depth : Nat} :
    bitValue
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        PackedStepLayout.iterationWire = boolValue s.iter := by
  rw [← readField_one]
  rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
    (by decide) (by decide) (by decide) (by decide)]
  rw [readField_one]
  exact PackedState.read_iteration s

private theorem packedState_workOne_prefix (s : State) :
    readField (PackedState.encoded s) PackedStepLayout.workOneOffset 256 =
      readField (encodeWork1 256 s) 0 256 := by
  calc
    readField (PackedState.encoded s) PackedStepLayout.workOneOffset 256 =
        readField
          (readField (PackedState.encoded s)
            PackedStepLayout.workOneOffset 259) 0 256 := by
      symm
      simpa [PackedStepLayout.workOneOffset] using
        (readField_readField_zero
          (i := PackedState.encoded s) (off := 0) (len := 256) (W := 259)
          (by omega))
    _ = readField (encodeWork1 256 s) 0 256 := by
      rw [PackedState.read_workOne]
      change readField (readField (encodeWork1 256 s) 0 259) 0 256 = _
      exact readField_readField_zero (by omega)

private theorem stepState_workOne_prefix (s : State) :
    readField (StepState.encoded 256 9 9 s) StepLayout.work1Offset 256 =
      readField (encodeWork1 256 s) 0 256 := by
  calc
    readField (StepState.encoded 256 9 9 s) StepLayout.work1Offset 256 =
        readField
          (readField (StepState.encoded 256 9 9 s)
            StepLayout.work1Offset 259) 0 256 := by
      symm
      simpa [StepLayout.work1Offset] using
        (readField_readField_zero
          (i := StepState.encoded 256 9 9 s) (off := 0) (len := 256)
          (W := 259) (by omega))
    _ = readField (encodeWork1 256 s) 0 256 := by
      rw [show (259 : Nat) = VQ.Euclid.workWidth 256 by
        norm_num [VQ.Euclid.workWidth], StepState.read_work1]
      change readField (readField (encodeWork1 256 s) 0 259) 0 256 = _
      exact readField_readField_zero (by omega)

theorem terminalEncoding_source
    {p : Nat} {s : State} {depth : Nat}
    (hpacked : Packed 256 9 9 s)
    (hterminal : Terminal s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : Relation p s)
    (hpFit : p < 2 ^ 256) :
    readField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        PackedStepLayout.workOneOffset 256 = p := by
  rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
    (by decide) (by decide) (by decide) (by decide),
    packedState_workOne_prefix]
  rw [← stepState_workOne_prefix]
  exact VQ.Euclid.TerminalCircuit.read_source_encoded_terminal_of_gcd
    hpacked hterminal hgcd hrelation hpFit

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
    actGates VQ.Euclid.PackedTerminalEndpoint.gates
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) =
      writeField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
        (decodedInverse p s) := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let E := writeField I VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
    s.tPrime
  have htPrimeFit : s.tPrime < 2 ^ 256 := htPrimeLt.trans hpFit
  have hendpoint :
      actGates VQ.Euclid.PackedTerminalEndpoint.endpointGates I = E := by
    exact endpointGates_act_terminalEncoding hterminal hshiftZero hfit
      htPrimeFit
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    exact terminalEncoding_pool (s := s) (depth := depth)
  have hcarryE : bitValue E PackedStepLayout.poolOffset = 0 := by
    rw [show E = writeField I
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 s.tPrime by rfl,
      bitValue_write_out (Or.inl (by decide)), ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hscratchE : E.testBit (PackedStepLayout.poolOffset + 1) = false := by
    have hvalue : bitValue E (PackedStepLayout.poolOffset + 1) = 0 := by
      rw [show E = writeField I
        VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 s.tPrime by rfl,
        bitValue_write_out (Or.inl (by decide)), ← readField_one]
      exact readField_sub_zero (by omega) (by omega) hpool
    cases hbit : E.testBit (PackedStepLayout.poolOffset + 1) <;>
      simp_all [bitValue]
  have hsourceE : readField E PackedStepLayout.workOneOffset 256 = p := by
    rw [show E = writeField I
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 s.tPrime by rfl,
      readField_writeField_of_disjoint (Or.inr (by decide))]
    exact terminalEncoding_source hpacked hterminal hgcd hrelation hpFit
  have htargetE : readField E
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 = s.tPrime := by
    exact readField_writeField_self htPrimeFit
  have hiterE : bitValue E PackedStepLayout.iterationWire =
      boolValue s.iter := by
    rw [show E = writeField I
      VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 s.tPrime by rfl,
      bitValue_write_out (Or.inl (by decide))]
    exact terminalEncoding_iteration
  have hsign := signGates_act hcarryE hscratchE
  rw [hsourceE, htargetE, hiterE] at hsign
  rw [VQ.Euclid.PackedTerminalEndpoint.gates, actGates_append, hendpoint,
    hsign, VQ.Euclid.TerminalCircuit.decodedInverse_eq_branch
      htPrimePos htPrimeLt]
  cases hiter : s.iter with
  | false =>
      simp only [boolValue, Bool.false_eq_true, if_false]
      have heq : p + 2 ^ 256 - s.tPrime =
          2 ^ 256 + (p - s.tPrime) := by omega
      have hdiffFit : p - s.tPrime < 2 ^ 256 := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hdiffFit]
      simp only [E, writeField_writeField, if_true]
      rfl
  | true => exact rfl

theorem inverterGates_act_of_terminal
    {p a tau depth : Nat} {rounds : List RGate}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p)
    (htau : 0 < tau)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run 9 9 k (preprocessedState p a)))
    (hterminal : Terminal (run 9 9 tau (preprocessedState p a)))
    (hshift : (run 9 9 tau (preprocessedState p a)).shift = 0)
    (hdepth : depth < 2 ^ (9 + 1))
    (hwellFormed : rounds.all (RGate.wellFormed PackedStepLayout.width) = true)
    (hforward : actGates rounds (PackedState.encoded (preprocessedState p a)) =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding
        (run 9 9 tau (preprocessedState p a)) depth) :
    ∃ inverse,
      actGates (rounds ++ VQ.Euclid.PackedTerminalEndpoint.gates ++ rounds.reverse)
          (PackedState.encoded (preprocessedState p a)) =
        writeField (PackedState.encoded (preprocessedState p a))
          VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 inverse ∧
      inverse < p ∧
      a * inverse ≡ 1 [MOD p] := by
  let initial := PackedState.encoded (preprocessedState p a)
  let final := run 9 9 tau (preprocessedState p a)
  have hinitial : ReachableStepDomain p 256 9 9
      (preprocessedState p a) :=
    preprocessedState_reachable hpFit
      (by norm_num [VQ.Euclid.workWidth]) ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  have hfinalReachable : ReachableStepDomain p 256 9 9 final := by
    exact hreachable tau (Nat.le_refl tau)
  have hpacked : Packed 256 9 9 final :=
    hfinalReachable.stepDomain.valid.1
  have hrelation : Relation p final := hfinalReachable.stepDomain.relation
  have hinverseRelation : InverseRelation p a final := by
    exact inverseRelation_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      (preprocessedState_inverseRelation ha0 ha) hlive
  have hgcd : Nat.gcd final.r final.rPrime = 1 := by
    have h := remainderGCD_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hlive
    rw [preprocessedState_gcd_eq_one hpPrime ha0 ha] at h
    exact h
  have hsigned :
      (a : Int) * signedCoefficient final ≡ 1 [ZMOD (p : Int)] :=
    signedCoefficient_is_inverse hinverseRelation hgcd hterminal
  have htPrimeBounds : 0 < final.tPrime ∧ final.tPrime < p := by
    exact first_terminal_tPrime_bounds hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hpPrime.two_le
      htau hlive hterminal hsigned
  have hendpoint :
      actGates VQ.Euclid.PackedTerminalEndpoint.gates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth) =
        writeField
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth)
          VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
          (decodedInverse p final) := by
    exact gates_act_terminalEncoding hpacked hterminal hshift
      hdepth hgcd hrelation
      htPrimeBounds.1 htPrimeBounds.2 hpFit
  have hforward' :
      actGates rounds initial =
        VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth := by
    exact hforward
  have hreverse :
      actGates rounds.reverse
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth) =
        initial := by
    have h := actGates_reverse hwellFormed initial
    simpa only [hforward'] using h
  have hreverseOutside :
      ∀ g ∈ rounds.reverse, ∀ q ∈ g.wires,
        q < VQ.Euclid.PackedTerminalEndpoint.outputOffset ∨
          VQ.Euclid.PackedTerminalEndpoint.outputOffset + 256 ≤ q := by
    intro g hg q hq
    left
    exact wire_lt_of_wellFormed
      (List.all_eq_true.mp hwellFormed g (List.mem_reverse.mp hg)) hq
  have haction :
      actGates (rounds ++ VQ.Euclid.PackedTerminalEndpoint.gates ++ rounds.reverse)
          initial =
        writeField initial VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
          (decodedInverse p final) := by
    rw [actGates_append, actGates_append, hforward', hendpoint,
      actGates_write_of_outside hreverseOutside]
    exact congrArg
      (fun value => writeField value
        VQ.Euclid.PackedTerminalEndpoint.outputOffset 256
        (decodedInverse p final)) hreverse
  refine ⟨decodedInverse p final, ?_, decodedInverse_lt hpPrime.pos final,
    decodedInverse_is_inverse hpPrime.pos hsigned⟩
  simpa [initial, final] using haction

theorem inverterGates_act_preprocessed
    {p a : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256)
    (hpBits : bitLength p = 256)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ inverse,
      actGates VQ.Euclid.PackedTerminalEndpoint.inverterGates
          (PackedState.encoded (preprocessedState p a)) =
        writeField (PackedState.encoded (preprocessedState p a))
          VQ.Euclid.PackedTerminalEndpoint.outputOffset 256 inverse ∧
      inverse < p ∧
      a * inverse ≡ 1 [MOD p] := by
  obtain ⟨tau, htauLower, _htauUpper, hlive, hterminal, hshift,
      hdepth, _haligned, _hcompressed, hforward⟩ :=
    VQMathlib.Euclid.PackedTerminalEpoch.preprocessed_roundsGates_act_1620
      hpPrime hpFit hpBits ha0 ha
  exact inverterGates_act_of_terminal hpPrime hpFit ha0 ha (by omega)
    hlive hterminal hshift (by omega)
    (VQ.Euclid.PackedTerminalEpoch.roundsGates_wellFormed 1620) hforward

end VQMathlib.Euclid.PackedTerminalEndpoint
