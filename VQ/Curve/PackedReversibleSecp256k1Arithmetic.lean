import VQ.Curve.PackedModularAddition
import VQ.Curve.PackedModularDoubling
import VQ.Curve.PackedReversibleSecp256k1

namespace VQ.Curve.PackedReversibleSecp256k1Arithmetic

open Reversible
open VQ.Curve.PackedReversibleSecp256k1

def constantOffset : Nat := 519

def probeOutputWire : Nat := 552

def oneWire : Nat := 553

def carryOffset : Nat := 554

def width : Nat := 562

def correctionLayout : Layout :=
  [wordWidth, wordWidth, 1, 1, 1, 1, chunkWidth, 1, 1, 8]

def correctionWiring : Wiring :=
  [PackedModularAddition.targetOffset, PackedModularAddition.sourceOffset wordWidth,
    PackedModularAddition.controlWire wordWidth, PackedModularAddition.carryInWire wordWidth,
    PackedModularAddition.reductionWire wordWidth, PackedModularAddition.scratchWire wordWidth,
    constantOffset, probeOutputWire, oneWire, carryOffset]

def placedDetectionGates : List RGate :=
  detectionGates.map (RGate.map (place correctionLayout correctionWiring))

def placedCorrectionGates : List RGate :=
  correctionGates.map (RGate.map (place correctionLayout correctionWiring))

def gathered (i : Nat) : Nat :=
  gatherBits (place correctionLayout correctionWiring)
    correctionLayout.width i

theorem correctionLayout_width : correctionLayout.width =
    VQ.Curve.PackedReversibleSecp256k1.width := by
  decide +kernel

theorem correctionWiring_disjoint :
    Wiring.Disjoint correctionLayout correctionWiring := by
  intro j k hj hk hne
  simp [correctionWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [correctionLayout, correctionWiring, Layout.size,
      PackedModularAddition.targetOffset, PackedModularAddition.sourceOffset,
      PackedModularAddition.controlWire, PackedModularAddition.carryInWire,
      PackedModularAddition.reductionWire, PackedModularAddition.scratchWire,
      constantOffset, probeOutputWire, oneWire, carryOffset,
      wordWidth, chunkWidth] <;> omega

theorem correctionWiring_length :
    correctionLayout.length ≤ correctionWiring.length := by
  simp [correctionLayout, correctionWiring]

theorem correctionWiring_bound {j : Nat}
    (hj : j < correctionLayout.length) :
    correctionWiring.getD j 0 + correctionLayout.size j ≤ width := by
  simp [correctionLayout] at hj
  interval_cases j <;>
    simp [correctionLayout, correctionWiring, Layout.size,
      PackedModularAddition.targetOffset, PackedModularAddition.sourceOffset,
      PackedModularAddition.controlWire, PackedModularAddition.carryInWire,
      PackedModularAddition.reductionWire, PackedModularAddition.scratchWire,
      constantOffset, probeOutputWire, oneWire, carryOffset,
      wordWidth, chunkWidth, width]

private theorem detectionGate_wellFormed :
    ∀ gate ∈ detectionGates,
      gate.wellFormed correctionLayout.width = true := by
  intro gate hgate
  rw [correctionLayout_width]
  exact List.all_eq_true.mp detectionGates_wellFormed gate hgate

private theorem correctionGate_wellFormed :
    ∀ gate ∈ correctionGates,
      gate.wellFormed correctionLayout.width = true := by
  intro gate hgate
  rw [correctionLayout_width]
  exact List.all_eq_true.mp correctionGates_wellFormed gate hgate

theorem placedDetectionGates_wellFormed :
    placedDetectionGates.all (RGate.wellFormed width) = true := by
  exact wellFormed_placeGates correctionWiring_disjoint
    correctionWiring_length (fun _ hj => correctionWiring_bound hj)
    detectionGate_wellFormed

theorem placedCorrectionGates_wellFormed :
    placedCorrectionGates.all (RGate.wellFormed width) = true := by
  exact wellFormed_placeGates correctionWiring_disjoint
    correctionWiring_length (fun _ hj => correctionWiring_bound hj)
    correctionGate_wellFormed

theorem readField_gathered_target (i : Nat) :
    readField (gathered i) targetOffset wordWidth =
      readField i PackedModularAddition.targetOffset wordWidth := by
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, targetOffset] using
      readField_gatherBits correctionLayout correctionWiring 0 i (by decide)

theorem readField_gathered_constant (i : Nat) :
    readField (gathered i)
        VQ.Curve.PackedReversibleSecp256k1.constantOffset chunkWidth =
      readField i constantOffset chunkWidth := by
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, VQ.Curve.PackedReversibleSecp256k1.constantOffset,
    wordWidth, chunkWidth]
    using readField_gatherBits correctionLayout correctionWiring 6 i (by decide)

theorem bitValue_gathered_zeroCarry (i : Nat) :
    bitValue (gathered i) zeroCarryWire =
      bitValue i (PackedModularAddition.carryInWire wordWidth) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, zeroCarryWire, wordWidth] using
      readField_gatherBits correctionLayout correctionWiring 3 i (by decide)

theorem bitValue_gathered_reduction (i : Nat) :
    bitValue (gathered i) reductionWire =
      bitValue i (PackedModularAddition.reductionWire wordWidth) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, reductionWire, wordWidth] using
      readField_gatherBits correctionLayout correctionWiring 4 i (by decide)

theorem bitValue_gathered_scratch (i : Nat) :
    bitValue (gathered i) scratchWire =
      bitValue i (PackedModularAddition.scratchWire wordWidth) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, scratchWire, wordWidth] using
      readField_gatherBits correctionLayout correctionWiring 5 i (by decide)

theorem bitValue_gathered_output (i : Nat) :
    bitValue (gathered i)
        VQ.Curve.PackedReversibleSecp256k1.probeOutputWire =
      bitValue i probeOutputWire := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, VQ.Curve.PackedReversibleSecp256k1.probeOutputWire,
    wordWidth, chunkWidth] using
      readField_gatherBits correctionLayout correctionWiring 7 i (by decide)

theorem bitValue_gathered_one (i : Nat) :
    bitValue (gathered i)
        VQ.Curve.PackedReversibleSecp256k1.oneWire = bitValue i oneWire := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, VQ.Curve.PackedReversibleSecp256k1.oneWire,
    wordWidth, chunkWidth] using
      readField_gatherBits correctionLayout correctionWiring 8 i (by decide)

theorem bitValue_gathered_carry {i chunk : Nat} (hchunk : chunk < 8) :
    bitValue (gathered i) (carryWire chunk) =
      bitValue i (carryOffset + chunk) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, correctionLayout, correctionWiring, Layout.offset,
    Layout.size, carryWire, wordWidth, chunkWidth] using
      readField_gatherBits_sub correctionLayout correctionWiring 9 chunk 1 i
        (by decide) (by
          simp [correctionLayout, Layout.size]
          omega)

theorem placedDetectionGates_act {i x : Nat}
    (hx : readField i PackedModularAddition.targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hone : bitValue i oneWire = 0)
    (hscratch : i.testBit (PackedModularAddition.scratchWire wordWidth) = false)
    (hzeroCarry : bitValue i (PackedModularAddition.carryInWire wordWidth) = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryOffset + chunk) = 0) :
    actGates placedDetectionGates i =
      writeField i (PackedModularAddition.reductionWire wordWidth) 1
        ((bitValue i (PackedModularAddition.reductionWire wordWidth) +
          (gap + x) / 2 ^ wordWidth) % 2) := by
  change actGates
      (detectionGates.map (RGate.map
        (place correctionLayout correctionWiring))) i = _
  apply actGates_placed_write (gs := detectionGates)
    correctionWiring_disjoint correctionWiring_length
    (k := 4) (by decide) detectionGate_wellFormed
  have hscratchLocal : (gathered i).testBit scratchWire = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 (by
      rw [bitValue_gathered_scratch]
      exact (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hscratch)
  have hlocal := detectionGates_act
    (i := gathered i) (x := x)
    (by simpa [readField_gathered_target] using hx)
    (by simpa [readField_gathered_constant] using hconstant)
    (by simpa [bitValue_gathered_output] using houtput)
    (by simpa [bitValue_gathered_one] using hone)
    hscratchLocal
    (by simpa [bitValue_gathered_zeroCarry] using hzeroCarry)
    (fun chunk hchunk => by
      rw [bitValue_gathered_carry hchunk]
      exact hcarries chunk hchunk)
  have hoff : correctionLayout.offset 4 = reductionWire := by decide +kernel
  have hsize : correctionLayout.size 4 = 1 := by decide +kernel
  change actGates detectionGates (gathered i) =
    writeField (gathered i) reductionWire 1
      ((bitValue i (PackedModularAddition.reductionWire wordWidth) +
        (gap + x) / 2 ^ wordWidth) % 2)
  simpa only [Layout.write, hoff, hsize, bitValue_gathered_reduction] using hlocal

theorem placedCorrectionGates_enabled {i x : Nat}
    (hx : readField i PackedModularAddition.targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i (PackedModularAddition.reductionWire wordWidth) = 1)
    (hscratch : i.testBit (PackedModularAddition.scratchWire wordWidth) = false)
    (hzeroCarry : bitValue i (PackedModularAddition.carryInWire wordWidth) = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryOffset + chunk) = 0) :
    actGates placedCorrectionGates i =
      writeField i PackedModularAddition.targetOffset wordWidth (gap + x) := by
  change actGates
      (correctionGates.map (RGate.map
        (place correctionLayout correctionWiring))) i = _
  apply actGates_placed_write (gs := correctionGates)
    correctionWiring_disjoint correctionWiring_length
    (k := 0) (by decide) correctionGate_wellFormed
  have hscratchLocal : (gathered i).testBit scratchWire = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 (by
      rw [bitValue_gathered_scratch]
      exact (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hscratch)
  have hlocal := correctionGates_enabled
    (i := gathered i) (x := x)
    (by simpa [readField_gathered_target] using hx)
    (by simpa [readField_gathered_constant] using hconstant)
    (by simpa [bitValue_gathered_output] using houtput)
    (by simpa [bitValue_gathered_reduction] using hcontrol)
    hscratchLocal
    (by simpa [bitValue_gathered_zeroCarry] using hzeroCarry)
    (fun chunk hchunk => by
      rw [bitValue_gathered_carry hchunk]
      exact hcarries chunk hchunk)
  have hoff : correctionLayout.offset 0 = targetOffset := by decide +kernel
  have hsize : correctionLayout.size 0 = wordWidth := by rfl
  change actGates correctionGates (gathered i) =
    writeField (gathered i) targetOffset wordWidth (gap + x)
  simpa only [Layout.write, hoff, hsize] using hlocal

theorem placedCorrectionGates_disabled {i : Nat}
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i (PackedModularAddition.reductionWire wordWidth) = 0)
    (hscratch : i.testBit (PackedModularAddition.scratchWire wordWidth) = false)
    (hzeroCarry : bitValue i (PackedModularAddition.carryInWire wordWidth) = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryOffset + chunk) = 0) :
    actGates placedCorrectionGates i = i := by
  change actGates
      (correctionGates.map (RGate.map
        (place correctionLayout correctionWiring))) i = actGates [] i
  apply actGates_placed_congr (gs := correctionGates) (hs := [])
    correctionWiring_disjoint correctionWiring_length
    correctionGate_wellFormed (by simp) i
  have hscratchLocal : (gathered i).testBit scratchWire = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 (by
      rw [bitValue_gathered_scratch]
      exact (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hscratch)
  change actGates correctionGates (gathered i) = actGates [] (gathered i)
  rw [correctionGates_disabled
    (by simpa [readField_gathered_constant] using hconstant)
    (by simpa [bitValue_gathered_output] using houtput)
    (by simpa [bitValue_gathered_reduction] using hcontrol)
    hscratchLocal
    (by simpa [bitValue_gathered_zeroCarry] using hzeroCarry)
    (fun chunk hchunk => by
      rw [bitValue_gathered_carry hchunk]
      exact hcarries chunk hchunk)]
  rfl

def rawSum (i : Nat) : Nat :=
  PackedModularAddition.selectedSource wordWidth i +
    readField i PackedModularAddition.targetOffset wordWidth

def wrappedValue (i : Nat) : Nat := rawSum i % 2 ^ wordWidth

def variableFlag (i : Nat) : Nat :=
  (bitValue i (PackedModularAddition.reductionWire wordWidth) +
    rawSum i / 2 ^ wordWidth) % 2

def detectionOverflow (i : Nat) : Nat :=
  (gap + wrappedValue i) / 2 ^ wordWidth

def reductionValue (i : Nat) : Nat :=
  (variableFlag i + detectionOverflow i) % 2

def correctedValue (i : Nat) : Nat :=
  if reductionValue i = 1 then
    (gap + wrappedValue i) % 2 ^ wordWidth
  else
    wrappedValue i

def finalFlag (i : Nat) : Nat :=
  (reductionValue i +
    bitValue i (PackedModularAddition.controlWire wordWidth) *
      Adder.borrow
        (readField i (PackedModularAddition.sourceOffset wordWidth) wordWidth)
        (correctedValue i)) % 2

def variableIndex (i : Nat) : Nat :=
  writeField
    (writeField i PackedModularAddition.targetOffset wordWidth (wrappedValue i))
    (PackedModularAddition.reductionWire wordWidth) 1 (variableFlag i)

def detectedIndex (i : Nat) : Nat :=
  writeField (variableIndex i)
    (PackedModularAddition.reductionWire wordWidth) 1 (reductionValue i)

def correctedIndex (i : Nat) : Nat :=
  writeField (detectedIndex i)
    PackedModularAddition.targetOffset wordWidth (correctedValue i)

def modularAddIndex (i : Nat) : Nat :=
  writeField (correctedIndex i)
    (PackedModularAddition.reductionWire wordWidth) 1 (finalFlag i)

def modularAddGates : List RGate :=
  PackedModularAddition.variableAddGates wordWidth ++
    placedDetectionGates ++
    placedCorrectionGates ++
    PackedModularAddition.flagEraseGates wordWidth

def modularDoubleGates : List RGate :=
  PackedModularDoubling.doubleShiftGates wordWidth ++
    placedDetectionGates ++
    placedCorrectionGates ++
    [.cx PackedModularAddition.targetOffset
      (PackedModularAddition.reductionWire wordWidth)]

structure CorrectionWorkspaceClear (i : Nat) : Prop where
  constant : readField i constantOffset chunkWidth = 0
  output : bitValue i probeOutputWire = 0
  one : bitValue i oneWire = 0
  scratch : bitValue i (PackedModularAddition.scratchWire wordWidth) = 0
  zeroCarry : bitValue i (PackedModularAddition.carryInWire wordWidth) = 0
  carries : ∀ chunk, chunk < 8 → bitValue i (carryOffset + chunk) = 0

theorem CorrectionWorkspaceClear.writeTarget {i : Nat}
    (h : CorrectionWorkspaceClear i) (value : Nat) :
    CorrectionWorkspaceClear
      (writeField i PackedModularAddition.targetOffset wordWidth value) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      left
      simp [PackedModularAddition.targetOffset, constantOffset, wordWidth])]
    exact h.constant
  · rw [bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset, probeOutputWire, wordWidth])]
    exact h.output
  · rw [bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset, oneWire, wordWidth])]
    exact h.one
  · rw [bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.scratchWire, wordWidth])]
    exact h.scratch
  · rw [bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.carryInWire, wordWidth])]
    exact h.zeroCarry
  · intro chunk hchunk
    rw [bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset, carryOffset, wordWidth]
      omega)]
    exact h.carries chunk hchunk

theorem CorrectionWorkspaceClear.writeReduction {i : Nat}
    (h : CorrectionWorkspaceClear i) (value : Nat) :
    CorrectionWorkspaceClear
      (writeField i (PackedModularAddition.reductionWire wordWidth) 1 value) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      left
      simp [PackedModularAddition.reductionWire, constantOffset, wordWidth])]
    exact h.constant
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire, probeOutputWire, wordWidth])]
    exact h.output
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire, oneWire, wordWidth])]
    exact h.one
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.scratchWire, wordWidth])]
    exact h.scratch
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.carryInWire, wordWidth])]
    exact h.zeroCarry
  · intro chunk hchunk
    rw [bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire, carryOffset, wordWidth]
      omega)]
    exact h.carries chunk hchunk

theorem CorrectionWorkspaceClear.writeControl {i : Nat}
    (h : CorrectionWorkspaceClear i) (value : Nat) :
    CorrectionWorkspaceClear
      (writeField i (PackedModularAddition.controlWire wordWidth) 1 value) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      left
      simp [PackedModularAddition.controlWire, constantOffset, wordWidth])]
    exact h.constant
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.controlWire, probeOutputWire, wordWidth])]
    exact h.output
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.controlWire, oneWire, wordWidth])]
    exact h.one
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.controlWire,
        PackedModularAddition.scratchWire, wordWidth])]
    exact h.scratch
  · rw [bitValue_write_ne (by
      simp [PackedModularAddition.controlWire,
        PackedModularAddition.carryInWire, wordWidth])]
    exact h.zeroCarry
  · intro chunk hchunk
    rw [bitValue_write_ne (by
      simp [PackedModularAddition.controlWire, carryOffset, wordWidth]
      omega)]
    exact h.carries chunk hchunk

theorem variableAddGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    actGates (PackedModularAddition.variableAddGates wordWidth) i =
      variableIndex i := by
  simpa [variableIndex, wrappedValue, variableFlag, rawSum] using
    PackedModularAddition.variableAddGates_act
      (wordWidth := wordWidth) (i := i) (by decide)
      hworkspace.zeroCarry hworkspace.scratch

theorem readField_variableIndex_target (i : Nat) :
    readField (variableIndex i)
      PackedModularAddition.targetOffset wordWidth = wrappedValue i := by
  rw [variableIndex,
    readField_writeField_of_disjoint (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.reductionWire, wordWidth]),
    readField_writeField]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))

theorem bitValue_variableIndex_reduction (i : Nat) :
    bitValue (variableIndex i)
      (PackedModularAddition.reductionWire wordWidth) = variableFlag i := by
  rw [variableIndex, bitValue_write_self]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))

theorem placedDetectionGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    actGates placedDetectionGates (variableIndex i) = detectedIndex i := by
  have hworkspace' :=
    (hworkspace.writeTarget (wrappedValue i)).writeReduction (variableFlag i)
  have hact := placedDetectionGates_act
    (i := variableIndex i) (x := wrappedValue i)
    (readField_variableIndex_target i)
    hworkspace'.constant hworkspace'.output hworkspace'.one
    ((testBit_eq_false_iff_bitValue_eq_zero _ _).2 hworkspace'.scratch)
    hworkspace'.zeroCarry hworkspace'.carries
  simpa [detectedIndex, reductionValue, detectionOverflow,
    bitValue_variableIndex_reduction] using hact

theorem readField_detectedIndex_target (i : Nat) :
    readField (detectedIndex i)
      PackedModularAddition.targetOffset wordWidth = wrappedValue i := by
  rw [detectedIndex,
    readField_writeField_of_disjoint (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.reductionWire, wordWidth]),
    readField_variableIndex_target]

theorem bitValue_detectedIndex_reduction (i : Nat) :
    bitValue (detectedIndex i)
      (PackedModularAddition.reductionWire wordWidth) = reductionValue i := by
  rw [detectedIndex, bitValue_write_self]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

theorem placedCorrectionGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    actGates placedCorrectionGates (detectedIndex i) = correctedIndex i := by
  have hworkspace' := ((hworkspace.writeTarget (wrappedValue i)).writeReduction
    (variableFlag i)).writeReduction (reductionValue i)
  have hcases : reductionValue i = 0 ∨ reductionValue i = 1 := by
    have hlt : reductionValue i < 2 := Nat.mod_lt _ (by omega)
    omega
  rcases hcases with hzero | hone
  · have hact := placedCorrectionGates_disabled
      (i := detectedIndex i)
      hworkspace'.constant hworkspace'.output
      (by simpa [bitValue_detectedIndex_reduction] using hzero)
      ((testBit_eq_false_iff_bitValue_eq_zero _ _).2 hworkspace'.scratch)
      hworkspace'.zeroCarry hworkspace'.carries
    rw [hact]
    unfold correctedIndex correctedValue
    simp only [hzero, zero_ne_one, if_false]
    rw [← readField_detectedIndex_target i, writeField_read]
  · have hact := placedCorrectionGates_enabled
      (i := detectedIndex i) (x := wrappedValue i)
      (readField_detectedIndex_target i)
      hworkspace'.constant hworkspace'.output
      (by simpa [bitValue_detectedIndex_reduction] using hone)
      ((testBit_eq_false_iff_bitValue_eq_zero _ _).2 hworkspace'.scratch)
      hworkspace'.zeroCarry hworkspace'.carries
    simpa [correctedIndex, correctedValue, hone, writeField_mod] using hact

theorem correctedValue_lt (i : Nat) : correctedValue i < 2 ^ wordWidth := by
  unfold correctedValue
  split
  · exact Nat.mod_lt _ (by positivity)
  · exact Nat.mod_lt _ (by positivity)

theorem readField_correctedIndex_target (i : Nat) :
    readField (correctedIndex i)
      PackedModularAddition.targetOffset wordWidth = correctedValue i := by
  rw [correctedIndex, readField_writeField,
    Nat.mod_eq_of_lt (correctedValue_lt i)]

theorem bitValue_correctedIndex_reduction (i : Nat) :
    bitValue (correctedIndex i)
      (PackedModularAddition.reductionWire wordWidth) = reductionValue i := by
  rw [correctedIndex, bitValue_write_out (by
    right
    simp [PackedModularAddition.targetOffset,
      PackedModularAddition.reductionWire, wordWidth]),
    bitValue_detectedIndex_reduction]

theorem readField_correctedIndex_source (i : Nat) :
    readField (correctedIndex i)
        (PackedModularAddition.sourceOffset wordWidth) wordWidth =
      readField i (PackedModularAddition.sourceOffset wordWidth) wordWidth := by
  rw [correctedIndex,
    readField_writeField_of_disjoint (by
      left
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.sourceOffset, wordWidth]),
    detectedIndex,
    readField_writeField_of_disjoint (by
      right
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.sourceOffset, wordWidth]),
    variableIndex,
    readField_writeField_of_disjoint (by
      right
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.sourceOffset, wordWidth]),
    readField_writeField_of_disjoint (by
      left
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.sourceOffset, wordWidth])]

theorem bitValue_correctedIndex_control (i : Nat) :
    bitValue (correctedIndex i)
        (PackedModularAddition.controlWire wordWidth) =
      bitValue i (PackedModularAddition.controlWire wordWidth) := by
  rw [correctedIndex, bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.controlWire, wordWidth]),
    detectedIndex, bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.controlWire, wordWidth]),
    variableIndex, bitValue_write_ne (by
      simp [PackedModularAddition.reductionWire,
        PackedModularAddition.controlWire, wordWidth]),
    bitValue_write_out (by
      right
      simp [PackedModularAddition.targetOffset,
        PackedModularAddition.controlWire, wordWidth])]

theorem flagEraseGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    actGates (PackedModularAddition.flagEraseGates wordWidth)
        (correctedIndex i) =
      modularAddIndex i := by
  have hworkspace' := (((hworkspace.writeTarget (wrappedValue i)).writeReduction
    (variableFlag i)).writeReduction (reductionValue i)).writeTarget
      (correctedValue i)
  have hact := PackedModularAddition.flagEraseGates_act
    (wordWidth := wordWidth) (i := correctedIndex i) (by decide)
    hworkspace'.zeroCarry hworkspace'.scratch
  simpa [modularAddIndex, finalFlag, bitValue_correctedIndex_reduction,
    bitValue_correctedIndex_control, readField_correctedIndex_source,
    readField_correctedIndex_target] using hact

private theorem all_wellFormed_mono {gates : List RGate} {w w' : Nat}
    (hww : w ≤ w')
    (h : gates.all (RGate.wellFormed w) = true) :
    gates.all (RGate.wellFormed w') = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  exact RGate.wellFormed_mono hww (List.all_eq_true.mp h gate hgate)

theorem modularAddGates_wellFormed :
    modularAddGates.all (RGate.wellFormed width) = true := by
  have hsmall : PackedModularAddition.width wordWidth ≤ width := by
    decide +kernel
  have hvariable := all_wellFormed_mono hsmall
    (PackedModularAddition.variableAddGates_wellFormed
      (wordWidth := wordWidth) (by decide))
  have herase := all_wellFormed_mono hsmall
    (PackedModularAddition.flagEraseGates_wellFormed
      (wordWidth := wordWidth) (by decide))
  simpa [modularAddGates, List.all_append] using
    And.intro hvariable
      (And.intro placedDetectionGates_wellFormed
        (And.intro placedCorrectionGates_wellFormed herase))

theorem modularAddGates_act {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    actGates modularAddGates i = modularAddIndex i := by
  simp only [modularAddGates, actGates_append]
  rw [variableAddGates_act_exact hworkspace,
    placedDetectionGates_act_exact hworkspace,
    placedCorrectionGates_act_exact hworkspace,
    flagEraseGates_act_exact hworkspace]

theorem modularDoubleGates_wellFormed :
    modularDoubleGates.all (RGate.wellFormed width) = true := by
  have hsmall : PackedModularAddition.width wordWidth ≤ width := by
    decide +kernel
  have hshift := all_wellFormed_mono hsmall
    (PackedModularDoubling.doubleShiftGates_wellFormed
      (wordWidth := wordWidth) (by decide))
  have herase :
      ([.cx PackedModularAddition.targetOffset
        (PackedModularAddition.reductionWire wordWidth)] : List RGate).all
          (RGate.wellFormed width) = true := by
    simp [RGate.wellFormed, width, PackedModularAddition.targetOffset,
      PackedModularAddition.reductionWire, wordWidth]
  simpa [modularDoubleGates, List.all_append] using
    And.intro hshift
      (And.intro placedDetectionGates_wellFormed
        (And.intro placedCorrectionGates_wellFormed herase))

def multiplierOffset : Nat := width

def productWidth : Nat := multiplierOffset + wordWidth

def controlToggleGates (bit : Nat) : List RGate :=
  [.cx (multiplierOffset + bit)
    (PackedModularAddition.controlWire wordWidth)]

def controlledAddGates (bit : Nat) : List RGate :=
  controlToggleGates bit ++ modularAddGates ++ controlToggleGates bit

def productGatesAux : List Nat → List RGate
  | [] => []
  | [bit] => controlledAddGates bit
  | bit :: nextBit :: rest =>
      productGatesAux (nextBit :: rest) ++ modularDoubleGates ++
        controlledAddGates bit

def modularProductGates : List RGate :=
  productGatesAux (List.range wordWidth)

theorem controlToggleGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlToggleGates bit).all (RGate.wellFormed productWidth) = true := by
  have hbit' : bit < 256 := by simpa [wordWidth] using hbit
  simp [controlToggleGates, RGate.wellFormed, multiplierOffset, productWidth,
    width, PackedModularAddition.controlWire, wordWidth]
  omega

private theorem modularAddGates_product_wellFormed :
    modularAddGates.all (RGate.wellFormed productWidth) = true := by
  exact all_wellFormed_mono (by
    simp [productWidth, multiplierOffset]) modularAddGates_wellFormed

private theorem modularDoubleGates_product_wellFormed :
    modularDoubleGates.all (RGate.wellFormed productWidth) = true := by
  exact all_wellFormed_mono (by
    simp [productWidth, multiplierOffset]) modularDoubleGates_wellFormed

theorem controlledAddGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlledAddGates bit).all (RGate.wellFormed productWidth) = true := by
  simp [controlledAddGates, controlToggleGates_wellFormed hbit,
    modularAddGates_product_wellFormed]

theorem productGatesAux_wellFormed :
    ∀ bits,
      (∀ bit ∈ bits, bit < wordWidth) →
      (productGatesAux bits).all (RGate.wellFormed productWidth) = true
  | [], _ => by rfl
  | [bit], hbits => by
      exact controlledAddGates_wellFormed (hbits bit (by simp))
  | bit :: nextBit :: rest, hbits => by
      simp only [productGatesAux, List.all_append, Bool.and_eq_true]
      exact And.intro
        (And.intro
          (productGatesAux_wellFormed (nextBit :: rest)
            (fun q hq => hbits q (List.mem_cons_of_mem bit hq)))
          modularDoubleGates_product_wellFormed)
        (controlledAddGates_wellFormed (hbits bit (by simp)))

theorem modularProductGates_wellFormed :
    modularProductGates.all (RGate.wellFormed productWidth) = true := by
  apply productGatesAux_wellFormed
  intro bit hbit
  exact List.mem_range.mp hbit

end VQ.Curve.PackedReversibleSecp256k1Arithmetic
