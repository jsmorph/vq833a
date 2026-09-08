import VQ.Curve.PackedReversibleSecp256k1Arithmetic
import VQMathlib.Curve.PackedModularDoubling

namespace VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

open VQ
open VQ.Reversible

namespace Arithmetic

open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

def controlBit (i : Nat) : Bool :=
  i.testBit (VQ.Curve.PackedModularAddition.controlWire wordWidth)

def sourceValue (i : Nat) : Nat :=
  readField i (VQ.Curve.PackedModularAddition.sourceOffset wordWidth) wordWidth

def targetValue (i : Nat) : Nat :=
  readField i VQ.Curve.PackedModularAddition.targetOffset wordWidth

theorem rawSum_eq_luo (i : Nat) :
    rawSum i = VQBridge.Curve.LuoMultiplication.rawSum
      (controlBit i) (sourceValue i) (targetValue i) := by
  cases hcontrol : i.testBit
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) <;>
    simp [rawSum, VQ.Curve.PackedModularAddition.selectedSource,
      controlBit, sourceValue, targetValue,
      VQBridge.Curve.LuoMultiplication.rawSum,
      VQBridge.Curve.LuoMultiplication.bitValue, hcontrol, Nat.add_comm]

theorem rawSum_lt_twice_p {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p) :
    rawSum i < 2 * VQ.Curve.p := by
  rw [rawSum_eq_luo]
  exact VQBridge.Curve.LuoMultiplication.rawSum_lt_twice_modulus
    hsource htarget

theorem variableFlag_eq_overflow {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    variableFlag i = if 2 ^ wordWidth ≤ rawSum i then 1 else 0 := by
  have hsum := rawSum_lt_twice_p hsource htarget
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hsumWord : rawSum i < 2 * 2 ^ wordWidth := by omega
  unfold variableFlag
  rw [hreduction, Nat.zero_add]
  by_cases hoverflow : 2 ^ wordWidth ≤ rawSum i
  · rw [if_pos hoverflow]
    have hdiv : rawSum i / 2 ^ wordWidth = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hoverflow
      · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsumWord
    simp [hdiv]
  · rw [if_neg hoverflow]
    have hlt : rawSum i < 2 ^ wordWidth := by omega
    rw [Nat.div_eq_of_lt hlt]

theorem detectionOverflow_eq_comparison (i : Nat) :
    detectionOverflow i =
      if VQ.Curve.p ≤ wrappedValue i then 1 else 0 := by
  have hpPos : 0 < VQ.Curve.p := VQ.Curve.p_pos
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hwrapped : wrappedValue i < 2 ^ wordWidth :=
    Nat.mod_lt _ (by positivity)
  rw [detectionOverflow, gap_eq]
  by_cases hcomparison : VQ.Curve.p ≤ wrappedValue i
  · rw [if_pos hcomparison]
    have hlower : 2 ^ wordWidth ≤
        2 ^ wordWidth - VQ.Curve.p + wrappedValue i := by omega
    have hupper : 2 ^ wordWidth - VQ.Curve.p + wrappedValue i <
        2 * 2 ^ wordWidth := by omega
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using hlower
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hupper
  · rw [if_neg hcomparison]
    have hlt : 2 ^ wordWidth - VQ.Curve.p + wrappedValue i <
        2 ^ wordWidth := by omega
    exact Nat.div_eq_of_lt hlt

theorem reductionValue_eq_flag {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    reductionValue i = VQBridge.Curve.LuoMultiplication.bitValue
      (VQBridge.Curve.LuoMultiplication.reductionFlag
        (2 ^ wordWidth) VQ.Curve.p (rawSum i)) := by
  rw [reductionValue, variableFlag_eq_overflow hsource htarget hreduction,
    detectionOverflow_eq_comparison]
  unfold wrappedValue
  unfold VQBridge.Curve.LuoMultiplication.reductionFlag
    VQBridge.Curve.LuoMultiplication.bitValue
  by_cases hoverflow : 2 ^ wordWidth ≤ rawSum i <;>
    by_cases hcomparison : VQ.Curve.p ≤ rawSum i % 2 ^ wordWidth <;>
      simp [hoverflow, hcomparison]

theorem correctedValue_eq_mod {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    correctedValue i = rawSum i % VQ.Curve.p := by
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hsum := rawSum_lt_twice_p hsource htarget
  have hcorrect :
      VQBridge.Curve.LuoMultiplication.wordCorrection
          (2 ^ wordWidth) VQ.Curve.p (rawSum i) =
        rawSum i % VQ.Curve.p :=
    VQBridge.Curve.LuoMultiplication.wordCorrection_correct
      VQ.Curve.p_pos hp hsum
  rw [correctedValue, reductionValue_eq_flag hsource htarget hreduction,
    gap_eq]
  rw [← hcorrect]
  cases hflag : VQBridge.Curve.LuoMultiplication.reductionFlag
      (2 ^ wordWidth) VQ.Curve.p (rawSum i) <;>
    simp [VQBridge.Curve.LuoMultiplication.wordCorrection,
      VQBridge.Curve.LuoMultiplication.bitValue, wrappedValue, hflag,
      Nat.add_comm]

theorem controlValue_eq_bitValue (i : Nat) :
    bitValue i (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue (controlBit i) := by
  unfold bitValue controlBit VQBridge.Curve.LuoMultiplication.bitValue
  cases i.testBit
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) <;> rfl

theorem finalFlag_eq_zero {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    finalFlag i = 0 := by
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have huncompute :
      VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) VQ.Curve.p (rawSum i) =
        (controlBit i && decide (rawSum i % VQ.Curve.p < sourceValue i)) := by
    have h := VQBridge.Curve.LuoMultiplication.reductionFlag_uncompute
      (controlBit i) hp hsource htarget
    simpa [VQBridge.Curve.LuoMultiplication.correctedAccumulator,
      ← rawSum_eq_luo] using h
  unfold finalFlag
  rw [reductionValue_eq_flag hsource htarget hreduction,
    correctedValue_eq_mod hsource htarget hreduction,
    controlValue_eq_bitValue]
  change
    (VQBridge.Curve.LuoMultiplication.bitValue
        (VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) VQ.Curve.p (rawSum i)) +
      VQBridge.Curve.LuoMultiplication.bitValue (controlBit i) *
        Adder.borrow (sourceValue i) (rawSum i % VQ.Curve.p)) % 2 = 0
  cases hcontrol : controlBit i <;>
    by_cases hlt : rawSum i % VQ.Curve.p < sourceValue i <;>
      simp [hcontrol, hlt] at huncompute <;>
      simp [hlt, huncompute,
        VQBridge.Curve.LuoMultiplication.bitValue,
        Adder.borrow]

theorem modularAddIndex_eq {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    modularAddIndex i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (rawSum i % VQ.Curve.p) := by
  have hdisjoint :
      VQ.Curve.PackedModularAddition.targetOffset + wordWidth ≤
        VQ.Curve.PackedModularAddition.reductionWire wordWidth ∨
      VQ.Curve.PackedModularAddition.reductionWire wordWidth + 1 ≤
        VQ.Curve.PackedModularAddition.targetOffset := by
    left
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.reductionWire, wordWidth]
  have hclear :
      writeField i (VQ.Curve.PackedModularAddition.reductionWire wordWidth)
        1 0 = i := by
    apply write_of_bitValue
    simp [hreduction]
  rw [modularAddIndex, correctedIndex, detectedIndex, variableIndex,
    correctedValue_eq_mod hsource htarget hreduction,
    finalFlag_eq_zero hsource htarget hreduction,
    writeField_writeField,
    writeField_overwrite_alternating_of_disjoint hdisjoint,
    writeField_comm hdisjoint, hclear]

theorem modularAddGates_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    actGates modularAddGates i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (rawSum i % VQ.Curve.p) := by
  rw [modularAddGates_act hworkspace,
    modularAddIndex_eq hsource htarget hreduction]

end Arithmetic

namespace Double

open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

def targetValue (i : Nat) : Nat :=
  readField i VQ.Curve.PackedModularAddition.targetOffset wordWidth

def rawDouble (i : Nat) : Nat := 2 * targetValue i

def wrappedValue (i : Nat) : Nat := rawDouble i % 2 ^ wordWidth

def variableFlag (i : Nat) : Nat := rawDouble i / 2 ^ wordWidth % 2

def detectionOverflow (i : Nat) : Nat :=
  (gap + wrappedValue i) / 2 ^ wordWidth

def reductionValue (i : Nat) : Nat :=
  (variableFlag i + detectionOverflow i) % 2

def correctedValue (i : Nat) : Nat :=
  if reductionValue i = 1 then
    (gap + wrappedValue i) % 2 ^ wordWidth
  else
    wrappedValue i

def shiftedIndex (i : Nat) : Nat :=
  VQ.Curve.PackedModularDoubling.shiftedIndex wordWidth i

def detectedIndex (i : Nat) : Nat :=
  writeField (shiftedIndex i)
    (VQ.Curve.PackedModularAddition.reductionWire wordWidth) 1
    (reductionValue i)

def correctedIndex (i : Nat) : Nat :=
  writeField (detectedIndex i)
    VQ.Curve.PackedModularAddition.targetOffset wordWidth (correctedValue i)

def finalFlag (i : Nat) : Nat :=
  (reductionValue i + correctedValue i % 2) % 2

def modularDoubleIndex (i : Nat) : Nat :=
  writeField (correctedIndex i)
    (VQ.Curve.PackedModularAddition.reductionWire wordWidth) 1 (finalFlag i)

theorem readField_shifted_constant (i : Nat) :
    readField (shiftedIndex i)
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset chunkWidth =
      readField i
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset chunkWidth := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_readField, testBit_readField]
  by_cases hbit : bit < chunkWidth
  · simp only [hbit, decide_true, Bool.true_and]
    unfold shiftedIndex VQ.Curve.PackedModularDoubling.shiftedIndex
    rw [VQ.Curve.PackedModularDoubling.doubleShiftGates_testBit_other
      (by decide) (by
        simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset,
          wordWidth]
        omega) (by
        simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset,
          VQ.Curve.PackedModularAddition.reductionWire, wordWidth]
        omega)]
  · simp [hbit]

theorem bitValue_shifted_other {i wire : Nat}
    (hge : wordWidth ≤ wire)
    (hne : wire ≠ VQ.Curve.PackedModularAddition.reductionWire wordWidth) :
    bitValue (shiftedIndex i) wire = bitValue i wire := by
  unfold bitValue shiftedIndex VQ.Curve.PackedModularDoubling.shiftedIndex
  rw [VQ.Curve.PackedModularDoubling.doubleShiftGates_testBit_other
    (by decide) hge hne]

theorem shiftedWorkspace {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i) :
    CorrectionWorkspaceClear (shiftedIndex i) := by
  constructor
  · rw [readField_shifted_constant]
    exact hworkspace.constant
  · rw [bitValue_shifted_other (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.probeOutputWire,
        wordWidth]) (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.probeOutputWire,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]
    exact hworkspace.output
  · rw [bitValue_shifted_other (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire,
        wordWidth]) (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]
    exact hworkspace.one
  · rw [bitValue_shifted_other (by
      simp [VQ.Curve.PackedModularAddition.scratchWire, wordWidth]) (by
      simp [VQ.Curve.PackedModularAddition.scratchWire,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]
    exact hworkspace.scratch
  · rw [bitValue_shifted_other (by
      simp [VQ.Curve.PackedModularAddition.carryInWire, wordWidth]) (by
      simp [VQ.Curve.PackedModularAddition.carryInWire,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]
    exact hworkspace.zeroCarry
  · intro chunk hchunk
    rw [bitValue_shifted_other (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset,
        wordWidth]
      omega) (by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth]
      omega)]
    exact hworkspace.carries chunk hchunk

theorem shiftedIndex_target {i : Nat}
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    readField (shiftedIndex i)
        VQ.Curve.PackedModularAddition.targetOffset wordWidth =
      wrappedValue i := by
  simpa [shiftedIndex, wrappedValue, rawDouble, targetValue,
    VQMathlib.Curve.PackedModularDoubling.rawDouble,
    VQMathlib.Curve.PackedModularDoubling.targetValue] using
    VQMathlib.Curve.PackedModularDoubling.shiftedIndex_target
      (wordWidth := wordWidth) (original := i) (by decide) hreduction

theorem shiftedIndex_reduction {i : Nat}
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    bitValue (shiftedIndex i)
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      variableFlag i := by
  simpa [shiftedIndex, variableFlag, rawDouble, targetValue,
    VQMathlib.Curve.PackedModularDoubling.rawDouble,
    VQMathlib.Curve.PackedModularDoubling.targetValue] using
    VQMathlib.Curve.PackedModularDoubling.shiftedIndex_reduction
      (wordWidth := wordWidth) (original := i) (by decide) hreduction

theorem placedDetectionGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    actGates placedDetectionGates (shiftedIndex i) = detectedIndex i := by
  have hworkspace' := shiftedWorkspace hworkspace
  have hact :=
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.placedDetectionGates_act
      (i := shiftedIndex i) (x := wrappedValue i)
      (shiftedIndex_target hreduction)
      hworkspace'.constant hworkspace'.output hworkspace'.one
      ((testBit_eq_false_iff_bitValue_eq_zero _ _).2 hworkspace'.scratch)
      hworkspace'.zeroCarry hworkspace'.carries
  simpa [detectedIndex, reductionValue, detectionOverflow,
    shiftedIndex_reduction hreduction] using hact

theorem readField_detectedIndex_target {i : Nat}
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    readField (detectedIndex i)
        VQ.Curve.PackedModularAddition.targetOffset wordWidth =
      wrappedValue i := by
  rw [detectedIndex, readField_writeField_of_disjoint (by
      right
      simp [VQ.Curve.PackedModularAddition.targetOffset,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth]),
    shiftedIndex_target hreduction]

theorem bitValue_detectedIndex_reduction (i : Nat) :
    bitValue (detectedIndex i)
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      reductionValue i := by
  rw [detectedIndex, bitValue_write_self]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

theorem placedCorrectionGates_act_exact {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    actGates placedCorrectionGates (detectedIndex i) = correctedIndex i := by
  have hworkspace' :=
    (shiftedWorkspace hworkspace).writeReduction (reductionValue i)
  have hcases : reductionValue i = 0 ∨ reductionValue i = 1 := by
    have hlt : reductionValue i < 2 := Nat.mod_lt _ (by omega)
    omega
  rcases hcases with hzero | hone
  · have hact :=
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.placedCorrectionGates_disabled
        (i := detectedIndex i)
        hworkspace'.constant hworkspace'.output
        (by simpa [bitValue_detectedIndex_reduction] using hzero)
        ((testBit_eq_false_iff_bitValue_eq_zero _ _).2 hworkspace'.scratch)
        hworkspace'.zeroCarry hworkspace'.carries
    rw [hact]
    unfold correctedIndex correctedValue
    simp only [hzero, zero_ne_one, if_false]
    rw [← readField_detectedIndex_target hreduction, writeField_read]
  · have hact :=
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.placedCorrectionGates_enabled
        (i := detectedIndex i) (x := wrappedValue i)
        (readField_detectedIndex_target hreduction)
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

theorem bitValue_correctedIndex_target (i : Nat) :
    bitValue (correctedIndex i)
        VQ.Curve.PackedModularAddition.targetOffset = correctedValue i % 2 := by
  rw [← readField_one, correctedIndex,
    readField_writeField_narrow (by decide),
    Nat.pow_one]

theorem bitValue_correctedIndex_reduction (i : Nat) :
    bitValue (correctedIndex i)
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      reductionValue i := by
  rw [correctedIndex, bitValue_write_out (by
      right
      simp [VQ.Curve.PackedModularAddition.targetOffset,
        VQ.Curve.PackedModularAddition.reductionWire, wordWidth]),
    bitValue_detectedIndex_reduction]

theorem finalEraseGates_act_exact {i : Nat} :
    actGates
        [.cx VQ.Curve.PackedModularAddition.targetOffset
          (VQ.Curve.PackedModularAddition.reductionWire wordWidth)]
        (correctedIndex i) =
      modularDoubleIndex i := by
  simp [modularDoubleIndex, finalFlag, actGates_cons, actGates_nil,
    act_cx_write, bitValue_correctedIndex_reduction,
    bitValue_correctedIndex_target]

theorem modularDoubleGates_act {i : Nat}
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    actGates modularDoubleGates i = modularDoubleIndex i := by
  simp only [modularDoubleGates, actGates_append]
  change actGates
      [.cx VQ.Curve.PackedModularAddition.targetOffset
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth)]
      (actGates placedCorrectionGates
        (actGates placedDetectionGates (shiftedIndex i))) = _
  rw [placedDetectionGates_act_exact hworkspace hreduction,
    placedCorrectionGates_act_exact hworkspace hreduction,
    finalEraseGates_act_exact]

theorem rawDouble_lt_twice_p {i : Nat} (htarget : targetValue i < VQ.Curve.p) :
    rawDouble i < 2 * VQ.Curve.p := by
  simp [rawDouble]
  omega

theorem variableFlag_eq_overflow {i : Nat}
    (htarget : targetValue i < VQ.Curve.p) :
    variableFlag i = if 2 ^ wordWidth ≤ rawDouble i then 1 else 0 := by
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hsum := rawDouble_lt_twice_p htarget
  have hsumWord : rawDouble i < 2 * 2 ^ wordWidth := by omega
  unfold variableFlag
  by_cases hoverflow : 2 ^ wordWidth ≤ rawDouble i
  · rw [if_pos hoverflow]
    have hdiv : rawDouble i / 2 ^ wordWidth = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hoverflow
      · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsumWord
    simp [hdiv]
  · rw [if_neg hoverflow]
    have hlt : rawDouble i < 2 ^ wordWidth := by omega
    rw [Nat.div_eq_of_lt hlt]

theorem detectionOverflow_eq_comparison (i : Nat) :
    detectionOverflow i =
      if VQ.Curve.p ≤ wrappedValue i then 1 else 0 := by
  have hpPos : 0 < VQ.Curve.p := VQ.Curve.p_pos
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hwrapped : wrappedValue i < 2 ^ wordWidth :=
    Nat.mod_lt _ (by positivity)
  rw [detectionOverflow, gap_eq]
  by_cases hcomparison : VQ.Curve.p ≤ wrappedValue i
  · rw [if_pos hcomparison]
    have hlower : 2 ^ wordWidth ≤
        2 ^ wordWidth - VQ.Curve.p + wrappedValue i := by omega
    have hupper : 2 ^ wordWidth - VQ.Curve.p + wrappedValue i <
        2 * 2 ^ wordWidth := by omega
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using hlower
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hupper
  · rw [if_neg hcomparison]
    have hlt : 2 ^ wordWidth - VQ.Curve.p + wrappedValue i <
        2 ^ wordWidth := by omega
    exact Nat.div_eq_of_lt hlt

theorem reductionValue_eq_flag {i : Nat}
    (htarget : targetValue i < VQ.Curve.p) :
    reductionValue i = VQBridge.Curve.LuoMultiplication.bitValue
      (VQBridge.Curve.LuoMultiplication.reductionFlag
        (2 ^ wordWidth) VQ.Curve.p (rawDouble i)) := by
  rw [reductionValue, variableFlag_eq_overflow htarget,
    detectionOverflow_eq_comparison]
  unfold wrappedValue
  unfold VQBridge.Curve.LuoMultiplication.reductionFlag
    VQBridge.Curve.LuoMultiplication.bitValue
  by_cases hoverflow : 2 ^ wordWidth ≤ rawDouble i <;>
    by_cases hcomparison : VQ.Curve.p ≤ rawDouble i % 2 ^ wordWidth <;>
      simp [hoverflow, hcomparison]

theorem correctedValue_eq_mod {i : Nat}
    (htarget : targetValue i < VQ.Curve.p) :
    correctedValue i = rawDouble i % VQ.Curve.p := by
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hsum := rawDouble_lt_twice_p htarget
  have hcorrect :
      VQBridge.Curve.LuoMultiplication.wordCorrection
          (2 ^ wordWidth) VQ.Curve.p (rawDouble i) =
        rawDouble i % VQ.Curve.p :=
    VQBridge.Curve.LuoMultiplication.wordCorrection_correct
      VQ.Curve.p_pos hp hsum
  rw [correctedValue, reductionValue_eq_flag htarget, gap_eq, ← hcorrect]
  cases hflag : VQBridge.Curve.LuoMultiplication.reductionFlag
      (2 ^ wordWidth) VQ.Curve.p (rawDouble i) <;>
    simp [VQBridge.Curve.LuoMultiplication.wordCorrection,
      VQBridge.Curve.LuoMultiplication.bitValue, wrappedValue, hflag,
      Nat.add_comm]

theorem finalFlag_eq_zero {i : Nat}
    (htarget : targetValue i < VQ.Curve.p) : finalFlag i = 0 := by
  have hp : VQ.Curve.p < 2 ^ wordWidth := by
    simpa [wordWidth] using VQ.Reversible.p_lt_two_pow
  have hsum := rawDouble_lt_twice_p htarget
  have hflag :
      VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) VQ.Curve.p (rawDouble i) =
        decide (VQ.Curve.p ≤ rawDouble i) :=
    VQBridge.Curve.LuoMultiplication.reductionFlag_correct hp hsum
  have hparity :
      decide (VQ.Curve.p ≤ rawDouble i) =
        decide ((rawDouble i % VQ.Curve.p) % 2 = 1) := by
    have h := VQBridge.Curve.LuoMultiplication.doubling_flag_from_low_bit
        (modulus := VQ.Curve.p) (accumulator := targetValue i)
        (by decide +kernel) htarget
    dsimp +instances only [rawDouble, targetValue,
      VQBridge.Curve.LuoMultiplication.doubledAccumulator] at h ⊢
    exact h
  rw [finalFlag, reductionValue_eq_flag htarget,
    correctedValue_eq_mod htarget, hflag, hparity]
  have hlow : rawDouble i % VQ.Curve.p % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hone : rawDouble i % VQ.Curve.p % 2 = 1
  · simp [hone, VQBridge.Curve.LuoMultiplication.bitValue]
  · have hzero : rawDouble i % VQ.Curve.p % 2 = 0 := by omega
    simp [hzero, VQBridge.Curve.LuoMultiplication.bitValue]

theorem shiftedIndex_eq {i : Nat}
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    shiftedIndex i =
      writeField
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (wrappedValue i))
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) 1
        (variableFlag i) := by
  apply Nat.eq_of_testBit_eq
  intro wire
  by_cases htargetWire : wire < wordWidth
  · have hbeforeReduction :
        wire < VQ.Curve.PackedModularAddition.reductionWire wordWidth := by
      simp [VQ.Curve.PackedModularAddition.reductionWire, wordWidth] at *
      omega
    rw [testBit_writeField_outside (Or.inl hbeforeReduction),
      testBit_writeField_inside (by
        simp [VQ.Curve.PackedModularAddition.targetOffset]) (by
        simp [VQ.Curve.PackedModularAddition.targetOffset]
        omega)]
    have htarget := congrArg (fun value => value.testBit wire)
      (shiftedIndex_target hreduction)
    rw [testBit_readField] at htarget
    simpa [VQ.Curve.PackedModularAddition.targetOffset, htargetWire] using htarget
  · by_cases hreductionWire :
        wire = VQ.Curve.PackedModularAddition.reductionWire wordWidth
    · subst wire
      apply testBit_eq_of_bitValue_eq
      rw [shiftedIndex_reduction hreduction, bitValue_write_self]
      exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))).symm
    · rw [testBit_writeField_outside (by omega),
        testBit_writeField_outside (Or.inr (by
          simp [VQ.Curve.PackedModularAddition.targetOffset]
          omega))]
      unfold shiftedIndex VQ.Curve.PackedModularDoubling.shiftedIndex
      exact VQ.Curve.PackedModularDoubling.doubleShiftGates_testBit_other
        (by decide) (by omega) hreductionWire

theorem modularDoubleIndex_eq {i : Nat}
    (htarget : targetValue i < VQ.Curve.p)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    modularDoubleIndex i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (rawDouble i % VQ.Curve.p) := by
  have hdisjoint :
      VQ.Curve.PackedModularAddition.targetOffset + wordWidth ≤
        VQ.Curve.PackedModularAddition.reductionWire wordWidth ∨
      VQ.Curve.PackedModularAddition.reductionWire wordWidth + 1 ≤
        VQ.Curve.PackedModularAddition.targetOffset := by
    left
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.reductionWire, wordWidth]
  have hclear :
      writeField i (VQ.Curve.PackedModularAddition.reductionWire wordWidth)
        1 0 = i := by
    apply write_of_bitValue
    simp [hreduction]
  rw [modularDoubleIndex, correctedIndex, detectedIndex,
    correctedValue_eq_mod htarget, finalFlag_eq_zero htarget,
    shiftedIndex_eq hreduction,
    writeField_writeField,
    writeField_overwrite_alternating_of_disjoint hdisjoint,
    writeField_comm hdisjoint, hclear]

theorem modularDoubleGates_correct {i : Nat}
    (htarget : targetValue i < VQ.Curve.p)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0) :
    actGates modularDoubleGates i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (rawDouble i % VQ.Curve.p) := by
  rw [modularDoubleGates_act hworkspace hreduction,
    modularDoubleIndex_eq htarget hreduction]

end Double

namespace Product

open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

def sourceValue (i : Nat) : Nat :=
  readField i (VQ.Curve.PackedModularAddition.sourceOffset wordWidth) wordWidth

def targetValue (i : Nat) : Nat :=
  readField i VQ.Curve.PackedModularAddition.targetOffset wordWidth

def multiplierBit (i bit : Nat) : Nat :=
  bitValue i (multiplierOffset + bit)

def controlIndex (i bit : Nat) : Nat :=
  writeField i (VQ.Curve.PackedModularAddition.controlWire wordWidth) 1
    (multiplierBit i bit)

theorem controlToggleGates_act {i bit : Nat}
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates (controlToggleGates bit) i = controlIndex i bit := by
  simp only [controlToggleGates, actGates_cons, actGates_nil, act_cx_write,
    hcontrol, Nat.zero_add]
  unfold controlIndex multiplierBit
  rw [Nat.mod_eq_of_lt (bitValue_lt i (multiplierOffset + bit))]

theorem sourceValue_controlIndex (i bit : Nat) :
    sourceValue (controlIndex i bit) = sourceValue i := by
  unfold sourceValue
  rw [controlIndex,
    readField_writeField_of_disjoint (by
      right
      simp [VQ.Curve.PackedModularAddition.controlWire,
        VQ.Curve.PackedModularAddition.sourceOffset, wordWidth])]

theorem targetValue_controlIndex (i bit : Nat) :
    targetValue (controlIndex i bit) = targetValue i := by
  unfold targetValue
  rw [controlIndex,
    readField_writeField_of_disjoint (by
      right
      simp [VQ.Curve.PackedModularAddition.controlWire,
        VQ.Curve.PackedModularAddition.targetOffset, wordWidth])]

theorem reduction_controlIndex (i bit : Nat) :
    bitValue (controlIndex i bit)
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      bitValue i (VQ.Curve.PackedModularAddition.reductionWire wordWidth) := by
  rw [controlIndex, bitValue_write_ne (by
    simp [VQ.Curve.PackedModularAddition.controlWire,
      VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]

theorem control_controlIndex (i bit : Nat) :
    bitValue (controlIndex i bit)
        (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
      multiplierBit i bit := by
  rw [controlIndex, bitValue_write_self]
  exact Nat.mod_eq_of_lt (bitValue_lt i (multiplierOffset + bit))

theorem multiplier_controlIndex (i bit : Nat) :
    bitValue (controlIndex i bit) (multiplierOffset + bit) =
      multiplierBit i bit := by
  rw [controlIndex, bitValue_write_ne (by
    simp [VQ.Curve.PackedModularAddition.controlWire, multiplierOffset,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.width, wordWidth]
    omega)]
  rfl

theorem rawSum_controlIndex (i bit : Nat) :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum (controlIndex i bit) =
      multiplierBit i bit * sourceValue i + targetValue i := by
  unfold VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum
    VQ.Curve.PackedModularAddition.selectedSource
  change (if (controlIndex i bit).testBit
        (VQ.Curve.PackedModularAddition.controlWire wordWidth) = true then
      sourceValue (controlIndex i bit) else 0) +
      targetValue (controlIndex i bit) = _
  rw [sourceValue_controlIndex, targetValue_controlIndex]
  have hcontrolTest :
      (controlIndex i bit).testBit
          (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
        i.testBit (multiplierOffset + bit) := by
    cases hbit : i.testBit (multiplierOffset + bit)
    · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
      rw [control_controlIndex]
      simp [multiplierBit, bitValue, hbit]
    · apply (testBit_eq_true_iff_bitValue_eq_one _ _).2
      rw [control_controlIndex]
      simp [multiplierBit, bitValue, hbit]
  rw [hcontrolTest]
  cases hbit : i.testBit (multiplierOffset + bit) <;>
    simp [multiplierBit, bitValue, hbit]

theorem controlledAddGates_correct {i bit : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates (controlledAddGates bit) i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        ((multiplierBit i bit * sourceValue i + targetValue i) % VQ.Curve.p) := by
  let toggled := controlIndex i bit
  let value :=
    (multiplierBit i bit * sourceValue i + targetValue i) % VQ.Curve.p
  have htoggled := controlToggleGates_act (i := i) (bit := bit) hcontrol
  have hsourceToggled : Arithmetic.sourceValue toggled = sourceValue i := by
    change sourceValue toggled = sourceValue i
    simpa only [toggled] using sourceValue_controlIndex i bit
  have htargetToggled : Arithmetic.targetValue toggled = targetValue i := by
    change targetValue toggled = targetValue i
    simpa only [toggled] using targetValue_controlIndex i bit
  have hworkspaceToggled : CorrectionWorkspaceClear toggled := by
    simpa only [toggled, controlIndex] using
      hworkspace.writeControl (multiplierBit i bit)
  have hreductionToggled : bitValue toggled
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
    rw [show toggled = controlIndex i bit by rfl, reduction_controlIndex]
    exact hreduction
  have hadd := Arithmetic.modularAddGates_correct
    (i := toggled)
    (by rw [hsourceToggled]; exact hsource)
    (by rw [htargetToggled]; exact htarget)
    hworkspaceToggled hreductionToggled
  have hadd' : actGates modularAddGates toggled =
      writeField toggled VQ.Curve.PackedModularAddition.targetOffset wordWidth
        value := by
    simpa [value, toggled, rawSum_controlIndex,
      Arithmetic.sourceValue, sourceValue, Arithmetic.targetValue,
      targetValue] using hadd
  have hcontrolAdded :
      bitValue
          (writeField toggled VQ.Curve.PackedModularAddition.targetOffset
            wordWidth value)
          (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
        multiplierBit i bit := by
    rw [bitValue_write_out (by
      right
      simp [VQ.Curve.PackedModularAddition.targetOffset,
        VQ.Curve.PackedModularAddition.controlWire, wordWidth]),
      control_controlIndex]
  have hmultiplierAdded :
      bitValue
          (writeField toggled VQ.Curve.PackedModularAddition.targetOffset
            wordWidth value)
          (multiplierOffset + bit) = multiplierBit i bit := by
    rw [bitValue_write_out (by
      right
      simp [VQ.Curve.PackedModularAddition.targetOffset, multiplierOffset,
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.width, wordWidth]
      omega),
      multiplier_controlIndex]
  have htwice : (multiplierBit i bit + multiplierBit i bit) % 2 = 0 := by
    have hlt := bitValue_lt i (multiplierOffset + bit)
    unfold multiplierBit
    omega
  have hdisjoint :
      VQ.Curve.PackedModularAddition.targetOffset + wordWidth ≤
        VQ.Curve.PackedModularAddition.controlWire wordWidth ∨
      VQ.Curve.PackedModularAddition.controlWire wordWidth + 1 ≤
        VQ.Curve.PackedModularAddition.targetOffset := by
    left
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.controlWire, wordWidth]
  have hclear :
      writeField i (VQ.Curve.PackedModularAddition.controlWire wordWidth) 1 0 =
        i := by
    apply write_of_bitValue
    simp [hcontrol]
  simp only [controlledAddGates, actGates_append]
  rw [htoggled, hadd']
  simp only [controlToggleGates, actGates_cons, actGates_nil, act_cx_write]
  rw [hcontrolAdded, hmultiplierAdded, htwice]
  unfold toggled controlIndex
  rw [writeField_comm hdisjoint, writeField_writeField, hclear]

def productValue (i : Nat) (bits : List Nat) : Nat :=
  VQBridge.Curve.LuoMultiplication.horner VQ.Curve.p (sourceValue i)
    (bits.map fun bit => i.testBit (multiplierOffset + bit))

theorem multiplierBit_eq (i bit : Nat) :
    multiplierBit i bit = VQBridge.Curve.LuoMultiplication.bitValue
      (i.testBit (multiplierOffset + bit)) := by
  unfold multiplierBit bitValue VQBridge.Curve.LuoMultiplication.bitValue
  cases i.testBit (multiplierOffset + bit) <;> rfl

theorem sourceValue_writeTarget (i value : Nat) :
    sourceValue
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value) =
      sourceValue i := by
  unfold sourceValue
  rw [readField_writeField_of_disjoint (by
    left
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.sourceOffset, wordWidth])]

theorem targetValue_writeTarget {i value : Nat}
    (hvalue : value < 2 ^ wordWidth) :
    targetValue
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value) =
      value := by
  exact readField_writeField_self hvalue

theorem multiplierBit_writeTarget (i value bit : Nat) :
    multiplierBit
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value) bit =
      multiplierBit i bit := by
  unfold multiplierBit
  rw [bitValue_write_out (by
    right
    simp [VQ.Curve.PackedModularAddition.targetOffset, multiplierOffset,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.width, wordWidth]
    omega)]

theorem reduction_writeTarget (i value : Nat) :
    bitValue
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value)
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      bitValue i (VQ.Curve.PackedModularAddition.reductionWire wordWidth) := by
  rw [bitValue_write_out (by
    right
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.reductionWire, wordWidth])]

theorem control_writeTarget (i value : Nat) :
    bitValue
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value)
        (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
      bitValue i (VQ.Curve.PackedModularAddition.controlWire wordWidth) := by
  rw [bitValue_write_out (by
    right
    simp [VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.controlWire, wordWidth])]

theorem productValue_lt {i : Nat} : ∀ {bits : List Nat}, bits ≠ [] →
    productValue i bits < VQ.Curve.p
  | [], hbits => (hbits rfl).elim
  | _ :: _, _ => by
      simp [productValue, VQBridge.Curve.LuoMultiplication.horner]
      exact Nat.mod_lt _ VQ.Curve.p_pos

theorem productGatesAux_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    ∀ bits,
      (∀ bit ∈ bits, bit < wordWidth) →
      actGates (productGatesAux bits) i =
        writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (productValue i bits)
  | [], _ => by
      simp only [productGatesAux, actGates_nil]
      rw [show productValue i [] = 0 by rfl, ← htarget]
      exact (writeField_read i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth).symm
  | [bit], _ => by
      have hadd := controlledAddGates_correct (i := i) (bit := bit) hsource
        (by rw [htarget]; exact VQ.Curve.p_pos) hworkspace hreduction hcontrol
      rw [productGatesAux]
      simpa [productValue, VQBridge.Curve.LuoMultiplication.horner,
        multiplierBit_eq, htarget, Nat.add_comm] using hadd
  | bit :: nextBit :: rest, hbits => by
      let tailBits := nextBit :: rest
      let tailValue := productValue i tailBits
      let tailIndex := writeField i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth tailValue
      let doubleValue := 2 * tailValue % VQ.Curve.p
      let doubleIndex := writeField i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth doubleValue
      let finalValue :=
        (multiplierBit i bit * sourceValue i + doubleValue) % VQ.Curve.p
      have htailBits : ∀ q ∈ tailBits, q < wordWidth := by
        intro q hq
        exact hbits q (List.mem_cons_of_mem bit hq)
      have htail := productGatesAux_correct hsource htarget hworkspace
        hreduction hcontrol tailBits htailBits
      change actGates (productGatesAux tailBits) i = tailIndex at htail
      have htailLt : tailValue < VQ.Curve.p :=
        productValue_lt (bits := tailBits) (by simp [tailBits])
      have htailFit : tailValue < 2 ^ wordWidth :=
        htailLt.trans (by
          simpa [wordWidth] using VQ.Reversible.p_lt_two_pow)
      have hsourceTail : sourceValue tailIndex = sourceValue i := by
        simpa only [tailIndex] using sourceValue_writeTarget i tailValue
      have htargetTail : Double.targetValue tailIndex = tailValue := by
        change targetValue tailIndex = tailValue
        simpa only [tailIndex] using
          targetValue_writeTarget (i := i) htailFit
      have hworkspaceTail : CorrectionWorkspaceClear tailIndex := by
        simpa only [tailIndex] using hworkspace.writeTarget tailValue
      have hreductionTail : bitValue tailIndex
          (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
        rw [show tailIndex = writeField i
          VQ.Curve.PackedModularAddition.targetOffset wordWidth tailValue by rfl,
          reduction_writeTarget]
        exact hreduction
      have hdouble := Double.modularDoubleGates_correct
        (i := tailIndex) (by rw [htargetTail]; exact htailLt)
        hworkspaceTail hreductionTail
      have hdouble' : actGates modularDoubleGates tailIndex = doubleIndex := by
        rw [hdouble]
        simp [doubleIndex, tailIndex, doubleValue, Double.rawDouble,
          htargetTail, writeField_writeField]
      have hdoubleLt : doubleValue < VQ.Curve.p :=
        Nat.mod_lt _ VQ.Curve.p_pos
      have hdoubleFit : doubleValue < 2 ^ wordWidth :=
        hdoubleLt.trans (by
          simpa [wordWidth] using VQ.Reversible.p_lt_two_pow)
      have hsourceDouble : sourceValue doubleIndex = sourceValue i := by
        simpa only [doubleIndex] using sourceValue_writeTarget i doubleValue
      have htargetDouble : targetValue doubleIndex = doubleValue := by
        simpa only [doubleIndex] using
          targetValue_writeTarget (i := i) hdoubleFit
      have hworkspaceDouble : CorrectionWorkspaceClear doubleIndex := by
        simpa only [doubleIndex] using hworkspace.writeTarget doubleValue
      have hreductionDouble : bitValue doubleIndex
          (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
        rw [show doubleIndex = writeField i
          VQ.Curve.PackedModularAddition.targetOffset wordWidth doubleValue by rfl,
          reduction_writeTarget]
        exact hreduction
      have hcontrolDouble : bitValue doubleIndex
          (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0 := by
        rw [show doubleIndex = writeField i
          VQ.Curve.PackedModularAddition.targetOffset wordWidth doubleValue by rfl,
          control_writeTarget]
        exact hcontrol
      have hadd := controlledAddGates_correct
        (i := doubleIndex) (bit := bit)
        (by rw [hsourceDouble]; exact hsource)
        (by rw [htargetDouble]; exact hdoubleLt) hworkspaceDouble
        hreductionDouble hcontrolDouble
      have hbitDouble : multiplierBit doubleIndex bit = multiplierBit i bit := by
        simpa only [doubleIndex] using multiplierBit_writeTarget i doubleValue bit
      have hadd' : actGates (controlledAddGates bit) doubleIndex =
          writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
            finalValue := by
        rw [hadd]
        simp [finalValue, hbitDouble, hsourceDouble, htargetDouble, doubleIndex,
          writeField_writeField]
      have hvalue : finalValue = productValue i (bit :: nextBit :: rest) := by
        calc
          finalValue =
              (doubleValue + multiplierBit i bit * sourceValue i) %
                VQ.Curve.p := by
            simp [finalValue, Nat.add_comm]
          _ = (2 * tailValue + multiplierBit i bit * sourceValue i) %
                VQ.Curve.p := by
            simp only [doubleValue]
            rw [Nat.mod_add_mod]
          _ = productValue i (bit :: nextBit :: rest) := by
            simp [productValue, VQBridge.Curve.LuoMultiplication.horner,
              tailValue, tailBits, multiplierBit_eq]
      simp only [productGatesAux, actGates_append]
      rw [htail, hdouble', hadd', hvalue]

theorem decode_append (xs ys : List Bool) :
    VQBridge.Curve.LuoMultiplication.decode (xs ++ ys) =
      VQBridge.Curve.LuoMultiplication.decode xs +
        2 ^ xs.length * VQBridge.Curve.LuoMultiplication.decode ys := by
  induction xs with
  | nil => simp [VQBridge.Curve.LuoMultiplication.decode]
  | cons bit xs ih =>
      simp [VQBridge.Curve.LuoMultiplication.decode, ih, Nat.pow_succ]
      ring

theorem decode_range_testBits_offset (index offset width : Nat) :
    VQBridge.Curve.LuoMultiplication.decode
        ((List.range width).map fun bit => index.testBit (offset + bit)) =
      readField index offset width := by
  induction width with
  | zero =>
      simp [VQBridge.Curve.LuoMultiplication.decode, readField_size_zero]
  | succ width ih =>
      rw [List.range_succ, List.map_append, decode_append, ih,
        readField_high]
      simp [VQBridge.Curve.LuoMultiplication.decode,
        VQBridge.Curve.LuoMultiplication.bitValue, bitValue]

theorem productValue_range (i : Nat) :
    productValue i (List.range wordWidth) =
      readField i multiplierOffset wordWidth * sourceValue i % VQ.Curve.p := by
  rw [productValue, VQBridge.Curve.LuoMultiplication.horner_correct,
    decode_range_testBits_offset]

theorem modularProductGates_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates modularProductGates i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (readField i multiplierOffset wordWidth * sourceValue i %
          VQ.Curve.p) := by
  rw [modularProductGates]
  have h := productGatesAux_correct hsource htarget hworkspace hreduction
    hcontrol (List.range wordWidth) (fun bit hbit => List.mem_range.mp hbit)
  rw [productValue_range] at h
  exact h

theorem modularProductGates_reverse_clears {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates modularProductGates.reverse
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (readField i multiplierOffset wordWidth * sourceValue i %
            VQ.Curve.p)) =
      i := by
  rw [← modularProductGates_correct hsource htarget hworkspace hreduction
    hcontrol]
  exact actGates_reverse modularProductGates_wellFormed i

end Product

end VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic
