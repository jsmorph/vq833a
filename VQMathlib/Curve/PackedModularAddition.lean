import VQ.Curve.PackedModularAddition
import VQMathlib.Curve.LuoMultiplication

namespace VQMathlib.Curve.PackedModularAddition

open VQ
open VQ.Algebra
open VQ.Reversible
open VQ.Semantics
open VQ.Curve.PackedModularAddition
open VQ.Curve.PackedModularProduct

def rawSum (wordWidth original : Nat) : Nat :=
  selectedSource wordWidth original +
    readField original (targetOffset) wordWidth

def controlBit (wordWidth original : Nat) : Bool :=
  original.testBit (controlWire wordWidth)

def sourceValue (wordWidth original : Nat) : Nat :=
  readField original (sourceOffset wordWidth) wordWidth

def targetValue (wordWidth original : Nat) : Nat :=
  readField original targetOffset wordWidth

theorem rawSum_eq_luo (wordWidth original : Nat) :
    rawSum wordWidth original =
      VQBridge.Curve.LuoMultiplication.rawSum
        (controlBit wordWidth original)
        (sourceValue wordWidth original)
        (targetValue wordWidth original) := by
  cases hcontrol : original.testBit (controlWire wordWidth) <;>
    simp [rawSum, selectedSource, controlBit, sourceValue, targetValue,
      VQBridge.Curve.LuoMultiplication.rawSum,
      VQBridge.Curve.LuoMultiplication.bitValue, hcontrol, Nat.add_comm]

theorem rawSum_lt_twice_modulus
    {modulus wordWidth original : Nat}
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus) :
    rawSum wordWidth original < 2 * modulus := by
  rw [rawSum_eq_luo]
  exact VQBridge.Curve.LuoMultiplication.rawSum_lt_twice_modulus
    hsource htarget

theorem variableIndex_eq
    {wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    variableIndex wordWidth original =
      writeField
        (writeField original targetOffset wordWidth
          (rawSum wordWidth original % 2 ^ wordWidth))
        (reductionWire wordWidth) 1
        (rawSum wordWidth original / 2 ^ wordWidth % 2) := by
  rw [variableIndex,
    variableAddGates_act hwidth hcarry hscratch]
  simp only [rawSum, hreduction, Nat.zero_add]

theorem variableIndex_targetWide
    {wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (variableIndex wordWidth original) targetOffset
      (wordWidth + 1) = rawSum wordWidth original % 2 ^ wordWidth := by
  have hextension' : bitValue original (targetOffset + wordWidth) = 0 := by
    simpa [targetOffset, targetExtensionWire] using hextension
  rw [variableIndex_eq hwidth hcarry hscratch hreduction,
    readField_writeField_of_disjoint (by
      simp [targetOffset, reductionWire]
      omega),
    readField_high,
    readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos wordWidth))]
  rw [bitValue_write_out (Or.inr (by
    simp [targetOffset])), hextension']
  simp

theorem variableIndex_reduction
    {wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    bitValue (variableIndex wordWidth original) (reductionWire wordWidth) =
      rawSum wordWidth original / 2 ^ wordWidth % 2 := by
  rw [variableIndex_eq hwidth hcarry hscratch hreduction,
    bitValue_write_self, Nat.mod_mod]

def firstValue (modulus wordWidth original : Nat) : Nat :=
  rawSum wordWidth original % 2 ^ wordWidth +
    (2 ^ wordWidth - modulus)

theorem firstValue_lt
    {modulus wordWidth original : Nat}
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth) :
    firstValue modulus wordWidth original < 2 ^ (wordWidth + 1) := by
  have hlow := Nat.mod_lt (rawSum wordWidth original)
    (Nat.two_pow_pos wordWidth)
  rw [Nat.pow_succ]
  simp only [firstValue]
  omega

theorem firstComparisonIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (firstComparisonIndex modulus wordWidth original) targetOffset
      (wordWidth + 1) = firstValue modulus wordWidth original := by
  simp only [targetOffset]
  have hvariable :
      readField (variableIndex wordWidth original) 0 (wordWidth + 1) =
        rawSum wordWidth original % 2 ^ wordWidth := by
    simpa only [targetOffset] using
      variableIndex_targetWide hwidth hcarry hscratch hreduction hextension
  have hconstant : 2 ^ wordWidth - modulus < 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    omega
  rw [firstComparisonIndex,
    readField_writeField_self (Nat.mod_lt _
      (Nat.two_pow_pos (wordWidth + 1))),
    hvariable,
    readField_zero,
    Nat.mod_eq_of_lt hconstant]
  change firstValue modulus wordWidth original % 2 ^ (wordWidth + 1) = _
  rw [Nat.mod_eq_of_lt (firstValue_lt hmodulusPos hmodulus)]

theorem firstComparisonIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (firstComparisonIndex modulus wordWidth original) targetOffset
      wordWidth = firstValue modulus wordWidth original % 2 ^ wordWidth := by
  have hwide := firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  have hpowdvd : 2 ^ wordWidth ∣ 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_right _ _
  have hmod := congrArg (fun value => value % 2 ^ wordWidth) hwide
  simpa only [targetOffset, readField_zero,
    Nat.mod_mod_of_dvd _ hpowdvd] using hmod

theorem firstComparisonIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (firstComparisonIndex modulus wordWidth original)
      (targetExtensionWire wordWidth) =
        if modulus ≤ rawSum wordWidth original % 2 ^ wordWidth then 1 else 0 := by
  have hwide := firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  rw [readField_high] at hwide
  have hlow := firstComparisonIndex_target hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  rw [hlow] at hwide
  simp only [targetOffset, targetExtensionWire, firstValue, Nat.zero_add] at hwide ⊢
  have hword : 0 < 2 ^ wordWidth := Nat.two_pow_pos wordWidth
  have hraw := Nat.mod_lt (rawSum wordWidth original)
    (Nat.two_pow_pos wordWidth)
  have hbit := bitValue_lt
    (firstComparisonIndex modulus wordWidth original) wordWidth
  have hbitCases : bitValue
      (firstComparisonIndex modulus wordWidth original) wordWidth = 0 ∨
      bitValue (firstComparisonIndex modulus wordWidth original) wordWidth = 1 := by
    omega
  by_cases hreduction : modulus ≤ rawSum wordWidth original % 2 ^ wordWidth
  · rw [if_pos hreduction]
    rcases hbitCases with hvalue | hvalue
    · rw [hvalue] at hwide ⊢
      simp only [Nat.mul_zero, Nat.add_zero] at hwide
      omega
    · exact hvalue
  · rw [if_neg hreduction]
    rcases hbitCases with hvalue | hvalue
    · exact hvalue
    · rw [hvalue] at hwide ⊢
      simp only [Nat.mul_one] at hwide
      omega

theorem firstComparisonIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    bitValue (firstComparisonIndex modulus wordWidth original)
      (reductionWire wordWidth) =
        rawSum wordWidth original / 2 ^ wordWidth % 2 := by
  rw [firstComparisonIndex,
    bitValue_write_out (Or.inr (by
      simp [reductionWire]
      omega)),
    variableIndex_reduction hwidth hcarry hscratch hreduction]

theorem copiedReductionIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (copiedReductionIndex modulus wordWidth original)
      (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawSum wordWidth original)) := by
  have hsum := rawSum_lt_twice_modulus hsource htarget
  have hsumWord : rawSum wordWidth original < 2 * 2 ^ wordWidth := by
    omega
  have hoverflow : rawSum wordWidth original / 2 ^ wordWidth % 2 =
      if 2 ^ wordWidth ≤ rawSum wordWidth original then 1 else 0 := by
    by_cases hword : 2 ^ wordWidth ≤ rawSum wordWidth original
    · rw [if_pos hword]
      have hdiv : rawSum wordWidth original / 2 ^ wordWidth = 1 := by
        apply Nat.div_eq_of_lt_le
        · simpa using hword
        · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsumWord
      simp [hdiv]
    · rw [if_neg hword]
      have hlt : rawSum wordWidth original < 2 ^ wordWidth := by omega
      rw [Nat.div_eq_of_lt hlt]
  rw [copiedReductionIndex, actGates_cons, actGates_nil, act_cx_write,
    bitValue_write_self, Nat.mod_mod,
    firstComparisonIndex_reduction hwidth hcarry hscratch hreduction,
    firstComparisonIndex_extension hwidth hmodulusPos hmodulus
      hcarry hscratch hreduction hextension,
    hoverflow]
  unfold VQBridge.Curve.LuoMultiplication.reductionFlag
  unfold VQBridge.Curve.LuoMultiplication.bitValue
  by_cases hword : 2 ^ wordWidth ≤ rawSum wordWidth original <;>
    by_cases hmod : modulus ≤ rawSum wordWidth original % 2 ^ wordWidth <;>
      simp [hword, hmod]

theorem copiedReductionIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (copiedReductionIndex modulus wordWidth original) targetOffset
      (wordWidth + 1) = firstValue modulus wordWidth original := by
  rw [copiedReductionIndex, actGates_cons, actGates_nil, act_cx_write,
    readField_writeField_of_disjoint (by
      simp [targetOffset, reductionWire]
      omega),
    firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
      hcarry hscratch hreduction hextension]

theorem secondComparisonIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (secondComparisonIndex modulus wordWidth original) targetOffset
      (wordWidth + 1) =
        rawSum wordWidth original % 2 ^ wordWidth + 2 ^ wordWidth := by
  have hcopied : readField (copiedReductionIndex modulus wordWidth original)
      0 (wordWidth + 1) = firstValue modulus wordWidth original := by
    simpa only [targetOffset] using
      copiedReductionIndex_targetWide hwidth hmodulusPos hmodulus
        hcarry hscratch hreduction hextension
  have hmodulusWide : modulus < 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    omega
  have hcombine : firstValue modulus wordWidth original + modulus =
      rawSum wordWidth original % 2 ^ wordWidth + 2 ^ wordWidth := by
    simp only [firstValue]
    omega
  have hresult :
      rawSum wordWidth original % 2 ^ wordWidth + 2 ^ wordWidth <
        2 ^ (wordWidth + 1) := by
    have hraw := Nat.mod_lt (rawSum wordWidth original)
      (Nat.two_pow_pos wordWidth)
    rw [Nat.pow_succ]
    omega
  simp only [targetOffset]
  rw [secondComparisonIndex,
    readField_writeField_self (Nat.mod_lt _
      (Nat.two_pow_pos (wordWidth + 1))),
    hcopied, readField_zero, Nat.mod_eq_of_lt hmodulusWide,
    hcombine, Nat.mod_eq_of_lt hresult]

theorem secondComparisonIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (secondComparisonIndex modulus wordWidth original) targetOffset
      wordWidth = rawSum wordWidth original % 2 ^ wordWidth := by
  have hwide := secondComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  have hpowdvd : 2 ^ wordWidth ∣ 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_right _ _
  have hmod := congrArg (fun value => value % 2 ^ wordWidth) hwide
  simpa only [targetOffset, readField_zero,
    Nat.mod_mod_of_dvd _ hpowdvd, Nat.add_mod_right,
    Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos wordWidth))] using hmod

theorem secondComparisonIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (secondComparisonIndex modulus wordWidth original)
      (targetExtensionWire wordWidth) = 1 := by
  have hwide := secondComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  rw [readField_high] at hwide
  have hlow := secondComparisonIndex_target hwidth hmodulusPos hmodulus
    hcarry hscratch hreduction hextension
  rw [hlow] at hwide
  simp only [targetOffset, targetExtensionWire, Nat.zero_add] at hwide ⊢
  have hword : 0 < 2 ^ wordWidth := Nat.two_pow_pos wordWidth
  have hbit := bitValue_lt
    (secondComparisonIndex modulus wordWidth original) wordWidth
  have hbitCases : bitValue
      (secondComparisonIndex modulus wordWidth original) wordWidth = 0 ∨
      bitValue (secondComparisonIndex modulus wordWidth original) wordWidth = 1 := by
    omega
  rcases hbitCases with hvalue | hvalue
  · rw [hvalue] at hwide ⊢
    simp only [Nat.mul_zero, Nat.add_zero] at hwide
    omega
  · exact hvalue

theorem clearedExtensionIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (clearedExtensionIndex modulus wordWidth original) targetOffset
      wordWidth = rawSum wordWidth original % 2 ^ wordWidth := by
  rw [clearedExtensionIndex, actGates_cons, actGates_nil, act_x_write,
    readField_writeField_of_disjoint (by
      simp [targetOffset, targetExtensionWire]),
    secondComparisonIndex_target hwidth hmodulusPos hmodulus
      hcarry hscratch hreduction hextension]

theorem clearedExtensionIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (clearedExtensionIndex modulus wordWidth original)
      (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawSum wordWidth original)) := by
  rw [clearedExtensionIndex, actGates_cons, actGates_nil, act_x_write,
    bitValue_write_ne (by
      simp [targetExtensionWire, reductionWire]
      omega)]
  rw [secondComparisonIndex,
    bitValue_write_out (Or.inr (by
      simp [reductionWire]
      omega)),
    copiedReductionIndex_reduction hwidth hmodulusPos hmodulus
      hsource htarget hcarry hscratch hreduction hextension]

theorem testBit_eq_bool_of_bitValue
    {i q : Nat} {b : Bool}
    (h : bitValue i q =
      VQBridge.Curve.LuoMultiplication.bitValue b) :
    i.testBit q = b := by
  unfold bitValue at h
  unfold VQBridge.Curve.LuoMultiplication.bitValue at h
  cases hi : i.testBit q <;> cases hb : b <;> simp_all

theorem correctedIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (correctedIndex modulus wordWidth original) targetOffset wordWidth =
      rawSum wordWidth original % modulus := by
  let cleared := clearedExtensionIndex modulus wordWidth original
  let flag := VQBridge.Curve.LuoMultiplication.reductionFlag
    (2 ^ wordWidth) modulus (rawSum wordWidth original)
  have hclearedTarget : readField cleared targetOffset wordWidth =
      rawSum wordWidth original % 2 ^ wordWidth := by
    exact clearedExtensionIndex_target hwidth hmodulusPos hmodulus
      hcarry hscratch hreduction hextension
  have hflagValue : bitValue cleared (reductionWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue flag := by
    exact clearedExtensionIndex_reduction hwidth hmodulusPos hmodulus
      hsource htarget hcarry hscratch hreduction hextension
  have hflagBit : cleared.testBit (reductionWire wordWidth) = flag :=
    testBit_eq_bool_of_bitValue hflagValue
  have hconstant : 2 ^ wordWidth - modulus < 2 ^ wordWidth := by
    omega
  have hselected : readField
      (selectedConstant (2 ^ wordWidth - modulus)
        (reductionWire wordWidth) cleared) 0 wordWidth =
      if flag then 2 ^ wordWidth - modulus else 0 := by
    unfold selectedConstant
    rw [hflagBit]
    cases flag <;>
      simp [readField_zero, Nat.mod_eq_of_lt hconstant]
  have hwordCorrection :
      (rawSum wordWidth original % 2 ^ wordWidth +
        (if flag then 2 ^ wordWidth - modulus else 0)) % 2 ^ wordWidth =
      VQBridge.Curve.LuoMultiplication.wordCorrection
        (2 ^ wordWidth) modulus (rawSum wordWidth original) := by
    unfold VQBridge.Curve.LuoMultiplication.wordCorrection
    change _ = if flag then _ else _
    cases flag <;> simp
  simp only [targetOffset] at hclearedTarget ⊢
  rw [correctedIndex]
  rw [readField_writeField_self (Nat.mod_lt _
    (Nat.two_pow_pos wordWidth)), hclearedTarget, hselected,
    hwordCorrection]
  exact VQBridge.Curve.LuoMultiplication.wordCorrection_correct
    hmodulusPos hmodulus (rawSum_lt_twice_modulus hsource htarget)

theorem modularAddIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (modularAddIndex modulus wordWidth original) targetOffset
      wordWidth = rawSum wordWidth original % modulus := by
  have hcorrected := correctedIndex_workspace (modulus := modulus)
    hwidth hworkspace
  rw [modularAddIndex,
    flagEraseGates_act hwidth hcorrected.1 hcorrected.2.2,
    readField_writeField_of_disjoint (by
      simp [targetOffset, reductionWire]
      omega)]
  exact correctedIndex_target hwidth hmodulusPos hmodulus hsource htarget
    hworkspace.1 hworkspace.2.2 hreduction hextension

theorem correctedIndex_source
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    readField (correctedIndex modulus wordWidth original)
      (sourceOffset wordWidth) wordWidth = sourceValue wordWidth original := by
  unfold sourceValue
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < wordWidth
  · simp only [hb, decide_true, Bool.true_and]
    apply correctedIndex_testBit_of_ge_targetExtension hwidth hworkspace
    · simp [sourceOffset]
    · simp [sourceOffset, reductionWire]
      omega
  · simp [hb]

theorem correctedIndex_control
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    (correctedIndex modulus wordWidth original).testBit
      (controlWire wordWidth) = controlBit wordWidth original := by
  unfold controlBit
  apply correctedIndex_testBit_of_ge_targetExtension hwidth hworkspace
  · simp [controlWire]
    omega
  · simp [controlWire, reductionWire]

theorem correctedIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (correctedIndex modulus wordWidth original)
      (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawSum wordWidth original)) := by
  rw [correctedIndex,
    bitValue_write_out (Or.inr (by
      simp [reductionWire]
      omega))]
  exact clearedExtensionIndex_reduction hwidth hmodulusPos hmodulus
    hsource htarget hcarry hscratch hreduction hextension

theorem correctedIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hscratch : bitValue original (scratchWire wordWidth) = 0)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (correctedIndex modulus wordWidth original)
      (targetExtensionWire wordWidth) = 0 := by
  rw [correctedIndex,
    bitValue_write_out (Or.inr (by
      simp [targetExtensionWire])),
    clearedExtensionIndex, actGates_cons, actGates_nil, act_x_write,
    bitValue_write_self,
    secondComparisonIndex_extension hwidth hmodulusPos hmodulus
      hcarry hscratch hreduction hextension]

theorem modularAddIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (modularAddIndex modulus wordWidth original)
      (reductionWire wordWidth) = 0 := by
  let corrected := correctedIndex modulus wordWidth original
  have hcorrectedWorkspace := correctedIndex_workspace
    (modulus := modulus) hwidth hworkspace
  have hcorrectedReduction : bitValue corrected (reductionWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue
        (VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) modulus (rawSum wordWidth original)) :=
    correctedIndex_reduction hwidth hmodulusPos hmodulus hsource htarget
      hworkspace.1 hworkspace.2.2 hreduction hextension
  have hcorrectedSource : readField corrected (sourceOffset wordWidth)
      wordWidth = sourceValue wordWidth original :=
    correctedIndex_source hwidth hworkspace
  have hcorrectedTarget : readField corrected targetOffset wordWidth =
      rawSum wordWidth original % modulus :=
    correctedIndex_target hwidth hmodulusPos hmodulus hsource htarget
      hworkspace.1 hworkspace.2.2 hreduction hextension
  have hcorrectedControl : bitValue corrected (controlWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue
        (controlBit wordWidth original) := by
    unfold bitValue VQBridge.Curve.LuoMultiplication.bitValue
    rw [correctedIndex_control hwidth hworkspace]
  have huncompute :
      VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) modulus (rawSum wordWidth original) =
        (controlBit wordWidth original &&
          decide (rawSum wordWidth original % modulus <
            sourceValue wordWidth original)) := by
    have h := VQBridge.Curve.LuoMultiplication.reductionFlag_uncompute
      (controlBit wordWidth original) hmodulus hsource htarget
    simpa [VQBridge.Curve.LuoMultiplication.correctedAccumulator,
      ← rawSum_eq_luo] using h
  rw [modularAddIndex, flagEraseGates_act hwidth
    hcorrectedWorkspace.1 hcorrectedWorkspace.2.2,
    bitValue_write_self, Nat.mod_mod, hcorrectedReduction,
    hcorrectedControl, hcorrectedSource, hcorrectedTarget]
  by_cases hlt : rawSum wordWidth original % modulus <
      sourceValue wordWidth original
  <;> cases hc : controlBit wordWidth original
  <;> simp [hlt, hc] at huncompute
  <;> simp [Adder.borrow, hlt, huncompute,
    VQBridge.Curve.LuoMultiplication.bitValue]

theorem modularAddIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (modularAddIndex modulus wordWidth original)
      (targetExtensionWire wordWidth) = 0 := by
  have hcorrectedWorkspace := correctedIndex_workspace
    (modulus := modulus) hwidth hworkspace
  rw [modularAddIndex, flagEraseGates_act hwidth
    hcorrectedWorkspace.1 hcorrectedWorkspace.2.2,
    bitValue_write_ne (by
      simp [targetExtensionWire, reductionWire]
      omega)]
  exact correctedIndex_extension hwidth hmodulusPos hmodulus
    hworkspace.1 hworkspace.2.2 hreduction hextension

theorem modularAddIndex_eq
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    modularAddIndex modulus wordWidth original =
      writeField original targetOffset wordWidth
        (rawSum wordWidth original % modulus) := by
  have hcorrectedWorkspace := correctedIndex_workspace
    (modulus := modulus) hwidth hworkspace
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases htargetBit : q < wordWidth
  · rw [testBit_writeField_inside (off := targetOffset)
      (n := wordWidth) (b := q) (by simp [targetOffset]) (by
        simp [targetOffset]
        omega)]
    have htargetEq := congrArg (fun value => value.testBit q)
      (modularAddIndex_target hwidth hmodulusPos hmodulus hsource htarget
        hworkspace hreduction hextension)
    rw [testBit_readField] at htargetEq
    simpa only [targetOffset, Nat.zero_add, Nat.sub_zero, htargetBit,
      decide_true, Bool.true_and] using htargetEq
  · rw [testBit_writeField_outside (off := targetOffset)
      (n := wordWidth) (b := q) (Or.inr (by
        simp only [targetOffset, Nat.zero_add]
        omega))]
    by_cases htargetExtension : q = targetExtensionWire wordWidth
    · subst q
      apply testBit_eq_of_bitValue_eq
      exact (modularAddIndex_extension hwidth hmodulusPos hmodulus
        hworkspace hreduction hextension).trans hextension.symm
    by_cases hreductionWire : q = reductionWire wordWidth
    · subst q
      apply testBit_eq_of_bitValue_eq
      exact (modularAddIndex_reduction hwidth hmodulusPos hmodulus
        hsource htarget hworkspace hreduction hextension).trans
          hreduction.symm
    · rw [modularAddIndex,
        flagEraseGates_act hwidth hcorrectedWorkspace.1
          hcorrectedWorkspace.2.2,
        testBit_writeField_outside (off := reductionWire wordWidth)
          (n := 1) (b := q) (by omega),
        correctedIndex_testBit_of_ge_targetExtension hwidth hworkspace
          (by
            simp only [targetExtensionWire] at htargetExtension
            omega)
          hreductionWire]

theorem modularAddOps_correct
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level)
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hsource : sourceValue wordWidth original ≤ modulus)
    (htarget : targetValue wordWidth original < modulus)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (modularAddOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (writeField original targetOffset wordWidth
        (rawSum wordWidth original % modulus)) := by
  calc
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (modularAddIndex modulus wordWidth original) :=
      modularAddOps_exact hl hwidth hworkspace rec creg hb
    _ = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (writeField original targetOffset wordWidth
          (rawSum wordWidth original % modulus)) := by
      rw [modularAddIndex_eq (by omega) hmodulusPos hmodulus hsource htarget
        hworkspace hreduction hextension]

end VQMathlib.Curve.PackedModularAddition
