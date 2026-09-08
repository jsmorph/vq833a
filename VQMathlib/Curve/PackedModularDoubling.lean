import VQ.Curve.PackedModularDoubling
import VQMathlib.Curve.LuoMultiplication
import VQMathlib.Curve.PackedModularAddition

namespace VQMathlib.Curve.PackedModularDoubling

open VQ
open VQ.Algebra
open VQ.Reversible
open VQ.Semantics
open VQ.Curve.PackedModularAddition
open VQ.Curve.PackedModularDoubling
open VQ.Curve.PackedModularProduct

def targetValue (wordWidth original : Nat) : Nat :=
  readField original targetOffset wordWidth

def rawDouble (wordWidth original : Nat) : Nat :=
  2 * targetValue wordWidth original

theorem doubleShiftPrefix_eq
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    actGates
        [.cx (wordWidth - 1) (reductionWire wordWidth),
          .cx (reductionWire wordWidth) (wordWidth - 1)] original =
      writeField
        (writeField original (reductionWire wordWidth) 1
          (bitValue original (wordWidth - 1)))
        (wordWidth - 1) 1 0 := by
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [hreduction, Nat.zero_add,
    bitValue_write_self, Nat.mod_mod,
    bitValue_write_ne (by
      simp [reductionWire]
      omega)]
  have hbit := bitValue_lt original (wordWidth - 1)
  have hbitmod : bitValue original (wordWidth - 1) % 2 =
      bitValue original (wordWidth - 1) := by
    omega
  have hdouble :
      (bitValue original (wordWidth - 1) +
        bitValue original (wordWidth - 1) % 2) % 2 = 0 := by
    omega
  rw [hdouble, hbitmod]

theorem clearedTop_target
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth) :
    readField
        (writeField
          (writeField original (reductionWire wordWidth) 1
            (bitValue original (wordWidth - 1)))
          (wordWidth - 1) 1 0)
        targetOffset wordWidth =
      targetValue wordWidth original % 2 ^ (wordWidth - 1) := by
  have hsplit := readField_high
    (writeField
      (writeField original (reductionWire wordWidth) 1
        (bitValue original (wordWidth - 1)))
      (wordWidth - 1) 1 0)
    targetOffset (wordWidth - 1)
  rw [show wordWidth - 1 + 1 = wordWidth by omega] at hsplit
  simp only [targetOffset, Nat.zero_add] at hsplit ⊢
  rw [bitValue_write_self, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hsplit
  have hlow : readField
      (writeField
        (writeField original (reductionWire wordWidth) 1
          (bitValue original (wordWidth - 1)))
        (wordWidth - 1) 1 0) 0 (wordWidth - 1) =
      readField original 0 (wordWidth - 1) := by
    rw [readField_writeField_of_disjoint
        (o₁ := wordWidth - 1) (n₁ := 1)
        (o₂ := 0) (n₂ := wordWidth - 1)
        (Or.inr (by simp)),
      readField_writeField_of_disjoint
        (o₁ := reductionWire wordWidth) (n₁ := 1)
        (o₂ := 0) (n₂ := wordWidth - 1) (Or.inr (by
        simp [reductionWire]
        omega))]
  rw [hsplit, hlow]
  unfold targetValue
  simp only [targetOffset, readField, Nat.shiftRight_zero]
  exact (Nat.mod_mod_of_dvd original
    (Nat.pow_dvd_pow 2 (by omega))).symm

theorem twice_mod_word_eq_twice_mod_low
    {wordWidth value : Nat}
    (hwidth : 1 ≤ wordWidth) :
    2 * value % 2 ^ wordWidth =
      2 * (value % 2 ^ (wordWidth - 1)) := by
  let lowWord := 2 ^ (wordWidth - 1)
  have hword : 2 ^ wordWidth = 2 * lowWord := by
    calc
      2 ^ wordWidth = 2 ^ ((wordWidth - 1) + 1) := by congr 1; omega
      _ = 2 ^ (wordWidth - 1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * lowWord := by simp [lowWord, Nat.mul_comm]
  have hlow : value % lowWord < lowWord :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsplit := Nat.mod_add_div value lowWord
  have heq : 2 * value =
      2 * (value % lowWord) + (2 * lowWord) * (value / lowWord) := by
    calc
      2 * value = 2 * (value % lowWord + lowWord * (value / lowWord)) := by
        rw [hsplit]
      _ = 2 * (value % lowWord) +
          (2 * lowWord) * (value / lowWord) := by ring
  calc
    2 * value % 2 ^ wordWidth =
        (2 * (value % lowWord) + (2 * lowWord) * (value / lowWord)) %
          (2 * lowWord) := by rw [hword, heq]
    _ = 2 * (value % lowWord) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem shiftedIndex_target
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    readField (shiftedIndex wordWidth original) targetOffset wordWidth =
      rawDouble wordWidth original % 2 ^ wordWidth := by
  let cleared :=
    writeField
      (writeField original (reductionWire wordWidth) 1
        (bitValue original (wordWidth - 1)))
      (wordWidth - 1) 1 0
  have hcleared : readField cleared targetOffset wordWidth =
      targetValue wordWidth original % 2 ^ (wordWidth - 1) :=
    clearedTop_target hwidth
  have htargetLt := readField_lt original targetOffset wordWidth
  rw [shiftedIndex, doubleShiftGates, actGates_append,
    doubleShiftPrefix_eq hwidth hreduction, rotateLeftGates_act]
  rw [readField_writeField_self
    (rotateLeftValue_lt wordWidth (readField cleared targetOffset wordWidth)),
    hcleared, rotateLeftValue_eq_twice_of_lt]
  · rw [rawDouble, targetValue,
      twice_mod_word_eq_twice_mod_low (by omega)]
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem shiftedIndex_reduction
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    bitValue (shiftedIndex wordWidth original) (reductionWire wordWidth) =
      rawDouble wordWidth original / 2 ^ wordWidth % 2 := by
  let cleared :=
    writeField
      (writeField original (reductionWire wordWidth) 1
      (bitValue original (wordWidth - 1)))
      (wordWidth - 1) 1 0
  have hbitmod : bitValue original (wordWidth - 1) % 2 =
      bitValue original (wordWidth - 1) := by
    have hbit := bitValue_lt original (wordWidth - 1)
    omega
  rw [shiftedIndex, doubleShiftGates, actGates_append,
    doubleShiftPrefix_eq hwidth hreduction, rotateLeftGates_act,
    bitValue_write_out (Or.inr (by
      simp [targetOffset, reductionWire]
      omega)), bitValue_write_ne (by
        simp [reductionWire]
        omega), bitValue_write_self, hbitmod]
  have htargetLt := readField_lt original targetOffset wordWidth
  have htop : bitValue original (wordWidth - 1) =
      rawDouble wordWidth original / 2 ^ wordWidth % 2 := by
    have hsplit := readField_high original targetOffset (wordWidth - 1)
    rw [show wordWidth - 1 + 1 = wordWidth by omega] at hsplit
    simp only [targetOffset, Nat.zero_add] at hsplit
    simp only [rawDouble, targetValue]
    simp only [targetOffset]
    rw [hsplit]
    let m := 2 ^ (wordWidth - 1)
    have hm : 0 < m := Nat.two_pow_pos _
    have hpow : 2 ^ wordWidth = 2 * m := by
      calc
        2 ^ wordWidth = 2 ^ ((wordWidth - 1) + 1) := by congr 1; omega
        _ = m * 2 := by simp [m, Nat.pow_succ]
        _ = 2 * m := by omega
    have hlow := readField_lt original 0 (wordWidth - 1)
    have hbit := bitValue_lt original (wordWidth - 1)
    have hreassoc :
        2 * (readField original 0 (wordWidth - 1) +
          m * bitValue original (wordWidth - 1)) =
        2 * readField original 0 (wordWidth - 1) +
          bitValue original (wordWidth - 1) * (2 * m) := by
      ring
    rw [show 2 ^ (wordWidth - 1) = m by rfl, hpow, hreassoc,
      Nat.mul_comm (bitValue original (wordWidth - 1)) (2 * m),
      Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (by omega), Nat.zero_add, hbitmod]
  exact htop

theorem shiftedIndex_targetWide
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (shiftedIndex wordWidth original) targetOffset (wordWidth + 1) =
      rawDouble wordWidth original % 2 ^ wordWidth := by
  rw [readField_high,
    shiftedIndex_target hwidth hreduction]
  have hext : bitValue (shiftedIndex wordWidth original)
      (targetExtensionWire wordWidth) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    simp only [shiftedIndex]
    rw [doubleShiftGates_testBit_other hwidth (by
      simp [targetExtensionWire]) (by
      simp [targetExtensionWire, reductionWire]
      omega)]
    exact (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hextension
  simpa [targetOffset, targetExtensionWire, hext]

def firstValue (modulus wordWidth original : Nat) : Nat :=
  rawDouble wordWidth original % 2 ^ wordWidth + (2 ^ wordWidth - modulus)

theorem firstValue_lt
    {modulus wordWidth original : Nat}
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth) :
    firstValue modulus wordWidth original < 2 ^ (wordWidth + 1) := by
  have hlow := Nat.mod_lt (rawDouble wordWidth original)
    (Nat.two_pow_pos wordWidth)
  rw [Nat.pow_succ]
  simp only [firstValue]
  omega

theorem firstComparisonIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.firstComparisonIndex
      modulus wordWidth original) targetOffset
      (wordWidth + 1) = firstValue modulus wordWidth original := by
  have hconstant : 2 ^ wordWidth - modulus < 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    omega
  rw [VQ.Curve.PackedModularDoubling.firstComparisonIndex,
    readField_writeField_self (Nat.mod_lt _
      (Nat.two_pow_pos (wordWidth + 1))),
    shiftedIndex_targetWide hwidth hreduction hextension,
    readField_zero, Nat.mod_eq_of_lt hconstant]
  exact Nat.mod_eq_of_lt (firstValue_lt hmodulusPos hmodulus)

theorem firstComparisonIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.firstComparisonIndex
      modulus wordWidth original) targetOffset
      wordWidth = firstValue modulus wordWidth original % 2 ^ wordWidth := by
  have hwide := firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hreduction hextension
  have hpowdvd : 2 ^ wordWidth ∣ 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_right _ _
  have hmod := congrArg (fun value => value % 2 ^ wordWidth) hwide
  simpa only [targetOffset, readField_zero,
    Nat.mod_mod_of_dvd _ hpowdvd] using hmod

theorem firstComparisonIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.firstComparisonIndex
      modulus wordWidth original)
      (targetExtensionWire wordWidth) =
        if modulus ≤ rawDouble wordWidth original % 2 ^ wordWidth then 1 else 0 := by
  have hwide := firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hreduction hextension
  rw [readField_high] at hwide
  have hlow := firstComparisonIndex_target hwidth hmodulusPos hmodulus
    hreduction hextension
  rw [hlow] at hwide
  simp only [targetOffset, targetExtensionWire, firstValue, Nat.zero_add] at hwide ⊢
  have hword : 0 < 2 ^ wordWidth := Nat.two_pow_pos wordWidth
  have hraw := Nat.mod_lt (rawDouble wordWidth original)
    (Nat.two_pow_pos wordWidth)
  have hbit := bitValue_lt
    (VQ.Curve.PackedModularDoubling.firstComparisonIndex
      modulus wordWidth original) wordWidth
  have hbitCases : bitValue
      (VQ.Curve.PackedModularDoubling.firstComparisonIndex
        modulus wordWidth original) wordWidth = 0 ∨
      bitValue
        (VQ.Curve.PackedModularDoubling.firstComparisonIndex
          modulus wordWidth original) wordWidth = 1 := by
    omega
  by_cases hreduce : modulus ≤ rawDouble wordWidth original % 2 ^ wordWidth
  · rw [if_pos hreduce]
    rcases hbitCases with hvalue | hvalue
    · rw [hvalue] at hwide ⊢
      simp only [Nat.mul_zero, Nat.add_zero] at hwide
      omega
    · exact hvalue
  · rw [if_neg hreduce]
    rcases hbitCases with hvalue | hvalue
    · exact hvalue
    · rw [hvalue] at hwide ⊢
      simp only [Nat.mul_one] at hwide
      omega

theorem firstComparisonIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.firstComparisonIndex
      modulus wordWidth original)
      (reductionWire wordWidth) =
        rawDouble wordWidth original / 2 ^ wordWidth % 2 := by
  rw [VQ.Curve.PackedModularDoubling.firstComparisonIndex,
    bitValue_write_out (Or.inr (by
      simp [targetOffset, reductionWire]
      omega)), shiftedIndex_reduction hwidth hreduction]

theorem rawDouble_lt_twice_modulus
    {modulus wordWidth original : Nat}
    (htarget : targetValue wordWidth original < modulus) :
    rawDouble wordWidth original < 2 * modulus := by
  simp only [rawDouble]
  omega

theorem copiedReductionIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.copiedReductionIndex
      modulus wordWidth original)
      (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawDouble wordWidth original)) := by
  have hsum := rawDouble_lt_twice_modulus htarget
  have hsumWord : rawDouble wordWidth original < 2 * 2 ^ wordWidth := by
    omega
  have hoverflow : rawDouble wordWidth original / 2 ^ wordWidth % 2 =
      if 2 ^ wordWidth ≤ rawDouble wordWidth original then 1 else 0 := by
    by_cases hword : 2 ^ wordWidth ≤ rawDouble wordWidth original
    · rw [if_pos hword]
      have hdiv : rawDouble wordWidth original / 2 ^ wordWidth = 1 := by
        apply Nat.div_eq_of_lt_le
        · simpa using hword
        · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsumWord
      simp [hdiv]
    · rw [if_neg hword]
      rw [Nat.div_eq_of_lt (by omega)]
  rw [VQ.Curve.PackedModularDoubling.copiedReductionIndex,
    actGates_cons, actGates_nil, act_cx_write,
    bitValue_write_self, Nat.mod_mod,
    firstComparisonIndex_reduction hwidth hreduction,
    firstComparisonIndex_extension hwidth hmodulusPos hmodulus
      hreduction hextension, hoverflow]
  unfold VQBridge.Curve.LuoMultiplication.reductionFlag
  unfold VQBridge.Curve.LuoMultiplication.bitValue
  by_cases hword : 2 ^ wordWidth ≤ rawDouble wordWidth original <;>
    by_cases hmod : modulus ≤ rawDouble wordWidth original % 2 ^ wordWidth <;>
      simp [hword, hmod]

theorem copiedReductionIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.copiedReductionIndex
      modulus wordWidth original) targetOffset
      (wordWidth + 1) = firstValue modulus wordWidth original := by
  rw [VQ.Curve.PackedModularDoubling.copiedReductionIndex,
    actGates_cons, actGates_nil, act_cx_write,
    readField_writeField_of_disjoint (by
      simp [targetOffset, reductionWire]
      omega),
    firstComparisonIndex_targetWide hwidth hmodulusPos hmodulus
      hreduction hextension]

theorem secondComparisonIndex_targetWide
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.secondComparisonIndex
      modulus wordWidth original) targetOffset
      (wordWidth + 1) =
        rawDouble wordWidth original % 2 ^ wordWidth + 2 ^ wordWidth := by
  have hcopied := copiedReductionIndex_targetWide hwidth hmodulusPos hmodulus
    hreduction hextension
  have hmodulusWide : modulus < 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    omega
  have hcombine : firstValue modulus wordWidth original + modulus =
      rawDouble wordWidth original % 2 ^ wordWidth + 2 ^ wordWidth := by
    simp only [firstValue]
    omega
  have hresult : rawDouble wordWidth original % 2 ^ wordWidth +
      2 ^ wordWidth < 2 ^ (wordWidth + 1) := by
    have hraw := Nat.mod_lt (rawDouble wordWidth original)
      (Nat.two_pow_pos wordWidth)
    rw [Nat.pow_succ]
    omega
  rw [VQ.Curve.PackedModularDoubling.secondComparisonIndex,
    readField_writeField_self (Nat.mod_lt _
      (Nat.two_pow_pos (wordWidth + 1))),
    hcopied, readField_zero, Nat.mod_eq_of_lt hmodulusWide,
    hcombine, Nat.mod_eq_of_lt hresult]

theorem secondComparisonIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.secondComparisonIndex
      modulus wordWidth original) targetOffset
      wordWidth = rawDouble wordWidth original % 2 ^ wordWidth := by
  have hwide := secondComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hreduction hextension
  have hpowdvd : 2 ^ wordWidth ∣ 2 ^ (wordWidth + 1) := by
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_right _ _
  have hmod := congrArg (fun value => value % 2 ^ wordWidth) hwide
  simpa only [targetOffset, readField_zero,
    Nat.mod_mod_of_dvd _ hpowdvd, Nat.add_mod_right,
    Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos wordWidth))] using hmod

theorem secondComparisonIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.secondComparisonIndex
      modulus wordWidth original)
      (targetExtensionWire wordWidth) = 1 := by
  have hwide := secondComparisonIndex_targetWide hwidth hmodulusPos hmodulus
    hreduction hextension
  rw [readField_high] at hwide
  have hlow := secondComparisonIndex_target hwidth hmodulusPos hmodulus
    hreduction hextension
  rw [hlow] at hwide
  simp only [targetOffset, targetExtensionWire, Nat.zero_add] at hwide ⊢
  have hword : 0 < 2 ^ wordWidth := Nat.two_pow_pos wordWidth
  have hbit := bitValue_lt
    (VQ.Curve.PackedModularDoubling.secondComparisonIndex
      modulus wordWidth original) wordWidth
  have hbitCases : bitValue
      (VQ.Curve.PackedModularDoubling.secondComparisonIndex
        modulus wordWidth original) wordWidth = 0 ∨
      bitValue
        (VQ.Curve.PackedModularDoubling.secondComparisonIndex
          modulus wordWidth original) wordWidth = 1 := by
    omega
  rcases hbitCases with hvalue | hvalue
  · rw [hvalue] at hwide ⊢
    simp only [Nat.mul_zero, Nat.add_zero] at hwide
    omega
  · exact hvalue

theorem clearedExtensionIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.clearedExtensionIndex
      modulus wordWidth original) targetOffset
      wordWidth = rawDouble wordWidth original % 2 ^ wordWidth := by
  rw [VQ.Curve.PackedModularDoubling.clearedExtensionIndex,
    actGates_cons, actGates_nil, act_x_write,
    readField_writeField_of_disjoint (by
      simp [targetOffset, targetExtensionWire]),
    secondComparisonIndex_target hwidth hmodulusPos hmodulus
      hreduction hextension]

theorem clearedExtensionIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.clearedExtensionIndex
      modulus wordWidth original)
      (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawDouble wordWidth original)) := by
  rw [VQ.Curve.PackedModularDoubling.clearedExtensionIndex,
    actGates_cons, actGates_nil, act_x_write,
    bitValue_write_ne (by
      simp [targetExtensionWire, reductionWire]
      omega), VQ.Curve.PackedModularDoubling.secondComparisonIndex,
    bitValue_write_out (Or.inr (by
      simp [targetOffset, reductionWire]
      omega)),
    copiedReductionIndex_reduction hwidth hmodulusPos hmodulus htarget
      hreduction hextension]

theorem correctedIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (VQ.Curve.PackedModularDoubling.correctedIndex
      modulus wordWidth original) targetOffset wordWidth =
      rawDouble wordWidth original % modulus := by
  let cleared := VQ.Curve.PackedModularDoubling.clearedExtensionIndex
    modulus wordWidth original
  let flag := VQBridge.Curve.LuoMultiplication.reductionFlag
    (2 ^ wordWidth) modulus (rawDouble wordWidth original)
  have hclearedTarget : readField cleared targetOffset wordWidth =
      rawDouble wordWidth original % 2 ^ wordWidth :=
    clearedExtensionIndex_target hwidth hmodulusPos hmodulus
      hreduction hextension
  have hflagValue : bitValue cleared (reductionWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue flag :=
    clearedExtensionIndex_reduction hwidth hmodulusPos hmodulus htarget
      hreduction hextension
  have hflagBit : cleared.testBit (reductionWire wordWidth) = flag :=
    VQMathlib.Curve.PackedModularAddition.testBit_eq_bool_of_bitValue hflagValue
  have hconstant : 2 ^ wordWidth - modulus < 2 ^ wordWidth := by omega
  have hselected : readField
      (selectedConstant (2 ^ wordWidth - modulus)
        (reductionWire wordWidth) cleared) 0 wordWidth =
      if flag then 2 ^ wordWidth - modulus else 0 := by
    unfold selectedConstant
    rw [hflagBit]
    cases flag <;> simp [readField_zero, Nat.mod_eq_of_lt hconstant]
  have hwordCorrection :
      (rawDouble wordWidth original % 2 ^ wordWidth +
        (if flag then 2 ^ wordWidth - modulus else 0)) % 2 ^ wordWidth =
      VQBridge.Curve.LuoMultiplication.wordCorrection
        (2 ^ wordWidth) modulus (rawDouble wordWidth original) := by
    unfold VQBridge.Curve.LuoMultiplication.wordCorrection
    change _ = if flag then _ else _
    cases flag <;> simp
  rw [VQ.Curve.PackedModularDoubling.correctedIndex,
    readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos wordWidth)),
    hclearedTarget, hselected, hwordCorrection]
  exact VQBridge.Curve.LuoMultiplication.wordCorrection_correct
    hmodulusPos hmodulus (rawDouble_lt_twice_modulus htarget)

theorem correctedIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.correctedIndex
      modulus wordWidth original) (reductionWire wordWidth) =
        VQBridge.Curve.LuoMultiplication.bitValue
          (VQBridge.Curve.LuoMultiplication.reductionFlag
            (2 ^ wordWidth) modulus (rawDouble wordWidth original)) := by
  rw [VQ.Curve.PackedModularDoubling.correctedIndex,
    bitValue_write_out (Or.inr (by
      simp [targetOffset, reductionWire]
      omega)),
    clearedExtensionIndex_reduction hwidth hmodulusPos hmodulus htarget
      hreduction hextension]

theorem correctedIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (VQ.Curve.PackedModularDoubling.correctedIndex
      modulus wordWidth original) (targetExtensionWire wordWidth) = 0 := by
  rw [VQ.Curve.PackedModularDoubling.correctedIndex,
    bitValue_write_out (Or.inr (by
      simp [targetOffset, targetExtensionWire])),
    VQ.Curve.PackedModularDoubling.clearedExtensionIndex,
    actGates_cons, actGates_nil, act_x_write, bitValue_write_self,
    secondComparisonIndex_extension hwidth hmodulusPos hmodulus
      hreduction hextension]

theorem correctedIndex_testBit_of_ge_targetExtension
    {modulus wordWidth original q : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hge : wordWidth + 1 ≤ q)
    (hreductionWire : q ≠ reductionWire wordWidth) :
    (VQ.Curve.PackedModularDoubling.correctedIndex
      modulus wordWidth original).testBit q = original.testBit q := by
  rw [VQ.Curve.PackedModularDoubling.correctedIndex,
    testBit_writeField_outside (Or.inr (by
      simp [targetOffset]
      omega)),
    VQ.Curve.PackedModularDoubling.clearedExtensionIndex,
    actGates_cons, actGates_nil, act_x_write,
    testBit_writeField_outside (Or.inr (by
      simpa only [targetExtensionWire] using hge)),
    VQ.Curve.PackedModularDoubling.secondComparisonIndex,
    testBit_writeField_outside (Or.inr (by
      simpa only [targetOffset, Nat.zero_add] using hge)),
    VQ.Curve.PackedModularDoubling.copiedReductionIndex,
    actGates_cons, actGates_nil, act_cx_write,
    testBit_writeField_outside (by
      simp only [reductionWire] at hreductionWire ⊢
      omega),
    VQ.Curve.PackedModularDoubling.firstComparisonIndex,
    testBit_writeField_outside (Or.inr (by
      simpa only [targetOffset, Nat.zero_add] using hge)),
    shiftedIndex, doubleShiftGates_testBit_other hwidth (by omega)
      hreductionWire]

theorem modularDoubleIndex_target
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    readField (modularDoubleIndex modulus wordWidth original)
      targetOffset wordWidth = rawDouble wordWidth original % modulus := by
  rw [modularDoubleIndex, actGates_cons, actGates_nil, act_cx_write,
    readField_writeField_of_disjoint (by
      simp [targetOffset, reductionWire]
      omega),
    correctedIndex_target hwidth hmodulusPos hmodulus htarget
      hreduction hextension]

theorem modularDoubleIndex_reduction
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (modularDoubleIndex modulus wordWidth original)
      (reductionWire wordWidth) = 0 := by
  let corrected := VQ.Curve.PackedModularDoubling.correctedIndex
    modulus wordWidth original
  have hcorrectedReduction : bitValue corrected (reductionWire wordWidth) =
      VQBridge.Curve.LuoMultiplication.bitValue
        (VQBridge.Curve.LuoMultiplication.reductionFlag
          (2 ^ wordWidth) modulus (rawDouble wordWidth original)) :=
    correctedIndex_reduction hwidth hmodulusPos hmodulus htarget
      hreduction hextension
  have hcorrectedTarget : readField corrected targetOffset wordWidth =
      rawDouble wordWidth original % modulus :=
    correctedIndex_target hwidth hmodulusPos hmodulus htarget
      hreduction hextension
  simp only [targetOffset] at hcorrectedTarget
  have htargetBit : bitValue corrected targetOffset =
      (rawDouble wordWidth original % modulus) % 2 := by
    simp only [targetOffset]
    rw [← readField_one]
    calc
      readField corrected 0 1 = readField corrected 0 wordWidth % 2 := by
        simp only [readField, Nat.shiftRight_zero, Nat.pow_one]
        exact (Nat.mod_mod_of_dvd corrected
          (Nat.pow_dvd_pow 2 (show 1 ≤ wordWidth by omega))).symm
      _ = (rawDouble wordWidth original % modulus) % 2 := by
        rw [hcorrectedTarget]
  have hflag : VQBridge.Curve.LuoMultiplication.reductionFlag
      (2 ^ wordWidth) modulus (rawDouble wordWidth original) =
      decide (modulus ≤ rawDouble wordWidth original) :=
    VQBridge.Curve.LuoMultiplication.reductionFlag_correct hmodulus
      (rawDouble_lt_twice_modulus htarget)
  have hparity := VQBridge.Curve.LuoMultiplication.doubling_flag_from_low_bit
    hmodulusOdd htarget
  dsimp +instances only [VQBridge.Curve.LuoMultiplication.doubledAccumulator] at hparity
  rw [modularDoubleIndex, actGates_cons, actGates_nil, act_cx_write,
    bitValue_write_self, Nat.mod_mod, hcorrectedReduction, hflag,
    htargetBit]
  by_cases hreduce : modulus ≤ 2 * targetValue wordWidth original
  · have hodd : (2 * targetValue wordWidth original % modulus) % 2 = 1 := by
      have hdecide : decide
          (2 * targetValue wordWidth original % modulus % 2 = 1) = true := by
        simpa [hreduce] using hparity.symm
      exact of_decide_eq_true hdecide
    simp [VQBridge.Curve.LuoMultiplication.bitValue, rawDouble, hreduce, hodd]
  · have hnotOdd :
        (2 * targetValue wordWidth original % modulus) % 2 ≠ 1 := by
      have hdecide : decide
          (2 * targetValue wordWidth original % modulus % 2 = 1) = false := by
        simpa [hreduce] using hparity.symm
      exact of_decide_eq_false hdecide
    have hparityBound := Nat.mod_lt
      (2 * targetValue wordWidth original % modulus) (by decide : 0 < 2)
    have heven : (2 * targetValue wordWidth original % modulus) % 2 = 0 := by
      omega
    simp [VQBridge.Curve.LuoMultiplication.bitValue, rawDouble, hreduce, heven]

theorem modularDoubleIndex_extension
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    bitValue (modularDoubleIndex modulus wordWidth original)
      (targetExtensionWire wordWidth) = 0 := by
  rw [modularDoubleIndex, actGates_cons, actGates_nil, act_cx_write,
    bitValue_write_ne (by
      simp [targetExtensionWire, reductionWire]
      omega),
    correctedIndex_extension hwidth hmodulusPos hmodulus
      hreduction hextension]

theorem modularDoubleIndex_eq
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (htarget : targetValue wordWidth original < modulus)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0) :
    modularDoubleIndex modulus wordWidth original =
      writeField original targetOffset wordWidth
        (rawDouble wordWidth original % modulus) := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases htargetBit : q < wordWidth
  · rw [testBit_writeField_inside (off := targetOffset)
      (n := wordWidth) (b := q) (by simp [targetOffset]) (by
        simp [targetOffset]
        omega)]
    have htargetEq := congrArg (fun value => value.testBit q)
      (modularDoubleIndex_target hwidth hmodulusPos hmodulus htarget
        hreduction hextension)
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
      exact (modularDoubleIndex_extension hwidth hmodulusPos hmodulus
        hreduction hextension).trans hextension.symm
    by_cases hreductionWire : q = reductionWire wordWidth
    · subst q
      apply testBit_eq_of_bitValue_eq
      exact (modularDoubleIndex_reduction hwidth hmodulusPos hmodulus
        hmodulusOdd htarget hreduction hextension).trans hreduction.symm
    · rw [modularDoubleIndex, actGates_cons, actGates_nil, act_cx_write,
        testBit_writeField_outside (by
          simp only [reductionWire] at hreductionWire ⊢
          omega),
        correctedIndex_testBit_of_ge_targetExtension hwidth (by
          simp only [targetExtensionWire] at htargetExtension
          omega) hreductionWire]

theorem modularDoubleOps_correct
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level)
    (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus)
    (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (htarget : targetValue wordWidth original < modulus)
    (hworkspace : WorkspaceClear wordWidth original)
    (hreduction : bitValue original (reductionWire wordWidth) = 0)
    (hextension : bitValue original (targetExtensionWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (modularDoubleOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (writeField original targetOffset wordWidth
        (rawDouble wordWidth original % modulus)) := by
  calc
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (modularDoubleIndex modulus wordWidth original) :=
      modularDoubleOps_exact hl hwidth hworkspace rec creg hb
    _ = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (writeField original targetOffset wordWidth
          (rawDouble wordWidth original % modulus)) := by
      rw [modularDoubleIndex_eq hwidth hmodulusPos hmodulus hmodulusOdd
        htarget hreduction hextension]

end VQMathlib.Curve.PackedModularDoubling
