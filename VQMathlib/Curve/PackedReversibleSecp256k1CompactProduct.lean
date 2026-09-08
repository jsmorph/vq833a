import VQ.Curve.PackedReversibleSecp256k1CompactProduct
import VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct

open VQ
open VQ.Reversible
open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1CompactProduct

def sourceValue (i : Nat) : Nat :=
  readField i (VQ.Curve.PackedModularAddition.sourceOffset wordWidth) wordWidth

def targetValue (i : Nat) : Nat :=
  readField i VQ.Curve.PackedModularAddition.targetOffset wordWidth

def multiplierBit (i bit : Nat) : Nat :=
  bitValue i (multiplierWire bit)

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
  rw [Nat.mod_eq_of_lt (bitValue_lt i (multiplierWire bit))]

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
  exact Nat.mod_eq_of_lt (bitValue_lt i (multiplierWire bit))

theorem multiplier_controlIndex (i bit : Nat) :
    bitValue (controlIndex i bit) (multiplierWire bit) =
      multiplierBit i bit := by
  rw [controlIndex, bitValue_write_ne
    (VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire_ne_control
      bit)]
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
        i.testBit (multiplierWire bit) := by
    cases hbit : i.testBit (multiplierWire bit)
    · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
      rw [control_controlIndex]
      simp [multiplierBit, bitValue, hbit]
    · apply (testBit_eq_true_iff_bitValue_eq_one _ _).2
      rw [control_controlIndex]
      simp [multiplierBit, bitValue, hbit]
  rw [hcontrolTest]
  cases hbit : i.testBit (multiplierWire bit) <;>
    simp [multiplierBit, bitValue, hbit]

theorem controlledAddGates_correct {i bit : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hworkspace :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates (controlledAddGates bit) i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        ((multiplierBit i bit * sourceValue i + targetValue i) %
          VQ.Curve.p) := by
  let toggled := controlIndex i bit
  let value :=
    (multiplierBit i bit * sourceValue i + targetValue i) % VQ.Curve.p
  have htoggled := controlToggleGates_act (i := i) (bit := bit) hcontrol
  have hsourceToggled :
      VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.sourceValue
          toggled = sourceValue i := by
    change sourceValue toggled = sourceValue i
    simpa only [toggled] using sourceValue_controlIndex i bit
  have htargetToggled :
      VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue
          toggled = targetValue i := by
    change targetValue toggled = targetValue i
    simpa only [toggled] using targetValue_controlIndex i bit
  have hworkspaceToggled :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear
        toggled := by
    simpa only [toggled, controlIndex] using
      hworkspace.writeControl (multiplierBit i bit)
  have hreductionToggled : bitValue toggled
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
    rw [show toggled = controlIndex i bit by rfl, reduction_controlIndex]
    exact hreduction
  have hadd :=
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.modularAddGates_correct
      (i := toggled)
      (by rw [hsourceToggled]; exact hsource)
      (by rw [htargetToggled]; exact htarget)
      hworkspaceToggled hreductionToggled
  have hadd' :
      actGates
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates toggled =
        writeField toggled VQ.Curve.PackedModularAddition.targetOffset
          wordWidth value := by
    simpa [value, toggled, rawSum_controlIndex,
      VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.sourceValue,
      sourceValue,
      VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue,
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
          (multiplierWire bit) = multiplierBit i bit := by
    rw [bitValue_write_out (by
      exact VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire_outside_target
        bit), multiplier_controlIndex]
  have htwice : (multiplierBit i bit + multiplierBit i bit) % 2 = 0 := by
    have hlt := bitValue_lt i (multiplierWire bit)
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
    (bits.map fun bit => i.testBit (multiplierWire bit))

def multiplierValue (i : Nat) : Nat :=
  VQBridge.Curve.LuoMultiplication.decode
    ((List.range wordWidth).map fun bit => i.testBit (multiplierWire bit))

theorem multiplierBit_eq (i bit : Nat) :
    multiplierBit i bit = VQBridge.Curve.LuoMultiplication.bitValue
      (i.testBit (multiplierWire bit)) := by
  unfold multiplierBit bitValue VQBridge.Curve.LuoMultiplication.bitValue
  cases i.testBit (multiplierWire bit) <;> rfl

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
  rw [bitValue_write_out
    (VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire_outside_target
      bit)]

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
    (hworkspace :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear i)
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
      have htargetTail :
          VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Double.targetValue
            tailIndex = tailValue := by
        change targetValue tailIndex = tailValue
        simpa only [tailIndex] using
          targetValue_writeTarget (i := i) htailFit
      have hworkspaceTail :
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear
            tailIndex := by
        simpa only [tailIndex] using hworkspace.writeTarget tailValue
      have hreductionTail : bitValue tailIndex
          (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
        rw [show tailIndex = writeField i
          VQ.Curve.PackedModularAddition.targetOffset wordWidth tailValue by rfl,
          reduction_writeTarget]
        exact hreduction
      have hdouble :=
        VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Double.modularDoubleGates_correct
          (i := tailIndex) (by rw [htargetTail]; exact htailLt)
          hworkspaceTail hreductionTail
      have hdouble' : actGates
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularDoubleGates
          tailIndex = doubleIndex := by
        rw [hdouble]
        simp [doubleIndex, tailIndex, doubleValue,
          VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Double.rawDouble,
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
      have hworkspaceDouble :
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear
            doubleIndex := by
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
        simpa only [doubleIndex] using
          multiplierBit_writeTarget i doubleValue bit
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

theorem productValue_range (i : Nat) :
    productValue i (List.range wordWidth) =
      multiplierValue i * sourceValue i % VQ.Curve.p := by
  rw [productValue, VQBridge.Curve.LuoMultiplication.horner_correct]
  rfl

theorem gates_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates gates i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (multiplierValue i * sourceValue i % VQ.Curve.p) := by
  rw [gates]
  have h := productGatesAux_correct hsource htarget hworkspace hreduction
    hcontrol (List.range wordWidth) (fun bit hbit => List.mem_range.mp hbit)
  rw [productValue_range] at h
  exact h

theorem gates_reverse_clears {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates gates.reverse
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (multiplierValue i * sourceValue i % VQ.Curve.p)) =
      i := by
  rw [← gates_correct hsource htarget hworkspace hreduction hcontrol]
  exact actGates_reverse
    VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates_wellFormed i

end VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct
