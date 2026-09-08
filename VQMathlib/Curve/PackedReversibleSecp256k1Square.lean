import VQ.Curve.PackedReversibleSecp256k1Square
import VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQMathlib.Curve.PackedReversibleSecp256k1Square

open VQ
open VQ.Reversible
open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic
open VQ.Curve.PackedReversibleSecp256k1Square
open VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

def sourceValue (i : Nat) : Nat :=
  readField i (VQ.Curve.PackedModularAddition.sourceOffset wordWidth) wordWidth

def targetValue (i : Nat) : Nat :=
  readField i VQ.Curve.PackedModularAddition.targetOffset wordWidth

def selectorBit (i bit : Nat) : Nat :=
  bitValue i (selectorWire bit)

def controlIndex (i bit : Nat) : Nat :=
  writeField i (VQ.Curve.PackedModularAddition.controlWire wordWidth) 1
    (selectorBit i bit)

theorem controlToggleGates_act {i bit : Nat}
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates
        (VQ.Curve.PackedReversibleSecp256k1Square.controlToggleGates bit) i =
      controlIndex i bit := by
  simp only [VQ.Curve.PackedReversibleSecp256k1Square.controlToggleGates,
    actGates_cons, actGates_nil, act_cx_write,
    hcontrol, Nat.zero_add]
  unfold controlIndex selectorBit
  rw [Nat.mod_eq_of_lt (bitValue_lt i (selectorWire bit))]

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
      selectorBit i bit := by
  rw [controlIndex, bitValue_write_self]
  exact Nat.mod_eq_of_lt (bitValue_lt i (selectorWire bit))

theorem selector_controlIndex {i bit : Nat} (hbit : bit < wordWidth) :
    bitValue (controlIndex i bit) (selectorWire bit) = selectorBit i bit := by
  rw [controlIndex, bitValue_write_ne
    (VQ.Curve.PackedReversibleSecp256k1Square.selectorWire_ne_control hbit)]
  rfl

theorem rawSum_controlIndex {i bit : Nat} :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum
        (controlIndex i bit) =
      selectorBit i bit * sourceValue i + targetValue i := by
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
        i.testBit (selectorWire bit) := by
    cases hselector : i.testBit (selectorWire bit)
    · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
      rw [control_controlIndex]
      simp [selectorBit, bitValue, hselector]
    · apply (testBit_eq_true_iff_bitValue_eq_one _ _).2
      rw [control_controlIndex]
      simp [selectorBit, bitValue, hselector]
  rw [hcontrolTest]
  cases hselector : i.testBit (selectorWire bit) <;>
    simp [selectorBit, bitValue, hselector]

theorem controlledAddGates_correct {i bit : Nat}
    (hbit : bit < wordWidth)
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i < VQ.Curve.p)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates
        (VQ.Curve.PackedReversibleSecp256k1Square.controlledAddGates bit) i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        ((selectorBit i bit * sourceValue i + targetValue i) % VQ.Curve.p) := by
  let toggled := controlIndex i bit
  let value :=
    (selectorBit i bit * sourceValue i + targetValue i) % VQ.Curve.p
  have htoggled := controlToggleGates_act (i := i) (bit := bit) hcontrol
  have hsourceToggled : Arithmetic.sourceValue toggled = sourceValue i := by
    change sourceValue toggled = sourceValue i
    simpa only [toggled] using sourceValue_controlIndex i bit
  have htargetToggled : Arithmetic.targetValue toggled = targetValue i := by
    change targetValue toggled = targetValue i
    simpa only [toggled] using targetValue_controlIndex i bit
  have hworkspaceToggled : CorrectionWorkspaceClear toggled := by
    simpa only [toggled, controlIndex] using
      hworkspace.writeControl (selectorBit i bit)
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
        selectorBit i bit := by
    rw [bitValue_write_out (by
      right
      simp [VQ.Curve.PackedModularAddition.targetOffset,
        VQ.Curve.PackedModularAddition.controlWire, wordWidth]),
      control_controlIndex]
  have hselectorAdded :
      bitValue
          (writeField toggled VQ.Curve.PackedModularAddition.targetOffset
            wordWidth value)
          (selectorWire bit) = selectorBit i bit := by
    rw [bitValue_write_out (by
      right
      simp [selectorWire, VQ.Curve.PackedModularAddition.targetOffset,
        VQ.Curve.PackedModularAddition.sourceOffset, wordWidth]
      omega),
      selector_controlIndex hbit]
  have htwice : (selectorBit i bit + selectorBit i bit) % 2 = 0 := by
    have hlt := bitValue_lt i (selectorWire bit)
    unfold selectorBit
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
  simp only [VQ.Curve.PackedReversibleSecp256k1Square.controlledAddGates,
    actGates_append]
  rw [htoggled, hadd']
  simp only [VQ.Curve.PackedReversibleSecp256k1Square.controlToggleGates,
    actGates_cons, actGates_nil, act_cx_write]
  rw [hcontrolAdded, hselectorAdded, htwice]
  unfold toggled controlIndex
  rw [writeField_comm hdisjoint, writeField_writeField, hclear]

def squareValue (i : Nat) (bits : List Nat) : Nat :=
  VQBridge.Curve.LuoMultiplication.horner VQ.Curve.p (sourceValue i)
    (bits.map fun bit => i.testBit (selectorWire bit))

theorem selectorBit_eq (i bit : Nat) :
    selectorBit i bit = VQBridge.Curve.LuoMultiplication.bitValue
      (i.testBit (selectorWire bit)) := by
  unfold selectorBit bitValue VQBridge.Curve.LuoMultiplication.bitValue
  cases i.testBit (selectorWire bit) <;> rfl

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

theorem selectorBit_writeTarget (i value bit : Nat) :
    selectorBit
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          value) bit =
      selectorBit i bit := by
  unfold selectorBit
  rw [bitValue_write_out (by
    right
    simp [selectorWire, VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedModularAddition.sourceOffset, wordWidth]
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

theorem squareValue_lt {i : Nat} : ∀ {bits : List Nat}, bits ≠ [] →
    squareValue i bits < VQ.Curve.p
  | [], hbits => (hbits rfl).elim
  | _ :: _, _ => by
      simp [squareValue, VQBridge.Curve.LuoMultiplication.horner]
      exact Nat.mod_lt _ VQ.Curve.p_pos

theorem squareGatesAux_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    ∀ bits,
      (∀ bit ∈ bits, bit < wordWidth) →
      actGates (squareGatesAux bits) i =
        writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (squareValue i bits)
  | [], _ => by
      simp only [squareGatesAux, actGates_nil]
      rw [show squareValue i [] = 0 by rfl, ← htarget]
      exact (writeField_read i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth).symm
  | [bit], hbits => by
      have hbit := hbits bit (by simp)
      have hadd := controlledAddGates_correct hbit hsource
        (by rw [htarget]; exact VQ.Curve.p_pos) hworkspace hreduction hcontrol
      rw [squareGatesAux]
      simpa [squareValue, VQBridge.Curve.LuoMultiplication.horner,
        selectorBit_eq, htarget, Nat.add_comm] using hadd
  | bit :: nextBit :: rest, hbits => by
      let tailBits := nextBit :: rest
      let tailValue := squareValue i tailBits
      let tailIndex := writeField i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth tailValue
      let doubleValue := 2 * tailValue % VQ.Curve.p
      let doubleIndex := writeField i
        VQ.Curve.PackedModularAddition.targetOffset wordWidth doubleValue
      let finalValue :=
        (selectorBit i bit * sourceValue i + doubleValue) % VQ.Curve.p
      have hbit : bit < wordWidth := hbits bit (by simp)
      have htailBits : ∀ q ∈ tailBits, q < wordWidth := by
        intro q hq
        exact hbits q (List.mem_cons_of_mem bit hq)
      have htail := squareGatesAux_correct hsource htarget hworkspace
        hreduction hcontrol tailBits htailBits
      change actGates (squareGatesAux tailBits) i = tailIndex at htail
      have htailLt : tailValue < VQ.Curve.p :=
        squareValue_lt (bits := tailBits) (by simp [tailBits])
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
      have hadd := controlledAddGates_correct (i := doubleIndex) hbit
        (by rw [hsourceDouble]; exact hsource)
        (by rw [htargetDouble]; exact hdoubleLt) hworkspaceDouble
        hreductionDouble hcontrolDouble
      have hbitDouble : selectorBit doubleIndex bit = selectorBit i bit := by
        simpa only [doubleIndex] using selectorBit_writeTarget i doubleValue bit
      have hadd' : actGates
          (VQ.Curve.PackedReversibleSecp256k1Square.controlledAddGates bit)
          doubleIndex =
          writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
            finalValue := by
        rw [hadd]
        simp [finalValue, hbitDouble, hsourceDouble, htargetDouble, doubleIndex,
          writeField_writeField]
      have hvalue : finalValue = squareValue i (bit :: nextBit :: rest) := by
        calc
          finalValue =
              (doubleValue + selectorBit i bit * sourceValue i) %
                VQ.Curve.p := by
            simp [finalValue, Nat.add_comm]
          _ = (2 * tailValue + selectorBit i bit * sourceValue i) %
                VQ.Curve.p := by
            simp only [doubleValue]
            rw [Nat.mod_add_mod]
          _ = squareValue i (bit :: nextBit :: rest) := by
            simp [squareValue, VQBridge.Curve.LuoMultiplication.horner,
              tailValue, tailBits, selectorBit_eq]
      simp only [squareGatesAux, actGates_append]
      rw [htail, hdouble', hadd', hvalue]

theorem squareValue_range (i : Nat) :
    squareValue i (List.range wordWidth) =
      sourceValue i * sourceValue i % VQ.Curve.p := by
  rw [squareValue, VQBridge.Curve.LuoMultiplication.horner_correct]
  simp only [selectorWire]
  rw [VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Product.decode_range_testBits_offset]
  rfl

theorem gates_correct {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates gates i =
      writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
        (sourceValue i * sourceValue i % VQ.Curve.p) := by
  rw [gates]
  have h := squareGatesAux_correct hsource htarget hworkspace hreduction
    hcontrol (List.range wordWidth) (fun bit hbit => List.mem_range.mp hbit)
  rw [squareValue_range] at h
  exact h

theorem reverse_clears {i : Nat}
    (hsource : sourceValue i ≤ VQ.Curve.p)
    (htarget : targetValue i = 0)
    (hworkspace : CorrectionWorkspaceClear i)
    (hreduction : bitValue i
      (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0)
    (hcontrol : bitValue i
      (VQ.Curve.PackedModularAddition.controlWire wordWidth) = 0) :
    actGates gates.reverse
        (writeField i VQ.Curve.PackedModularAddition.targetOffset wordWidth
          (sourceValue i * sourceValue i % VQ.Curve.p)) =
      i := by
  rw [← gates_correct hsource htarget hworkspace hreduction hcontrol]
  exact actGates_reverse
    VQ.Curve.PackedReversibleSecp256k1Square.gates_wellFormed i

end VQMathlib.Curve.PackedReversibleSecp256k1Square
