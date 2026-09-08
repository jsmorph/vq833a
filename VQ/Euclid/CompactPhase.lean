/-
Phase update with an eight-bit remainder-length register.

The established nine-bit phase circuit uses only seven of its nine selector
scratch wires.  A temporary high bit embeds the eight-bit truth-minus-one
remainder-length code into the nine-bit code during the update.
-/
import VQ.Euclid.Phase

namespace VQ
namespace Euclid
namespace CompactPhase

open Reversible

def phase1Wire : Nat := 0
def phase2Wire : Nat := 1
def signWire : Nat := 2
def lenQOffset : Nat := 3
def lenRPrimeOffset : Nat := 12
def extensionWire : Nat := 20
def shiftOffset : Nat := 21
def zeroQWire : Nat := 30
def zeroRPrimeWire : Nat := 31
def zeroShiftWire : Nat := 32
def conditionWire : Nat := 33
def temporaryWire : Nat := 34
def scratchOffset : Nat := 35
def scratchWidth : Nat := 7

def layout : Layout := [1, 1, 1, 9, 8, 1, 9, 1, 1, 1, 1, 1, scratchWidth]

def prepared (i : Nat) : Nat :=
  writeField i extensionWire 1 ((bitValue i extensionWire + 1) % 2)

def restored (i : Nat) : Nat :=
  writeField i extensionWire 1 ((bitValue i extensionWire + 1) % 2)

def gates : List RGate :=
  [.x extensionWire] ++ Phase.gates 9 9 ++ [.x extensionWire]

def circuit : RCircuit := { width := layout.width, gates := gates }

theorem layout_width : layout.width = 42 := by
  decide

theorem old_wire_alignment :
    Phase.phase1Wire = phase1Wire ∧
    Phase.phase2Wire = phase2Wire ∧
    Phase.signWire = signWire ∧
    Phase.lenQOffset = lenQOffset ∧
    Phase.lenRPrimeOffset 9 = lenRPrimeOffset ∧
    Phase.shiftOffset 9 = shiftOffset ∧
    Phase.zeroQWire 9 9 = zeroQWire ∧
    Phase.zeroRPrimeWire 9 9 = zeroRPrimeWire ∧
    Phase.zeroShiftWire 9 9 = zeroShiftWire ∧
    Phase.conditionWire 9 9 = conditionWire ∧
    Phase.temporaryWire 9 9 = temporaryWire ∧
    Phase.poolOffset 9 9 = scratchOffset := by
  decide

theorem prepared_act (i : Nat) :
    RGate.act (.x extensionWire) i = prepared i := by
  simpa [prepared] using act_x_write extensionWire i

theorem restored_act (i : Nat) :
    RGate.act (.x extensionWire) i = restored i := by
  simpa [restored] using act_x_write extensionWire i

theorem prepared_extension {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    bitValue (prepared i) extensionWire = 1 := by
  simp [prepared, bitValue_write_self, hextension]

theorem prepared_bit_of_ne {i q : Nat} (h : q ≠ extensionWire) :
    bitValue (prepared i) q = bitValue i q := by
  exact bitValue_write_ne h

theorem restored_bit_of_ne {i q : Nat} (h : q ≠ extensionWire) :
    bitValue (restored i) q = bitValue i q := by
  exact bitValue_write_ne h

theorem prepared_rPrime {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    readField (prepared i) lenRPrimeOffset 9 =
      readField i lenRPrimeOffset 8 + 256 := by
  rw [show 9 = 8 + 1 by decide, readField_high]
  rw [show lenRPrimeOffset + 8 = extensionWire by decide,
    prepared_extension hextension]
  have hlow : readField (prepared i) lenRPrimeOffset 8 =
      readField i lenRPrimeOffset 8 := by
    simp only [prepared]
    rw [readField_writeField_of_disjoint (by
      simp [lenRPrimeOffset, extensionWire])]
  rw [hlow]

theorem prepared_rPrime_is_zero {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    readField (prepared i) lenRPrimeOffset 9 = encodedZero 9 ↔
      readField i lenRPrimeOffset 8 = encodedZero 8 := by
  rw [prepared_rPrime hextension]
  have hlt := readField_lt i lenRPrimeOffset 8
  norm_num [encodedZero] at hlt ⊢
  omega

def zeroQValue (i : Nat) : Nat :=
  if readField i lenQOffset 9 = encodedZero 9 then 1 else 0

def zeroRPrimeValue (i : Nat) : Nat :=
  if readField i lenRPrimeOffset 8 = encodedZero 8 then 1 else 0

def zeroShiftValue (i : Nat) : Nat :=
  if readField i shiftOffset 9 = encodedZero 9 then 1 else 0

def conditionValue (i : Nat) : Nat :=
  if zeroRPrimeValue i = 0 then zeroQValue i else 0

def middlePhase2Value (i : Nat) : Nat :=
  (bitValue i phase2Wire + conditionValue i *
    ((bitValue i signWire + bitValue i phase1Wire) % 2)) % 2

def phase1Value (i : Nat) : Nat :=
  (bitValue i phase1Wire + zeroShiftValue i) % 2

def phase2Value (i : Nat) : Nat :=
  (middlePhase2Value i + zeroShiftValue i) % 2

def signValue (i : Nat) : Nat :=
  (bitValue i signWire + conditionValue i * middlePhase2Value i) % 2

theorem prepared_lenQ (i : Nat) :
    readField (prepared i) lenQOffset 9 = readField i lenQOffset 9 := by
  simp only [prepared]
  rw [readField_writeField_of_disjoint (by
    simp [lenQOffset, extensionWire])]

theorem prepared_shift (i : Nat) :
    readField (prepared i) shiftOffset 9 = readField i shiftOffset 9 := by
  simp only [prepared]
  rw [readField_writeField_of_disjoint (by
    simp [shiftOffset, extensionWire])]

theorem selectorQ_prepared (i : Nat) :
    Phase.selectorValue 9 Phase.lenQOffset (prepared i) = zeroQValue i := by
  simp only [Phase.selectorValue, zeroQValue]
  rw [show Phase.lenQOffset = lenQOffset by decide, prepared_lenQ]

theorem selectorRPrime_prepared {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    Phase.selectorValue 9 (Phase.lenRPrimeOffset 9) (prepared i) =
      zeroRPrimeValue i := by
  simp only [Phase.selectorValue, zeroRPrimeValue]
  rw [show Phase.lenRPrimeOffset 9 = lenRPrimeOffset by decide]
  by_cases h : readField i lenRPrimeOffset 8 = encodedZero 8
  · have hold := (prepared_rPrime_is_zero hextension).2 h
    simp [h, hold]
  · have hold : readField (prepared i) lenRPrimeOffset 9 ≠ encodedZero 9 :=
      fun h' => h ((prepared_rPrime_is_zero hextension).1 h')
    simp [h, hold]

theorem selectorShift_prepared (i : Nat) :
    Phase.selectorValue 9 (Phase.shiftOffset 9) (prepared i) =
      zeroShiftValue i := by
  simp only [Phase.selectorValue, zeroShiftValue]
  rw [show Phase.shiftOffset 9 = shiftOffset by decide, prepared_shift]

theorem selected_values {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    let s := Phase.selected 9 9 (prepared i)
    bitValue s phase1Wire = bitValue i phase1Wire ∧
    bitValue s phase2Wire = bitValue i phase2Wire ∧
    bitValue s signWire = bitValue i signWire ∧
    bitValue s zeroQWire = zeroQValue i ∧
    bitValue s zeroRPrimeWire = zeroRPrimeValue i ∧
    bitValue s zeroShiftWire = zeroShiftValue i := by
  let s := Phase.selected 9 9 (prepared i)
  have hflags := Phase.selected_flags 9 9 (prepared i)
  simp only at hflags
  have hp1 := Phase.selected_preserves_bit
    (lengthWidth := 9) (shiftWidth := 9) (i := prepared i)
    (q := phase1Wire) (by decide) (by decide) (by decide)
  have hp2 := Phase.selected_preserves_bit
    (lengthWidth := 9) (shiftWidth := 9) (i := prepared i)
    (q := phase2Wire) (by decide) (by decide) (by decide)
  have hsign := Phase.selected_preserves_bit
    (lengthWidth := 9) (shiftWidth := 9) (i := prepared i)
    (q := signWire) (by decide) (by decide) (by decide)
  change bitValue s phase1Wire = _ ∧ bitValue s phase2Wire = _ ∧
    bitValue s signWire = _ ∧ bitValue s zeroQWire = _ ∧
    bitValue s zeroRPrimeWire = _ ∧ bitValue s zeroShiftWire = _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl, hp1,
      prepared_bit_of_ne (by decide)]
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl, hp2,
      prepared_bit_of_ne (by decide)]
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl, hsign,
      prepared_bit_of_ne (by decide)]
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl,
      show zeroQWire = Phase.zeroQWire 9 9 by decide,
      hflags.1, selectorQ_prepared]
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl,
      show zeroRPrimeWire = Phase.zeroRPrimeWire 9 9 by decide,
      hflags.2.1, selectorRPrime_prepared hextension]
  · rw [show s = Phase.selected 9 9 (prepared i) from rfl,
      show zeroShiftWire = Phase.zeroShiftWire 9 9 by decide,
      hflags.2.2, selectorShift_prepared]

theorem selected_phase_values {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    let s := Phase.selected 9 9 (prepared i)
    Phase.phase1Value 9 9 s = phase1Value i ∧
    Phase.phase2Value 9 9 s = phase2Value i ∧
    Phase.signValue 9 9 s = signValue i := by
  let s := Phase.selected 9 9 (prepared i)
  have h := selected_values hextension
  simp only at h
  change Phase.phase1Value 9 9 s = _ ∧ Phase.phase2Value 9 9 s = _ ∧
    Phase.signValue 9 9 s = _
  rcases h with ⟨hp1, hp2, hsign, hzq, hzrp, hzs⟩
  have hc : Phase.conditionValue 9 9 s = conditionValue i := by
    simp only [Phase.conditionValue, conditionValue]
    rw [show Phase.zeroRPrimeWire 9 9 = zeroRPrimeWire by decide,
      show Phase.zeroQWire 9 9 = zeroQWire by decide, hzrp, hzq]
  have hm : Phase.middlePhase2Value 9 9 s = middlePhase2Value i := by
    simp only [Phase.middlePhase2Value, middlePhase2Value]
    rw [show Phase.phase2Wire = phase2Wire by decide,
      show Phase.signWire = signWire by decide,
      show Phase.phase1Wire = phase1Wire by decide, hp2, hsign, hp1, hc]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Phase.phase1Value, phase1Value]
    rw [show Phase.phase1Wire = phase1Wire by decide,
      show Phase.zeroShiftWire 9 9 = zeroShiftWire by decide, hp1, hzs]
  · simp only [Phase.phase2Value, phase2Value]
    rw [show Phase.zeroShiftWire 9 9 = zeroShiftWire by decide, hm, hzs]
  · simp only [Phase.signValue, signValue]
    rw [show Phase.signWire = signWire by decide, hsign, hc, hm]

theorem old_pool_clear {i : Nat}
    (hfit : i < 2 ^ layout.width)
    (hscratch : readField i scratchOffset scratchWidth = 0) :
    readField (prepared i) (Phase.poolOffset 9 9) (Phase.poolWidth 9 9) = 0 := by
  have htail : readField i 42 2 = 0 := by
    simp [readField, Nat.shiftRight_eq_zero i 42 (by simpa [layout_width] using hfit)]
  have hpool : readField i scratchOffset 9 = 0 := by
    change readField i 35 9 = 0
    rw [show 9 = 7 + 2 by omega, readField_split]
    constructor
    · simpa [scratchOffset, scratchWidth] using hscratch
    · simpa using htail
  rw [show Phase.poolOffset 9 9 = scratchOffset by decide,
    show Phase.poolWidth 9 9 = 9 by decide]
  simpa [prepared, scratchOffset, extensionWire] using
    (readField_writeField_of_disjoint
      (i := i) (o₁ := extensionWire) (n₁ := 1)
      (v := (bitValue i extensionWire + 1) % 2)
      (o₂ := scratchOffset) (n₂ := 9)
      (by simp [extensionWire, scratchOffset])).trans hpool

theorem prepared_zeroQ {i : Nat} (h : bitValue i zeroQWire = 0) :
    bitValue (prepared i) (Phase.zeroQWire 9 9) = 0 := by
  rw [show Phase.zeroQWire 9 9 = zeroQWire by decide,
    prepared_bit_of_ne (by decide), h]

theorem prepared_zeroRPrime {i : Nat}
    (h : bitValue i zeroRPrimeWire = 0) :
    bitValue (prepared i) (Phase.zeroRPrimeWire 9 9) = 0 := by
  rw [show Phase.zeroRPrimeWire 9 9 = zeroRPrimeWire by decide,
    prepared_bit_of_ne (by decide), h]

theorem prepared_zeroShift {i : Nat} (h : bitValue i zeroShiftWire = 0) :
    bitValue (prepared i) (Phase.zeroShiftWire 9 9) = 0 := by
  rw [show Phase.zeroShiftWire 9 9 = zeroShiftWire by decide,
    prepared_bit_of_ne (by decide), h]

theorem prepared_condition {i : Nat} (h : bitValue i conditionWire = 0) :
    bitValue (prepared i) (Phase.conditionWire 9 9) = 0 := by
  rw [show Phase.conditionWire 9 9 = conditionWire by decide,
    prepared_bit_of_ne (by decide), h]

theorem prepared_temporary {i : Nat} (h : bitValue i temporaryWire = 0) :
    bitValue (prepared i) (Phase.temporaryWire 9 9) = 0 := by
  rw [show Phase.temporaryWire 9 9 = temporaryWire by decide,
    prepared_bit_of_ne (by decide), h]

theorem act_circuit {i : Nat}
    (hfit : i < 2 ^ layout.width)
    (hzeroQ : bitValue i zeroQWire = 0)
    (hzeroRPrime : bitValue i zeroRPrimeWire = 0)
    (hzeroShift : bitValue i zeroShiftWire = 0)
    (hcondition : bitValue i conditionWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0) :
    act circuit i = restored (Phase.out 9 9 (prepared i)) := by
  have hq := prepared_zeroQ hzeroQ
  have hrp := prepared_zeroRPrime hzeroRPrime
  have hs := prepared_zeroShift hzeroShift
  have hc := prepared_condition hcondition
  have ht := prepared_temporary htemporary
  have hp := old_pool_clear hfit hscratch
  change actGates gates i = _
  simp only [gates, actGates_append]
  rw [show actGates [.x extensionWire] i = prepared i by
    simp [actGates, prepared_act]]
  rw [show actGates (Phase.gates 9 9) (prepared i) =
      Phase.out 9 9 (prepared i) by
    exact Phase.act_circuit hq hrp hs hc ht hp]
  simp [actGates, restored_act]

theorem circuit_bits {i : Nat}
    (hfit : i < 2 ^ layout.width)
    (hextension : bitValue i extensionWire = 0)
    (hzeroQ : bitValue i zeroQWire = 0)
    (hzeroRPrime : bitValue i zeroRPrimeWire = 0)
    (hzeroShift : bitValue i zeroShiftWire = 0)
    (hcondition : bitValue i conditionWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0) :
    let result := act circuit i
    bitValue result phase1Wire = phase1Value i ∧
    bitValue result phase2Wire = phase2Value i ∧
    bitValue result signWire = signValue i ∧
    bitValue result extensionWire = 0 ∧
    bitValue result zeroQWire = 0 ∧
    bitValue result zeroRPrimeWire = 0 ∧
    bitValue result zeroShiftWire = 0 ∧
    bitValue result conditionWire = 0 ∧
    bitValue result temporaryWire = 0 ∧
    readField result scratchOffset scratchWidth = 0 := by
  let p := prepared i
  let j := act (Phase.circuit 9 9) p
  let result := act circuit i
  have hq := prepared_zeroQ hzeroQ
  have hrp := prepared_zeroRPrime hzeroRPrime
  have hs := prepared_zeroShift hzeroShift
  have hc := prepared_condition hcondition
  have ht := prepared_temporary htemporary
  have hp := old_pool_clear hfit hscratch
  have hj : j = Phase.out 9 9 p := by
    exact Phase.act_circuit hq hrp hs hc ht hp
  have hold := Phase.circuit_bits hq hrp hs hc ht hp
  simp only at hold
  change let _ := Phase.selected 9 9 p
    let result' := act (Phase.circuit 9 9) p
    _ at hold
  simp only at hold
  rcases hold with
    ⟨hphase1, hphase2, hsign, hzq, hzrp, hzs, hcond, htmp, hpool⟩
  have hvalues := selected_phase_values hextension
  simp only at hvalues
  rcases hvalues with ⟨hvalue1, hvalue2, hvalueSign⟩
  have hresult : result = restored j := by
    rw [show result = act circuit i from rfl, act_circuit hfit hzeroQ
      hzeroRPrime hzeroShift hcondition htemporary hscratch, hj]
  have hjextension : bitValue j extensionWire = 1 := by
    rw [hj, Phase.out_eq_writeFields hq hrp hs hc ht hp]
    repeat' rw [bitValue_write_ne (by decide)]
    exact prepared_extension hextension
  change bitValue result phase1Wire = _ ∧ bitValue result phase2Wire = _ ∧
    bitValue result signWire = _ ∧ bitValue result extensionWire = 0 ∧
    bitValue result zeroQWire = 0 ∧ bitValue result zeroRPrimeWire = 0 ∧
    bitValue result zeroShiftWire = 0 ∧ bitValue result conditionWire = 0 ∧
    bitValue result temporaryWire = 0 ∧
    readField result scratchOffset scratchWidth = 0
  rw [hresult]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [restored_bit_of_ne (by decide),
      show phase1Wire = Phase.phase1Wire by decide, hphase1, hvalue1]
  · rw [restored_bit_of_ne (by decide),
      show phase2Wire = Phase.phase2Wire by decide, hphase2, hvalue2]
  · rw [restored_bit_of_ne (by decide),
      show signWire = Phase.signWire by decide, hsign, hvalueSign]
  · simp [restored, bitValue_write_self, hjextension]
  · rw [restored_bit_of_ne (by decide),
      show zeroQWire = Phase.zeroQWire 9 9 by decide, hzq]
  · rw [restored_bit_of_ne (by decide),
      show zeroRPrimeWire = Phase.zeroRPrimeWire 9 9 by decide, hzrp]
  · rw [restored_bit_of_ne (by decide),
      show zeroShiftWire = Phase.zeroShiftWire 9 9 by decide, hzs]
  · rw [restored_bit_of_ne (by decide),
      show conditionWire = Phase.conditionWire 9 9 by decide, hcond]
  · rw [restored_bit_of_ne (by decide),
      show temporaryWire = Phase.temporaryWire 9 9 by decide, htmp]
  · simp only [restored]
    rw [readField_writeField_of_disjoint (by
      simp [extensionWire, scratchOffset])]
    exact readField_narrow (by decide) hpool

theorem act_circuit_eq_writeFields {i : Nat}
    (hfit : i < 2 ^ layout.width)
    (hextension : bitValue i extensionWire = 0)
    (hzeroQ : bitValue i zeroQWire = 0)
    (hzeroRPrime : bitValue i zeroRPrimeWire = 0)
    (hzeroShift : bitValue i zeroShiftWire = 0)
    (hcondition : bitValue i conditionWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0) :
    let result := act circuit i
    result =
      writeField
        (writeField
          (writeField i phase1Wire 1 (bitValue result phase1Wire))
          phase2Wire 1 (bitValue result phase2Wire))
        signWire 1 (bitValue result signWire) := by
  let result := act circuit i
  have hq := prepared_zeroQ hzeroQ
  have hrp := prepared_zeroRPrime hzeroRPrime
  have hs := prepared_zeroShift hzeroShift
  have hc := prepared_condition hcondition
  have ht := prepared_temporary htemporary
  have hp := old_pool_clear hfit hscratch
  have hact : result = restored (Phase.out 9 9 (prepared i)) := by
    exact act_circuit hfit hzeroQ hzeroRPrime hzeroShift hcondition htemporary
      hscratch
  have hout := Phase.out_eq_writeFields hq hrp hs hc ht hp
  simp only at hout
  rw [show Phase.phase1Wire = phase1Wire by decide,
    show Phase.phase2Wire = phase2Wire by decide,
    show Phase.signWire = signWire by decide] at hout
  have hbits := circuit_bits hfit hextension hzeroQ hzeroRPrime hzeroShift
    hcondition htemporary hscratch
  simp only at hbits
  rcases hbits with
    ⟨_, _, _, hextensionResult, _, _, _, _, _, _⟩
  have hframe := eq_write_three_fields
    (i := i) (j := result)
    (o₁ := phase1Wire) (n₁ := 1)
    (o₂ := phase2Wire) (n₂ := 1)
    (o₃ := signWire) (n₃ := 1)
    (by decide) (by decide) (by decide)
    (fun b hphase1 hphase2 hsign => by
      by_cases he : b = extensionWire
      · subst b
        rw [(testBit_eq_false_iff_bitValue_eq_zero result extensionWire).2
            hextensionResult,
          (testBit_eq_false_iff_bitValue_eq_zero i extensionWire).2
            hextension]
      · rw [hact]
        simp only [restored]
        rw [testBit_writeField_outside (by omega), hout,
          testBit_writeField_outside hsign,
          testBit_writeField_outside hphase2,
          testBit_writeField_outside hphase1]
        simp only [prepared]
        rw [testBit_writeField_outside (by omega)])
  simpa [result, readField_one] using hframe

set_option maxRecDepth 4096 in
theorem circuit_wellFormed : circuit.wellFormed = true := by
  decide +kernel

theorem circuit_length : circuit.gates.length = (Phase.circuit 9 9).gates.length + 2 := by
  simp [circuit, gates, Phase.circuit]

theorem circuit_ccx :
    circuit.gates.countP RGate.isCcx =
      (Phase.circuit 9 9).gates.countP RGate.isCcx := by
  simp [circuit, gates, Phase.circuit, RGate.isCcx]

end CompactPhase
end Euclid
end VQ
