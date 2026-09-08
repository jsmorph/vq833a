/-
State transformation of the compact phase update in the 571-wire layout.
-/
import VQ.Euclid.PackedState

namespace VQ
namespace Euclid
namespace PackedPhase

open Reversible

def localLayout : Layout := PackedStepLayout.phaseLayout

def wiring : Wiring := PackedStepLayout.phaseWiring

def input (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

def phaseOneValue (I : Nat) : Nat := CompactPhase.phase1Value (input I)

def phaseTwoValue (I : Nat) : Nat := CompactPhase.phase2Value (input I)

def signValue (I : Nat) : Nat := CompactPhase.signValue (input I)

def output (I : Nat) : Nat :=
  writeField
    (writeField
      (writeField I PackedStepLayout.phaseOneWire 1 (phaseOneValue I))
      PackedStepLayout.phaseTwoWire 1 (phaseTwoValue I))
    PackedStepLayout.signWire 1 (signValue I)

theorem input_field (j I : Nat) (hj : j < wiring.length) :
    localLayout.read (input I) j =
      readField I (wiring.getD j 0) (localLayout.size j) := by
  exact read_gatherBits localLayout wiring j I hj

theorem input_phaseOne (I : Nat) :
    bitValue (input I) CompactPhase.phase1Wire =
      bitValue I PackedStepLayout.phaseOneWire := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.phase1Wire] using
      input_field 0 I (by decide)

theorem input_phaseTwo (I : Nat) :
    bitValue (input I) CompactPhase.phase2Wire =
      bitValue I PackedStepLayout.phaseTwoWire := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.phase2Wire] using
      input_field 1 I (by decide)

theorem input_sign (I : Nat) :
    bitValue (input I) CompactPhase.signWire =
      bitValue I PackedStepLayout.signWire := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.signWire] using
      input_field 2 I (by decide)

theorem input_lengthQ (I : Nat) :
    readField (input I) CompactPhase.lenQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.lenQOffset] using
      input_field 3 I (by decide)

theorem input_lengthRPrime (I : Nat) :
    readField (input I) CompactPhase.lenRPrimeOffset 8 =
      readField I PackedStepLayout.lengthRPrimeOffset 8 := by
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.lenRPrimeOffset] using
      input_field 4 I (by decide)

theorem input_shift (I : Nat) :
    readField (input I) CompactPhase.shiftOffset 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.shiftOffset] using
      input_field 6 I (by decide)

theorem input_extension (I : Nat) :
    bitValue (input I) CompactPhase.extensionWire =
      bitValue I PackedStepLayout.extensionWire := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.extensionWire] using
      input_field 5 I (by decide)

theorem input_zeroQ (I : Nat) :
    bitValue (input I) CompactPhase.zeroQWire =
      bitValue I (PackedStepLayout.poolOffset + 1) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.zeroQWire] using
      input_field 7 I (by decide)

theorem input_zeroRPrime (I : Nat) :
    bitValue (input I) CompactPhase.zeroRPrimeWire =
      bitValue I (PackedStepLayout.poolOffset + 2) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.zeroRPrimeWire] using
      input_field 8 I (by decide)

theorem input_zeroShift (I : Nat) :
    bitValue (input I) CompactPhase.zeroShiftWire =
      bitValue I (PackedStepLayout.poolOffset + 3) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.zeroShiftWire] using
      input_field 9 I (by decide)

theorem input_condition (I : Nat) :
    bitValue (input I) CompactPhase.conditionWire =
      bitValue I (PackedStepLayout.poolOffset + 4) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.conditionWire] using
      input_field 10 I (by decide)

theorem input_temporary (I : Nat) :
    bitValue (input I) CompactPhase.temporaryWire =
      bitValue I (PackedStepLayout.poolOffset + 5) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.temporaryWire] using
      input_field 11 I (by decide)

theorem input_scratch (I : Nat) :
    readField (input I) CompactPhase.scratchOffset
        CompactPhase.scratchWidth =
      readField I (PackedStepLayout.poolOffset + 6) 7 := by
  simpa [input, localLayout, wiring, PackedStepLayout.phaseLayout,
    PackedStepLayout.phaseWiring, CompactPhase.layout, Layout.read,
    Layout.offset, Layout.size, CompactPhase.scratchOffset,
    CompactPhase.scratchWidth] using input_field 12 I (by decide)

theorem gates_act {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates PackedStepLayout.phaseGates I = output I := by
  have hzeroQPhysical :
      bitValue I (PackedStepLayout.poolOffset + 1) = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroRPrimePhysical :
      bitValue I (PackedStepLayout.poolOffset + 2) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hzeroShiftPhysical :
      bitValue I (PackedStepLayout.poolOffset + 3) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hconditionPhysical :
      bitValue I (PackedStepLayout.poolOffset + 4) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have htemporaryPhysical :
      bitValue I (PackedStepLayout.poolOffset + 5) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hscratchPhysical :
      readField I (PackedStepLayout.poolOffset + 6) 7 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hextensionInput :
      bitValue (input I) CompactPhase.extensionWire = 0 :=
    (input_extension I).trans hextension
  have hzeroQInput : bitValue (input I) CompactPhase.zeroQWire = 0 :=
    (input_zeroQ I).trans hzeroQPhysical
  have hzeroRPrimeInput :
      bitValue (input I) CompactPhase.zeroRPrimeWire = 0 :=
    (input_zeroRPrime I).trans hzeroRPrimePhysical
  have hzeroShiftInput :
      bitValue (input I) CompactPhase.zeroShiftWire = 0 :=
    (input_zeroShift I).trans hzeroShiftPhysical
  have hconditionInput :
      bitValue (input I) CompactPhase.conditionWire = 0 :=
    (input_condition I).trans hconditionPhysical
  have htemporaryInput :
      bitValue (input I) CompactPhase.temporaryWire = 0 :=
    (input_temporary I).trans htemporaryPhysical
  have hscratchInput :
      readField (input I) CompactPhase.scratchOffset
        CompactPhase.scratchWidth = 0 :=
    (input_scratch I).trans hscratchPhysical
  have hlocal := CompactPhase.act_circuit_eq_writeFields
    (gatherBits_lt _ _ _) hextensionInput hzeroQInput hzeroRPrimeInput
    hzeroShiftInput hconditionInput htemporaryInput hscratchInput
  simp only at hlocal
  have hbits := CompactPhase.circuit_bits
    (gatherBits_lt _ _ _) hextensionInput hzeroQInput hzeroRPrimeInput
    hzeroShiftInput hconditionInput htemporaryInput hscratchInput
  simp only at hbits
  rw [hbits.1, hbits.2.1, hbits.2.2.1] at hlocal
  have hplaced := actGates_placed_write₃
    (gs := CompactPhase.gates) (L := localLayout) (W := wiring)
    (k₁ := 0) (k₂ := 1) (k₃ := 2)
    PackedStepLayout.phase_disjoint (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun g hg => RCircuit.wellFormed_mem CompactPhase.circuit_wellFormed hg)
    (by simpa [Reversible.act, CompactPhase.circuit, localLayout,
      PackedStepLayout.phaseLayout, CompactPhase.layout, Layout.write,
      Layout.offset, Layout.size, CompactPhase.phase1Wire,
      CompactPhase.phase2Wire, CompactPhase.signWire] using hlocal)
  simpa [PackedStepLayout.phaseGates, PackedStepLayout.placed, localLayout,
    wiring, PackedStepLayout.phaseWiring, output, phaseOneValue,
    phaseTwoValue, signValue, input, PackedStepLayout.phaseLayout,
    CompactPhase.layout, Layout.size] using hplaced

theorem gates_cleanup {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    bitValue (actGates PackedStepLayout.phaseGates I)
        PackedStepLayout.extensionWire = 0 ∧
      readField (actGates PackedStepLayout.phaseGates I)
        (PackedStepLayout.poolOffset + 1) 12 = 0 := by
  rw [gates_act hextension htail]
  constructor
  · simp only [output]
    repeat' rw [bitValue_write_ne (by decide)]
    exact hextension
  · simp only [output]
    repeat' rw [readField_writeField_of_disjoint (by decide)]
    exact htail

private theorem phaseOne_values {I lengthQ lengthRPrime shift : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 lengthQ)
    (hlengthQPositive : 0 < lengthQ)
    (hlengthQBound : lengthQ < 2 ^ 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftBound : shift < 2 ^ 9) :
    phaseOneValue I = (if shift = 0 then 1 else 0) ∧
      phaseTwoValue I = (if shift = 0 then 0 else 1) ∧
      signValue I = 0 := by
  have hphaseOneInput :
      bitValue (input I) CompactPhase.phase1Wire = 0 :=
    (input_phaseOne I).trans hphaseOne
  have hphaseTwoInput :
      bitValue (input I) CompactPhase.phase2Wire = 1 :=
    (input_phaseTwo I).trans hphaseTwo
  have hsignInput : bitValue (input I) CompactPhase.signWire = 0 :=
    (input_sign I).trans hsign
  have hlengthQInput :
      readField (input I) CompactPhase.lenQOffset 9 =
        encodeLength 9 lengthQ :=
    (input_lengthQ I).trans hlengthQ
  have hlengthRPrimeInput :
      readField (input I) CompactPhase.lenRPrimeOffset 8 =
        encodeLength 8 lengthRPrime :=
    (input_lengthRPrime I).trans hlengthRPrime
  have hshiftInput : readField (input I) CompactPhase.shiftOffset 9 =
      encodeLength 9 shift :=
    (input_shift I).trans hshift
  have hlengthQNonzero :
      encodeLength 9 lengthQ ≠ encodedZero 9 := by
    intro hencoded
    have hzero :=
      (encodeLength_eq_encodedZero_iff hlengthQBound).mp hencoded
    omega
  have hlengthRPrimeFit : lengthRPrime < 2 ^ 8 := by
    norm_num
    omega
  have hlengthRPrimeNonzero :
      encodeLength 8 lengthRPrime ≠ encodedZero 8 := by
    intro hencoded
    have hzero :=
      (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).mp hencoded
    omega
  have hzeroQ : CompactPhase.zeroQValue (input I) = 0 := by
    simp [CompactPhase.zeroQValue, hlengthQInput, hlengthQNonzero]
  have hzeroRPrime : CompactPhase.zeroRPrimeValue (input I) = 0 := by
    simp [CompactPhase.zeroRPrimeValue, hlengthRPrimeInput,
      hlengthRPrimeNonzero]
  have hzeroShift : CompactPhase.zeroShiftValue (input I) =
      if shift = 0 then 1 else 0 := by
    simp only [CompactPhase.zeroShiftValue, hshiftInput]
    by_cases hzero : shift = 0
    · subst shift
      simp [encodeLength]
    · have hencoded : encodeLength 9 shift ≠ encodedZero 9 := by
        intro h
        exact hzero ((encodeLength_eq_encodedZero_iff hshiftBound).mp h)
      simp [hzero, hencoded]
  by_cases hzero : shift = 0
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hzero]
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hzero]

theorem gates_act_phaseOne_encoded
    {s : State}
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hsign : s.sign = false)
    (hlengthQPositive : 0 < s.lenQ)
    (hlengthQBound : s.lenQ < 2 ^ 9)
    (hlengthRPrimePositive : 0 < s.lenRPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hshiftBound : s.shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates (PackedState.encoded s) =
      PackedState.encoded
        { s with
          phase1 := decide (s.shift = 0)
          phase2 := decide (s.shift ≠ 0)
          sign := false } := by
  have htail : readField (PackedState.encoded s)
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by omega) (by omega)
  rw [gates_act (PackedState.read_extension s) htail]
  have hvalues := phaseOne_values
    (I := PackedState.encoded s) (lengthQ := s.lenQ)
    (lengthRPrime := s.lenRPrime) (shift := s.shift)
    (by simp [PackedState.read_phaseOne, hphaseOne, boolValue])
    (by simp [PackedState.read_phaseTwo, hphaseTwo, boolValue])
    (by simp [PackedState.read_sign, hsign, boolValue])
    (PackedState.read_lengthQ s) hlengthQPositive hlengthQBound
    (PackedState.read_lengthRPrime s) hlengthRPrimePositive
    hlengthRPrimeBound (PackedState.read_shift s) hshiftBound
  simp only [output]
  rw [hvalues.1, hvalues.2.1, hvalues.2.2]
  by_cases hzero : s.shift = 0
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s true false false)
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s false true false)

private theorem phaseZero_values {I lengthRPrime shift : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftPositive : 0 < shift)
    (hshiftBound : shift < 2 ^ 9) :
    phaseOneValue I = 0 ∧
      phaseTwoValue I = bitValue I PackedStepLayout.signWire ∧
      signValue I = 0 := by
  have hphaseOneInput :
      bitValue (input I) CompactPhase.phase1Wire = 0 :=
    (input_phaseOne I).trans hphaseOne
  have hphaseTwoInput :
      bitValue (input I) CompactPhase.phase2Wire = 0 :=
    (input_phaseTwo I).trans hphaseTwo
  have hsignInput : bitValue (input I) CompactPhase.signWire =
      bitValue I PackedStepLayout.signWire := input_sign I
  have hlengthQInput :
      readField (input I) CompactPhase.lenQOffset 9 = encodedZero 9 :=
    (input_lengthQ I).trans hlengthQ
  have hlengthRPrimeInput :
      readField (input I) CompactPhase.lenRPrimeOffset 8 =
        encodeLength 8 lengthRPrime :=
    (input_lengthRPrime I).trans hlengthRPrime
  have hshiftInput : readField (input I) CompactPhase.shiftOffset 9 =
      encodeLength 9 shift :=
    (input_shift I).trans hshift
  have hlengthRPrimeFit : lengthRPrime < 2 ^ 8 := by
    norm_num
    omega
  have hlengthRPrimeNonzero :
      encodeLength 8 lengthRPrime ≠ encodedZero 8 := by
    intro hencoded
    have hzero :=
      (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).mp hencoded
    omega
  have hshiftNonzero : encodeLength 9 shift ≠ encodedZero 9 := by
    intro hencoded
    have hzero := (encodeLength_eq_encodedZero_iff hshiftBound).mp hencoded
    omega
  have hzeroQ : CompactPhase.zeroQValue (input I) = 1 := by
    simp [CompactPhase.zeroQValue, hlengthQInput]
  have hzeroRPrime : CompactPhase.zeroRPrimeValue (input I) = 0 := by
    simp [CompactPhase.zeroRPrimeValue, hlengthRPrimeInput,
      hlengthRPrimeNonzero]
  have hzeroShift : CompactPhase.zeroShiftValue (input I) = 0 := by
    simp [CompactPhase.zeroShiftValue, hshiftInput, hshiftNonzero]
  rcases Nat.eq_zero_or_pos
      (bitValue I PackedStepLayout.signWire) with hsign | hsign
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hsign]
  · have hsign' : bitValue I PackedStepLayout.signWire = 1 := by
      have hlt := bitValue_lt I PackedStepLayout.signWire
      omega
    norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hsign']

theorem gates_act_phaseZero {I lengthRPrime shift : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftPositive : 0 < shift)
    (hshiftBound : shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates I =
      writeField
        (writeField
          (writeField I PackedStepLayout.phaseOneWire 1 0)
          PackedStepLayout.phaseTwoWire 1
          (bitValue I PackedStepLayout.signWire))
        PackedStepLayout.signWire 1 0 := by
  rw [gates_act hextension htail]
  have hvalues := phaseZero_values hphaseOne hphaseTwo hlengthQ
    hlengthRPrime hlengthRPrimePositive hlengthRPrimeBound hshift
    hshiftPositive hshiftBound
  simp only [output]
  rw [hvalues.1, hvalues.2.1, hvalues.2.2]

theorem gates_identity_terminal {I shift : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftPositive : 0 < shift)
    (hshiftBound : shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates I = I := by
  have hphaseOneInput : bitValue (input I) CompactPhase.phase1Wire = 0 :=
    (input_phaseOne I).trans hphaseOne
  have hphaseTwoInput : bitValue (input I) CompactPhase.phase2Wire = 0 :=
    (input_phaseTwo I).trans hphaseTwo
  have hsignInput : bitValue (input I) CompactPhase.signWire = 0 :=
    (input_sign I).trans hsign
  have hlengthQInput : readField (input I) CompactPhase.lenQOffset 9 =
      encodedZero 9 := (input_lengthQ I).trans hlengthQ
  have hlengthRPrimeInput :
      readField (input I) CompactPhase.lenRPrimeOffset 8 = encodedZero 8 :=
    (input_lengthRPrime I).trans hlengthRPrime
  have hshiftInput : readField (input I) CompactPhase.shiftOffset 9 =
      encodeLength 9 shift := (input_shift I).trans hshift
  have hshiftNonzero : encodeLength 9 shift ≠ encodedZero 9 := by
    intro hzero
    exact (Nat.ne_of_gt hshiftPositive)
      ((encodeLength_eq_encodedZero_iff hshiftBound).mp hzero)
  have hzeroQ : CompactPhase.zeroQValue (input I) = 1 := by
    simp [CompactPhase.zeroQValue, hlengthQInput]
  have hzeroRPrime : CompactPhase.zeroRPrimeValue (input I) = 1 := by
    simp [CompactPhase.zeroRPrimeValue, hlengthRPrimeInput]
  have hzeroShift : CompactPhase.zeroShiftValue (input I) = 0 := by
    simp [CompactPhase.zeroShiftValue, hshiftInput, hshiftNonzero]
  have hvalues : phaseOneValue I = 0 ∧ phaseTwoValue I = 0 ∧
      signValue I = 0 := by
    norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift]
  rw [gates_act hextension htail]
  simp only [output]
  rw [hvalues.1, hvalues.2.1, hvalues.2.2]
  have hwritePhaseOne : writeField I PackedStepLayout.phaseOneWire 1 0 = I := by
    apply write_of_bitValue
    simp [hphaseOne]
  have hwritePhaseTwo : writeField I PackedStepLayout.phaseTwoWire 1 0 = I := by
    apply write_of_bitValue
    simp [hphaseTwo]
  have hwriteSign : writeField I PackedStepLayout.signWire 1 0 = I := by
    apply write_of_bitValue
    simp [hsign]
  rw [hwritePhaseOne, hwritePhaseTwo, hwriteSign]

theorem phaseFour_values {I lengthRPrime shift : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftBound : shift < 2 ^ 9) :
    phaseOneValue I = (if shift = 0 then 0 else 1) ∧
      phaseTwoValue I = (if shift = 0 then 0 else 1) ∧
      signValue I = 0 := by
  have hphaseOneInput :
      bitValue (input I) CompactPhase.phase1Wire = 1 :=
    (input_phaseOne I).trans hphaseOne
  have hphaseTwoInput :
      bitValue (input I) CompactPhase.phase2Wire = 1 :=
    (input_phaseTwo I).trans hphaseTwo
  have hsignInput : bitValue (input I) CompactPhase.signWire = 1 :=
    (input_sign I).trans hsign
  have hlengthQInput :
      readField (input I) CompactPhase.lenQOffset 9 = encodedZero 9 :=
    (input_lengthQ I).trans hlengthQ
  have hlengthRPrimeInput :
      readField (input I) CompactPhase.lenRPrimeOffset 8 =
        encodeLength 8 lengthRPrime :=
    (input_lengthRPrime I).trans hlengthRPrime
  have hshiftInput : readField (input I) CompactPhase.shiftOffset 9 =
      encodeLength 9 shift :=
    (input_shift I).trans hshift
  have hlengthRPrimeFit : lengthRPrime < 2 ^ 8 := by
    norm_num
    omega
  have hlengthRPrimeNonzero :
      encodeLength 8 lengthRPrime ≠ encodedZero 8 := by
    intro hencoded
    have hzero :=
      (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).mp hencoded
    omega
  have hzeroQ : CompactPhase.zeroQValue (input I) = 1 := by
    simp [CompactPhase.zeroQValue, hlengthQInput]
  have hzeroRPrime : CompactPhase.zeroRPrimeValue (input I) = 0 := by
    simp [CompactPhase.zeroRPrimeValue, hlengthRPrimeInput,
      hlengthRPrimeNonzero]
  have hzeroShift : CompactPhase.zeroShiftValue (input I) =
      if shift = 0 then 1 else 0 := by
    simp only [CompactPhase.zeroShiftValue, hshiftInput]
    by_cases hzero : shift = 0
    · subst shift
      simp [encodeLength]
    · have hencoded : encodeLength 9 shift ≠ encodedZero 9 := by
        intro h
        exact hzero ((encodeLength_eq_encodedZero_iff hshiftBound).mp h)
      simp [hzero, hencoded]
  by_cases hshiftZero : shift = 0
  · subst shift
    norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift]
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hshiftZero]

theorem gates_act_phaseFour {I lengthRPrime shift : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftBound : shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates I =
      writeField
        (writeField
          (writeField I PackedStepLayout.phaseOneWire 1
            (if shift = 0 then 0 else 1))
          PackedStepLayout.phaseTwoWire 1
          (if shift = 0 then 0 else 1))
        PackedStepLayout.signWire 1 0 := by
  rw [gates_act hextension htail]
  have hvalues := phaseFour_values hphaseOne hphaseTwo hsign hlengthQ
    hlengthRPrime hlengthRPrimePositive hlengthRPrimeBound hshift hshiftBound
  simp only [output]
  rw [hvalues.1, hvalues.2.1, hvalues.2.2]

theorem gates_act_phaseFour_encoded
    {s : State}
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hsign : s.sign = true)
    (hlengthQ : s.lenQ = 0)
    (hlengthRPrimePositive : 0 < s.lenRPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hshiftBound : s.shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates (PackedState.encoded s) =
      PackedState.encoded
        { s with
          phase1 := decide (s.shift ≠ 0)
          phase2 := decide (s.shift ≠ 0)
          sign := false } := by
  have htail : readField (PackedState.encoded s)
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by omega) (by omega)
  rw [gates_act_phaseFour
    (I := PackedState.encoded s) (lengthRPrime := s.lenRPrime)
    (shift := s.shift) (PackedState.read_extension s) htail
    (by simp [PackedState.read_phaseOne, hphaseOne, boolValue])
    (by simp [PackedState.read_phaseTwo, hphaseTwo, boolValue])
    (by simp [PackedState.read_sign, hsign, boolValue])
    (by simp [PackedState.read_lengthQ, hlengthQ, encodeLength,
      encodedZero])
    (PackedState.read_lengthRPrime s) hlengthRPrimePositive
    hlengthRPrimeBound (PackedState.read_shift s) hshiftBound]
  by_cases hzero : s.shift = 0
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s false false false)
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s true true false)

theorem phaseTwo_values {I lengthQ lengthRPrime shift : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 lengthQ)
    (hlengthQBound : lengthQ < 2 ^ 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftPositive : 0 < shift)
    (hshiftBound : shift < 2 ^ 9) :
    phaseOneValue I = 1 ∧
      phaseTwoValue I = (if lengthQ = 0 then 1 else 0) ∧
      signValue I = (if lengthQ = 0 then 1 else 0) := by
  have hphaseOneInput :
      bitValue (input I) CompactPhase.phase1Wire = 1 :=
    (input_phaseOne I).trans hphaseOne
  have hphaseTwoInput :
      bitValue (input I) CompactPhase.phase2Wire = 0 :=
    (input_phaseTwo I).trans hphaseTwo
  have hsignInput : bitValue (input I) CompactPhase.signWire = 0 :=
    (input_sign I).trans hsign
  have hlengthQInput :
      readField (input I) CompactPhase.lenQOffset 9 =
        encodeLength 9 lengthQ :=
    (input_lengthQ I).trans hlengthQ
  have hlengthRPrimeInput :
      readField (input I) CompactPhase.lenRPrimeOffset 8 =
        encodeLength 8 lengthRPrime :=
    (input_lengthRPrime I).trans hlengthRPrime
  have hshiftInput : readField (input I) CompactPhase.shiftOffset 9 =
      encodeLength 9 shift :=
    (input_shift I).trans hshift
  have hlengthRPrimeFit : lengthRPrime < 2 ^ 8 := by omega
  have hlengthRPrimeNonzero :
      encodeLength 8 lengthRPrime ≠ encodedZero 8 := by
    intro hencoded
    have hzero :=
      (encodeLength_eq_encodedZero_iff hlengthRPrimeFit).mp hencoded
    omega
  have hzeroQ : CompactPhase.zeroQValue (input I) =
      if lengthQ = 0 then 1 else 0 := by
    simp only [CompactPhase.zeroQValue, hlengthQInput]
    by_cases hzero : lengthQ = 0
    · subst lengthQ
      simp [encodeLength]
    · have hencoded : encodeLength 9 lengthQ ≠ encodedZero 9 := by
        intro h
        exact hzero ((encodeLength_eq_encodedZero_iff hlengthQBound).mp h)
      simp [hzero, hencoded]
  have hzeroRPrime : CompactPhase.zeroRPrimeValue (input I) = 0 := by
    simp [CompactPhase.zeroRPrimeValue, hlengthRPrimeInput,
      hlengthRPrimeNonzero]
  have hzeroShift : CompactPhase.zeroShiftValue (input I) = 0 := by
    have hencoded : encodeLength 9 shift ≠ encodedZero 9 := by
      intro h
      have hzero := (encodeLength_eq_encodedZero_iff hshiftBound).mp h
      omega
    simp [CompactPhase.zeroShiftValue, hshiftInput, hencoded]
  by_cases hzero : lengthQ = 0
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hzero]
  · norm_num [phaseOneValue, phaseTwoValue, signValue,
      CompactPhase.phase1Value, CompactPhase.phase2Value,
      CompactPhase.signValue, CompactPhase.middlePhase2Value,
      CompactPhase.conditionValue, hphaseOneInput, hphaseTwoInput,
      hsignInput, hzeroQ, hzeroRPrime, hzeroShift, hzero]

theorem gates_act_phaseTwo {I lengthQ lengthRPrime shift : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 lengthQ)
    (hlengthQBound : lengthQ < 2 ^ 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 lengthRPrime)
    (hlengthRPrimePositive : 0 < lengthRPrime)
    (hlengthRPrimeBound : lengthRPrime ≤ 255)
    (hshift : readField I PackedStepLayout.shiftOffset 9 =
      encodeLength 9 shift)
    (hshiftPositive : 0 < shift)
    (hshiftBound : shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates I =
      writeField
        (writeField
          (writeField I PackedStepLayout.phaseOneWire 1 1)
          PackedStepLayout.phaseTwoWire 1
          (if lengthQ = 0 then 1 else 0))
        PackedStepLayout.signWire 1
        (if lengthQ = 0 then 1 else 0) := by
  rw [gates_act hextension htail]
  have hvalues := phaseTwo_values hphaseOne hphaseTwo hsign hlengthQ
    hlengthQBound hlengthRPrime hlengthRPrimePositive hlengthRPrimeBound
    hshift hshiftPositive hshiftBound
  simp only [output]
  rw [hvalues.1, hvalues.2.1, hvalues.2.2]

theorem gates_act_phaseTwo_encoded
    {s : State}
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false)
    (hsign : s.sign = false)
    (hlengthQBound : s.lenQ < 2 ^ 9)
    (hlengthRPrimePositive : 0 < s.lenRPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hshiftPositive : 0 < s.shift)
    (hshiftBound : s.shift < 2 ^ 9) :
    actGates PackedStepLayout.phaseGates (PackedState.encoded s) =
      PackedState.encoded
        { s with
          phase1 := true
          phase2 := decide (s.lenQ = 0)
          sign := decide (s.lenQ = 0) } := by
  have htail : readField (PackedState.encoded s)
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by omega) (by omega)
  rw [gates_act_phaseTwo
    (I := PackedState.encoded s) (lengthQ := s.lenQ)
    (lengthRPrime := s.lenRPrime) (shift := s.shift)
    (PackedState.read_extension s) htail
    (by simp [PackedState.read_phaseOne, hphaseOne, boolValue])
    (by simp [PackedState.read_phaseTwo, hphaseTwo, boolValue])
    (by simp [PackedState.read_sign, hsign, boolValue])
    (PackedState.read_lengthQ s) hlengthQBound
    (PackedState.read_lengthRPrime s) hlengthRPrimePositive
    hlengthRPrimeBound (PackedState.read_shift s) hshiftPositive hshiftBound]
  by_cases hzero : s.lenQ = 0
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s true true true)
  · simpa [hzero, boolValue] using
      (PackedState.encoded_write_phaseSign s true false false)

end PackedPhase
end Euclid
end VQ
