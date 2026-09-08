import VQMathlib.Euclid.LuoWindowedOwnershipRound
import VQ.Curve.PackedAffineRetainedDivision
import VQMathlib.Curve.Laws
import VQMathlib.Curve.PackedAffineProduct
import VQMathlib.Curve.PackedAffineQuotient
import VQMathlib.Curve.PackedAffineTerminal
import VQMathlib.Curve.PackedAffineTerminalProduct

namespace VQMathlib.Curve.PackedAffineRetainedDivision

open VQ
open VQ.Algebra
open VQ.Reversible
open VQ.Semantics

private theorem xorShiftedField_eq_writeField
    (I value offset width : Nat) :
    I ^^^ (readField value 0 width <<< offset) =
      writeField I offset width
        (readField I offset width ^^^ readField value 0 width) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hin : offset ≤ q ∧ q < offset + width
  · rw [testBit_writeField_inside hin.1 hin.2, Nat.testBit_xor,
      testBit_readField, testBit_readField]
    simp [hin.1, show q - offset < width by omega,
      show offset + (q - offset) = q by omega]
  · rw [testBit_writeField_outside (by omega)]
    by_cases hlo : offset ≤ q
    · have hhi : offset + width ≤ q := by omega
      have hbit : (readField value 0 width).testBit (q - offset) = false := by
        rw [testBit_readField]
        simp [show ¬q - offset < width by omega]
      simp [hlo, hbit]
    · simp [hlo]

theorem modulusGates_act (I : Nat) :
    actGates VQ.Curve.PackedAffineRetainedDivision.modulusGates I =
      writeField I VQ.Euclid.PackedStepLayout.workOneOffset 256
        (readField I VQ.Euclid.PackedStepLayout.workOneOffset 256 ^^^
          VQ.Curve.p) := by
  rw [VQ.Curve.PackedAffineRetainedDivision.modulusGates,
    act_constantXorGates]
  rw [xorShiftedField_eq_writeField]
  have hp := VQ.Reversible.p_lt_two_pow
  rw [readField_zero, Nat.mod_eq_of_lt hp]

theorem modulusGates_clear {I : Nat}
    (hsource : readField I VQ.Euclid.PackedStepLayout.workOneOffset 256 =
      VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.modulusGates I =
      writeField I VQ.Euclid.PackedStepLayout.workOneOffset 256 0 := by
  rw [modulusGates_act, hsource, Nat.xor_self]

theorem modulusGates_load {I : Nat}
    (hsource : readField I VQ.Euclid.PackedStepLayout.workOneOffset 256 = 0) :
    actGates VQ.Curve.PackedAffineRetainedDivision.modulusGates I =
      writeField I VQ.Euclid.PackedStepLayout.workOneOffset 256 VQ.Curve.p := by
  rw [modulusGates_act, hsource, Nat.zero_xor]

theorem relocationGates_act {I quotient : Nat}
    (hsource : readField I VQ.Euclid.PackedStepLayout.workOneOffset 256 =
      quotient)
    (htarget : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates VQ.Curve.PackedAffineRetainedDivision.relocationGates I =
      writeField
        (writeField I VQ.Euclid.PackedStepLayout.workOneOffset 256 0)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient := by
  have hforward :
      VQ.Euclid.PackedStepLayout.workOneOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  have hreverse :
      VQ.Euclid.PackedStepLayout.workOneOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  have hquotient : quotient < 2 ^ 256 := by
    rw [← hsource]
    exact readField_lt I VQ.Euclid.PackedStepLayout.workOneOffset 256
  rw [VQ.Curve.PackedAffineRetainedDivision.relocationGates,
    actGates_append,
    actGates_copyField
      (s := VQ.Curve.PackedAffineLayout.inverseOffset)
      (d := VQ.Euclid.PackedStepLayout.workOneOffset)
      (len := 256) (Or.inr hreverse),
    actGates_copyField
      (s := VQ.Euclid.PackedStepLayout.workOneOffset)
      (d := VQ.Curve.PackedAffineLayout.inverseOffset)
      (len := 256) (Or.inl hforward), htarget, hsource,
    Nat.zero_xor]
  rw [readField_writeField_of_disjoint (Or.inr hreverse), hsource,
    readField_writeField_self hquotient, Nat.xor_self]
  rw [writeField_comm (Or.inr hreverse)]

theorem numeratorMoveGates_act {I numerator : Nat}
    (hsource : readField I VQ.Euclid.PackedStepLayout.workTwoOffset 256 =
      numerator)
    (htarget : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates I =
      writeField
        (writeField I VQ.Euclid.PackedStepLayout.workTwoOffset 256 0)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator := by
  have hdisjoint :
      VQ.Euclid.PackedStepLayout.workTwoOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  have hnumerator : numerator < 2 ^ 256 := by
    rw [← hsource]
    exact readField_lt I VQ.Euclid.PackedStepLayout.workTwoOffset 256
  rw [VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates,
    actGates_append,
    actGates_copyField
      (s := VQ.Curve.PackedAffineLayout.inverseOffset)
      (d := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (len := 256) (Or.inr hdisjoint),
    actGates_copyField
      (s := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (d := VQ.Curve.PackedAffineLayout.inverseOffset)
      (len := 256) (Or.inl hdisjoint), htarget, hsource,
    Nat.zero_xor]
  rw [readField_writeField_of_disjoint (Or.inr hdisjoint), hsource,
    readField_writeField_self hnumerator, Nat.xor_self]
  rw [writeField_comm (Or.inr hdisjoint)]

theorem quotientMoveGates_act {I quotient : Nat}
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 =
      quotient)
    (htarget : readField I VQ.Euclid.PackedStepLayout.workTwoOffset 256 = 0) :
    actGates VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates I =
      writeField
        (writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 0)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 quotient := by
  have hdisjoint :
      VQ.Euclid.PackedStepLayout.workTwoOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  have hquotient : quotient < 2 ^ 256 := by
    rw [← hsource]
    exact readField_lt I VQ.Curve.PackedAffineLayout.inverseOffset 256
  rw [VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates,
    actGates_append,
    actGates_copyField
      (s := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (d := VQ.Curve.PackedAffineLayout.inverseOffset)
      (len := 256) (Or.inl hdisjoint),
    actGates_copyField
      (s := VQ.Curve.PackedAffineLayout.inverseOffset)
      (d := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (len := 256) (Or.inr hdisjoint), htarget, hsource,
    Nat.zero_xor]
  rw [readField_writeField_of_disjoint (Or.inl hdisjoint), hsource,
    readField_writeField_self hquotient, Nat.xor_self]
  rw [writeField_comm (Or.inl hdisjoint)]

theorem clearMeasuredNumerator (I : Nat) :
    VQ.Lookup.MeasuredUncompute.clearBits
        VQ.Curve.PackedAffineLayout.inverseOffset 0 256 I =
      writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 0 := by
  simpa [VQ.Lookup.layout, Layout.write, Layout.offset, Layout.size] using
      VQ.Lookup.MeasuredUncompute.clearBits_zero
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 I

def readyState (E numerator : Nat) : Nat :=
  writeField
    (writeField
      (actGates VQ.Curve.PackedAffineTerminal.gates E)
      VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)
    VQ.Euclid.PackedStepLayout.workOneOffset 256 0

def quotientValue (E numerator : Nat) : Nat :=
  readField (actGates VQ.Curve.PackedAffineTerminal.gates E)
      VQ.Euclid.PackedStepLayout.workTwoOffset 256 * numerator % VQ.Curve.p

def quotientState (E numerator : Nat) : Nat :=
  writeField (readyState E numerator)
    VQ.Euclid.PackedStepLayout.workOneOffset 256
    (quotientValue E numerator)

def measuredQuotientState (E numerator : Nat) : Nat :=
  VQ.Lookup.MeasuredUncompute.clearBits
    VQ.Curve.PackedAffineLayout.inverseOffset 0 256
    (quotientState E numerator)

def finalQuotientState (E numerator : Nat) : Nat :=
  writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256
    (quotientValue E numerator)

def terminalAmplitude (level E numerator creg : Nat) :
    Algebra.Dy (deg level) :=
  Algebra.Dy.invSqrt2 (deg level) ^ 256 *
    VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
      (VQ.Lookup.BatchedUncompute.measurementMask
        VQ.Curve.PackedAffineLayout.inverseOffset
        (quotientState E numerator) 0 256 creg)

theorem terminalGates_read_source
    {p : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.gates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = p := by
  rw [VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
    hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt hpFit,
    readField_writeField_of_disjoint (Or.inr (by decide)),
    VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
      (by decide +kernel)]
  exact VQMathlib.Euclid.PackedTerminalEndpoint.terminalEncoding_source
    hpacked hterminal hgcd hrelation hpFit

theorem terminalGates_read_inverse
    {p : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.gates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 =
      VQ.Euclid.decodedInverse p s := by
  rw [VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
    hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt hpFit,
    readField_writeField_self]
  exact (VQ.Euclid.decodedInverse_lt (htPrimePos.trans htPrimeLt) s).trans
    hpFit

private theorem terminalGates_workHigh
    {p : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.gates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        (VQ.Euclid.PackedStepLayout.workTwoOffset + 256) 3 = 0 := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let P := actGates VQ.Curve.PackedAffineTerminal.preparationGates I
  have htPrimeFit : s.tPrime < 2 ^ 256 := htPrimeLt.trans hpFit
  have hworkWide : readField P
      VQ.Euclid.PackedStepLayout.workTwoOffset 259 = s.tPrime := by
    exact VQMathlib.Curve.PackedAffineTerminal.preparationGates_read_workTwo
      hterminal hshiftZero hfit
      (htPrimeFit.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
    hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt hpFit,
    readField_writeField_of_disjoint (Or.inl (by decide))]
  change readField P
    (VQ.Euclid.PackedStepLayout.workTwoOffset + 256) 3 = 0
  calc
    _ = readField
        (readField P VQ.Euclid.PackedStepLayout.workTwoOffset 259)
        256 3 := by
      symm
      exact VQ.Reversible.readField_readField (by omega)
    _ = readField s.tPrime 256 3 := by rw [hworkWide]
    _ = 0 := by
      simp [readField,
        Nat.shiftRight_eq_zero s.tPrime 256 htPrimeFit]

private theorem terminalGates_workOneHigh
    {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation VQ.Curve.p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < VQ.Curve.p) :
    readField
        (actGates VQ.Curve.PackedAffineTerminal.gates
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth))
        (VQ.Euclid.PackedStepLayout.workOneOffset + 256) 3 = 4 := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  have hr : s.r = 1 := by
    have h := hgcd
    rw [hterminal.1, Nat.gcd_zero_right] at h
    exact h
  have ht : s.t = VQ.Curve.p := by
    have h := hrelation
    simp [VQ.Euclid.Relation, hr, hterminal.1, hterminal.2.2.1] at h
    exact h
  have hlenT : s.lenT = 256 := by
    rw [hpacked.1, ht]
    decide +kernel
  have hpacked' := hpacked
  rcases hpacked' with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hworkTwoAllocation, htFit,
      _hqAligned, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hworkFit : VQ.Euclid.encodeWork1 256 s < 2 ^ 259 := by
    simpa [VQ.Euclid.workWidth] using
      VQ.Euclid.encodeWork1_lt htFit hallocation
  have hbase : readField I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 256) 3 = 4 := by
    rw [show I =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth by rfl,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide)]
    calc
      readField (VQ.Euclid.PackedState.encoded s)
          (VQ.Euclid.PackedStepLayout.workOneOffset + 256) 3 =
          readField
            (readField (VQ.Euclid.PackedState.encoded s)
              VQ.Euclid.PackedStepLayout.workOneOffset 259) 256 3 := by
        symm
        exact readField_readField (by omega)
      _ = readField (VQ.Euclid.encodeWork1 256 s) 256 3 := by
        rw [VQ.Euclid.PackedState.read_workOne,
          Nat.mod_eq_of_lt hworkFit]
      _ = 4 := by
        rw [VQ.Euclid.encodeWork1_of_lenQ_zero hterminal.2.2.2.1,
          hlenT, ht, hr]
        decide +kernel
  rw [VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
    hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
      VQ.Reversible.p_lt_two_pow,
    readField_writeField_of_disjoint (Or.inr (by decide)),
    VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
      (by decide +kernel)]
  exact hbase

private theorem terminalGates_auxiliaryBits
    {p : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    let result := actGates VQ.Curve.PackedAffineTerminal.gates
      (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
    bitValue result VQ.Euclid.PackedStepLayout.phaseOneWire = 0 ∧
      bitValue result VQ.Euclid.PackedStepLayout.phaseTwoWire = 0 ∧
      bitValue result VQ.Euclid.PackedStepLayout.signWire = 0 := by
  dsimp only
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let P := actGates VQ.Curve.PackedAffineTerminal.preparationGates I
  have hact : actGates VQ.Curve.PackedAffineTerminal.gates I =
      writeField P VQ.Euclid.PackedStepLayout.workTwoOffset 256
        (VQ.Euclid.decodedInverse p s) := by
    exact VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
      hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
        hpFit
  have hphaseOneI : bitValue I
      VQ.Euclid.PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      readField_one, VQ.Euclid.PackedState.read_phaseOne,
      hterminal.2.2.2.2.1]
    rfl
  have hphaseTwoI : bitValue I
      VQ.Euclid.PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      readField_one, VQ.Euclid.PackedState.read_phaseTwo,
      hterminal.2.2.2.2.2.1]
    rfl
  have hphaseOneP : bitValue P
      VQ.Euclid.PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one,
      VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
        (by decide +kernel),
      readField_one]
    exact hphaseOneI
  have hphaseTwoP : bitValue P
      VQ.Euclid.PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one,
      VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
        (by decide +kernel),
      readField_one]
    exact hphaseTwoI
  have hsignP : bitValue P VQ.Euclid.PackedStepLayout.signWire = 0 := by
    rw [← readField_one,
      VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
        (by decide +kernel),
      readField_one]
    exact VQMathlib.Euclid.PackedTerminalEpoch.read_sign
      hterminal.2.2.2.2.2.2
  rw [show VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth = I
      by rfl,
    hact]
  refine ⟨?_, ?_, ?_⟩
  · rw [bitValue_write_out
      (i := P) (off := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (len := 256) (v := VQ.Euclid.decodedInverse p s)
      (r := VQ.Euclid.PackedStepLayout.phaseOneWire)
      (Or.inr (by decide))]
    exact hphaseOneP
  · rw [bitValue_write_out
      (i := P) (off := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (len := 256) (v := VQ.Euclid.decodedInverse p s)
      (r := VQ.Euclid.PackedStepLayout.phaseTwoWire)
      (Or.inr (by decide))]
    exact hphaseTwoP
  · rw [bitValue_write_out
      (i := P) (off := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (len := 256) (v := VQ.Euclid.decodedInverse p s)
      (r := VQ.Euclid.PackedStepLayout.signWire)
      (Or.inr (by decide))]
    exact hsignP

theorem readyState_auxiliary_terminalEncoding
    {p numerator : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ 256) :
    VQMathlib.Curve.PackedAffineQuotient.AuxiliaryClear
      (readyState
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        numerator) := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let T := actGates VQ.Curve.PackedAffineTerminal.gates I
  have hworkHigh : readField T
      (VQ.Euclid.PackedStepLayout.workTwoOffset + 256) 3 = 0 := by
    exact terminalGates_workHigh hpacked hterminal hshiftZero hfit hgcd
      hrelation htPrimePos htPrimeLt hpFit
  have hbits :
      bitValue T VQ.Euclid.PackedStepLayout.phaseOneWire = 0 ∧
        bitValue T VQ.Euclid.PackedStepLayout.phaseTwoWire = 0 ∧
        bitValue T VQ.Euclid.PackedStepLayout.signWire = 0 := by
    exact terminalGates_auxiliaryBits hpacked hterminal hshiftZero hfit hgcd
      hrelation htPrimePos htPrimeLt hpFit
  constructor
  · simp only [readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide))]
    exact hworkHigh
  · simp only [readyState]
    rw [bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inl (by decide))]
    exact hbits.1
  · simp only [readyState]
    rw [bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inl (by decide))]
    exact hbits.2.1
  · simp only [readyState]
    rw [bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inl (by decide))]
    exact hbits.2.2

theorem readyState_terminalProductWorkspace
    {numerator : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation VQ.Curve.p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < VQ.Curve.p) :
    VQMathlib.Curve.PackedAffineTerminalProduct.EncodedWorkspace
      (readyState
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        numerator) := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let R := readyState I numerator
  have hr : s.r = 1 := by
    have h := hgcd
    rw [hterminal.1, Nat.gcd_zero_right] at h
    exact h
  have ht : s.t = VQ.Curve.p := by
    have h := hrelation
    simp [VQ.Euclid.Relation, hr, hterminal.1, hterminal.2.2.1] at h
    exact h
  have htPrimeFit : s.tPrime < 2 ^ 259 :=
    (htPrimeLt.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hpreparation :=
    VQMathlib.Curve.PackedAffineTerminal.preparationGates_workspace
      hterminal hshiftZero hfit htPrimeFit
  have haux : VQMathlib.Curve.PackedAffineQuotient.AuxiliaryClear R := by
    exact readyState_auxiliary_terminalEncoding hpacked hterminal hshiftZero
      hfit hgcd hrelation htPrimePos htPrimeLt
        VQ.Reversible.p_lt_two_pow
  have hlengthT : readField R
      VQ.Euclid.PackedStepLayout.lengthTOffset 9 = 255 := by
    simp only [R, readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
        hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
          VQ.Reversible.p_lt_two_pow,
      readField_writeField_of_disjoint (Or.inl (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
        (by decide +kernel),
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      VQ.Euclid.PackedState.read_lengthT, hpacked.1, ht]
    decide +kernel
  have hlengthQ : readField R
      VQ.Euclid.PackedStepLayout.lengthQOffset 9 = 511 := by
    simp only [R, readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
        hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
          VQ.Reversible.p_lt_two_pow,
      readField_writeField_of_disjoint (Or.inl (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.preparationGates_readField_of_outside
        (by decide +kernel),
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (by decide) (by decide) (by decide) (by decide),
      VQ.Euclid.PackedState.read_lengthQ, hterminal.2.2.2.1]
    decide +kernel
  have hlengthRPrime : readField R
      VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 = 255 := by
    simp only [R, readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
        hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
          VQ.Reversible.p_lt_two_pow,
      readField_writeField_of_disjoint (Or.inl (by decide))]
    exact hpreparation.2
  have hpool : readField R VQ.Euclid.PackedStepLayout.poolOffset 13 = 0 := by
    simp only [R, readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      VQMathlib.Curve.PackedAffineTerminal.gates_act_terminalEncoding
        hpacked hterminal hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
          VQ.Reversible.p_lt_two_pow,
      readField_writeField_of_disjoint (Or.inl (by decide))]
    exact hpreparation.1
  have htargetHigh : readField R
      (VQ.Euclid.PackedStepLayout.workOneOffset + 256) 3 = 4 := by
    simp only [R, readyState]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide))]
    exact terminalGates_workOneHigh hpacked hterminal hshiftZero hfit hgcd
      hrelation htPrimePos htPrimeLt
  refine ⟨hlengthT, hlengthQ, hlengthRPrime, ?_, hpool,
    haux.workHigh, htargetHigh⟩
  rw [show 2 = 1 + 1 by omega, readField_split]
  exact ⟨by simpa [readField_one] using haux.phaseOne,
    by simpa [readField_one,
      VQ.Euclid.PackedStepLayout.phaseOneWire,
      VQ.Euclid.PackedStepLayout.phaseTwoWire] using haux.phaseTwo⟩

theorem quotientValue_terminalEncoding
    {numerator : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation VQ.Curve.p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < VQ.Curve.p) :
    quotientValue
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        numerator =
      VQ.Euclid.decodedInverse VQ.Curve.p s * numerator % VQ.Curve.p := by
  rw [quotientValue, terminalGates_read_inverse hpacked hterminal hshiftZero
    hfit hgcd hrelation htPrimePos htPrimeLt VQ.Reversible.p_lt_two_pow]

theorem terminalProductGates_act_terminalEncoding
    {numerator : Nat} {s : VQ.Euclid.State} {depth : Nat}
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation VQ.Curve.p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates
        (readyState
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
          numerator) =
      quotientState
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        numerator := by
  let E := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  let R := readyState E numerator
  have hnumeratorFit : numerator < 2 ^ 256 :=
    hnumerator.trans VQ.Reversible.p_lt_two_pow
  have hsource : readField R
      VQ.Curve.PackedAffineTerminalProduct.sourceOffset 256 =
        VQ.Euclid.decodedInverse VQ.Curve.p s := by
    simp only [R, readyState,
      VQ.Curve.PackedAffineTerminalProduct.sourceOffset]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide))]
    exact terminalGates_read_inverse hpacked hterminal hshiftZero hfit hgcd
      hrelation htPrimePos htPrimeLt VQ.Reversible.p_lt_two_pow
  have hmultiplier : readField R
      VQ.Curve.PackedAffineTerminalProduct.multiplierOffset 256 = numerator := by
    simp only [R, readyState,
      VQ.Curve.PackedAffineTerminalProduct.multiplierOffset]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_self hnumeratorFit]
  have htarget : readField R
      VQ.Curve.PackedAffineTerminalProduct.targetOffset 256 = 0 := by
    simp only [R, readyState,
      VQ.Curve.PackedAffineTerminalProduct.targetOffset]
    exact readField_writeField_self (by norm_num)
  have hworkspace :
      VQMathlib.Curve.PackedAffineTerminalProduct.EncodedWorkspace R := by
    simpa [R, E] using readyState_terminalProductWorkspace hpacked hterminal
      hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt
  have hsourceLe : readField R
      VQ.Curve.PackedAffineTerminalProduct.sourceOffset 256 ≤ VQ.Curve.p := by
    rw [hsource]
    exact Nat.le_of_lt
      (VQ.Euclid.decodedInverse_lt (htPrimePos.trans htPrimeLt) s)
  rw [show readyState
      (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
      numerator = R by rfl,
    VQMathlib.Curve.PackedAffineTerminalProduct.terminalGates_correct
      hsourceLe htarget hworkspace,
    hmultiplier, hsource]
  simp only [quotientState]
  rw [show readyState
      (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
      numerator = R by rfl,
    quotientValue_terminalEncoding hpacked hterminal hshiftZero hfit hgcd
      hrelation htPrimePos htPrimeLt,
    Nat.mul_comm]
  rfl

theorem preQuotientGates_act {E numerator : Nat}
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.preQuotientGates
        (writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator) =
      readyState E numerator := by
  rw [VQ.Curve.PackedAffineRetainedDivision.preQuotientGates,
    actGates_append,
    actGates_write_of_outside
      VQ.Curve.PackedAffineTerminal.gates_avoids_inverse]
  have hsource' : readField
      (writeField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)
      VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p := by
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hsource]
  exact modulusGates_clear hsource'

theorem quotientState_read_multiplier (E numerator : Nat) :
    readField (readyState E numerator)
        VQ.Curve.PackedAffineQuotient.multiplierOffset 256 =
      readField (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 := by
  simp only [readyState, VQ.Curve.PackedAffineQuotient.multiplierOffset]
  rw [readField_writeField_of_disjoint
      (o₁ := VQ.Euclid.PackedStepLayout.workOneOffset) (n₁ := 256)
      (o₂ := VQ.Euclid.PackedStepLayout.workTwoOffset) (n₂ := 256)
      (Or.inl (by decide)),
    readField_writeField_of_disjoint
      (o₁ := VQ.Curve.PackedAffineLayout.inverseOffset) (n₁ := 256)
      (o₂ := VQ.Euclid.PackedStepLayout.workTwoOffset) (n₂ := 256)
      (Or.inr (by decide))]

theorem quotientState_read_multiplicand {E numerator : Nat}
    (hnumerator : numerator < 2 ^ 256) :
    readField (readyState E numerator)
      VQ.Curve.PackedAffineQuotient.multiplicandOffset 256 = numerator := by
  simp only [readyState,
    VQ.Curve.PackedAffineQuotient.multiplicandOffset]
  rw [readField_writeField_of_disjoint (Or.inl (by decide)),
    readField_writeField_self hnumerator]

theorem quotientState_read_target (E numerator : Nat) :
    readField (readyState E numerator)
        VQ.Curve.PackedAffineQuotient.targetOffset 256 = 0 := by
  exact readField_writeField_self (by norm_num)

private theorem normalizeQuotientWrites (T numerator quotient : Nat) :
    writeField
        (writeField
          (writeField
            (writeField T VQ.Curve.PackedAffineLayout.inverseOffset 256
              numerator)
            VQ.Euclid.PackedStepLayout.workOneOffset 256 0)
          VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 =
      writeField
        (writeField T VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 := by
  have hdisjoint :
      VQ.Euclid.PackedStepLayout.workOneOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  calc
    _ = writeField
        (writeField
          (writeField T VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)
          VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 := by
      rw [writeField_writeField]
    _ = writeField
        (writeField
          (writeField T VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
          VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 := by
      rw [writeField_comm (Or.inr hdisjoint)]
    _ = _ := by rw [writeField_writeField]

set_option maxRecDepth 4096 in
theorem clearQuotientState {E numerator : Nat} :
    VQ.Lookup.MeasuredUncompute.clearBits
        VQ.Curve.PackedAffineLayout.inverseOffset 0 256
        (quotientState E numerator) =
      writeField
        (writeField
          (actGates VQ.Curve.PackedAffineTerminal.gates E)
          VQ.Euclid.PackedStepLayout.workOneOffset 256
          (quotientValue E numerator))
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0 := by
  rw [clearMeasuredNumerator]
  simp only [quotientState, readyState]
  exact normalizeQuotientWrites
    (actGates VQ.Curve.PackedAffineTerminal.gates E)
    numerator (quotientValue E numerator)

theorem cleanupGates_act {E quotient : Nat}
    (hquotient : quotient < 2 ^ 256)
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.cleanupGates
        (writeField
          (writeField
            (actGates VQ.Curve.PackedAffineTerminal.gates E)
            VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
          VQ.Curve.PackedAffineLayout.inverseOffset 256 0) =
      writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient := by
  let T := actGates VQ.Curve.PackedAffineTerminal.gates E
  let M := writeField
    (writeField T VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
    VQ.Curve.PackedAffineLayout.inverseOffset 256 0
  have hdisjoint :
      VQ.Euclid.PackedStepLayout.workOneOffset + 256 ≤
        VQ.Curve.PackedAffineLayout.inverseOffset := by decide
  have hMsource :
      readField M VQ.Euclid.PackedStepLayout.workOneOffset 256 = quotient := by
    change readField
      (writeField
        (writeField T VQ.Euclid.PackedStepLayout.workOneOffset 256 quotient)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 0)
      VQ.Euclid.PackedStepLayout.workOneOffset 256 = quotient
    rw [readField_writeField_of_disjoint (Or.inr hdisjoint),
      readField_writeField_self hquotient]
  have hMtarget :
      readField M VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0 := by
    exact readField_writeField_self (by norm_num)
  rw [VQ.Curve.PackedAffineRetainedDivision.cleanupGates,
    actGates_append, actGates_append]
  change actGates VQ.Curve.PackedAffineTerminal.gates.reverse
      (actGates VQ.Curve.PackedAffineRetainedDivision.modulusGates
        (actGates VQ.Curve.PackedAffineRetainedDivision.relocationGates M)) = _
  rw [relocationGates_act hMsource hMtarget]
  have hrelocatedSource :
      readField
          (writeField
            (writeField M VQ.Euclid.PackedStepLayout.workOneOffset 256 0)
            VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient)
          VQ.Euclid.PackedStepLayout.workOneOffset 256 = 0 := by
    rw [readField_writeField_of_disjoint (Or.inr hdisjoint),
      readField_writeField_self (by norm_num)]
  rw [modulusGates_load hrelocatedSource]
  have hrestore : writeField T
      VQ.Euclid.PackedStepLayout.workOneOffset 256 VQ.Curve.p = T := by
    rw [← hsource]
    exact writeField_read T VQ.Euclid.PackedStepLayout.workOneOffset 256
  have hstate :
      writeField
          (writeField
            (writeField M VQ.Euclid.PackedStepLayout.workOneOffset 256 0)
            VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient)
          VQ.Euclid.PackedStepLayout.workOneOffset 256 VQ.Curve.p =
        writeField T VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient := by
    dsimp only [M]
    rw [writeField_comm (Or.inr hdisjoint), writeField_writeField,
      writeField_comm (Or.inr hdisjoint), writeField_writeField,
      writeField_writeField, hrestore]
  rw [hstate]
  exact VQMathlib.Curve.PackedAffineTerminal.reverseGates_act_write_inverse
    E quotient

theorem preQuotientOps_run
    {level E numerator input : Nat}
    (hl : 3 ≤ level)
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineRetainedDivision.gateOps
          VQ.Curve.PackedAffineRetainedDivision.preQuotientGates)
        (Branch.mk rec creg
          (basis (writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256
            numerator)) input) =
      [Branch.mk rec creg (basis (readyState E numerator)) input] := by
  change runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedModularProduct.gateOps
        VQ.Curve.PackedAffineRetainedDivision.preQuotientGates)
      (Branch.mk rec creg
        (basis (writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256
          numerator)) input) = _
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
    VQ.Curve.PackedAffineRetainedDivision.preQuotientGates_wellFormed,
    preQuotientGates_act hsource]

set_option maxRecDepth 4096 in
theorem cleanupOps_run
    {level E numerator input : Nat}
    (hl : 3 ≤ level)
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineRetainedDivision.gateOps
          VQ.Curve.PackedAffineRetainedDivision.cleanupGates)
        (Branch.mk rec creg
          (basis (measuredQuotientState E numerator)) input) =
      [Branch.mk rec creg
        (basis (finalQuotientState E numerator)) input] := by
  have hquotientFit : quotientValue E numerator < 2 ^ 256 := by
    exact (Nat.mod_lt _ VQ.Curve.p_pos).trans VQ.Reversible.p_lt_two_pow
  change runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedModularProduct.gateOps
        VQ.Curve.PackedAffineRetainedDivision.cleanupGates)
      (Branch.mk rec creg
        (basis (measuredQuotientState E numerator)) input) = _
  dsimp only [measuredQuotientState, finalQuotientState]
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
    VQ.Curve.PackedAffineRetainedDivision.cleanupGates_wellFormed,
    clearQuotientState, cleanupGates_act hquotientFit hsource]

theorem terminalProductOps_run
    {level E numerator input : Nat}
    (hl : 3 ≤ level)
    (hproduct :
      actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates
          (readyState E numerator) =
        quotientState E numerator)
    (rec : List Bool) (creg : Nat) :
    runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineRetainedDivision.gateOps
          VQ.Curve.PackedAffineTerminalProduct.terminalGates)
        (Branch.mk rec creg (basis (readyState E numerator)) input) =
      [Branch.mk rec creg (basis (quotientState E numerator)) input] := by
  change runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedModularProduct.gateOps
        VQ.Curve.PackedAffineTerminalProduct.terminalGates)
      (Branch.mk rec creg (basis (readyState E numerator)) input) = _
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
    VQ.Curve.PackedAffineTerminalProduct.terminalGates_wellFormed,
    hproduct]

theorem measureQuotientOps_correct
    {level E numerator : Nat}
    (hl : 3 ≤ level)
    {amplitude : Algebra.Dy (deg level)}
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude • basis (quotientState E numerator))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Lookup.BatchedReconstruction.measureOps
        VQ.Curve.PackedAffineLayout.inverseOffset 0 256) start) :
    finish.state =
      (amplitude *
        (Algebra.Dy.invSqrt2 (deg level) ^ 256 *
          VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
            (VQ.Lookup.BatchedUncompute.measurementMask
              VQ.Curve.PackedAffineLayout.inverseOffset
              (quotientState E numerator) 0 256 finish.creg))) •
        basis (measuredQuotientState E numerator) := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  have hnormalizedState :=
    VQ.Lookup.BatchedUncompute.measureOutputOps_mask
      (w := VQ.Curve.PackedAffineLayout.width)
      (addressWidth := VQ.Curve.PackedAffineLayout.inverseOffset)
      (bit := 0) (count := 256) (i := quotientState E numerator)
      hl (by decide) start.outcomes start.creg start.input normalized (by
        simpa [VQ.Lookup.BatchedReconstruction.measureOps] using hnormalized)
  have hfinishCreg : finish.creg = normalized.creg := by
    simpa [smulBranch] using congrArg
      (fun branch : Branch (deg level) => branch.creg) hfinish
  rw [hfinishCreg]
  calc
    finish.state = amplitude • normalized.state := by
      simpa [smulBranch] using congrArg
        (fun branch : Branch (deg level) => branch.state) hfinish
    _ = amplitude •
        (Algebra.Dy.invSqrt2 (deg level) ^ 256 •
          (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
            (VQ.Lookup.BatchedUncompute.measurementMask
              VQ.Curve.PackedAffineLayout.inverseOffset
              (quotientState E numerator) 0 256 normalized.creg) •
            basis (measuredQuotientState E numerator))) := by
      rw [hnormalizedState]
      rfl
    _ = _ := by simp only [Vec.smul_smul]

set_option maxRecDepth 4096 in
theorem quotientMeasureOps_correct
    {level E numerator input : Nat}
    (hl : 3 ≤ level)
    (hproduct :
      actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates
          (readyState E numerator) =
        quotientState E numerator)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRetainedDivision.gateOps
          VQ.Curve.PackedAffineTerminalProduct.terminalGates ++
        VQ.Lookup.BatchedReconstruction.measureOps
          VQ.Curve.PackedAffineLayout.inverseOffset 0 256)
      (Branch.mk rec creg (basis (readyState E numerator)) input)) :
    b.state = terminalAmplitude level E numerator b.creg •
      basis (measuredQuotientState E numerator) := by
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterQuotient, hquotient, hmeasurement⟩ := hb
  have hquotientState : afterQuotient =
      Branch.mk rec creg (basis (quotientState E numerator)) input := by
    rw [terminalProductOps_run hl hproduct rec creg,
      List.mem_singleton] at hquotient
    exact hquotient
  subst afterQuotient
  have hmeasurementState := measureQuotientOps_correct
    (E := E) (numerator := numerator)
    (amplitude := Algebra.Dy.one (deg level))
    hl (Vec.one_smul _).symm hmeasurement
  simpa only [terminalAmplitude, Algebra.Dy.one_mul] using hmeasurementState

theorem cleanupOps_smul_correct
    {level E numerator : Nat}
    (hl : 3 ≤ level)
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p)
    {amplitude : Algebra.Dy (deg level)}
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude • basis (measuredQuotientState E numerator))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRetainedDivision.gateOps
        VQ.Curve.PackedAffineRetainedDivision.cleanupGates) start) :
    finish.state = amplitude • basis (finalQuotientState E numerator) ∧
      finish.creg = start.creg := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  have hnormalizedEq : normalized =
      Branch.mk start.outcomes start.creg
        (basis (finalQuotientState E numerator)) start.input := by
    rw [cleanupOps_run hl hsource start.outcomes start.creg,
      List.mem_singleton] at hnormalized
    exact hnormalized
  constructor
  · calc
      finish.state = amplitude • normalized.state := by
        simpa [smulBranch] using congrArg
          (fun branch : Branch (deg level) => branch.state) hfinish
      _ = amplitude • basis (finalQuotientState E numerator) := by
        rw [hnormalizedEq]
  · calc
      finish.creg = normalized.creg := by
        simpa [smulBranch] using congrArg
          (fun branch : Branch (deg level) => branch.creg) hfinish
      _ = start.creg := by rw [hnormalizedEq]

theorem terminalOps_correct
    {level E numerator input : Nat}
    (hl : 3 ≤ level)
    (hsource : readField
        (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p)
    (hproduct :
      actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates
          (readyState E numerator) =
        quotientState E numerator)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.terminalOps
      (Branch.mk rec creg
        (basis (writeField E VQ.Curve.PackedAffineLayout.inverseOffset 256
          numerator)) input)) :
    b.state = terminalAmplitude level E numerator b.creg •
      basis (finalQuotientState E numerator) := by
  have hterminalOps :
      VQ.Curve.PackedAffineRetainedDivision.terminalOps =
        VQ.Curve.PackedAffineRetainedDivision.gateOps
            VQ.Curve.PackedAffineRetainedDivision.preQuotientGates ++
          ((VQ.Curve.PackedAffineRetainedDivision.gateOps
                VQ.Curve.PackedAffineTerminalProduct.terminalGates ++
              VQ.Lookup.BatchedReconstruction.measureOps
                VQ.Curve.PackedAffineLayout.inverseOffset 0 256) ++
            VQ.Curve.PackedAffineRetainedDivision.gateOps
              VQ.Curve.PackedAffineRetainedDivision.cleanupGates) := by
    simp [VQ.Curve.PackedAffineRetainedDivision.terminalOps,
      List.append_assoc]
  rw [hterminalOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterPreQuotient, hpreQuotient, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterMeasurement, hmeasurement, hcleanup⟩ := hb
  have hpreQuotientEq : afterPreQuotient =
      Branch.mk rec creg (basis (readyState E numerator)) input := by
    rw [preQuotientOps_run hl hsource rec creg,
      List.mem_singleton] at hpreQuotient
    exact hpreQuotient
  subst afterPreQuotient
  have hmeasurementState := quotientMeasureOps_correct
    hl hproduct rec creg hmeasurement
  obtain ⟨hfinalState, hcreg⟩ := cleanupOps_smul_correct
    hl hsource hmeasurementState hcleanup
  rw [hcreg]
  exact hfinalState

theorem terminalOps_correct_terminalEncoding
    {level numerator input : Nat}
    {s : VQ.Euclid.State} {depth : Nat}
    (hl : 3 ≤ level)
    (hpacked : VQ.Euclid.Packed 256 9 9 s)
    (hterminal : VQ.Euclid.Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1))
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : VQ.Euclid.Relation VQ.Curve.p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.terminalOps
      (Branch.mk rec creg
        (basis (writeField
          (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
          VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)) input)) :
    b.state = terminalAmplitude level
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        numerator b.creg •
      basis (writeField
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth)
        VQ.Curve.PackedAffineLayout.inverseOffset 256
        (VQ.Euclid.decodedInverse VQ.Curve.p s * numerator %
          VQ.Curve.p)) := by
  have hsource := terminalGates_read_source hpacked hterminal hshiftZero hfit
    hgcd hrelation htPrimePos htPrimeLt VQ.Reversible.p_lt_two_pow
  have hproduct := terminalProductGates_act_terminalEncoding hpacked hterminal
    hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt hnumerator
  have hstate := terminalOps_correct hl hsource hproduct rec creg hb
  rw [finalQuotientState, quotientValue_terminalEncoding hpacked hterminal
    hshiftZero hfit hgcd hrelation htPrimePos htPrimeLt] at hstate
  exact hstate

private theorem decodedInverse_eq_curveInv
    {denominator : Nat} {s : VQ.Euclid.State}
    (hinverse :
      denominator * VQ.Euclid.decodedInverse VQ.Curve.p s ≡
        1 [MOD VQ.Curve.p]) :
    VQ.Euclid.decodedInverse VQ.Curve.p s =
      VQ.Curve.inv denominator := by
  apply VQBridge.Curve.natCast_inj_of_lt
    (VQ.Euclid.decodedInverse_lt VQ.Curve.p_pos s)
    (VQ.Curve.inv_lt denominator)
  have hproduct :
      ((denominator : Nat) : ZMod VQ.Curve.p) *
          ((VQ.Euclid.decodedInverse VQ.Curve.p s : Nat) :
            ZMod VQ.Curve.p) = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff]
    exact hinverse
  have hinverseCast :
      ((denominator : ZMod VQ.Curve.p))⁻¹ =
        ((VQ.Euclid.decodedInverse VQ.Curve.p s : Nat) :
          ZMod VQ.Curve.p) :=
    ZMod.inv_eq_of_mul_eq_one VQ.Curve.p _ _ hproduct
  exact hinverseCast.symm.trans
    (VQBridge.Curve.cast_inv denominator).symm

theorem terminalOps_correct_preprocessed
    {level denominator numerator input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.terminalOps
      (Branch.mk rec creg
        (basis (writeField
          (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
            (VQ.Euclid.PackedState.encoded
              (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
          VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)) input)) :
    b.state = terminalAmplitude level
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        numerator b.creg •
      basis (writeField
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        VQ.Curve.PackedAffineLayout.inverseOffset 256
        (VQ.Curve.inv denominator * numerator % VQ.Curve.p)) := by
  obtain ⟨tau, _htauLower, _htauUpper, hlive, hterminal, hshift,
      hdepth, _haligned, _hcompressed, hforward⟩ :=
    VQMathlib.LuoSchedule.WindowedOwnership.preprocessed_roundsGates_act_1620
      VQBridge.Prime.prime_p (by norm_num [VQ.Curve.p]) VQ.Reversible.p_lt_two_pow (by decide +kernel)
      hdenominatorPos hdenominator
  let initial := VQ.Euclid.preprocessedState VQ.Curve.p denominator
  let final := VQ.Euclid.run 9 9 tau initial
  let depth := 1620 - tau
  have hinitial : VQ.Euclid.ReachableStepDomain VQ.Curve.p 256 9 9 initial :=
    VQ.Euclid.preprocessedState_reachable VQ.Reversible.p_lt_two_pow
      (by norm_num [VQ.Euclid.workWidth]) hdenominatorPos hdenominator
  have hreachable := VQ.Euclid.Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  have hfinalReachable :
      VQ.Euclid.ReachableStepDomain VQ.Curve.p 256 9 9 final := by
    exact hreachable tau (Nat.le_refl tau)
  have hpacked : VQ.Euclid.Packed 256 9 9 final :=
    hfinalReachable.stepDomain.valid.1
  have hrelation : VQ.Euclid.Relation VQ.Curve.p final :=
    hfinalReachable.stepDomain.relation
  have hinverseRelation :
      VQ.Euclid.InverseRelation VQ.Curve.p denominator final := by
    exact VQ.Euclid.inverseRelation_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      (VQ.Euclid.preprocessedState_inverseRelation
        hdenominatorPos hdenominator) hlive
  have hgcd : Nat.gcd final.r final.rPrime = 1 := by
    have h := VQ.Euclid.remainderGCD_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hlive
    rw [VQ.Euclid.preprocessedState_gcd_eq_one
      VQBridge.Prime.prime_p hdenominatorPos hdenominator] at h
    exact h
  have hsigned :
      (denominator : Int) * VQ.Euclid.signedCoefficient final ≡
        1 [ZMOD (VQ.Curve.p : Int)] :=
    VQ.Euclid.signedCoefficient_is_inverse hinverseRelation hgcd hterminal
  have htPrimeBounds : 0 < final.tPrime ∧ final.tPrime < VQ.Curve.p :=
    VQ.Euclid.first_terminal_tPrime_bounds hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      VQBridge.Prime.prime_p.two_le (by omega) hlive hterminal hsigned
  have hinverse :
      denominator * VQ.Euclid.decodedInverse VQ.Curve.p final ≡
        1 [MOD VQ.Curve.p] :=
    VQ.Euclid.decodedInverse_is_inverse VQ.Curve.p_pos hsigned
  have hdecoded : VQ.Euclid.decodedInverse VQ.Curve.p final =
      VQ.Curve.inv denominator :=
    decodedInverse_eq_curveInv hinverse
  have hforward' :
      actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded initial) =
        VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth := by
    simpa [initial, final, depth] using hforward
  rw [show VQ.Euclid.preprocessedState VQ.Curve.p denominator = initial
      by rfl, hforward'] at hb ⊢
  have hstate := terminalOps_correct_terminalEncoding
    hl hpacked hterminal hshift (by dsimp [depth]; omega) hgcd hrelation
      htPrimeBounds.1 htPrimeBounds.2 hnumerator
      rec creg hb
  rw [hdecoded] at hstate
  exact hstate

theorem reversalGates_act
    {denominator quotient : Nat}
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.reversalGates
        (writeField
          (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
            (VQ.Euclid.PackedState.encoded
              (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
          VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient) =
      writeField denominator VQ.Curve.PackedAffineLayout.inverseOffset 256
        quotient := by
  let rounds := VQ.Euclid.LuoWindowedOwnership.roundsGates 1620
  let prepared := VQ.Euclid.PackedState.encoded
    (VQ.Euclid.preprocessedState VQ.Curve.p denominator)
  have hroundsOutside : ∀ gate ∈ rounds.reverse, ∀ wire ∈ gate.wires,
      wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
        VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    intro gate hgate wire hwire
    simpa [rounds, VQ.Curve.PackedAffineLayout.inverseOffset] using
      VQ.Curve.PackedAffineLayout.roundsGates_avoid_inverse
        gate (List.mem_reverse.mp hgate) wire hwire
  have hpreparationOutside :
      ∀ gate ∈ (VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p).reverse,
        ∀ wire ∈ gate.wires,
          wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    intro gate hgate wire hwire
    exact VQ.Curve.PackedAffineLayout.inputPreparationGates_avoid_inverse
      VQ.Curve.p gate (List.mem_reverse.mp hgate) wire hwire
  rw [VQ.Curve.PackedAffineRetainedDivision.reversalGates,
    actGates_append, actGates_write_of_outside hroundsOutside]
  change actGates (VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p).reverse
      (writeField
        (actGates rounds.reverse (actGates rounds prepared))
        VQ.Curve.PackedAffineLayout.inverseOffset 256 quotient) = _
  rw [actGates_reverse
      (VQ.Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide : 1620 ≤ 1620))
      prepared,
    actGates_write_of_outside hpreparationOutside,
    VQ.Euclid.PackedInputPreparation.reverse_gates_act
      VQ.Reversible.p_lt_two_pow hdenominatorPos hdenominator]

def reversedState (denominator numerator : Nat) : Nat :=
  writeField denominator VQ.Curve.PackedAffineLayout.inverseOffset 256
    (VQ.Curve.inv denominator * numerator % VQ.Curve.p)

def selectedState (denominator numerator : Nat) : Nat :=
  writeField denominator VQ.Curve.PackedAffineLayout.inverseOffset 256
    numerator

def inputState (denominator numerator : Nat) : Nat :=
  writeField denominator VQ.Euclid.PackedStepLayout.workTwoOffset 256
    numerator

def outputState (denominator numerator : Nat) : Nat :=
  writeField denominator VQ.Euclid.PackedStepLayout.workTwoOffset 256
    (VQ.Curve.inv denominator * numerator % VQ.Curve.p)

def totalInputState (denominator numerator auxiliary : Nat) : Nat :=
  writeField (inputState denominator numerator)
    VQ.Curve.PackedAffineLayout.auxiliaryOffset
    VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary

def totalOutputState (denominator numerator auxiliary : Nat) : Nat :=
  writeField
    (inputState denominator
      (VQ.Curve.inv (VQ.Curve.PackedFieldInversion.selectedInput denominator) *
        numerator % VQ.Curve.p))
    VQ.Curve.PackedAffineLayout.auxiliaryOffset
    VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary

private theorem coreGates_avoid_auxiliary
    {gates : List RGate}
    (hwellFormed : gates.all
      (RGate.wellFormed VQ.Curve.PackedAffineLayout.auxiliaryOffset) = true) :
    ∀ gate ∈ gates, ∀ wire ∈ gate.wires,
      wire < VQ.Curve.PackedAffineLayout.auxiliaryOffset ∨
        VQ.Curve.PackedAffineLayout.auxiliaryOffset +
          VQ.Curve.PackedAffineLayout.auxiliaryWidth ≤ wire := by
  intro gate hgate wire hwire
  exact Or.inl (wire_lt_of_wellFormed
    (List.all_eq_true.mp hwellFormed gate hgate) hwire)

private theorem raw_readField_zero
    {value offset width : Nat}
    (hvalue : value < 2 ^ offset) :
    readField value offset width = 0 := by
  simp [readField, Nat.shiftRight_eq_zero value offset hvalue]

theorem inputState_read_numerator
    {denominator numerator : Nat}
    (hnumerator : numerator < VQ.Curve.p) :
    readField (inputState denominator numerator)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 = numerator := by
  rw [inputState, readField_writeField_self]
  exact hnumerator.trans VQ.Reversible.p_lt_two_pow

theorem inputState_read_inverse
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    readField (inputState denominator numerator)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0 := by
  rw [inputState,
    readField_writeField_of_disjoint (Or.inl (by decide))]
  apply raw_readField_zero
  exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
    (Nat.pow_le_pow_right (by omega) (by decide))

theorem numeratorMoveGates_act_input
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates
        (inputState denominator numerator) =
      writeField denominator VQ.Curve.PackedAffineLayout.inverseOffset 256
        numerator := by
  rw [numeratorMoveGates_act
      (inputState_read_numerator hnumerator)
      (inputState_read_inverse hdenominator),
    inputState, writeField_writeField]
  have hzero : readField denominator
      VQ.Euclid.PackedStepLayout.workTwoOffset 256 = 0 := by
    apply raw_readField_zero
    exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [← hzero, writeField_read]

theorem numeratorMoveGates_act_totalInput
    {denominator numerator auxiliary : Nat}
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates
        (totalInputState denominator numerator auxiliary) =
      VQ.Curve.PackedFieldInversion.invertedState
        denominator numerator auxiliary := by
  rw [totalInputState,
    actGates_write_of_outside
      (coreGates_avoid_auxiliary
        VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates_wellFormed_core),
    numeratorMoveGates_act_input hdenominator hnumerator]
  rfl

theorem forwardGates_act_input
    {denominator numerator : Nat}
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.forwardGates
        (inputState denominator numerator) =
      writeField
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator := by
  have hpreparationOutside :
      ∀ gate ∈ VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p,
        ∀ wire ∈ gate.wires,
          wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    intro gate hgate wire hwire
    exact VQ.Curve.PackedAffineLayout.inputPreparationGates_avoid_inverse
      VQ.Curve.p gate hgate wire hwire
  have hroundsOutside :
      ∀ gate ∈ VQ.Euclid.LuoWindowedOwnership.roundsGates 1620,
        ∀ wire ∈ gate.wires,
          wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    exact VQ.Curve.PackedAffineLayout.roundsGates_avoid_inverse
  rw [VQ.Curve.PackedAffineRetainedDivision.forwardGates,
    actGates_append,
    numeratorMoveGates_act_input hdenominator hnumerator,
    VQ.Curve.PackedAffineRetainedDivision.scheduleGates,
    actGates_append,
    actGates_write_of_outside hpreparationOutside,
    VQ.Euclid.PackedInputPreparation.gates_act
      VQ.Reversible.p_lt_two_pow hdenominatorPos hdenominator,
    actGates_write_of_outside hroundsOutside]

theorem scheduleGates_act_selected
    {denominator numerator : Nat}
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.scheduleGates
        (selectedState denominator numerator) =
      writeField
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator := by
  have hpreparationOutside :
      ∀ gate ∈ VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p,
        ∀ wire ∈ gate.wires,
          wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    intro gate hgate wire hwire
    exact VQ.Curve.PackedAffineLayout.inputPreparationGates_avoid_inverse
      VQ.Curve.p gate hgate wire hwire
  have hroundsOutside :
      ∀ gate ∈ VQ.Euclid.LuoWindowedOwnership.roundsGates 1620,
        ∀ wire ∈ gate.wires,
          wire < VQ.Curve.PackedAffineLayout.inverseOffset ∨
            VQ.Curve.PackedAffineLayout.inverseOffset + 256 ≤ wire := by
    exact VQ.Curve.PackedAffineLayout.roundsGates_avoid_inverse
  rw [VQ.Curve.PackedAffineRetainedDivision.scheduleGates,
    actGates_append, selectedState,
    actGates_write_of_outside hpreparationOutside,
    VQ.Euclid.PackedInputPreparation.gates_act
      VQ.Reversible.p_lt_two_pow hdenominatorPos hdenominator,
    actGates_write_of_outside hroundsOutside]

theorem reversalOps_smul_correct
    {level denominator numerator : Nat}
    {amplitude : Algebra.Dy (deg level)}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    {start finish : Branch (deg level)}
    (hstate : start.state = amplitude •
      basis (writeField
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        VQ.Curve.PackedAffineLayout.inverseOffset 256
        (VQ.Curve.inv denominator * numerator % VQ.Curve.p)))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRetainedDivision.gateOps
        VQ.Curve.PackedAffineRetainedDivision.reversalGates) start) :
    finish.state = amplitude • basis (reversedState denominator numerator) ∧
      finish.creg = start.creg := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  change normalized ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.reversalGates)
    (Branch.mk start.outcomes start.creg
      (basis (writeField
        (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
          (VQ.Euclid.PackedState.encoded
            (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
        VQ.Curve.PackedAffineLayout.inverseOffset 256
        (VQ.Curve.inv denominator * numerator % VQ.Curve.p)))
      start.input) at hnormalized
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.reversalGates_wellFormed,
    reversalGates_act hdenominatorPos hdenominator,
    List.mem_singleton] at hnormalized
  subst normalized
  constructor
  · simpa [reversedState, smulBranch] using congrArg
      (fun branch : Branch (deg level) => branch.state) hfinish
  · simpa [smulBranch] using congrArg
      (fun branch : Branch (deg level) => branch.creg) hfinish

private theorem reversedState_readField_zero
    {denominator numerator offset width : Nat}
    (hdenominator : denominator < 2 ^ 256)
    (hoffset : 256 ≤ offset)
    (hfield : offset + width ≤ VQ.Curve.PackedAffineLayout.inverseOffset) :
    readField (reversedState denominator numerator) offset width = 0 := by
  rw [reversedState,
    readField_writeField_of_disjoint (Or.inr hfield)]
  have hfit : denominator < 2 ^ offset :=
    hdenominator.trans_le
      (Nat.pow_le_pow_right (by omega) hoffset)
  simp [readField, Nat.shiftRight_eq_zero denominator offset hfit]

theorem reversedState_read_source
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    readField (reversedState denominator numerator)
        VQ.Curve.PackedAffineProduct.sourceOffset 256 = denominator := by
  rw [reversedState,
    readField_writeField_of_disjoint (Or.inr (by decide))]
  simp [VQ.Curve.PackedAffineProduct.sourceOffset, readField,
    VQ.Euclid.PackedStepLayout.workOneOffset, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (hdenominator.trans VQ.Reversible.p_lt_two_pow)]

theorem reversedState_read_multiplier
    {denominator numerator : Nat} :
    readField (reversedState denominator numerator)
        VQ.Curve.PackedAffineProduct.multiplierOffset 256 =
      VQ.Curve.inv denominator * numerator % VQ.Curve.p := by
  rw [reversedState, VQ.Curve.PackedAffineProduct.multiplierOffset,
    readField_writeField_self]
  exact (Nat.mod_lt _ VQ.Curve.p_pos).trans VQ.Reversible.p_lt_two_pow

theorem reversedState_read_target
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    readField (reversedState denominator numerator)
        VQ.Curve.PackedAffineProduct.targetOffset 256 = 0 := by
  exact reversedState_readField_zero
    (hdenominator.trans VQ.Reversible.p_lt_two_pow)
    (by decide) (by decide)

theorem quotientMoveGates_act_reversed
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates
        (reversedState denominator numerator) =
      outputState denominator numerator := by
  rw [quotientMoveGates_act reversedState_read_multiplier
      (reversedState_read_target hdenominator),
    reversedState, writeField_writeField, outputState]
  have hzero : readField denominator
      VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0 := by
    apply raw_readField_zero
    exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [← hzero, writeField_read]

theorem quotientMoveGates_act_selected
    {denominator quotient : Nat}
    (hdenominator : denominator < VQ.Curve.p)
    (hquotient : quotient < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates
        (selectedState denominator quotient) =
      inputState denominator quotient := by
  have hsource : readField (selectedState denominator quotient)
      VQ.Curve.PackedAffineLayout.inverseOffset 256 = quotient := by
    rw [selectedState, readField_writeField_self]
    exact hquotient.trans VQ.Reversible.p_lt_two_pow
  have htarget : readField (selectedState denominator quotient)
      VQ.Euclid.PackedStepLayout.workTwoOffset 256 = 0 := by
    rw [selectedState,
      readField_writeField_of_disjoint (Or.inr (by decide))]
    apply raw_readField_zero
    exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [quotientMoveGates_act hsource htarget,
    selectedState, writeField_writeField, inputState]
  have hzero : readField denominator
      VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0 := by
    apply raw_readField_zero
    exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [← hzero, writeField_read]

theorem quotientMoveGates_act_total
    {denominator quotient auxiliary : Nat}
    (hdenominator : denominator < VQ.Curve.p)
    (hquotient : quotient < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates
        (VQ.Curve.PackedFieldInversion.invertedState
          denominator quotient auxiliary) =
      writeField (inputState denominator quotient)
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary := by
  rw [VQ.Curve.PackedFieldInversion.invertedState,
    actGates_write_of_outside
      (coreGates_avoid_auxiliary
        VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates_wellFormed_core)]
  change writeField
      (actGates VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates
        (selectedState denominator quotient))
      VQ.Curve.PackedAffineLayout.auxiliaryOffset
      VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary = _
  rw [quotientMoveGates_act_selected hdenominator hquotient]

private theorem reversedState_bit_zero
    {denominator numerator wire : Nat}
    (hdenominator : denominator < VQ.Curve.p)
    (hwireLower : 256 ≤ wire)
    (hwireUpper : wire + 1 ≤ VQ.Curve.PackedAffineLayout.inverseOffset) :
    bitValue (reversedState denominator numerator) wire = 0 := by
  rw [← readField_one]
  exact reversedState_readField_zero
    (hdenominator.trans VQ.Reversible.p_lt_two_pow)
    hwireLower hwireUpper

theorem reversedState_productWorkspace
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    VQMathlib.Curve.PackedAffineProduct.WorkspaceClear
      (reversedState denominator numerator) := by
  constructor
  · exact reversedState_readField_zero
      (hdenominator.trans VQ.Reversible.p_lt_two_pow)
      (by decide) (by decide)
  · exact reversedState_bit_zero hdenominator (by decide) (by decide)
  · exact reversedState_bit_zero hdenominator (by decide) (by decide)
  · exact reversedState_bit_zero hdenominator (by decide) (by decide)
  · exact reversedState_bit_zero hdenominator (by decide) (by decide)
  · intro chunk hchunk
    exact reversedState_bit_zero hdenominator
      (by
        rw [VQ.Euclid.PackedStepLayout.phaseOneWire]
        omega)
      (by
        rw [VQ.Euclid.PackedStepLayout.phaseOneWire,
          VQ.Curve.PackedAffineLayout.inverseOffset,
          VQ.Euclid.PackedTerminalEndpoint.outputOffset,
          VQ.Euclid.PackedStepLayout.layout_width]
        omega)

theorem reversedState_productReduction
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    bitValue (reversedState denominator numerator)
        (VQ.Curve.PackedAffineProduct.targetOffset + 258) = 0 := by
  exact reversedState_bit_zero hdenominator (by decide) (by decide)

theorem reversedState_productControl
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    bitValue (reversedState denominator numerator)
        VQ.Euclid.PackedStepLayout.lengthTOffset = 0 := by
  exact reversedState_bit_zero hdenominator (by decide) (by decide)

private theorem quotientState_read_measuredNumerator
    {E numerator : Nat}
    (hnumerator : numerator < VQ.Curve.p) :
    readField (quotientState E numerator)
        VQ.Curve.PackedAffineProduct.multiplierOffset 256 = numerator := by
  rw [quotientState,
    readField_writeField_of_disjoint (Or.inl (by decide))]
  exact quotientState_read_multiplicand
    (hnumerator.trans VQ.Reversible.p_lt_two_pow)

theorem phaseRepair_reconstructs
    {E denominator numerator : Nat}
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p) :
    VQ.Lookup.BatchedReconstruction.ReconstructsWord
      VQ.Curve.PackedAffineProduct.circuit
      VQ.Curve.PackedAffineLayout.inverseOffset
      VQ.Curve.PackedAffineProduct.targetOffset 256
      (quotientState E numerator) (reversedState denominator numerator) := by
  apply VQMathlib.Curve.PackedAffineProduct.reconstructs_numerator
    (by
      rw [reversedState_read_source hdenominator]
      exact hdenominator.le)
    (reversedState_read_target hdenominator)
    (reversedState_productWorkspace hdenominator)
    (reversedState_productReduction hdenominator)
    (reversedState_productControl hdenominator)
  rw [reversedState_read_multiplier,
    reversedState_read_source hdenominator,
    quotientState_read_measuredNumerator hnumerator]
  change VQ.Curve.mul (VQ.Curve.mul (VQ.Curve.inv denominator) numerator)
      denominator = numerator
  rw [VQ.Curve.mul_comm (VQ.Curve.inv denominator) numerator]
  exact VQ.Curve.mul_inv_cancel VQBridge.Curve.inverseLaw hnumerator
    hdenominator (Nat.ne_of_gt hdenominatorPos)

theorem phaseRepairOps_cancel
    {level E denominator numerator input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
      (VQ.Lookup.BatchedUncompute.measurementMask
        VQ.Curve.PackedAffineLayout.inverseOffset
        (quotientState E numerator) 0 256 creg)
    runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.phaseRepairOps
      (Branch.mk rec creg
        (phase • basis (reversedState denominator numerator)) input) =
      [Branch.mk rec creg
        (basis (reversedState denominator numerator)) input] := by
  exact VQ.Lookup.BatchedReconstruction.repairAtOps_cancel_phase hl
    VQ.Curve.PackedAffineProduct.circuit_wellFormed (by decide)
    (phaseRepair_reconstructs hdenominatorPos hdenominator hnumerator)
    rec creg input

theorem phaseRepairOps_smul_cancel
    {level E denominator numerator : Nat}
    {amplitude : Algebra.Dy (deg level)}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude •
        (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
          (VQ.Lookup.BatchedUncompute.measurementMask
            VQ.Curve.PackedAffineLayout.inverseOffset
            (quotientState E numerator) 0 256 start.creg) •
          basis (reversedState denominator numerator)))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.phaseRepairOps start) :
    finish.state =
        amplitude • basis (reversedState denominator numerator) ∧
      finish.creg = start.creg := by
  let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
    (VQ.Lookup.BatchedUncompute.measurementMask
      VQ.Curve.PackedAffineLayout.inverseOffset
      (quotientState E numerator) 0 256 start.creg)
  let base : Branch (deg level) :=
    Branch.mk start.outcomes start.creg
      (phase • basis (reversedState denominator numerator)) start.input
  have hstart : start = smulBranch amplitude base := by
    cases start with
    | mk outcomes creg state input =>
        change state = amplitude • (phase •
          basis (reversedState denominator numerator)) at hstate
        simp only [base, smulBranch]
        rw [hstate]
  rw [hstart, (runOps_smul level VQ.Curve.PackedAffineLayout.width).2,
    List.mem_map] at hmem
  obtain ⟨normalized, hnormalized, rfl⟩ := hmem
  have hrun := phaseRepairOps_cancel
    (E := E) hl hdenominatorPos hdenominator hnumerator
    base.outcomes base.creg (input := base.input)
  rw [hrun, List.mem_singleton] at hnormalized
  subst normalized
  exact ⟨rfl, rfl⟩

def postForwardAmplitude (level : Nat) : Algebra.Dy (deg level) :=
  Algebra.Dy.invSqrt2 (deg level) ^ 256

theorem postForwardOps_correct_preprocessed
    {level denominator numerator input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.postForwardOps
      (Branch.mk rec creg
        (basis (writeField
          (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
            (VQ.Euclid.PackedState.encoded
              (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
          VQ.Curve.PackedAffineLayout.inverseOffset 256 numerator)) input)) :
    b.state = postForwardAmplitude level •
      basis (reversedState denominator numerator) := by
  rw [VQ.Curve.PackedAffineRetainedDivision.postForwardOps,
    runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterTerminal, hterminal, hrest⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hrest
  obtain ⟨afterReversal, hreversal, hrepair⟩ := hrest
  have hterminalState := terminalOps_correct_preprocessed
    hl hdenominatorPos hdenominator hnumerator rec creg hterminal
  have hreversalState := reversalOps_smul_correct
    hl hdenominatorPos hdenominator hterminalState hreversal
  have hphaseState : afterReversal.state =
      postForwardAmplitude level •
        (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
          (VQ.Lookup.BatchedUncompute.measurementMask
            VQ.Curve.PackedAffineLayout.inverseOffset
            (quotientState
              (actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
                (VQ.Euclid.PackedState.encoded
                  (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
              numerator) 0 256 afterReversal.creg) •
          basis (reversedState denominator numerator)) := by
    rw [hreversalState.1, ← hreversalState.2]
    simp only [terminalAmplitude, postForwardAmplitude, Vec.smul_smul]
  exact (phaseRepairOps_smul_cancel
    (E := actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
      (VQ.Euclid.PackedState.encoded
        (VQ.Euclid.preprocessedState VQ.Curve.p denominator)))
    hl hdenominatorPos hdenominator hnumerator hphaseState hrepair).1

theorem selectedDivisionOps_correct
    {level denominator numerator input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps
      (Branch.mk rec creg
        (basis (selectedState denominator numerator)) input)) :
    b.state = postForwardAmplitude level •
      basis (reversedState denominator numerator) := by
  rw [VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps,
    runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterSchedule, hschedule, hpost⟩ := hb
  change afterSchedule ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.scheduleGates)
    (Branch.mk rec creg
      (basis (selectedState denominator numerator)) input) at hschedule
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.scheduleGates_wellFormed,
    scheduleGates_act_selected hdenominatorPos hdenominator,
    List.mem_singleton] at hschedule
  subst afterSchedule
  exact postForwardOps_correct_preprocessed
    hl hdenominatorPos hdenominator hnumerator rec creg hpost

private theorem selectedState_lt
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    selectedState denominator numerator <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryOffset := by
  apply writeField_lt
  · decide
  · exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))

private theorem reversedState_lt
    {denominator numerator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    reversedState denominator numerator <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryOffset := by
  apply writeField_lt
  · decide
  · exact (hdenominator.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))

theorem sourceIndex_invertedState
    {denominator numerator auxiliary : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    sourceIndex id VQ.Curve.PackedAffineLayout.auxiliaryOffset
        (VQ.Curve.PackedFieldInversion.invertedState
          denominator numerator auxiliary) =
      selectedState denominator numerator := by
  rw [sourceIndex_id_eq_readField,
    VQ.Curve.PackedFieldInversion.invertedState,
    readField_writeField_of_disjoint (Or.inr (by decide))]
  change readField (selectedState denominator numerator) 0
      VQ.Curve.PackedAffineLayout.auxiliaryOffset =
    selectedState denominator numerator
  simp [readField, Nat.mod_eq_of_lt (selectedState_lt hdenominator)]

theorem replaceBits_reversedState
    {denominator numerator auxiliary : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    replaceBits id VQ.Curve.PackedAffineLayout.auxiliaryOffset
        (reversedState denominator numerator)
        (VQ.Curve.PackedFieldInversion.invertedState
          denominator numerator auxiliary) =
      VQ.Curve.PackedFieldInversion.invertedState denominator
        (VQ.Curve.inv denominator * numerator % VQ.Curve.p) auxiliary := by
  rw [replaceBits_id_eq_writeField]
  change writeField
      (writeField (selectedState denominator numerator)
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary)
      0 VQ.Curve.PackedAffineLayout.auxiliaryOffset
        (reversedState denominator numerator) =
    writeField (reversedState denominator numerator)
      VQ.Curve.PackedAffineLayout.auxiliaryOffset
      VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary
  rw [writeField_comm (Or.inr (by decide)),
    writeField_zero_eq (selectedState_lt hdenominator)
      (reversedState_lt hdenominator)]

theorem selectedDivisionOps_correct_auxiliary
    {level denominator numerator auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps
      (Branch.mk rec creg
        (basis (VQ.Curve.PackedFieldInversion.invertedState
          denominator numerator auxiliary)) input)) :
    b.state = postForwardAmplitude level •
      basis (VQ.Curve.PackedFieldInversion.invertedState denominator
        (VQ.Curve.inv denominator * numerator % VQ.Curve.p) auxiliary) := by
  let coreWidth := VQ.Curve.PackedAffineLayout.auxiliaryOffset
  let localOriginal := selectedState denominator numerator
  let fullOriginal := VQ.Curve.PackedFieldInversion.invertedState
    denominator numerator auxiliary
  have hlocalFit : localOriginal < 2 ^ coreWidth := by
    exact selectedState_lt hdenominator
  have hsource : sourceIndex id coreWidth fullOriginal = localOriginal := by
    exact sourceIndex_invertedState hdenominator
  have hinj : ∀ x y, x < coreWidth → y < coreWidth → id x = id y → x = y := by
    intro x y _ _ hxy
    exact hxy
  have hlt : ∀ q, q < coreWidth → id q <
      VQ.Curve.PackedAffineLayout.width := by
    intro q hq
    exact hq.trans (by decide)
  have hrun := runOps_relabel
    (level := level) (width := coreWidth)
    (totalWidth := VQ.Curve.PackedAffineLayout.width)
    (inputBits := 0) (cbits := 256) (f := id) (ambient := fullOriginal)
    (ops := VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps)
    (b := Branch.mk rec creg (basis localOriginal) input)
    hlt hinj
    (VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps_wellFormed_core
      hl)
    (wfVec_basis hlocalFit)
  simp only [Op.relabelAll_id] at hrun
  have hstart : placeBranch id coreWidth fullOriginal
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis fullOriginal) input := by
    rw [← hsource]
    exact placeBranch_sourceIndex_basis hinj rec creg input
  rw [hstart] at hrun
  change b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps
      (Branch.mk rec creg (basis fullOriginal) input) at hb
  rw [hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := hb
  have hrunZero := runOps_relabel
    (level := level) (width := coreWidth)
    (totalWidth := VQ.Curve.PackedAffineLayout.width)
    (inputBits := 0) (cbits := 256) (f := id) (ambient := 0)
    (ops := VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps)
    (b := Branch.mk rec creg (basis localOriginal) input)
    hlt hinj
    (VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps_wellFormed_core
      hl)
    (wfVec_basis hlocalFit)
  simp only [Op.relabelAll_id] at hrunZero
  have hstartZero : placeBranch id coreWidth 0
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis localOriginal) input := by
    simp only [placeBranch]
    rw [placeVec_id_zero (wfVec_basis hlocalFit)]
  rw [hstartZero] at hrunZero
  have hplacedMember : placeBranch id coreWidth 0 localBranch ∈
      runOps level VQ.Curve.PackedAffineLayout.width
        VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps
        (Branch.mk rec creg (basis localOriginal) input) := by
    rw [hrunZero]
    exact List.mem_map.mpr ⟨localBranch, hlocalBranch, rfl⟩
  have hplacedState := selectedDivisionOps_correct hl hdenominatorPos
    hdenominator hnumerator rec creg hplacedMember
  have hlocalWF : WFVec (2 ^ coreWidth) localBranch.state :=
    wfVec_runOps level coreWidth
      VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps
      (wfVec_basis hlocalFit) hlocalBranch
  have hlocalState : localBranch.state = postForwardAmplitude level •
      basis (reversedState denominator numerator) := by
    have hplaceState : (placeBranch id coreWidth 0 localBranch).state =
        localBranch.state := by
      rw [placeBranch_state,
        placeVec_id_zero (width := coreWidth) hlocalWF]
    rw [hplaceState] at hplacedState
    exact hplacedState
  calc
    (placeBranch id coreWidth fullOriginal localBranch).state =
        placeVec id coreWidth fullOriginal localBranch.state :=
      placeBranch_state id coreWidth fullOriginal localBranch
    _ = placeVec id coreWidth fullOriginal
        (postForwardAmplitude level •
          basis (reversedState denominator numerator)) := by
      rw [hlocalState]
    _ = postForwardAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState denominator
          (VQ.Curve.inv denominator * numerator % VQ.Curve.p)
          auxiliary) := by
      rw [placeVec_smul,
        placeVec_basis (reversedState_lt hdenominator),
        replaceBits_reversedState hdenominator]

private theorem selectedInput_pos (denominator : Nat) :
    0 < VQ.Curve.PackedFieldInversion.selectedInput denominator := by
  by_cases h : denominator = 0
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h]
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h,
      Nat.pos_of_ne_zero h]

private theorem selectedInput_lt
    {denominator : Nat}
    (hdenominator : denominator < VQ.Curve.p) :
    VQ.Curve.PackedFieldInversion.selectedInput denominator < VQ.Curve.p := by
  by_cases h : denominator = 0
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h]
    decide +kernel
  · simpa [VQ.Curve.PackedFieldInversion.selectedInput, h] using hdenominator

theorem totalDivisionOps_correct
    {level denominator numerator auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps
      (Branch.mk rec creg
        (basis (totalInputState denominator numerator auxiliary)) input)) :
    b.state = postForwardAmplitude level •
      basis (totalOutputState denominator numerator auxiliary) := by
  rw [VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps] at hb
  simp only [List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterMove, hmove, hrest⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hrest
  obtain ⟨afterPrepare, hprepare, hrest⟩ := hrest
  rw [runOps_append, List.mem_flatMap] at hrest
  obtain ⟨afterSelected, hselected, hrest⟩ := hrest
  rw [runOps_append, List.mem_flatMap] at hrest
  obtain ⟨afterRestore, hrestore, hquotient⟩ := hrest
  change afterMove ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates)
    (Branch.mk rec creg
      (basis (totalInputState denominator numerator auxiliary)) input) at hmove
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates_wellFormed,
    numeratorMoveGates_act_totalInput hdenominator hnumerator,
    List.mem_singleton] at hmove
  subst afterMove
  change afterPrepare ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedFieldInversion.prepareGates)
    (Branch.mk rec creg
      (basis (VQ.Curve.PackedFieldInversion.invertedState
        denominator numerator auxiliary)) input) at hprepare
  have hdenominatorWidth : denominator <
      2 ^ VQ.Curve.PackedFieldInversion.sourceWidth := by
    simpa [VQ.Curve.PackedFieldInversion.sourceWidth] using
      hdenominator.trans VQ.Reversible.p_lt_two_pow
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedFieldInversion.prepareGates_wellFormed,
    VQ.Curve.PackedFieldInversion.prepareGates_act_inverted
      hdenominatorWidth hauxiliary hzeroFactor,
    List.mem_singleton] at hprepare
  subst afterPrepare
  let selected := VQ.Curve.PackedFieldInversion.selectedInput denominator
  let tagged := VQ.Curve.PackedFieldInversion.taggedAuxiliary
    denominator auxiliary
  let quotient := VQ.Curve.inv selected * numerator % VQ.Curve.p
  have hselectedPos : 0 < selected := selectedInput_pos denominator
  have hselectedLt : selected < VQ.Curve.p :=
    selectedInput_lt hdenominator
  have hselectedState : afterSelected.state =
      postForwardAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState
          selected quotient tagged) := by
    exact selectedDivisionOps_correct_auxiliary hl hselectedPos hselectedLt
      hnumerator rec creg hselected
  have hrestoreState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedFieldInversion.restoreGates_wellFormed
      hselectedState hrestore
  have hrestoreState' : afterRestore.state =
      postForwardAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState
          denominator quotient auxiliary) := by
    rw [VQ.Curve.PackedFieldInversion.restoreGates_act
      hdenominatorWidth hauxiliary hzeroFactor] at hrestoreState
    exact hrestoreState
  have hquotientLt : quotient < VQ.Curve.p := by
    exact Nat.mod_lt _ VQ.Curve.p_pos
  have houtputState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates_wellFormed
      hrestoreState' hquotient
  rw [quotientMoveGates_act_total hdenominator hquotientLt] at houtputState
  simpa [totalOutputState, selected, quotient] using houtputState

theorem positiveDivisionOps_correct
    {level denominator numerator input : Nat}
    (hl : 3 ≤ level)
    (hdenominatorPos : 0 < denominator)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.positiveDivisionOps
      (Branch.mk rec creg
        (basis (inputState denominator numerator)) input)) :
    b.state = postForwardAmplitude level •
      basis (outputState denominator numerator) := by
  rw [VQ.Curve.PackedAffineRetainedDivision.positiveDivisionOps,
    runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterPost, hprefix, houtput⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hprefix
  obtain ⟨afterForward, hforward, hpost⟩ := hprefix
  change afterForward ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.forwardGates)
    (Branch.mk rec creg (basis (inputState denominator numerator)) input)
      at hforward
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.forwardGates_wellFormed,
    forwardGates_act_input hdenominatorPos hdenominator hnumerator,
    List.mem_singleton] at hforward
  subst afterForward
  have hpostState := postForwardOps_correct_preprocessed
    hl hdenominatorPos hdenominator hnumerator rec creg hpost
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hpostState houtput
  change normalized ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates)
    (Branch.mk afterPost.outcomes afterPost.creg
      (basis (reversedState denominator numerator)) afterPost.input) at hnormalized
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates_wellFormed,
    quotientMoveGates_act_reversed hdenominator,
    List.mem_singleton] at hnormalized
  subst normalized
  simpa [smulBranch] using congrArg
    (fun branch : Branch (deg level) => branch.state) hfinish

end VQMathlib.Curve.PackedAffineRetainedDivision
