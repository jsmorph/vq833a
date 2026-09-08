import VQ.Euclid.SignCorrectionPlaced

namespace VQ.Euclid.TerminalCircuit

open Reversible

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  ExtractionPlaced.layout n lengthWidth shiftWidth

def gates (n lengthWidth shiftWidth : Nat) : List RGate :=
  ExtractionPlaced.gates n lengthWidth shiftWidth ++
    SignCorrectionPlaced.gates n lengthWidth shiftWidth

def circuit (n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout n lengthWidth shiftWidth).width,
    gates := gates n lengthWidth shiftWidth }

theorem read_source_encoded_terminal
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hr : s.r = 1)
    (hrelation : Relation p s)
    (hpFit : p < 2 ^ n) :
    readField (StepState.encoded n lengthWidth shiftWidth s)
      StepLayout.work1Offset n = p := by
  rcases hpacked with
    ⟨hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hwork1Allocation, _hwork2Allocation, htFit,
      _hqAligned, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have ht : s.t = p := by
    have h := hrelation
    simp [Relation, hr, hterminal.1, hterminal.2.2.1] at h
    exact h
  have htN : s.t < 2 ^ n := by
    simpa [ht] using hpFit
  have hwork : n ≤ workWidth n := by
    simp [workWidth]
  have hworkZero : 0 + n ≤ workWidth n := by omega
  rw [show StepLayout.work1Offset = 0 by rfl,
    ← readField_readField_zero
    (i := StepState.encoded n lengthWidth shiftWidth s)
    (off := 0) (len := n) (W := workWidth n) hworkZero]
  rw [show readField (StepState.encoded n lengthWidth shiftWidth s) 0
      (workWidth n) = encodeWork1 n s % 2 ^ workWidth n by
    simpa [StepLayout.work1Offset] using
      StepState.read_work1 n lengthWidth shiftWidth s]
  change readField (readField (encodeWork1 n s) 0 (workWidth n)) 0 n = p
  rw [readField_readField_zero hworkZero]
  by_cases hnarrow : n ≤ s.lenT + 1
  · calc
      readField (encodeWork1 n s) 0 n =
          readField
            (readField (encodeWork1 n s) 0 (s.lenT + 1)) 0 n :=
        (readField_readField_zero (by omega)).symm
      _ = readField s.t 0 n := by
        rw [readField_encodeWork1_coefficient htFit]
      _ = s.t := by
        rw [readField_zero, Nat.mod_eq_of_lt htN]
      _ = p := ht
  · rw [readField_encodeWork1_coefficient_padding
      hterminal.2.2.2.1 htFit (by omega)]
    · exact ht
    · rw [hr]
      have hlog : Nat.log2 1 = 0 := by decide
      simp [bitLength, workWidth, hlog]

theorem read_source_encoded_terminal_of_gcd
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : Relation p s)
    (hpFit : p < 2 ^ n) :
    readField (StepState.encoded n lengthWidth shiftWidth s)
      StepLayout.work1Offset n = p := by
  have hr : s.r = 1 := by
    have h := hgcd
    rw [hterminal.1, Nat.gcd_zero_right] at h
    exact h
  exact read_source_encoded_terminal hpacked hterminal hr hrelation hpFit

theorem decodedInverse_eq_branch
    {p : Nat} {s : State}
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p) :
    decodedInverse p s =
      if s.iter then s.tPrime else p - s.tPrime := by
  cases hiter : s.iter with
  | false =>
      simp only [decodedInverse, signedCoefficient, orientation, hiter,
        Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, neg_mul,
        one_mul]
      rw [Int.emod_eq_add_self_emod,
        Int.emod_eq_of_lt (by omega) (by omega)]
      have hdiff :
          -(s.tPrime : Int) + (p : Int) = (p - s.tPrime : Nat) := by
        omega
      rw [hdiff, Int.toNat_natCast]
  | true =>
      simp only [decodedInverse, signedCoefficient, orientation, hiter,
        ↓reduceIte, one_mul]
      rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem gates_act_encoded
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hsource :
      readField (StepState.encoded n lengthWidth shiftWidth s)
        StepLayout.work1Offset n = p)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLe : s.tPrime ≤ p)
    (hpFit : p < 2 ^ n) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (if s.iter then s.tPrime else p - s.tPrime) := by
  let input := StepState.encoded n lengthWidth shiftWidth s
  let output := ExtractionPlaced.outputOffset n lengthWidth shiftWidth
  let extracted := writeField input output n s.tPrime
  have htPrimeFit : s.tPrime < 2 ^ n := htPrimeLe.trans_lt hpFit
  have hextract := ExtractionPlaced.gates_act_encoded_terminal_of_fit
    hpacked hterminal htPrimeFit
  have hcarryEncoded :
      bitValue input (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    apply StepState.Internal.read_aux_bit
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  have haccumulatorEncoded :
      input.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) = false := by
    have hvalue :
        bitValue input
          (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
      apply StepState.Internal.read_aux_bit <;>
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    cases hbit : input.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) <;>
      simp_all [bitValue]
  have hcarryExtracted :
      bitValue extracted
        (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    rw [bitValue_write_out (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.auxWidth]
      omega))]
    exact hcarryEncoded
  have haccumulatorExtracted :
      extracted.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) = false := by
    rw [testBit_writeField_outside (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.auxWidth]
      omega))]
    exact haccumulatorEncoded
  have hsourceExtracted :
      readField extracted StepLayout.work1Offset n = p := by
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [output, ExtractionPlaced.outputOffset, ExtractionPlaced.baseWidth,
        StepLayout.work1Offset, StepLayout.layout, VQ.Euclid.layout,
        Layout.width, workWidth]
      omega))]
    exact hsource
  have htargetExtracted : readField extracted output n = s.tPrime := by
    exact readField_writeField_self htPrimeFit
  have hiterExtracted :
      bitValue extracted (StepLayout.iterWire n lengthWidth shiftWidth) =
        boolValue s.iter := by
    rw [bitValue_write_out (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.iterWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
        StepLayout.auxOffset, StepLayout.auxWidth]
      omega))]
    exact StepState.read_iter n lengthWidth shiftWidth s
  have hcorrect := SignCorrectionPlaced.gates_act
    hn hcarryExtracted haccumulatorExtracted
  rw [hsourceExtracted, htargetExtracted, hiterExtracted] at hcorrect
  have hminus :
      (p + 2 ^ n - s.tPrime) % 2 ^ n = p - s.tPrime := by
    have heq : p + 2 ^ n - s.tPrime =
        2 ^ n + (p - s.tPrime) := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  rw [gates, actGates_append]
  change actGates (ExtractionPlaced.gates n lengthWidth shiftWidth) input =
    extracted at hextract
  rw [hextract]
  cases hiter : s.iter <;>
    simp [hiter, boolValue, output, input, extracted, hminus,
      writeField_writeField] at hcorrect ⊢ <;>
    exact hcorrect

theorem gates_act_encoded_of_iter_true
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hiter : s.iter = true)
    (htPrimeFit : s.tPrime < 2 ^ n) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        s.tPrime := by
  let input := StepState.encoded n lengthWidth shiftWidth s
  let output := ExtractionPlaced.outputOffset n lengthWidth shiftWidth
  let extracted := writeField input output n s.tPrime
  have hextract := ExtractionPlaced.gates_act_encoded_terminal_of_fit
    hpacked hterminal htPrimeFit
  have hcarryEncoded :
      bitValue input (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    apply StepState.Internal.read_aux_bit
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  have haccumulatorEncoded :
      input.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) = false := by
    have hvalue :
        bitValue input
          (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
      apply StepState.Internal.read_aux_bit <;>
        simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    cases hbit : input.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) <;>
      simp_all [bitValue]
  have hcarryExtracted :
      bitValue extracted
        (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    rw [bitValue_write_out (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.auxWidth]
      omega))]
    exact hcarryEncoded
  have haccumulatorExtracted :
      extracted.testBit
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) = false := by
    rw [testBit_writeField_outside (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.auxWidth]
      omega))]
    exact haccumulatorEncoded
  have hiterExtracted :
      bitValue extracted
        (StepLayout.iterWire n lengthWidth shiftWidth) = 1 := by
    rw [bitValue_write_out (Or.inl (by
      simp [output, ExtractionPlaced.outputOffset,
        ExtractionPlaced.baseWidth, StepLayout.layout_width,
        StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.auxOffset,
        StepLayout.auxWidth]
      omega))]
    simpa [input, hiter, boolValue] using
      StepState.read_iter n lengthWidth shiftWidth s
  have hcorrect := SignCorrectionPlaced.gates_act
    hn hcarryExtracted haccumulatorExtracted
  rw [hiterExtracted] at hcorrect
  rw [gates, actGates_append]
  change actGates (ExtractionPlaced.gates n lengthWidth shiftWidth) input =
    extracted at hextract
  rw [hextract]
  simpa [extracted] using hcorrect

theorem gates_act_encoded_of_relation
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLe : s.tPrime ≤ p)
    (hpFit : p < 2 ^ n) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (if s.iter then s.tPrime else p - s.tPrime) := by
  apply gates_act_encoded hn hpacked hterminal
    (read_source_encoded_terminal_of_gcd
      hpacked hterminal hgcd hrelation hpFit)
    htPrimePos htPrimeLe hpFit

theorem gates_act_encoded_decodedInverse
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hrelation : Relation p s)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hpFit : p < 2 ^ n) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (decodedInverse p s) := by
  rw [decodedInverse_eq_branch htPrimePos htPrimeLt]
  exact gates_act_encoded_of_relation hn hpacked hterminal hgcd hrelation
    htPrimePos (Nat.le_of_lt htPrimeLt) hpFit

theorem gates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  rw [gates, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨ExtractionPlaced.gates_wellFormed n lengthWidth shiftWidth,
    SignCorrectionPlaced.gates_wellFormed n lengthWidth shiftWidth⟩

theorem circuit_wellFormed (n lengthWidth shiftWidth : Nat) :
    (circuit n lengthWidth shiftWidth).wellFormed = true :=
  gates_wellFormed n lengthWidth shiftWidth

theorem gates_length_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length ≤
      2 * (Increment.lengthCost shiftWidth + 2 +
        3 * workWidth n * shiftWidth) + n + (11 * n + 4) := by
  rw [gates, List.length_append]
  exact Nat.add_le_add
    (ExtractionPlaced.gates_length_le n lengthWidth shiftWidth)
    (SignCorrectionPlaced.gates_length_le n lengthWidth shiftWidth)

theorem gates_ccx_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
        10 * n := by
  rw [gates, List.countP_append]
  exact Nat.add_le_add
    (ExtractionPlaced.gates_ccx_le n lengthWidth shiftWidth)
    (le_of_eq (SignCorrectionPlaced.gates_ccx n lengthWidth shiftWidth))

theorem gates_cx_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n +
        (7 * n + 2) := by
  rw [gates, List.countP_append]
  exact Nat.add_le_add
    (ExtractionPlaced.gates_cx_le n lengthWidth shiftWidth)
    (SignCorrectionPlaced.gates_cx_le n lengthWidth shiftWidth)

end VQ.Euclid.TerminalCircuit
