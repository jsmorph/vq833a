import VQ.Euclid.LengthWriter
import VQ.Euclid.TerminalPadding
import VQMathlib.Euclid.LuoAntinorm

namespace VQMathlib.Euclid.LuoActiveWindows

open VQ
open VQ.Euclid
open VQ.Reversible

def workWidth (n : Nat) : Nat := n + 3

def coefficientWriterUpper (n T : Nat) : Nat :=
  min (T / 4 + 3) (n + 2)

def remainderWriterUpper (n : Nat) : Nat := workWidth n

def logicalRemainderRight (n remainderLength : Nat) : Nat :=
  workWidth n + 1 - remainderLength

def physicalRemainderRight (n remainderLength : Nat) : Nat :=
  min (workWidth n) (logicalRemainderRight n remainderLength)

theorem logicalRemainderRight_zero (n : Nat) :
    logicalRemainderRight n 0 = workWidth n + 1 := by
  simp [logicalRemainderRight]

theorem logicalRemainderRight_zero_exceeds_register (n : Nat) :
    workWidth n < logicalRemainderRight n 0 := by
  simp [logicalRemainderRight]

theorem physicalRemainderRight_zero (n : Nat) :
    physicalRemainderRight n 0 = workWidth n := by
  simp [physicalRemainderRight, logicalRemainderRight]

theorem physicalRemainderRight_le_register (n remainderLength : Nat) :
    physicalRemainderRight n remainderLength ≤ remainderWriterUpper n := by
  simp [physicalRemainderRight, remainderWriterUpper]

theorem coefficientWriterRight_le
    {n T remainderLength : Nat}
    (hremainderPositive : 0 < remainderLength)
    (hremainderFit : remainderLength ≤ n)
    (hgrowth : n - remainderLength ≤ T / 4) :
    workWidth n - remainderLength ≤ coefficientWriterUpper n T := by
  simp only [workWidth, coefficientWriterUpper, Nat.le_min]
  constructor <;> omega

theorem coefficientWriterInterval_contained
    {n T lower coefficientLength remainderLength : Nat}
    (hlower : lower ≤ coefficientLength)
    (hremainderPositive : 0 < remainderLength)
    (hremainderFit : remainderLength ≤ n)
    (hgrowth : n - remainderLength ≤ T / 4) :
    lower ≤ coefficientLength ∧
      workWidth n - remainderLength ≤ coefficientWriterUpper n T := by
  exact ⟨hlower,
    coefficientWriterRight_le hremainderPositive hremainderFit hgrowth⟩

theorem remainderWriterInterval_nonempty
    {n coefficientLength remainderLength : Nat}
    (hcoefficientFit : coefficientLength ≤ n)
    (hliveFit : remainderLength = 0 ∨
      coefficientLength + remainderLength ≤ n + 1) :
    coefficientLength + 2 ≤ physicalRemainderRight n remainderLength := by
  by_cases hremainderZero : remainderLength = 0
  · subst remainderLength
    simp [physicalRemainderRight_zero, workWidth]
    omega
  · have hliveFit' : coefficientLength + remainderLength ≤ n + 1 :=
      hliveFit.resolve_left hremainderZero
    have hremainderPositive : 0 < remainderLength := Nat.pos_of_ne_zero hremainderZero
    have hlogical :
        coefficientLength + 2 ≤ logicalRemainderRight n remainderLength := by
      simp only [logicalRemainderRight, workWidth]
      apply Nat.le_sub_of_add_le
      omega
    rw [physicalRemainderRight, Nat.min_eq_right]
    · exact hlogical
    · simp only [logicalRemainderRight, workWidth]
      omega

theorem remainderWriterInterval_contained
    {n lower coefficientLength remainderLength : Nat}
    (hlower : lower ≤ coefficientLength + 2)
    (hcoefficientFit : coefficientLength ≤ n)
    (hliveFit : remainderLength = 0 ∨
      coefficientLength + remainderLength ≤ n + 1) :
    lower ≤ coefficientLength + 2 ∧
      coefficientLength + 2 ≤ physicalRemainderRight n remainderLength ∧
      physicalRemainderRight n remainderLength ≤ remainderWriterUpper n := by
  exact ⟨hlower,
    remainderWriterInterval_nonempty hcoefficientFit hliveFit,
    physicalRemainderRight_le_register n remainderLength⟩

theorem lowerGates_act_capped_zero
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary)
    (hupper : boundary ≤ start + count)
    (hstable : Interval.Stable boundary right (count + 1) endpointWidth I)
    (haccumulator : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → bitValue I j = 0) :
    actGates (LengthWriter.lowerGates n start (count + 1) endpointWidth) I =
      I ^^^ (encodedZero endpointWidth <<<
        LengthWriter.targetOffset (count + 1) endpointWidth) := by
  apply LengthWriter.lowerGates_act_none hwidth hlower hupper hstable
    haccumulator
  intro j hj _hboundary
  exact hzero j hj

theorem lowerGates_act_capped_zero_of_clear_target
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary)
    (hupper : boundary ≤ start + count)
    (hstable : Interval.Stable boundary right (count + 1) endpointWidth I)
    (haccumulator : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → bitValue I j = 0)
    (htarget : readField I
      (LengthWriter.targetOffset (count + 1) endpointWidth) endpointWidth = 0) :
    actGates (LengthWriter.lowerGates n start (count + 1) endpointWidth) I =
      writeField I (LengthWriter.targetOffset (count + 1) endpointWidth)
        endpointWidth (encodedZero endpointWidth) := by
  rw [lowerGates_act_capped_zero hwidth hlower hupper hstable
    haccumulator hzero]
  symm
  simpa [htarget, readField_zero,
    Nat.mod_eq_of_lt (encodedZero_lt endpointWidth)] using
    (writeField_xor_value I (encodedZero endpointWidth)
      (LengthWriter.targetOffset (count + 1) endpointWidth) endpointWidth)

def terminalEncoded (shiftWidth depth : Nat) : Nat :=
  encodeLength (shiftWidth + 1) depth

def terminalLow (shiftWidth depth : Nat) : Nat :=
  readField (terminalEncoded shiftWidth depth) 0 shiftWidth

def terminalEpoch (shiftWidth depth : Nat) : Nat :=
  if bitValue (terminalEncoded shiftWidth depth) shiftWidth = 1 then 0 else 1

def terminalZeroSelected (shiftWidth depth : Nat) : Prop :=
  terminalLow shiftWidth depth = encodedZero shiftWidth ∧
    terminalEpoch shiftWidth depth = 0

theorem terminalLow_succ
    {shiftWidth depth : Nat} (hfit : depth + 1 < 2 ^ (shiftWidth + 1)) :
    (terminalLow shiftWidth depth + 1) % 2 ^ shiftWidth =
      terminalLow shiftWidth (depth + 1) := by
  have hsucc := encodeLength_succ hfit
  have hdvd : 2 ^ shiftWidth ∣ 2 ^ (shiftWidth + 1) := by
    exact Nat.pow_dvd_pow 2 (by omega)
  simp only [terminalLow, terminalEncoded, readField_zero]
  rw [← hsucc, Nat.mod_mod_of_dvd _ hdvd]
  simp [Nat.add_mod]

theorem bitValue_increment
    {width value : Nat} (hvalue : value < 2 ^ (width + 1)) :
    bitValue ((value + 1) % 2 ^ (width + 1)) width =
      (bitValue value width +
        if (readField value 0 width + 1) % 2 ^ width = 0 then 1 else 0) % 2 := by
  have hfull := readField_high value 0 width
  simp only [Nat.zero_add, readField_zero,
    Nat.mod_eq_of_lt hvalue] at hfull
  have hlowlt := readField_lt value 0 width
  have hhighlt := bitValue_lt value width
  have hp : 0 < 2 ^ width := Nat.two_pow_pos width
  have hpow : 2 ^ (width + 1) = 2 ^ width * 2 := by
    rw [Nat.pow_succ]
  by_cases hlast : readField value 0 width = 2 ^ width - 1
  · have hlowIncrement :
        (readField value 0 width + 1) % 2 ^ width = 0 := by
      rw [hlast, Nat.sub_add_cancel (by omega), Nat.mod_self]
    have hlast' : value % 2 ^ width = 2 ^ width - 1 := by
      simpa [readField_zero] using hlast
    rw [hlowIncrement, if_pos rfl]
    rcases (show bitValue value width = 0 ∨ bitValue value width = 1 by omega) with
      hhigh | hhigh
    · have hvalueEq : value = 2 ^ width - 1 := by
        rw [hlast', hhigh, Nat.mul_zero, Nat.add_zero] at hfull
        exact hfull
      have hnext : (value + 1) % 2 ^ (width + 1) = 2 ^ width := by
        rw [hvalueEq, Nat.sub_add_cancel (by omega), hpow,
          Nat.mod_eq_of_lt (by omega)]
      rw [hnext, hhigh]
      simp [bitValue_shift, Nat.shiftRight_eq_div_pow, hp]
    · have hvalueEq : value + 1 = 2 ^ (width + 1) := by
        rw [hfull, hlast', hhigh, hpow]
        omega
      rw [hvalueEq, Nat.mod_self, hhigh]
      simp [bitValue]
  · have hlowBound : readField value 0 width + 1 < 2 ^ width := by
      have hpred : 2 ^ width - 1 + 1 = 2 ^ width :=
        Nat.sub_add_cancel (by omega)
      omega
    have hlowBound' : value % 2 ^ width + 1 < 2 ^ width := by
      simpa [readField_zero] using hlowBound
    have htotal : value + 1 < 2 ^ (width + 1) := by
      rcases (show bitValue value width = 0 ∨ bitValue value width = 1 by omega) with
        hhigh | hhigh
      · rw [hfull, hhigh, Nat.mul_zero, Nat.add_zero, hpow]
        omega
      · rw [hfull, hhigh, Nat.mul_one, hpow]
        omega
    rw [Nat.mod_eq_of_lt htotal, Nat.mod_eq_of_lt hlowBound,
      if_neg (by omega)]
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hhighlt]
    have hnextDiv : (value + 1) / 2 ^ width = bitValue value width := by
      rw [show value + 1 =
            (value % 2 ^ width + 1) + 2 ^ width * bitValue value width by
          omega,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlowBound', Nat.zero_add]
    have hvalueDiv : value / 2 ^ width = bitValue value width := by
      calc
        value / 2 ^ width =
            (value % 2 ^ width + 2 ^ width * bitValue value width) /
              2 ^ width := congrArg (fun x => x / 2 ^ width) hfull
        _ = bitValue value width := by
          rw [Nat.add_mul_div_left _ _ hp,
            Nat.div_eq_of_lt (by simpa [readField_zero] using hlowlt),
            Nat.zero_add]
    rw [bitValue_shift, bitValue_shift]
    simp only [Nat.shiftRight_eq_div_pow]
    rw [hnextDiv, hvalueDiv]

theorem terminalEpoch_succ
    {shiftWidth depth : Nat} (hfit : depth + 1 < 2 ^ (shiftWidth + 1)) :
    (terminalEpoch shiftWidth depth +
      if terminalLow shiftWidth (depth + 1) = 0 then 1 else 0) % 2 =
        terminalEpoch shiftWidth (depth + 1) := by
  have hbit := bitValue_increment
    (width := shiftWidth) (value := terminalEncoded shiftWidth depth)
    (encodeLength_lt (shiftWidth + 1) depth)
  have hencodedSucc :
      (terminalEncoded shiftWidth depth + 1) % 2 ^ (shiftWidth + 1) =
        terminalEncoded shiftWidth (depth + 1) := by
    simpa [terminalEncoded] using encodeLength_succ hfit
  have hlowSucc := terminalLow_succ hfit
  change bitValue
      ((terminalEncoded shiftWidth depth + 1) % 2 ^ (shiftWidth + 1))
        shiftWidth =
      (bitValue (terminalEncoded shiftWidth depth) shiftWidth +
        if (terminalLow shiftWidth depth + 1) % 2 ^ shiftWidth = 0 then
          1 else 0) % 2 at hbit
  rw [hencodedSucc, hlowSucc] at hbit
  have holdlt := bitValue_lt (terminalEncoded shiftWidth depth) shiftWidth
  rcases (show bitValue (terminalEncoded shiftWidth depth) shiftWidth = 0 ∨
      bitValue (terminalEncoded shiftWidth depth) shiftWidth = 1 by omega) with
    hold | hold
  · by_cases hwrap : terminalLow shiftWidth (depth + 1) = 0 <;>
      simp [terminalEpoch, hold, hwrap] at hbit ⊢ <;> omega
  · by_cases hwrap : terminalLow shiftWidth (depth + 1) = 0 <;>
      simp [terminalEpoch, hold, hwrap] at hbit ⊢ <;> omega

theorem terminalGates_act_succ
    {shiftWidth depth i : Nat}
    (hshift : 0 < shiftWidth)
    (hfit : depth + 1 < 2 ^ (shiftWidth + 1))
    (hlow : readField i (VQ.Euclid.TerminalEpoch.lowOffset) shiftWidth =
      terminalLow shiftWidth depth)
    (hcontrol : bitValue i
      (VQ.Euclid.TerminalEpoch.controlWire shiftWidth) = 1)
    (hscratch : readField i
      (VQ.Euclid.TerminalEpoch.scratchOffset shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i
      (VQ.Euclid.TerminalEpoch.wrappedWire shiftWidth) = 0)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalEpoch.epochWire shiftWidth) =
        terminalEpoch shiftWidth depth) :
    actGates (VQ.Euclid.TerminalEpoch.gates shiftWidth) i =
      writeField
        (writeField
          (writeField i VQ.Euclid.TerminalEpoch.lowOffset shiftWidth
            (terminalLow shiftWidth (depth + 1)))
          (VQ.Euclid.TerminalEpoch.wrappedWire shiftWidth) 1 0)
        (VQ.Euclid.TerminalEpoch.epochWire shiftWidth) 1
          (terminalEpoch shiftWidth (depth + 1)) := by
  rw [VQ.Euclid.TerminalEpoch.gates_act hshift hscratch hwrapped]
  simp only [VQ.Euclid.TerminalEpoch.out,
    VQ.Euclid.TerminalEpoch.nextLow,
    VQ.Euclid.TerminalEpoch.nextEpoch,
    VQ.Euclid.TerminalEpoch.wrapped, hlow, hcontrol, Nat.one_mul]
  rw [terminalLow_succ hfit, hepoch, terminalEpoch_succ hfit]

theorem terminalPaddingGates_act_succ
    {workWidth shiftWidth depth i : Nat}
    (hshift : 0 < shiftWidth)
    (hfit : depth + 1 < 2 ^ (shiftWidth + 1))
    (hlow : readField i (VQ.Euclid.TerminalPadding.lowOffset workWidth)
      shiftWidth = terminalLow shiftWidth depth)
    (hcontrol : bitValue i
      (VQ.Euclid.TerminalPadding.controlWire workWidth shiftWidth) = 1)
    (hscratch : readField i
      (VQ.Euclid.TerminalPadding.scratchOffset workWidth shiftWidth)
        shiftWidth = 0)
    (hwrapped : bitValue i
      (VQ.Euclid.TerminalPadding.wrappedWire workWidth shiftWidth) = 0)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalPadding.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth) :
    actGates (VQ.Euclid.TerminalPadding.gates workWidth shiftWidth) i =
      writeField
        (writeField
          (writeField
            (writeField i VQ.Euclid.TerminalPadding.workOffset workWidth
              (rotateRightValue workWidth
                (readField i VQ.Euclid.TerminalPadding.workOffset workWidth)))
            (VQ.Euclid.TerminalPadding.lowOffset workWidth) shiftWidth
              (terminalLow shiftWidth (depth + 1)))
          (VQ.Euclid.TerminalPadding.wrappedWire workWidth shiftWidth) 1 0)
        (VQ.Euclid.TerminalPadding.epochWire workWidth shiftWidth) 1
          (terminalEpoch shiftWidth (depth + 1)) := by
  rw [VQ.Euclid.TerminalPadding.gates_act hshift hcontrol hscratch hwrapped]
  simp only [VQ.Euclid.TerminalPadding.out,
    VQ.Euclid.TerminalPadding.nextLow,
    VQ.Euclid.TerminalPadding.nextEpoch,
    VQ.Euclid.TerminalPadding.wrapped, hlow, hcontrol, Nat.one_mul]
  rw [terminalLow_succ hfit, hepoch, terminalEpoch_succ hfit]

theorem terminalZeroSelected_iff
    {shiftWidth depth : Nat} (hfit : depth < 2 ^ (shiftWidth + 1)) :
    terminalZeroSelected shiftWidth depth ↔ depth = 0 := by
  constructor
  · rintro ⟨hlow, hepoch⟩
    have hbit :
        bitValue (terminalEncoded shiftWidth depth) shiftWidth = 1 := by
      by_contra hne
      have hzero :
          bitValue (terminalEncoded shiftWidth depth) shiftWidth = 0 := by
        have hlt := bitValue_lt (terminalEncoded shiftWidth depth) shiftWidth
        omega
      simp [terminalEpoch, hzero] at hepoch
    have hfull := readField_high
      (terminalEncoded shiftWidth depth) 0 shiftWidth
    simp only [Nat.zero_add] at hfull
    have hencodedFit :
        terminalEncoded shiftWidth depth < 2 ^ (shiftWidth + 1) :=
      encodeLength_lt _ _
    have hread :
        readField (terminalEncoded shiftWidth depth) 0 (shiftWidth + 1) =
          terminalEncoded shiftWidth depth := by
      simp [readField_zero, Nat.mod_eq_of_lt hencodedFit]
    have hlow' :
        readField (terminalEncoded shiftWidth depth) 0 shiftWidth =
          encodedZero shiftWidth := hlow
    rw [hread, hlow', hbit] at hfull
    have hencoded :
        terminalEncoded shiftWidth depth = encodedZero (shiftWidth + 1) := by
      calc
        terminalEncoded shiftWidth depth =
            encodedZero shiftWidth + 2 ^ shiftWidth := by
          simpa using hfull
        _ = encodedZero (shiftWidth + 1) := by
          simp only [encodedZero, Nat.pow_succ]
          have hpow := Nat.two_pow_pos shiftWidth
          omega
    exact (encodeLength_eq_encodedZero_iff hfit).mp hencoded
  · rintro rfl
    constructor
    · simp only [terminalLow, terminalEncoded]
      rw [readField_zero,
        encodeLength_mod_of_le (by omega) (Nat.two_pow_pos shiftWidth)]
      simp [encodeLength]
    · simp [terminalEpoch, terminalEncoded, encodeLength, encodedZero,
        bitValue]

theorem terminalPadding_not_selected
    {shiftWidth depth : Nat}
    (hpositive : 0 < depth) (hfit : depth < 2 ^ (shiftWidth + 1)) :
    ¬ terminalZeroSelected shiftWidth depth := by
  rw [terminalZeroSelected_iff hfit]
  omega

def physicalTerminalZeroSelected (shiftWidth i : Nat) : Prop :=
  readField i VQ.Euclid.TerminalEpoch.lowOffset shiftWidth =
      encodedZero shiftWidth ∧
    bitValue i (VQ.Euclid.TerminalEpoch.epochWire shiftWidth) = 0

theorem terminalGates_padding_not_selected
    {shiftWidth depth i : Nat}
    (hshift : 0 < shiftWidth)
    (hfit : depth + 1 < 2 ^ (shiftWidth + 1))
    (hlow : readField i VQ.Euclid.TerminalEpoch.lowOffset shiftWidth =
      terminalLow shiftWidth depth)
    (hcontrol : bitValue i
      (VQ.Euclid.TerminalEpoch.controlWire shiftWidth) = 1)
    (hscratch : readField i
      (VQ.Euclid.TerminalEpoch.scratchOffset shiftWidth) shiftWidth = 0)
    (hwrapped : bitValue i
      (VQ.Euclid.TerminalEpoch.wrappedWire shiftWidth) = 0)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalEpoch.epochWire shiftWidth) =
        terminalEpoch shiftWidth depth) :
    ¬ physicalTerminalZeroSelected shiftWidth
      (actGates (VQ.Euclid.TerminalEpoch.gates shiftWidth) i) := by
  rw [terminalGates_act_succ hshift hfit hlow hcontrol hscratch hwrapped hepoch]
  intro hselected
  apply terminalPadding_not_selected (shiftWidth := shiftWidth)
    (depth := depth + 1) (by omega) hfit
  rcases hselected with ⟨hlowSelected, hepochSelected⟩
  constructor
  · have hlowFit : terminalLow shiftWidth (depth + 1) < 2 ^ shiftWidth := by
      exact readField_lt _ _ _
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [VQ.Euclid.TerminalEpoch.lowOffset,
          VQ.Euclid.TerminalEpoch.epochWire]; omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [VQ.Euclid.TerminalEpoch.lowOffset,
          VQ.Euclid.TerminalEpoch.wrappedWire]; omega)),
      readField_writeField_self hlowFit] at hlowSelected
    exact hlowSelected
  · have hepochFit : terminalEpoch shiftWidth (depth + 1) < 2 := by
      unfold terminalEpoch
      split <;> omega
    simpa only [physicalTerminalZeroSelected, bitValue_write_self,
      Nat.mod_eq_of_lt hepochFit] using hepochSelected

end VQMathlib.Euclid.LuoActiveWindows
