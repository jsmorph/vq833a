import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.BitVec
import Mathlib.Data.Int.Bitwise
import Mathlib.Tactic

/-!
A word-level model of a signed ping-pong binary-Euclid recurrence.  Each
round selects addition or subtraction from the second-lowest bits, divides
the selected numerator by two, and alternates the updated coordinate.  The
module proves exact fixed-width behavior under signed-range hypotheses and
reversibility from the recorded sign sequence.
-/

namespace VQ.Euclid.PingPongWalk

/-- Signed integers represented by a `width`-bit two's-complement word. -/
def encode (width : Nat) (value : Int) : BitVec width :=
  BitVec.ofInt width value

/-- Signed decoding of a fixed-width two's-complement word. -/
def decode {width : Nat} (word : BitVec width) : Int :=
  word.toInt

/-- The signed interval represented without wraparound at `width` bits. -/
def FitsSigned (width : Nat) (value : Int) : Prop :=
  -2 ^ (width - 1) <= value ∧ value < 2 ^ (width - 1)

instance fitsSignedDecidable (width : Nat) (value : Int) :
    Decidable (FitsSigned width value) := by
  unfold FitsSigned
  infer_instance

theorem decode_encode {width : Nat} (hwidth : 0 < width) {value : Int}
    (hfit : FitsSigned width value) :
    decode (encode width value) = value := by
  exact BitVec.toInt_ofInt_eq_self hwidth hfit.1 hfit.2

/-- Bit one of the two's-complement representation.  Two bits suffice to read the second least-significant bit. -/
def bitOne (value : Int) : Bool :=
  (encode 2 value).getLsbD 1

theorem bitOne_eq_encodedBitOne {width : Nat} (hwidth : 2 <= width)
    (value : Int) :
    bitOne value = (encode width value).getLsbD 1 := by
  simp only [bitOne, encode, BitVec.getLsbD, BitVec.toNat_ofInt]
  have hdvdNat : 2 ^ 2 ∣ 2 ^ width := Nat.pow_dvd_pow 2 hwidth
  have hdvdInt : (2 ^ 2 : Int) ∣ (2 ^ width : Int) := by
    exact_mod_cast hdvdNat
  have hnonnegWidth : 0 <= value % (2 ^ width : Int) :=
    Int.emod_nonneg value (by positivity)
  have hnonnegTwo : 0 <= value % (2 ^ 2 : Int) :=
    Int.emod_nonneg value (by positivity)
  have hresidue :
      (value % (2 ^ width : Int)).toNat % 2 ^ 2 =
        (value % (2 ^ 2 : Int)).toNat := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_emod, Int.ofNat_toNat,
      Int.max_eq_left hnonnegWidth, Int.ofNat_toNat,
      Int.max_eq_left hnonnegTwo]
    exact Int.emod_emod_of_dvd value hdvdInt
  calc
    (value % (2 ^ 2 : Int)).toNat.testBit 1 =
        ((value % (2 ^ width : Int)).toNat % 2 ^ 2).testBit 1 := by
      rw [hresidue]
    _ = (value % (2 ^ width : Int)).toNat.testBit 1 := by
      simpa using Nat.testBit_mod_two_pow
        (value % (2 ^ width : Int)).toNat 2 1

/-- The recurrence subtracts exactly when the two bit-one values differ. -/
def chooseSubtract (source target : Int) : Bool :=
  Bool.xor (bitOne target) (bitOne source)

theorem chooseSubtract_eq_encodedBits {width : Nat} (hwidth : 2 <= width)
    (source target : Int) :
    chooseSubtract source target =
      Bool.xor ((encode width target).getLsbD 1)
        ((encode width source).getLsbD 1) := by
  rw [chooseSubtract, bitOne_eq_encodedBitOne hwidth,
    bitOne_eq_encodedBitOne hwidth]

/-- Integer numerator selected by the recorded source sign. -/
def chosenNumerator (source target : Int) : Int :=
  if chooseSubtract source target then target - source else target + source

/-- The wrapped word update performed before the source's shift. -/
def wrappedNumeratorWord (width : Nat) (source target : Int) : BitVec width :=
  if chooseSubtract source target then
    encode width target - encode width source
  else
    encode width target + encode width source

theorem wrappedNumeratorWord_eq_encode (width : Nat) (source target : Int) :
    wrappedNumeratorWord width source target =
      encode width (chosenNumerator source target) := by
  by_cases hsign : chooseSubtract source target
  · simp only [wrappedNumeratorWord, chosenNumerator, hsign, if_true]
    simp [encode, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  · simp only [wrappedNumeratorWord, chosenNumerator, hsign]
    exact (BitVec.ofInt_add target source).symm

/-- Wrapped addition or subtraction followed by an arithmetic right shift. -/
def cellWord (width : Nat) (source target : Int) : BitVec width :=
  (wrappedNumeratorWord width source target).sshiftRight 1

def cellValue (width : Nat) (source target : Int) : Int :=
  decode (cellWord width source target)

theorem cellValue_eq_half {width : Nat} (hwidth : 2 <= width)
    {source target : Int}
    (_hsource : FitsSigned width source)
    (_htarget : FitsSigned width target)
    (hnumerator : FitsSigned width (chosenNumerator source target)) :
    cellValue width source target = chosenNumerator source target / 2 := by
  have hwidthPos : 0 < width := by omega
  rw [cellValue, cellWord, wrappedNumeratorWord_eq_encode, decode,
    BitVec.toInt_sshiftRight]
  unfold encode
  rw [BitVec.toInt_ofInt_eq_self hwidthPos hnumerator.1 hnumerator.2,
    Int.shiftRight_eq_div_pow]
  norm_num

private theorem emod_four_eq_one_or_three_of_odd {value : Int}
    (hodd : Odd value) : value % 4 = 1 ∨ value % 4 = 3 := by
  have htwo : value % 2 = 1 := Int.odd_iff.mp hodd
  have hnested : (value % 4) % 2 = value % 2 :=
    Int.emod_emod_of_dvd value (by norm_num)
  have hnonneg := Int.emod_nonneg value (by norm_num : (4 : Int) ≠ 0)
  have hlt := Int.emod_lt_of_pos value (by norm_num : (0 : Int) < 4)
  omega

private theorem odd_half_of_emod_four_eq_two {value : Int}
    (hmod : value % 4 = 2) : Odd (value / 2) := by
  rw [Int.odd_iff]
  omega

private theorem bitOne_eq_false_of_emod_four_eq_one {value : Int}
    (hmod : value % 4 = 1) : bitOne value = false := by
  simp [bitOne, encode, BitVec.getLsbD, hmod, Nat.testBit]

private theorem bitOne_eq_true_of_emod_four_eq_three {value : Int}
    (hmod : value % 4 = 3) : bitOne value = true := by
  simp [bitOne, encode, BitVec.getLsbD, hmod, Nat.testBit]

theorem chosenNumerator_even {source target : Int}
    (hsource : Odd source) (htarget : Odd target) :
    Even (chosenNumerator source target) := by
  unfold chosenNumerator
  split
  · exact htarget.sub_odd hsource
  · exact htarget.add_odd hsource

theorem chosenNumerator_half_odd {source target : Int}
    (hsource : Odd source) (htarget : Odd target) :
    Odd (chosenNumerator source target / 2) := by
  rcases emod_four_eq_one_or_three_of_odd hsource with hs | hs <;>
    rcases emod_four_eq_one_or_three_of_odd htarget with ht | ht
  · apply odd_half_of_emod_four_eq_two
    simp [chosenNumerator, chooseSubtract,
      bitOne_eq_false_of_emod_four_eq_one hs,
      bitOne_eq_false_of_emod_four_eq_one ht,
      Int.add_emod, hs, ht]
  · apply odd_half_of_emod_four_eq_two
    simp [chosenNumerator, chooseSubtract,
      bitOne_eq_false_of_emod_four_eq_one hs,
      bitOne_eq_true_of_emod_four_eq_three ht,
      Int.sub_emod, hs, ht]
  · apply odd_half_of_emod_four_eq_two
    simp [chosenNumerator, chooseSubtract,
      bitOne_eq_true_of_emod_four_eq_three hs,
      bitOne_eq_false_of_emod_four_eq_one ht,
      Int.sub_emod, hs, ht]
  · apply odd_half_of_emod_four_eq_two
    simp [chosenNumerator, chooseSubtract,
      bitOne_eq_true_of_emod_four_eq_three hs,
      bitOne_eq_true_of_emod_four_eq_three ht,
      Int.add_emod, hs, ht]

theorem cellValue_odd {width : Nat} (hwidth : 2 <= width)
    {source target : Int}
    (hsourceFit : FitsSigned width source)
    (htargetFit : FitsSigned width target)
    (hnumeratorFit : FitsSigned width (chosenNumerator source target))
    (hsourceOdd : Odd source) (htargetOdd : Odd target) :
    Odd (cellValue width source target) := by
  rw [cellValue_eq_half hwidth hsourceFit htargetFit hnumeratorFit]
  exact chosenNumerator_half_odd hsourceOdd htargetOdd

def reconstructedTarget (source output : Int) (sign : Bool) : Int :=
  if sign then 2 * output + source else 2 * output - source

theorem encode_double_eq_shiftLeft (width : Nat) (output : Int) :
    encode width (2 * output) = encode width output <<< 1 := by
  have htwo : BitVec.ofInt width 2 = BitVec.twoPow width 1 := by
    apply BitVec.eq_of_toNat_eq
    cases width <;>
      simp [BitVec.twoPow, Nat.shiftLeft_eq, Nat.pow_succ]
  change BitVec.ofInt width (2 * output) =
    BitVec.ofInt width output <<< 1
  rw [BitVec.ofInt_mul, BitVec.mul_comm, htwo,
    BitVec.mul_twoPow_eq_shiftLeft]

/-- Reverse word update using the recorded sign.  Encoding `2 * output`
represents the inverse left shift before the wrapped add or subtract. -/
def reverseCellWord (width : Nat) (source output : Int)
    (sign : Bool) : BitVec width :=
  if sign then
    encode width (2 * output) + encode width source
  else
    encode width (2 * output) - encode width source

def reverseCellValue (width : Nat) (source output : Int)
    (sign : Bool) : Int :=
  decode (reverseCellWord width source output sign)

theorem reverseCellWord_eq_encode (width : Nat) (source output : Int)
    (sign : Bool) :
    reverseCellWord width source output sign =
      encode width (reconstructedTarget source output sign) := by
  cases sign <;>
    simp [reverseCellWord, reconstructedTarget, encode, sub_eq_add_neg,
      BitVec.ofInt_add, BitVec.ofInt_neg]

theorem reverseCellValue_eq_reconstructed {width : Nat} (hwidth : 0 < width)
    {source output : Int} {sign : Bool}
    (hreconstructed : FitsSigned width
      (reconstructedTarget source output sign)) :
    reverseCellValue width source output sign =
      reconstructedTarget source output sign := by
  rw [reverseCellValue, reverseCellWord_eq_encode]
  exact decode_encode hwidth hreconstructed

theorem reverseCell_recovers {width : Nat} (hwidth : 2 <= width)
    {source target : Int}
    (hsourceFit : FitsSigned width source)
    (htargetFit : FitsSigned width target)
    (hnumeratorFit : FitsSigned width (chosenNumerator source target))
    (hsourceOdd : Odd source) (htargetOdd : Odd target) :
    reverseCellValue width source (cellValue width source target)
      (chooseSubtract source target) = target := by
  have hforward := cellValue_eq_half hwidth hsourceFit htargetFit hnumeratorFit
  have heven := chosenNumerator_even hsourceOdd htargetOdd
  have hdouble :
      2 * (chosenNumerator source target / 2) =
        chosenNumerator source target := by
    exact Int.mul_ediv_cancel_of_dvd (even_iff_two_dvd.mp heven)
  have hreconstruction :
      reconstructedTarget source (chosenNumerator source target / 2)
        (chooseSubtract source target) = target := by
    by_cases hsign : chooseSubtract source target
    · have hcase : 2 * ((target - source) / 2) = target - source := by
        simpa [chosenNumerator, hsign] using hdouble
      simp [reconstructedTarget, chosenNumerator, hsign, hcase]
    · have hcase : 2 * ((target + source) / 2) = target + source := by
        simpa [chosenNumerator, hsign] using hdouble
      simp [reconstructedTarget, chosenNumerator, hsign, hcase]
  rw [hforward]
  have hreconstructionFit : FitsSigned width
      (reconstructedTarget source (chosenNumerator source target / 2)
        (chooseSubtract source target)) := by
    rwa [hreconstruction]
  have hwidthPos : 0 < width := by omega
  rw [reverseCellValue_eq_reconstructed hwidthPos hreconstructionFit,
    hreconstruction]

structure WalkValues where
  u : Int
  v : Int
  deriving DecidableEq, Repr

def evenRound (round : Nat) : Bool :=
  decide (Even round)

def sourceAt (round : Nat) (values : WalkValues) : Int :=
  if evenRound round then values.u else values.v

def targetAt (round : Nat) (values : WalkValues) : Int :=
  if evenRound round then values.v else values.u

def setTargetAt (round : Nat) (values : WalkValues)
    (target : Int) : WalkValues :=
  if evenRound round then { values with v := target }
  else { values with u := target }

@[simp] theorem sourceAt_setTargetAt (round : Nat) (values : WalkValues)
    (target : Int) :
    sourceAt round (setTargetAt round values target) = sourceAt round values := by
  by_cases hround : evenRound round <;>
    simp [sourceAt, setTargetAt, hround]

@[simp] theorem targetAt_setTargetAt (round : Nat) (values : WalkValues)
    (target : Int) :
    targetAt round (setTargetAt round values target) = target := by
  by_cases hround : evenRound round <;>
    simp [targetAt, setTargetAt, hround]

structure RoundResult where
  values : WalkValues
  sign : Bool
  deriving DecidableEq, Repr

/-- The normal walk alternates the target between `v` and `u`. -/
def walkRound (width round : Nat) (values : WalkValues) : RoundResult :=
  let source := sourceAt round values
  let target := targetAt round values
  { values := setTargetAt round values (cellValue width source target)
    sign := chooseSubtract source target }

def walkBackRound (width round : Nat) (values : WalkValues)
    (sign : Bool) : WalkValues :=
  setTargetAt round values
    (reverseCellValue width (sourceAt round values)
      (targetAt round values) sign)

theorem walkRound_source_preserved (width round : Nat) (values : WalkValues) :
    sourceAt round (walkRound width round values).values =
      sourceAt round values := by
  simp [walkRound]

theorem walkRound_target_eq_half {width round : Nat} (hwidth : 2 <= width)
    {values : WalkValues}
    (hsource : FitsSigned width (sourceAt round values))
    (htarget : FitsSigned width (targetAt round values))
    (hnumerator : FitsSigned width
      (chosenNumerator (sourceAt round values) (targetAt round values))) :
    targetAt round (walkRound width round values).values =
      chosenNumerator (sourceAt round values) (targetAt round values) / 2 := by
  simp only [walkRound, targetAt_setTargetAt]
  exact cellValue_eq_half hwidth hsource htarget hnumerator

theorem walkRound_target_odd {width round : Nat} (hwidth : 2 <= width)
    {values : WalkValues}
    (hsourceFit : FitsSigned width (sourceAt round values))
    (htargetFit : FitsSigned width (targetAt round values))
    (hnumeratorFit : FitsSigned width
      (chosenNumerator (sourceAt round values) (targetAt round values)))
    (hsourceOdd : Odd (sourceAt round values))
    (htargetOdd : Odd (targetAt round values)) :
    Odd (targetAt round (walkRound width round values).values) := by
  rw [walkRound_target_eq_half hwidth hsourceFit htargetFit hnumeratorFit]
  exact chosenNumerator_half_odd hsourceOdd htargetOdd

theorem walkBackRound_walkRound {width round : Nat} (hwidth : 2 <= width)
    {values : WalkValues}
    (hsourceFit : FitsSigned width (sourceAt round values))
    (htargetFit : FitsSigned width (targetAt round values))
    (hnumeratorFit : FitsSigned width
      (chosenNumerator (sourceAt round values) (targetAt round values)))
    (hsourceOdd : Odd (sourceAt round values))
    (htargetOdd : Odd (targetAt round values)) :
    walkBackRound width round (walkRound width round values).values
      (walkRound width round values).sign = values := by
  have hrecover := reverseCell_recovers hwidth hsourceFit htargetFit
    hnumeratorFit hsourceOdd htargetOdd
  by_cases hround : evenRound round <;>
    simp [walkRound, walkBackRound, sourceAt, targetAt, setTargetAt,
      hround] at hrecover ⊢
  all_goals simp [hrecover]

/-- A width schedule assigns the signed word width used at each global round. -/
abbrev WidthSchedule := Nat -> Nat

/-- A nonincreasing width schedule. -/
def ScheduleNonincreasing (schedule : WidthSchedule) : Prop :=
  forall round, schedule (round + 1) <= schedule round

structure WalkTrace where
  values : WalkValues
  signs : List Bool
  deriving DecidableEq, Repr

/-- Forward iteration records signs in increasing round order. -/
def forwardRounds (schedule : WidthSchedule) (round : Nat) :
    Nat -> WalkValues -> WalkTrace
  | 0, values => { values, signs := [] }
  | count + 1, values =>
      let first := walkRound (schedule round) round values
      let tail := forwardRounds schedule (round + 1) count first.values
      { values := tail.values, signs := first.sign :: tail.signs }

/-- Reverse iteration consumes a chronological sign tape after recursively
restoring its later rounds. -/
def reverseRounds (schedule : WidthSchedule) (round : Nat) :
    Nat -> List Bool -> WalkValues -> Option WalkValues
  | 0, [], values => some values
  | 0, _ :: _, _ => none
  | _ + 1, [], _ => none
  | count + 1, sign :: signs, values =>
      match reverseRounds schedule (round + 1) count signs values with
      | none => none
      | some restored =>
          some (walkBackRound (schedule round) round restored sign)

structure RoundAdmissible (width round : Nat) (values : WalkValues) : Prop where
  width_ge_two : 2 <= width
  source_fits : FitsSigned width (sourceAt round values)
  target_fits : FitsSigned width (targetAt round values)
  numerator_fits : FitsSigned width
    (chosenNumerator (sourceAt round values) (targetAt round values))
  source_odd : Odd (sourceAt round values)
  target_odd : Odd (targetAt round values)

instance roundAdmissibleDecidable (width round : Nat) (values : WalkValues) :
    Decidable (RoundAdmissible width round values) := by
  refine decidable_of_iff
    (2 <= width ∧
      FitsSigned width (sourceAt round values) ∧
      FitsSigned width (targetAt round values) ∧
      FitsSigned width
        (chosenNumerator (sourceAt round values) (targetAt round values)) ∧
      Odd (sourceAt round values) ∧ Odd (targetAt round values)) ?_
  constructor
  · rintro ⟨hwidth, hsourceFit, htargetFit, hnumeratorFit,
      hsourceOdd, htargetOdd⟩
    exact ⟨hwidth, hsourceFit, htargetFit, hnumeratorFit,
      hsourceOdd, htargetOdd⟩
  · intro h
    exact ⟨h.width_ge_two, h.source_fits, h.target_fits,
      h.numerator_fits, h.source_odd, h.target_odd⟩

/-- Per-round hypotheses evaluated on the forward state entering each cell. -/
def RoundsAdmissible (schedule : WidthSchedule) (round : Nat) :
    Nat -> WalkValues -> Prop
  | 0, _ => True
  | count + 1, values =>
      RoundAdmissible (schedule round) round values ∧
        RoundsAdmissible schedule (round + 1) count
          (walkRound (schedule round) round values).values

instance roundsAdmissibleDecidable (schedule : WidthSchedule)
    (round count : Nat) (values : WalkValues) :
    Decidable (RoundsAdmissible schedule round count values) := by
  induction count generalizing round values with
  | zero => exact isTrue trivial
  | succ count ih =>
      change Decidable
        (RoundAdmissible (schedule round) round values ∧
          RoundsAdmissible schedule (round + 1) count
            (walkRound (schedule round) round values).values)
      exact @instDecidableAnd _ _ inferInstance
        (ih (round + 1) (walkRound (schedule round) round values).values)

theorem forwardRounds_signs_length (schedule : WidthSchedule) (round count : Nat)
    (values : WalkValues) :
    (forwardRounds schedule round count values).signs.length = count := by
  induction count generalizing round values with
  | zero => rfl
  | succ count ih =>
      simp [forwardRounds, ih]

theorem reverseRounds_forwardRounds (schedule : WidthSchedule)
    (round count : Nat) (values : WalkValues)
    (hadmissible : RoundsAdmissible schedule round count values) :
    reverseRounds schedule round count
      (forwardRounds schedule round count values).signs
      (forwardRounds schedule round count values).values = some values := by
  induction count generalizing round values with
  | zero => simp [forwardRounds, reverseRounds]
  | succ count ih =>
      rcases hadmissible with ⟨hfirst, htail⟩
      let first := walkRound (schedule round) round values
      have htailRecover := ih (round + 1) first.values htail
      have hfirstRecover := walkBackRound_walkRound hfirst.width_ge_two
        hfirst.source_fits hfirst.target_fits hfirst.numerator_fits
        hfirst.source_odd hfirst.target_odd
      simp only [forwardRounds, reverseRounds]
      rw [htailRecover]
      exact congrArg some hfirstRecover

/-- A terminal signed value whose non-sign wires are determined by the sign
and the constant least-significant bit. -/
def TerminalUnit (value : Int) : Prop :=
  value = 1 ∨ value = -1

def TerminalUnits (values : WalkValues) : Prop :=
  TerminalUnit values.u ∧ TerminalUnit values.v

instance terminalUnitDecidable (value : Int) : Decidable (TerminalUnit value) := by
  unfold TerminalUnit
  infer_instance

instance terminalUnitsDecidable (values : WalkValues) :
    Decidable (TerminalUnits values) := by
  unfold TerminalUnits
  infer_instance

/-- Bit condition for borrowing the non-sign wires of a terminal word. -/
def LoanableWord {width : Nat} (word : BitVec width) : Prop :=
  word.getLsbD 0 = true ∧
    forall bit, 0 < bit -> bit + 1 < width ->
      word.getLsbD bit = word.msb

theorem terminalUnit_loanable {width : Nat} (hwidth : 2 <= width)
    {value : Int} (hterminal : TerminalUnit value) :
    LoanableWord (encode width value) := by
  rcases hterminal with rfl | rfl
  · constructor
    · have hwidthPos : 0 < width := by omega
      simp [encode, hwidthPos]
    · intro bit hbit htop
      have hwidthPos : 0 < width := by omega
      have hwidthNeOne : width ≠ 1 := by omega
      simp [encode, BitVec.msb_one, BitVec.getLsbD_one, hwidthPos,
        hwidthNeOne, hbit.ne']
  · have hword : encode width (-1) = BitVec.allOnes width := by
      change BitVec.ofInt width (Int.negSucc 0) = BitVec.allOnes width
      rw [BitVec.ofInt_negSucc_eq_not_ofNat]
      exact BitVec.not_zero
    rw [hword]
    constructor
    · have hwidthPos : 0 < width := by omega
      simp [hwidthPos]
    · intro bit hbit htop
      have hwidthPos : 0 < width := by omega
      have hbitLt : bit < width := by omega
      simp [BitVec.msb_allOnes hwidthPos, hbitLt]

theorem terminalUnits_justify_loans {width : Nat} (hwidth : 2 <= width)
    {values : WalkValues} (hterminal : TerminalUnits values) :
    LoanableWord (encode width values.u) ∧
      LoanableWord (encode width values.v) :=
  ⟨terminalUnit_loanable hwidth hterminal.1,
    terminalUnit_loanable hwidth hterminal.2⟩

end VQ.Euclid.PingPongWalk
