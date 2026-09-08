import VQMathlib.Curve.Laws

namespace VQBridge.Curve.LuoMultiplication

/-- The integer selected by a control bit. -/
def bitValue (b : Bool) : Nat := if b then 1 else 0

/-- The unreduced accumulator sum in one controlled modular-addition block. -/
def rawSum (control : Bool) (addend accumulator : Nat) : Nat :=
  accumulator + bitValue control * addend

/-- The reduction flag computed from the word overflow and the fixed-modulus comparison. -/
def reductionFlag (wordSize modulus sum : Nat) : Bool :=
  decide (wordSize ≤ sum) != decide (modulus ≤ sum % wordSize)

/-- Conditional subtraction of the modulus in word arithmetic. -/
def wordCorrection (wordSize modulus sum : Nat) : Nat :=
  if reductionFlag wordSize modulus sum then
    (sum % wordSize + (wordSize - modulus)) % wordSize
  else
    sum % wordSize

theorem rawSum_lt_twice_modulus {control : Bool} {addend accumulator modulus : Nat}
    (haddend : addend ≤ modulus) (haccumulator : accumulator < modulus) :
    rawSum control addend accumulator < 2 * modulus := by
  cases control <;> simp [rawSum, bitValue] <;> omega

theorem reductionFlag_correct {wordSize modulus sum : Nat}
    (hmodulus : modulus < wordSize) (hsum : sum < 2 * modulus) :
    reductionFlag wordSize modulus sum = decide (modulus ≤ sum) := by
  by_cases hoverflow : wordSize ≤ sum
  · have hsumWord : sum - wordSize < wordSize := by omega
    have hsumMod : sum % wordSize = sum - wordSize := by
      have hsplit : sum = sum - wordSize + wordSize := by omega
      calc
        sum % wordSize = (sum - wordSize + wordSize) % wordSize :=
          congrArg (· % wordSize) hsplit
        _ = sum - wordSize := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsumWord]
    have hbelow : sum % wordSize < modulus := by omega
    have habove : modulus ≤ sum := by omega
    simp [reductionFlag, hoverflow, hbelow, habove]
  · have hsumWord : sum < wordSize := by omega
    rw [reductionFlag, Nat.mod_eq_of_lt hsumWord]
    simp [hoverflow]

theorem wordCorrection_correct {wordSize modulus sum : Nat}
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < wordSize)
    (hsum : sum < 2 * modulus) :
    wordCorrection wordSize modulus sum = sum % modulus := by
  rw [wordCorrection, reductionFlag_correct hmodulus hsum]
  by_cases hreduction : modulus ≤ sum
  · have hsumModulus : sum % modulus = sum - modulus := by
      have hlt : sum - modulus < modulus := by omega
      have hsplit : sum = sum - modulus + modulus := by omega
      calc
        sum % modulus = (sum - modulus + modulus) % modulus :=
          congrArg (· % modulus) hsplit
        _ = sum - modulus := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    simp only [decide_eq_true_eq, hreduction, if_true, hsumModulus]
    by_cases hoverflow : wordSize ≤ sum
    · have hword : sum % wordSize = sum - wordSize := by
        have hlt : sum - wordSize < wordSize := by omega
        have hsplit : sum = sum - wordSize + wordSize := by omega
        calc
          sum % wordSize = (sum - wordSize + wordSize) % wordSize :=
            congrArg (· % wordSize) hsplit
          _ = sum - wordSize := by
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      have hcombine : sum - wordSize + (wordSize - modulus) = sum - modulus := by omega
      rw [hword, hcombine, Nat.mod_eq_of_lt (by omega)]
    · have hword : sum < wordSize := by omega
      rw [Nat.mod_eq_of_lt hword]
      have hcombine : sum + (wordSize - modulus) = sum - modulus + wordSize := by omega
      rw [hcombine, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have hsumModulus : sum < modulus := by omega
    have hsumWord : sum < wordSize := by omega
    simp [hreduction, Nat.mod_eq_of_lt hsumModulus, Nat.mod_eq_of_lt hsumWord]

/-- The corrected accumulator value specified by the modular-addition block. -/
def correctedAccumulator (modulus : Nat) (control : Bool)
    (addend accumulator : Nat) : Nat :=
  rawSum control addend accumulator % modulus

theorem reductionFlag_uncompute {wordSize modulus addend accumulator : Nat}
    (control : Bool) (hmodulus : modulus < wordSize)
    (haddend : addend ≤ modulus) (haccumulator : accumulator < modulus) :
    reductionFlag wordSize modulus (rawSum control addend accumulator) =
      (control && decide (correctedAccumulator modulus control addend accumulator < addend)) := by
  rw [reductionFlag_correct hmodulus
    (rawSum_lt_twice_modulus haddend haccumulator)]
  cases control with
  | false =>
      have hbelow : ¬ modulus ≤ accumulator := by omega
      simp [rawSum, bitValue, correctedAccumulator, Nat.mod_eq_of_lt haccumulator,
        hbelow]
  | true =>
      simp only [Bool.true_and]
      by_cases hreduction : modulus ≤ accumulator + addend
      · have hsum : accumulator + addend < 2 * modulus := by omega
        have hrem : (accumulator + addend) % modulus = accumulator + addend - modulus := by
          have hlt : accumulator + addend - modulus < modulus := by omega
          have hsplit : accumulator + addend =
              accumulator + addend - modulus + modulus := by omega
          calc
            (accumulator + addend) % modulus =
                (accumulator + addend - modulus + modulus) % modulus :=
              congrArg (· % modulus) hsplit
            _ = accumulator + addend - modulus := by
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
        have hfinal : accumulator + addend - modulus < addend := by omega
        simp [rawSum, bitValue, correctedAccumulator, hreduction, hrem, hfinal]
      · have hsum : accumulator + addend < modulus := by omega
        have hfinal : ¬ accumulator + addend < addend := by omega
        simp [rawSum, bitValue, correctedAccumulator, hreduction,
          Nat.mod_eq_of_lt hsum, hfinal]

/-- Modular doubling of a canonical accumulator. -/
def doubledAccumulator (modulus accumulator : Nat) : Nat := 2 * accumulator % modulus

theorem doubling_flag_from_low_bit {modulus accumulator : Nat}
    (hmodulusOdd : modulus % 2 = 1) (haccumulator : accumulator < modulus) :
    decide (modulus ≤ 2 * accumulator) =
      decide (doubledAccumulator modulus accumulator % 2 = 1) := by
  by_cases hreduction : modulus ≤ 2 * accumulator
  · have hsum : 2 * accumulator < 2 * modulus := by omega
    have hrem : 2 * accumulator % modulus = 2 * accumulator - modulus := by
      have hlt : 2 * accumulator - modulus < modulus := by omega
      have hsplit : 2 * accumulator = 2 * accumulator - modulus + modulus := by omega
      calc
        2 * accumulator % modulus =
            (2 * accumulator - modulus + modulus) % modulus :=
          congrArg (· % modulus) hsplit
        _ = 2 * accumulator - modulus := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    have hodd : (2 * accumulator - modulus) % 2 = 1 := by omega
    simp [hreduction, doubledAccumulator, hrem, hodd]
  · have hsum : 2 * accumulator < modulus := by omega
    have heven : (2 * accumulator) % 2 = 0 := by omega
    simp [hreduction, doubledAccumulator, Nat.mod_eq_of_lt hsum, heven]

/-- The value transformation implemented by the inverse modular-doubling block. -/
def halvedAccumulator (modulus accumulator : Nat) : Nat :=
  if accumulator % 2 = 1 then (accumulator + modulus) / 2 else accumulator / 2

theorem halve_doubled {modulus accumulator : Nat}
    (hmodulusOdd : modulus % 2 = 1) (haccumulator : accumulator < modulus) :
    halvedAccumulator modulus (doubledAccumulator modulus accumulator) = accumulator := by
  by_cases hreduction : modulus ≤ 2 * accumulator
  · have hsum : 2 * accumulator < 2 * modulus := by omega
    have hrem : doubledAccumulator modulus accumulator = 2 * accumulator - modulus := by
      have hlt : 2 * accumulator - modulus < modulus := by omega
      have hsplit : 2 * accumulator = 2 * accumulator - modulus + modulus := by omega
      unfold doubledAccumulator
      calc
        2 * accumulator % modulus =
            (2 * accumulator - modulus + modulus) % modulus :=
          congrArg (· % modulus) hsplit
        _ = 2 * accumulator - modulus := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    have hodd : (2 * accumulator - modulus) % 2 = 1 := by omega
    rw [halvedAccumulator, hrem, if_pos hodd]
    omega
  · have hsum : 2 * accumulator < modulus := by omega
    have heven : (2 * accumulator) % 2 ≠ 1 := by omega
    rw [halvedAccumulator, doubledAccumulator, Nat.mod_eq_of_lt hsum, if_neg heven]
    omega

/-- Little-endian binary decoding. -/
def decode : List Bool → Nat
  | [] => 0
  | b :: bits => bitValue b + 2 * decode bits

/-- Horner double-and-add, written on little-endian input so the recursive call
processes the higher bits first. -/
def horner (modulus multiplicand : Nat) : List Bool → Nat
  | [] => 0
  | b :: bits => (2 * horner modulus multiplicand bits + bitValue b * multiplicand) % modulus

theorem horner_correct {modulus multiplicand : Nat} (bits : List Bool) :
    horner modulus multiplicand bits = decode bits * multiplicand % modulus := by
  induction bits with
  | nil => simp [horner, decode]
  | cons b bits ih =>
      rw [horner, decode, ih]
      have hmod :
          (2 * (decode bits * multiplicand % modulus) + bitValue b * multiplicand) % modulus =
            (2 * (decode bits * multiplicand) + bitValue b * multiplicand) % modulus := by
        calc
          (2 * (decode bits * multiplicand % modulus) +
              bitValue b * multiplicand) % modulus =
              ((2 * (decode bits * multiplicand % modulus)) % modulus +
                bitValue b * multiplicand) % modulus := by
            rw [Nat.mod_add_mod]
          _ = ((2 * (decode bits * multiplicand)) % modulus +
                bitValue b * multiplicand) % modulus := by
            rw [Nat.mul_mod_mod]
          _ = (2 * (decode bits * multiplicand) +
                bitValue b * multiplicand) % modulus := by
            rw [Nat.mod_add_mod]
      rw [hmod]
      congr 1
      ring

end VQBridge.Curve.LuoMultiplication
