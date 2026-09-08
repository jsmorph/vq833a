import VQ.Euclid.ScheduleBound
import VQ.Euclid.TerminalCompression
import VQMathlib.Euclid.LuoActiveWindows
import VQMathlib.Euclid.LuoScheduleBound

namespace VQMathlib.Euclid.LuoTerminalCompression

open VQ
open VQ.Euclid
open VQ.Reversible
open LuoActiveWindows

def compressionCode (shiftWidth depth : Nat) : Nat :=
  readField (terminalLow shiftWidth depth) 0 2 +
    4 * terminalEpoch shiftWidth depth

def compressedEpoch (shiftWidth depth : Nat) : Nat :=
  bitValue
    (TerminalCompression.compressCode (compressionCode shiftWidth depth)) 2

theorem euclidWeight_gcd_le :
    ∀ a b : Nat, b ≤ a →
      a ≤ 2 ^ euclidWeight a b * Nat.gcd a b := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      intro hba
      by_cases hb : b = 0
      · subst b
        simp
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hrlt : a % b < b := Nat.mod_lt a hbpos
        have hrec := ih (a % b) hrlt b (Nat.le_of_lt hrlt)
        have hqbound : a / b + 1 ≤ 2 ^ bitLength (a / b) := by
          have hlt := lt_two_pow_bitLength (a / b)
          omega
        have hstep : a < b * 2 ^ bitLength (a / b) := by
          calc
            a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
            _ < b * (a / b) + b := Nat.add_lt_add_left hrlt _
            _ = b * (a / b + 1) := by simp [Nat.mul_add]
            _ ≤ b * 2 ^ bitLength (a / b) :=
              Nat.mul_le_mul_left b hqbound
        have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
          calc
            Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b
            _ = Nat.gcd (a % b) b := Nat.gcd_rec b a
            _ = Nat.gcd b (a % b) := Nat.gcd_comm _ _
        calc
          a ≤ 2 ^ bitLength (a / b) * b := by
            simpa [Nat.mul_comm] using Nat.le_of_lt hstep
          _ ≤ 2 ^ bitLength (a / b) *
                (2 ^ euclidWeight b (a % b) * Nat.gcd b (a % b)) :=
            Nat.mul_le_mul_left _ hrec
          _ = 2 ^ euclidWeight a b * Nat.gcd a b := by
            simp [euclidWeight_of_pos hbpos, pow_add, hgcd, Nat.mul_assoc]

theorem euclidWeight_gcd_lt
    {a b : Nat} (hb : 0 < b) (hba : b ≤ a) :
    a < 2 ^ euclidWeight a b * Nat.gcd a b := by
  have hrlt : a % b < b := Nat.mod_lt a hb
  have hrec := euclidWeight_gcd_le b (a % b) (Nat.le_of_lt hrlt)
  have hqbound : a / b + 1 ≤ 2 ^ bitLength (a / b) := by
    have hqpos : 0 < a / b := Nat.div_pos hba hb
    have hlt := lt_two_pow_bitLength (a / b)
    omega
  have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
    calc
      Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b
      _ = Nat.gcd (a % b) b := Nat.gcd_rec b a
      _ = Nat.gcd b (a % b) := Nat.gcd_comm _ _
  calc
    a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
    _ < b * (a / b) + b := Nat.add_lt_add_left hrlt _
    _ = b * (a / b + 1) := by simp [Nat.mul_add]
    _ ≤ b * 2 ^ bitLength (a / b) := Nat.mul_le_mul_left b hqbound
    _ = 2 ^ bitLength (a / b) * b := Nat.mul_comm _ _
    _ ≤ 2 ^ bitLength (a / b) *
          (2 ^ euclidWeight b (a % b) * Nat.gcd b (a % b)) :=
      Nat.mul_le_mul_left _ hrec
    _ = 2 ^ euclidWeight a b * Nat.gcd a b := by
      simp [euclidWeight_of_pos hb, pow_add, hgcd, Nat.mul_assoc]

theorem bitLength_le_euclidWeight
    {a b : Nat} (hb : 0 < b) (hba : b ≤ a)
    (hcoprime : Nat.Coprime a b) :
    bitLength a ≤ euclidWeight a b := by
  have hbound := euclidWeight_gcd_lt hb hba
  have hpower : a < 2 ^ euclidWeight a b := by
    simpa [hcoprime.gcd_eq_one] using hbound
  exact bitLength_le_of_lt_two_pow hpower

theorem preprocessed_euclidWeight_lower
    {p a : Nat} (hpPrime : p.Prime)
    (ha0 : 0 < a) (ha : a < p) :
    bitLength p ≤ euclidWeight p (normalizedInput p a) := by
  have hx0 := normalizedInput_pos ha0 ha
  have hx := normalizedInput_lt ha0 ha
  have hcoprime : Nat.Coprime p (normalizedInput p a) :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt hx0) hx hpPrime
  exact bitLength_le_euclidWeight hx0 (Nat.le_of_lt hx) hcoprime

theorem preprocessed_terminal_suffix
    {p a n lengthWidth shiftWidth rounds : Nat}
    (hpFit : p < 2 ^ n)
    (hwork : VQ.Euclid.workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hrounds : 4 * euclidWeight p (normalizedInput p a) ≤ rounds)
    (haligned : rounds % 4 = 0) :
    ∃ tau, 0 < tau ∧
      tau = 4 * euclidWeight p (normalizedInput p a) ∧
      tau ≤ rounds ∧
      (∀ k, k < tau →
        ¬ Terminal (run lengthWidth shiftWidth k
          (preprocessedState p a))) ∧
      Terminal (run lengthWidth shiftWidth tau
        (preprocessedState p a)) ∧
      (run lengthWidth shiftWidth tau
        (preprocessedState p a)).shift = 0 ∧
      (rounds - tau) % 4 = 0 := by
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  obtain ⟨tau, htau, htauMeasure, hlive, hterminal, hshift⟩ :=
    exists_first_terminal_schedule hinitial hwork hwidths
      (preprocessedState_not_terminal ha0 ha)
  have htauExact :
      tau = 4 * euclidWeight p (normalizedInput p a) := by
    rw [htauMeasure, preprocessed_scheduleMeasure]
  have htauBound : tau ≤ rounds := by omega
  have hsuffix : (rounds - tau) % 4 = 0 := by
    have htauAligned : tau % 4 = 0 := by
      rw [htauExact]
      omega
    omega
  exact ⟨tau, htau, htauExact, htauBound, hlive, hterminal, hshift,
    hsuffix⟩

theorem compressCode_involutive (code : Nat) :
    TerminalCompression.compressCode
        (TerminalCompression.compressCode code) = code :=
  TerminalCompression.compressCode_involutive code

theorem terminalLow_two_bits
    {shiftWidth depth : Nat}
    (hwidth : 2 ≤ shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hmultiple : depth % 4 = 0) :
    readField (terminalLow shiftWidth depth) 0 2 = 3 := by
  have hmod : terminalEncoded shiftWidth depth % 4 = 3 := by
    by_cases hzero : depth = 0
    · subst depth
      have h := encodeLength_mod_of_le
        (lowWidth := 2) (highWidth := shiftWidth + 1) (length := 0)
        (by omega) (by norm_num)
      simpa [terminalEncoded, encodeLength, encodedZero] using h
    · have hpositive : 0 < depth := Nat.pos_of_ne_zero hzero
      have hdvd : 4 ∣ depth := Nat.dvd_of_mod_eq_zero hmultiple
      obtain ⟨k, hk⟩ := hdvd
      have hkpositive : 0 < k := by
        rw [hk] at hpositive
        omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpositive)
      have hpred : 4 * (j + 1) - 1 = 4 * j + 3 := by omega
      simp only [terminalEncoded, encodeLength, if_neg (by omega)]
      have hpredFit : depth - 1 < 2 ^ (shiftWidth + 1) := by omega
      rw [Nat.mod_eq_of_lt hpredFit, hk, hpred]
      simp [Nat.add_mod]
  have hdvd : 2 ^ 2 ∣ 2 ^ shiftWidth := Nat.pow_dvd_pow 2 hwidth
  simp only [terminalLow, readField_zero]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  simpa using hmod

theorem compressionCode_eq_three_or_seven
    {shiftWidth depth : Nat}
    (hwidth : 2 ≤ shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hmultiple : depth % 4 = 0) :
    compressionCode shiftWidth depth = 3 ∨
      compressionCode shiftWidth depth = 7 := by
  have hlow := terminalLow_two_bits hwidth hfit hmultiple
  have hepochLt : terminalEpoch shiftWidth depth < 2 := by
    unfold terminalEpoch
    split <;> omega
  rcases (show terminalEpoch shiftWidth depth = 0 ∨
      terminalEpoch shiftWidth depth = 1 by omega) with hepoch | hepoch
  · left
    simp [compressionCode, hlow, hepoch]
  · right
    simp [compressionCode, hlow, hepoch]

theorem compression_clears_epoch
    {shiftWidth depth : Nat}
    (hwidth : 2 ≤ shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hmultiple : depth % 4 = 0) :
    compressedEpoch shiftWidth depth = 0 := by
  rcases compressionCode_eq_three_or_seven hwidth hfit hmultiple with
    hcode | hcode
  · unfold compressedEpoch
    rw [hcode]
    decide
  · unfold compressedEpoch
    rw [hcode]
    decide

theorem compression_gates_clear_epoch
    {shiftWidth depth : Nat}
    (hwidth : 2 ≤ shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hmultiple : depth % 4 = 0) :
    bitValue
        (actGates TerminalCompression.gates
          (compressionCode shiftWidth depth + 8)) 2 = 0 := by
  rcases compressionCode_eq_three_or_seven hwidth hfit hmultiple with
    hcode | hcode
  · rw [hcode]
    have hact := TerminalCompression.gates_act
      (i := 3 + 8) (by decide +kernel) (by decide +kernel)
    rw [hact]
    decide +kernel
  · rw [hcode]
    have hact := TerminalCompression.gates_act
      (i := 7 + 8) (by decide +kernel) (by decide +kernel)
    rw [hact]
    decide +kernel

theorem preprocessed_luo_terminal_compression
    {p a : Nat} (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256) (hpBits : bitLength p = 256)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ tau, 0 < tau ∧
      tau = 4 * euclidWeight p (normalizedInput p a) ∧
      1024 ≤ tau ∧ tau ≤ 1620 ∧
      (∀ k, k < tau →
        ¬ Terminal (run 9 9 k (preprocessedState p a))) ∧
      Terminal (run 9 9 tau (preprocessedState p a)) ∧
      (run 9 9 tau (preprocessedState p a)).shift = 0 ∧
      1620 - tau ≤ 596 ∧
      (1620 - tau) % 4 = 0 ∧
      compressedEpoch 9 (1620 - tau) = 0 := by
  have hrounds := preprocessed_luo_round_bound hpPrime hpFit ha0 ha
  obtain ⟨tau, htau, htauExact, htauUpper, hlive, hterminal, hshift,
      haligned⟩ :=
    preprocessed_terminal_suffix
      (n := 256) (lengthWidth := 9) (shiftWidth := 9) (rounds := 1620)
      hpFit (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      ha0 ha hrounds (by norm_num)
  have hweightLower := preprocessed_euclidWeight_lower hpPrime ha0 ha
  rw [hpBits] at hweightLower
  have htauLower : 1024 ≤ tau := by
    rw [htauExact]
    omega
  have hdepth : 1620 - tau ≤ 596 := by omega
  have hfit : 1620 - tau < 2 ^ (9 + 1) := by norm_num; omega
  have hcompressed : compressedEpoch 9 (1620 - tau) = 0 :=
    compression_clears_epoch (by norm_num) hfit haligned
  exact ⟨tau, htau, htauExact, htauLower, htauUpper, hlive, hterminal,
    hshift, hdepth, haligned, hcompressed⟩

end VQMathlib.Euclid.LuoTerminalCompression
