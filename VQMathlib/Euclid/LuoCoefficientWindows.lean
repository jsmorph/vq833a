import VQ.Euclid.LuoOwnershipWindows
import VQMathlib.Euclid.LuoCoefficientBoundary
import VQMathlib.Euclid.LuoCoefficientTrace
import VQMathlib.Euclid.LuoActiveWindows

namespace VQMathlib.LuoSchedule

open VQ.Euclid.LuoWindowedOwnership
open VQ.Euclid

theorem coefficientEta_gt_half : (1 / 2 : ℝ) < coefficientEta := by
  rw [coefficientEta_eq]
  have hsqrt := sqrt_three_bounds.1
  have hlambda := lambda_bounds.1
  have hfactor : (1 / 4 : ℝ) < (4 * Real.sqrt 3 - 3) / 13 := by
    nlinarith
  have hsquare : (2 : ℝ) < lambda ^ 2 := by
    nlinarith
  have hfirst :
      (1 / 2 : ℝ) < ((4 * Real.sqrt 3 - 3) / 13) * 2 := by
    nlinarith
  have hsecond :
      ((4 * Real.sqrt 3 - 3) / 13) * 2 <
        ((4 * Real.sqrt 3 - 3) / 13) * lambda ^ 2 :=
    mul_lt_mul_of_pos_left hsquare (by nlinarith)
  exact hfirst.trans hsecond

private theorem lambda_pow_eight_gt : (2 : ℝ) ^ 5 < lambda ^ 8 := by
  let a : ℝ := 15511 / 10000
  have ha : a < lambda := lambda_bounds.1
  have hpow : (2 : ℝ) ^ 5 < a ^ 8 := by
    dsimp [a]
    norm_num
  exact hpow.trans (pow_lt_pow_left₀ ha (by norm_num [a]) (by norm_num))

private theorem lambda_pow_nineteen_gt :
    (2 : ℝ) ^ 12 < lambda ^ 19 := by
  let a : ℝ := 15511 / 10000
  have ha : a < lambda := lambda_bounds.1
  have hpow : (2 : ℝ) ^ 12 < a ^ 19 := by
    dsimp [a]
    norm_num
  exact hpow.trans (pow_lt_pow_left₀ ha (by norm_num [a]) (by norm_num))

private theorem lambda_pow_fortyNine_gt :
    (2 : ℝ) ^ 31 < lambda ^ 49 := by
  let a : ℝ := 15511 / 10000
  have ha : a < lambda := lambda_bounds.1
  have hpow : (2 : ℝ) ^ 31 < a ^ 49 := by
    dsimp [a]
    norm_num
  exact hpow.trans (pow_lt_pow_left₀ ha (by norm_num [a]) (by norm_num))

private theorem certifiedExponent_le_lambda_pow (weight : Nat) :
    (2 : ℝ) ^ (31 * (weight / 49) +
        12 * ((weight % 49) / 19) +
        5 * (((weight % 49) % 19) / 8)) ≤
      lambda ^ weight := by
  let blocks49 := weight / 49
  let remainder49 := weight % 49
  let blocks19 := remainder49 / 19
  let remainder19 := remainder49 % 19
  let blocks8 := remainder19 / 8
  let remainder8 := remainder19 % 8
  have h49 : ((2 : ℝ) ^ 31) ^ blocks49 ≤
      (lambda ^ 49) ^ blocks49 :=
    pow_le_pow_left₀ (by positivity) lambda_pow_fortyNine_gt.le blocks49
  have h19 : ((2 : ℝ) ^ 12) ^ blocks19 ≤
      (lambda ^ 19) ^ blocks19 :=
    pow_le_pow_left₀ (by positivity) lambda_pow_nineteen_gt.le blocks19
  have h8 : ((2 : ℝ) ^ 5) ^ blocks8 ≤
      (lambda ^ 8) ^ blocks8 :=
    pow_le_pow_left₀ (by positivity) lambda_pow_eight_gt.le blocks8
  have hused : 49 * blocks49 + 19 * blocks19 + 8 * blocks8 ≤ weight := by
    dsimp [blocks49, remainder49, blocks19, remainder19, blocks8, remainder8]
    omega
  change (2 : ℝ) ^ (31 * blocks49 + 12 * blocks19 + 5 * blocks8) ≤
    lambda ^ weight
  calc
    (2 : ℝ) ^ (31 * blocks49 + 12 * blocks19 + 5 * blocks8) =
        ((2 : ℝ) ^ 31) ^ blocks49 *
          ((2 : ℝ) ^ 12) ^ blocks19 *
          ((2 : ℝ) ^ 5) ^ blocks8 := by
      rw [pow_add, pow_add, pow_mul, pow_mul, pow_mul]
    _ ≤ (lambda ^ 49) ^ blocks49 *
          (lambda ^ 19) ^ blocks19 *
          (lambda ^ 8) ^ blocks8 := by
      exact mul_le_mul
        (mul_le_mul h49 h19
          (pow_nonneg (by norm_num) _)
          (pow_nonneg (pow_nonneg lambda_pos.le 49) blocks49))
        h8
        (pow_nonneg (by norm_num) _)
        (mul_nonneg
          (pow_nonneg (pow_nonneg lambda_pos.le 49) blocks49)
          (pow_nonneg (pow_nonneg lambda_pos.le 19) blocks19))
    _ = lambda ^ (49 * blocks49 + 19 * blocks19 + 8 * blocks8) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_add]
    _ ≤ lambda ^ weight :=
      (pow_le_pow_iff_right₀
        (lt_trans (by norm_num) lambda_bounds.1)).2 hused

theorem coefficientBitLower_le_bitLength
    {weight value : Nat}
    (hlower : coefficientEta * lambda ^ weight ≤ value) :
    coefficientBitLower weight ≤ bitLength value := by
  let exponent := 31 * (weight / 49) +
    12 * ((weight % 49) / 19) +
    5 * (((weight % 49) % 19) / 8)
  have hlambda := certifiedExponent_le_lambda_pow weight
  have heta : (1 / 2 : ℝ) < coefficientEta := coefficientEta_gt_half
  have hvaluePositive : 0 < value := by
    have hpositive : (0 : ℝ) < coefficientEta * lambda ^ weight :=
      mul_pos (lt_trans (by norm_num) heta) (pow_pos lambda_pos weight)
    exact_mod_cast hpositive.trans_le hlower
  by_cases hexponent : exponent = 0
  · change max 1 exponent ≤ bitLength value
    rw [hexponent]
    have := bitLength_pos hvaluePositive
    omega
  · have hexponentPositive : 0 < exponent := Nat.pos_of_ne_zero hexponent
    have hhalfPower :
        (2 : ℝ) ^ (exponent - 1) = (1 / 2) * (2 : ℝ) ^ exponent := by
      calc
        (2 : ℝ) ^ (exponent - 1) =
            (1 / 2) * ((2 : ℝ) ^ (exponent - 1) * 2) := by ring
        _ = (1 / 2) * (2 : ℝ) ^ ((exponent - 1) + 1) := by
          rw [pow_succ]
        _ = (1 / 2) * (2 : ℝ) ^ exponent := by
          congr 2
          omega
    have hpowerReal : (2 : ℝ) ^ (exponent - 1) < value := by
      calc
        (2 : ℝ) ^ (exponent - 1) =
            (1 / 2) * (2 : ℝ) ^ exponent := hhalfPower
        _ ≤ (1 / 2) * lambda ^ weight :=
          mul_le_mul_of_nonneg_left hlambda (by norm_num)
        _ < coefficientEta * lambda ^ weight :=
          mul_lt_mul_of_pos_right heta (pow_pos lambda_pos weight)
        _ ≤ value := hlower
    have hpowerNat : 2 ^ (exponent - 1) < value := by
      exact_mod_cast hpowerReal
    have hbits : exponent - 1 < bitLength value := by
      apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp
      exact hpowerNat.trans (lt_two_pow_bitLength value)
    change max 1 exponent ≤ bitLength value
    omega

theorem coefficientTrace_phaseZero_bitLength_lower
    {steps : Nat} {s : State}
    (htrace : CoefficientTrace steps s)
    (hsteps : 0 < steps)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hshift : s.shift = 0) :
    coefficientBitLower (steps / 4) ≤ bitLength s.t :=
  coefficientBitLower_le_bitLength
    (coefficientTrace_phaseZero_boundary_lower htrace hsteps
      hphase1 hphase2 hshift)

theorem coefficientTrace_phaseFour_bitLength_lower
    {steps : Nat} {s : State}
    (htrace : CoefficientTrace steps s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hshift : 0 < s.shift) :
    coefficientBitLower ((steps + s.shift) / 4) ≤ bitLength s.tPrime :=
  coefficientBitLower_le_bitLength
    (coefficientTrace_phaseFour_lower htrace hphase1 hphase2 hshift)

theorem coefficientTrace_phaseFour_remainder_growth
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hn : 0 < n) (hpLower : 2 ^ (n - 1) ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    n - s.lenRPrime ≤ (steps + s.shift) / 4 := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, _hfirst, hclock⟩
  rcases ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2 with
    ⟨hrPrime, hq, _hlenQ, _hshift, _hshiftFit, hr, _hsign⟩
  have ht : 0 < s.t := h.positiveLiveCoefficient hrPrime
  have hclock' :
      4 * (quotientWeight quotients : Int) - s.shift = steps := by
    simpa [coefficientClock, hphase1, hphase2] using hclock
  have hclockNat :
      4 * quotientWeight quotients = steps + s.shift := by
    exact_mod_cast (show
      4 * (quotientWeight quotients : Int) = steps + s.shift by omega)
  have hweight :
      quotientWeight quotients = (steps + s.shift) / 4 := by
    omega
  have hpair' : (s.tPrime, s.t) = coefficientPair quotients := by
    simpa [liveCoefficientPair, hphase1, hphase2] using hpair
  have hsum := coefficientPair_sum_le quotients hpositive
  rw [← congrArg Prod.fst hpair', ← congrArg Prod.snd hpair', hweight]
    at hsum
  have hrelation := h.stepDomain.relation
  unfold Relation at hrelation
  rw [hq] at hrelation
  simp only [Nat.zero_mul] at hrelation
  have hpPair : p < s.rPrime * (s.tPrime + s.t) := by
    calc
      p = s.r * s.t + s.rPrime * s.tPrime := hrelation.symm
      _ < s.rPrime * s.t + s.rPrime * s.tPrime :=
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hr ht) _
      _ = s.rPrime * (s.tPrime + s.t) := by ring
  have hpPower :
      p < s.rPrime * 2 ^ ((steps + s.shift) / 4) :=
    hpPair.trans_le (Nat.mul_le_mul_left s.rPrime hsum)
  have hrPrimePower : s.rPrime < 2 ^ bitLength s.rPrime :=
    lt_two_pow_bitLength s.rPrime
  have hpExponent :
      2 ^ (n - 1) <
        2 ^ ((steps + s.shift) / 4 + bitLength s.rPrime) := by
    calc
      2 ^ (n - 1) ≤ p := hpLower
      _ < s.rPrime * 2 ^ ((steps + s.shift) / 4) := hpPower
      _ < 2 ^ bitLength s.rPrime *
          2 ^ ((steps + s.shift) / 4) :=
        Nat.mul_lt_mul_of_pos_right hrPrimePower (Nat.two_pow_pos _)
      _ = 2 ^ ((steps + s.shift) / 4 + bitLength s.rPrime) := by
        rw [pow_add]
        exact Nat.mul_comm _ _
  have hexponent :
      n - 1 < (steps + s.shift) / 4 + bitLength s.rPrime :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpExponent
  have hlength : s.lenRPrime = bitLength s.rPrime :=
    h.stepDomain.valid.1.2.1
  omega

theorem coefficientTrace_phaseFour_ownership_windows
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hn : 0 < n) (hpLower : 2 ^ (n - 1) ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    1 ≤ s.lenT ∧
      workWidth n - s.lenRPrime ≤
        VQMathlib.Euclid.LuoActiveWindows.coefficientWriterUpper n
          (steps + 1) ∧
      ownershipRemainderLower (steps + 1) ≤ bitLength s.tPrime + 2 ∧
      bitLength s.tPrime + 2 ≤
        VQMathlib.Euclid.LuoActiveWindows.physicalRemainderRight n
          (bitLength s.r) ∧
      VQMathlib.Euclid.LuoActiveWindows.physicalRemainderRight n
          (bitLength s.r) ≤
        VQMathlib.Euclid.LuoActiveWindows.remainderWriterUpper n := by
  rcases ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2 with
    ⟨hrPrime, _hq, _hlenQ, hshiftPositive, _hshiftFit, _hr, _hsign⟩
  have hshift : s.shift = 1 := by omega
  have ht : 0 < s.t := h.positiveLiveCoefficient hrPrime
  have hlenT : s.lenT = bitLength s.t := h.stepDomain.valid.1.1
  have hlenTPositive : 1 ≤ s.lenT := by
    rw [hlenT]
    exact bitLength_pos ht
  have hlenRPrime : s.lenRPrime = bitLength s.rPrime :=
    h.stepDomain.valid.1.2.1
  have hlenRPrimePositive : 0 < s.lenRPrime := by
    rw [hlenRPrime]
    exact bitLength_pos hrPrime
  have hlengthSum := StepDomain.phaseFour_bitLength_sum
    h.stepDomain hphase1 hphase2
  have htPrimePositive := StepDomain.phaseFour_tPrime_pos
    h.stepDomain hphase1 hphase2
  have htPrimeLengthPositive : 0 < bitLength s.tPrime :=
    bitLength_pos htPrimePositive
  have hlenRPrimeFit : s.lenRPrime ≤ n := by
    rw [hlenRPrime]
    omega
  have htPrimeFit : bitLength s.tPrime ≤ n := by
    omega
  have hgrowth := coefficientTrace_phaseFour_remainder_growth
    h hn hpLower htrace hphase1 hphase2
  rw [hshift] at hgrowth
  have hcoefficient :=
    VQMathlib.Euclid.LuoActiveWindows.coefficientWriterInterval_contained
      (n := n) (T := steps + 1) (lower := 1)
      (coefficientLength := s.lenT) (remainderLength := s.lenRPrime)
      hlenTPositive hlenRPrimePositive hlenRPrimeFit (by simpa using hgrowth)
  have hlower := coefficientTrace_phaseFour_bitLength_lower
    htrace hphase1 hphase2 hshiftPositive
  rw [hshift] at hlower
  have hremainder :=
    VQMathlib.Euclid.LuoActiveWindows.remainderWriterInterval_contained
      (n := n) (lower := ownershipRemainderLower (steps + 1))
      (coefficientLength := bitLength s.tPrime)
      (remainderLength := bitLength s.r)
      (by simpa [ownershipRemainderLower] using Nat.add_le_add_right hlower 2)
      htPrimeFit
      (Or.inr (StepDomain.phaseFour_tPrime_length_with_r
        h.stepDomain hphase1 hphase2))
  exact ⟨hcoefficient.1, hcoefficient.2, hremainder.1,
    hremainder.2.1, hremainder.2.2⟩

def coefficientWindowCount (step : Nat) : Nat :=
  VQMathlib.Euclid.LuoCoefficientBoundary.coefficientArithmeticUpper 256 step

def coefficientWindowCellSum : Nat :=
  ((List.range 1620).map (fun index ↦ coefficientWindowCount (index + 1))).sum

def coefficientWindowRoundToffoli (step : Nat) : Nat :=
  22 * coefficientWindowCount step + 126

def coefficientWindowScheduleToffoli : Nat :=
  ((List.range 1620).map
    (fun index ↦ coefficientWindowRoundToffoli (index + 1))).sum

set_option maxRecDepth 10000 in
theorem coefficientWindowCellSum_eq : coefficientWindowCellSum = 286035 := by
  decide

set_option maxRecDepth 10000 in
theorem coefficientWindowScheduleToffoli_eq :
    coefficientWindowScheduleToffoli = 6496890 := by
  decide

theorem coefficientWindowSchedule_saving :
    1620 * (22 * 257 + 126) - coefficientWindowScheduleToffoli = 2866710 := by
  rw [coefficientWindowScheduleToffoli_eq]

end VQMathlib.LuoSchedule
