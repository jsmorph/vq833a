import VQ.Euclid.State

namespace VQ
namespace Euclid

structure StepDomain
    (p n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  valid : Valid n lengthWidth shiftWidth s
  relation : Relation p s
  modulusPositive : 0 < p
  modulusFits : p < 2 ^ n
  coefficientOrder :
    s.phase1 = true → s.phase2 = true → s.t ≤ s.tPrime
  terminalNoWrap : Terminal s → s.shift + 1 < 2 ^ shiftWidth

def EarlyCoefficientOrder (s : State) : Prop :=
  s.phase1 = false → 0 < s.rPrime → s.tPrime < s.t

def PhaseOneReachable (n : Nat) (s : State) : Prop :=
  s.phase1 = false → s.phase2 = true →
    s.lenT + 1 + s.lenQ + s.lenRPrime + s.shift ≤ workWidth n ∧
      (s.lenQ = 0 → shifted s.rPrime (s.shift - 1) ≤ s.r)

def LateCoefficientOrder (s : State) : Prop :=
  s.phase1 = true → s.phase2 = true → 0 < s.r → s.t < s.tPrime

def NormalizedFirstDivisor (p : Nat) (s : State) : Prop :=
  s.tPrime = 0 → 2 * s.rPrime * s.t ≤ p

def PhaseFourLowerBound (s : State) : Prop :=
  s.phase1 = true → s.phase2 = true →
    shifted s.t (s.shift - 1) ≤ s.tPrime

def PositiveLiveCoefficient (s : State) : Prop :=
  0 < s.rPrime → 0 < s.t

structure ReachableStepDomain
    (p n lengthWidth shiftWidth : Nat) (s : State) : Prop where
  stepDomain : StepDomain p n lengthWidth shiftWidth s
  earlyCoefficientOrder : EarlyCoefficientOrder s
  phaseOneReachable : PhaseOneReachable n s
  lateCoefficientOrder : LateCoefficientOrder s
  normalizedFirstDivisor : NormalizedFirstDivisor p s
  phaseFourLowerBound : PhaseFourLowerBound s
  positiveLiveCoefficient : PositiveLiveCoefficient s

namespace StepDomain

open Reversible

theorem terminal_nextCounter
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hterminal : Terminal s) :
    nextCounter shiftWidth s.shift = s.shift + 1 := by
  exact nextCounter_eq_add_one (h.terminalNoWrap hterminal)

theorem terminal_nextCounter_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hterminal : Terminal s) :
    0 < nextCounter shiftWidth s.shift := by
  rw [terminal_nextCounter h hterminal]
  omega

theorem increment_noWrap
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase2 : s.phase2 = false) :
    s.shift + 1 < 2 ^ shiftWidth := by
  have hpowers : 2 ^ lengthWidth ≤ 2 ^ shiftWidth :=
    Nat.pow_le_pow_right (by omega) hwidths
  cases hphase1 : s.phase1
  · have hready := h.valid.2
    simp [PhaseReady, hphase1, hphase2] at hready
    rcases hready with
      ⟨hsign, hq, hlenQ, hrPrimeZero | hrPrimePositive⟩
    · apply h.terminalNoWrap
      have hlenRPrime : s.lenRPrime = 0 := by
        rw [h.valid.1.2.1, bitLength_eq_zero_iff]
        exact hrPrimeZero
      exact ⟨hrPrimeZero, hlenRPrime, hq, hlenQ,
        hphase1, hphase2, hsign⟩
    · omega
  · have hready := h.valid.2
    simp [PhaseReady, hphase1, hphase2] at hready
    omega

theorem increment_nextCounter
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase2 : s.phase2 = false) :
    nextCounter shiftWidth s.shift = s.shift + 1 := by
  exact nextCounter_eq_add_one
    (increment_noWrap h hwork hwidths hphase2)

theorem relation_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s) :
    Relation p (step lengthWidth shiftWidth s) :=
  relation_step_of_valid h.relation h.valid

theorem remainderCoefficientProduct_lt
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s) :
    s.r * s.t < 2 ^ n := by
  have hrelation := h.relation
  unfold Relation at hrelation
  have hle : s.r * s.t ≤ p := by omega
  exact hle.trans_lt h.modulusFits

theorem shift_lt_bitLength_of_shifted_le
    {x y shift : Nat} (hx : 0 < x)
    (hxy : shifted x shift ≤ y) :
    shift < bitLength y := by
  have hshifted : 0 < shifted x shift :=
    Nat.mul_pos (Nat.two_pow_pos shift) hx
  have hy : 0 < y := hshifted.trans_le hxy
  have hpow : 2 ^ shift ≤ y := by
    calc
      2 ^ shift ≤ 2 ^ shift * x := Nat.le_mul_of_pos_right _ hx
      _ = shifted x shift := rfl
      _ ≤ y := hxy
  have hlog : shift ≤ Nat.log2 y :=
    (Nat.le_log2 (Nat.ne_of_gt hy)).2 hpow
  rw [bitLength, if_neg (Nat.ne_of_gt hy)]
  omega

theorem phaseFour_rPrime_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    0 < s.rPrime := by
  have hready := h.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  exact hready.1

theorem phaseFour_q_zero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    s.q = 0 := by
  have hready := h.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  exact hready.2.1

theorem phaseFour_tPrime_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    0 < s.tPrime := by
  have hq := phaseFour_q_zero h hphase1 hphase2
  have horder := h.coefficientOrder hphase1 hphase2
  by_contra hnot
  have htPrime : s.tPrime = 0 := Nat.eq_zero_of_not_pos hnot
  have ht : s.t = 0 := by omega
  have hrelation := h.relation
  simp [Relation, htPrime, ht, hq] at hrelation
  have hp := h.modulusPositive
  omega

theorem phaseFour_product_lt
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (_hphase1 : s.phase1 = true) (_hphase2 : s.phase2 = true) :
    s.rPrime * s.tPrime < 2 ^ n := by
  have hrelation := h.relation
  unfold Relation at hrelation
  have hle : s.rPrime * s.tPrime ≤ p := by omega
  exact hle.trans_lt h.modulusFits

theorem phaseFour_bitLength_sum
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    bitLength s.rPrime + bitLength s.tPrime ≤ n + 1 := by
  exact bitLength_add_le_of_mul_lt_two_pow
    (phaseFour_rPrime_pos h hphase1 hphase2)
    (phaseFour_tPrime_pos h hphase1 hphase2)
    (phaseFour_product_lt h hphase1 hphase2)

theorem phaseFour_stored_length_sum
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    s.lenT + s.lenRPrime ≤ n + 1 := by
  have hsum := phaseFour_bitLength_sum h hphase1 hphase2
  have hmono := bitLength_mono (h.coefficientOrder hphase1 hphase2)
  have hpacked := h.valid.1
  rw [hpacked.1, hpacked.2.1]
  omega

theorem phaseFour_length_core
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    0 < s.tPrime ∧
      s.lenT ≤ bitLength s.tPrime ∧
      bitLength s.r ≤ s.lenRPrime ∧
      bitLength s.tPrime + s.lenRPrime ≤ n + 1 := by
  have htPrime := phaseFour_tPrime_pos h hphase1 hphase2
  have ht := bitLength_mono (h.coefficientOrder hphase1 hphase2)
  have hready := h.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hr := bitLength_mono (Nat.le_of_lt hready.2.2.2.2.2.1)
  have hsum := phaseFour_bitLength_sum h hphase1 hphase2
  rw [← h.valid.1.1] at ht
  rw [← h.valid.1.2.1] at hr
  rw [← h.valid.1.2.1] at hsum
  exact ⟨htPrime, ht, hr, by omega⟩

theorem phaseFour_r_length_le
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    bitLength s.r ≤ s.lenRPrime := by
  have hready := h.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hmono := bitLength_mono (Nat.le_of_lt hready.2.2.2.2.2.1)
  rw [h.valid.1.2.1]
  exact hmono

theorem phaseFour_tPrime_length_with_r
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    bitLength s.tPrime + bitLength s.r ≤ n + 1 := by
  have hsum := phaseFour_bitLength_sum h hphase1 hphase2
  have hr := phaseFour_r_length_le h hphase1 hphase2
  rw [h.valid.1.2.1] at hr
  omega

theorem phaseFour_upperBoundary_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    1 ≤ workWidth n - s.lenRPrime := by
  have hsum := phaseFour_stored_length_sum h hphase1 hphase2
  simp only [workWidth]
  omega

theorem phaseFour_lenT_le_upperBoundary
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    s.lenT ≤ workWidth n - s.lenRPrime := by
  have hsum := phaseFour_stored_length_sum h hphase1 hphase2
  simp only [workWidth]
  omega

theorem phaseFour_tPrime_le_upperBoundary
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    bitLength s.tPrime ≤ workWidth n - s.lenRPrime := by
  have hsum := phaseFour_bitLength_sum h hphase1 hphase2
  rw [← h.valid.1.2.1] at hsum
  simp only [workWidth]
  omega

theorem phaseFour_lowerBoundary_le
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    bitLength s.tPrime + 2 ≤ n + 2 := by
  have hsum := phaseFour_bitLength_sum h hphase1 hphase2
  have hpositive := bitLength_pos
    (phaseFour_rPrime_pos h hphase1 hphase2)
  omega

theorem work1_split_facts
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hlenQ : s.lenQ = 0) :
    let split := s.lenT + 1
    split ≤ workWidth n ∧
      s.t < 2 ^ split ∧
      bitLength s.r ≤ workWidth n - split := by
  rcases hpacked with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, htFit, _hqShift,
      _hlenQValue, hrFit, _htPrimeFit, _hrPrimeFit⟩
  dsimp only
  have hsplit : s.lenT + 1 ≤ workWidth n := by
    simpa [hlenQ] using hallocation
  have htPower : 2 ^ s.lenT ≤ 2 ^ (s.lenT + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hrLength := bitLength_le_of_lt_two_pow hrFit
  simp [hlenQ] at hrLength
  exact ⟨hsplit, htFit.trans_le htPower, hrLength⟩

theorem work2_split_facts
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s) :
    let split := workWidth n - s.lenRPrime
    split ≤ workWidth n ∧
      s.tPrime < 2 ^ split ∧
      bitLength s.rPrime ≤ workWidth n - split := by
  rcases hpacked with
    ⟨_hlenT, hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, hlenRPrimeWork, _htFit, _hqShift,
      _hlenQValue, _hrFit, htPrimeFit, _hrPrimeFit⟩
  dsimp only
  refine ⟨Nat.sub_le _ _, htPrimeFit, ?_⟩
  rw [← hlenRPrime]
  omega

theorem ownershipUpperCancelFacts
    {n lenT lenTPrime lenR lenRPrime : Nat}
    (hT : lenT ≤ lenTPrime) (hR : lenR ≤ lenRPrime)
    (hRpos : 0 < lenRPrime)
    (hscale : lenTPrime + lenRPrime ≤ n + 1) :
    let width := workWidth n
    let split := lenT + 1
    let boundary := width - lenRPrime
    split ≤ width ∧
      lenT ≤ split ∧
      lenT ≤ boundary ∧
      boundary ≤ split + (width - split - lenR) ∧
      1 ≤ boundary ∧
      boundary ≤ n + 2 := by
  simp only [workWidth]
  omega

theorem ownershipUpperNewFacts
    {n lenTPrime lenRPrime : Nat}
    (hRpos : 0 < lenRPrime)
    (hscale : lenTPrime + lenRPrime ≤ n + 1) :
    let width := workWidth n
    let split := width - lenRPrime
    let boundary := split
    split ≤ width ∧
      lenTPrime ≤ split ∧
      lenTPrime ≤ boundary ∧
      boundary ≤ split + (width - split - lenRPrime) ∧
      1 ≤ boundary ∧
      boundary ≤ n + 2 := by
  simp only [workWidth]
  omega

theorem ownershipLowerCancelFacts
    {n lenTPrime lenRPrime : Nat}
    (hRpos : 0 < lenRPrime)
    (hscale : lenTPrime + lenRPrime ≤ n + 1) :
    let width := workWidth n
    let split := width - lenRPrime
    let boundary := lenTPrime + 2
    split ≤ width ∧
      lenRPrime ≤ width - split ∧
      lenTPrime < boundary ∧
      boundary ≤ split + (width - split - lenRPrime) + 1 ∧
      1 ≤ boundary ∧
      boundary ≤ n + 2 := by
  simp only [workWidth]
  omega

theorem ownershipLowerNewFacts
    {n lenT lenTPrime lenR lenRPrime : Nat}
    (hT : lenT ≤ lenTPrime) (hR : lenR ≤ lenRPrime)
    (hRpos : 0 < lenRPrime)
    (hscale : lenTPrime + lenRPrime ≤ n + 1) :
    let width := workWidth n
    let split := lenT + 1
    let boundary := lenTPrime + 2
    split ≤ width ∧
      lenR ≤ width - split ∧
      lenT < boundary ∧
      boundary ≤ split + (width - split - lenR) + 1 ∧
      1 ≤ boundary ∧
      boundary ≤ n + 2 := by
  simp only [workWidth]
  omega

theorem upperBoundary_encodeLength
    {n width length : Nat}
    (hpos : 0 < length) (hfit : length < 2 ^ width)
    (hle : length ≤ n + 3) :
    n + 2 - encodeLength width length = workWidth n - length := by
  have hpred : length - 1 < 2 ^ width := by omega
  rw [encodeLength, if_neg (Nat.ne_of_gt hpos), Nat.mod_eq_of_lt hpred]
  simp only [workWidth]
  omega

theorem lowerBoundary_encodeLength
    {width length : Nat}
    (hpos : 0 < length) (hfit : length + 2 < 2 ^ width) :
    (readField 3 0 width + encodeLength width length) % 2 ^ width =
      length + 2 := by
  have hthree : 3 < 2 ^ width := by omega
  have hpred : length - 1 < 2 ^ width := by omega
  rw [readField_zero, Nat.mod_eq_of_lt hthree, encodeLength,
    if_neg (Nat.ne_of_gt hpos), Nat.mod_eq_of_lt hpred,
    show 3 + (length - 1) = length + 2 by omega,
    Nat.mod_eq_of_lt hfit]

theorem terminal_iff_rPrime_eq_zero
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : StepDomain p n lengthWidth shiftWidth s) :
    Terminal s ↔ s.rPrime = 0 := by
  constructor
  · exact fun hterminal => hterminal.1
  · intro hz
    have hpacked := h.valid.1
    have hready := h.valid.2
    cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
    · have hlenRPrime : s.lenRPrime = 0 := by
        calc
          s.lenRPrime = bitLength s.rPrime := hpacked.2.1
          _ = 0 := by rw [hz]; rfl
      simp [PhaseReady, hphase1, hphase2] at hready
      exact ⟨hz, hlenRPrime, hready.2.1, hready.2.2.1,
        hphase1, hphase2, hready.1⟩
    · simp [PhaseReady, hphase1, hphase2, hz] at hready
    · simp [PhaseReady, hphase1, hphase2, hz] at hready
    · simp [PhaseReady, hphase1, hphase2, hz] at hready

end StepDomain

namespace ReachableStepDomain

open Reversible

theorem phaseOne_window
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    s.lenT + 1 + s.lenQ + s.lenRPrime + s.shift ≤ workWidth n :=
  (h.phaseOneReachable hphase1 hphase2).1

theorem phaseOne_firstBit
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hlenQ : s.lenQ = 0) :
    shifted s.rPrime (s.shift - 1) ≤ s.r :=
  (h.phaseOneReachable hphase1 hphase2).2 hlenQ

theorem phaseOne_stateFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    0 < s.rPrime ∧ 0 < s.shift ∧ s.shift < workWidth n := by
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  exact ⟨hready.2.1, hready.2.2.1, hready.2.2.2.1⟩

theorem phaseOne_tPrime_lt_t
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    s.tPrime < s.t := by
  exact h.earlyCoefficientOrder hphase1
    (phaseOne_stateFacts h hphase1 hphase2).1

theorem phaseZero_t_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hrPrime : 0 < s.rPrime) :
    0 < s.t := by
  have horder := h.earlyCoefficientOrder hphase1 hrPrime
  omega

theorem phaseZero_length_shift_le
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    s.lenT + s.shift ≤ n := by
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  rcases hready.2.2.2 with hrPrimeZero | hlive
  · omega
  · have hrPos : 0 < s.r := by
      have hshifted : 0 < shifted s.rPrime s.shift :=
        Nat.mul_pos (Nat.two_pow_pos s.shift) hrPrime
      exact hshifted.trans_le hlive.2.2
    have htPos := phaseZero_t_pos h hphase1 hrPrime
    have hsum := bitLength_add_le_of_mul_lt_two_pow hrPos htPos
      (StepDomain.remainderCoefficientProduct_lt h.stepDomain)
    have hshift := StepDomain.shift_lt_bitLength_of_shifted_le
      hrPrime hlive.2.2
    rw [← h.stepDomain.valid.1.1] at hsum
    omega

theorem phaseZero_nextWindow
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    s.lenT + 1 + s.lenRPrime + (s.shift + 1) ≤ workWidth n := by
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  rcases hready.2.2.2 with hrPrimeZero | hlive
  · omega
  · have hshiftedPos : 0 < shifted s.rPrime s.shift :=
      Nat.mul_pos (Nat.two_pow_pos s.shift) hrPrime
    have htPos := phaseZero_t_pos h hphase1 hrPrime
    have hproduct : shifted s.rPrime s.shift * s.t < 2 ^ n :=
      (Nat.mul_le_mul_right s.t hlive.2.2).trans_lt
        (StepDomain.remainderCoefficientProduct_lt h.stepDomain)
    have hsum := bitLength_add_le_of_mul_lt_two_pow
      hshiftedPos htPos hproduct
    rw [bitLength_shifted hrPrime s.shift,
      ← h.stepDomain.valid.1.1,
      ← h.stepDomain.valid.1.2.1] at hsum
    simp only [workWidth]
    omega

theorem phaseZero_liveFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    s.q = 0 ∧ s.lenQ = 0 ∧ s.shift < workWidth n ∧
      shifted s.rPrime s.shift ≤ s.r := by
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  rcases hready.2.2.2 with hrPrimeZero | hlive
  · omega
  · exact ⟨hready.2.1, hready.2.2.1, hlive.2.1, hlive.2.2⟩

theorem phaseZero_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false) :
    step lengthWidth shiftWidth s =
      { s with
        shift := s.shift + 1
        phase2 := decide
          (s.r < shifted s.rPrime (s.shift + 1))
        sign := false } := by
  simp [step, hphase1, hphase2,
    StepDomain.increment_nextCounter h.stepDomain hwork hwidths hphase2]

theorem phaseZero_packed_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false) :
    Packed n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  rw [phaseZero_step_eq h hwork hwidths hphase1 hphase2]
  unfold Packed
  dsimp only
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      _hshiftFit, hallocation, hwork2Allocation, htFit,
      _hq, _hlenQ, hrFit, htPrimeFit, hrPrimeFit⟩
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  refine ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
    StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2,
    hallocation, hwork2Allocation, htFit, ?_, ?_, hrFit,
    htPrimeFit, hrPrimeFit⟩
  · simp [hready.2.1]
  · simp [hready.2.1, hready.2.2.1, bitLength]

theorem phaseZero_phaseReady_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    PhaseReady n (step lengthWidth shiftWidth s) := by
  rw [phaseZero_step_eq h hwork hwidths hphase1 hphase2]
  have hlive := phaseZero_liveFacts h hphase1 hphase2 hrPrime
  have hnextWindow := phaseZero_nextWindow h hphase1 hphase2 hrPrime
  have hshiftBound : s.shift + 1 < workWidth n := by omega
  by_cases hcross : s.r < shifted s.rPrime (s.shift + 1)
  · simp [PhaseReady, hphase1, hcross, hrPrime, hshiftBound]
  · have hcomparison : shifted s.rPrime (s.shift + 1) ≤ s.r :=
      Nat.le_of_not_gt hcross
    simp [PhaseReady, hphase1, hcross, hlive.1, hlive.2.1, hrPrime,
      hshiftBound, hcomparison]

theorem phaseZero_stepDomain_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    StepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  have hstep := phaseZero_step_eq h hwork hwidths hphase1 hphase2
  have houtPhase1 :
      (step lengthWidth shiftWidth s).phase1 = false := by
    rw [hstep]
    exact hphase1
  refine
    { valid := ⟨phaseZero_packed_after_step
          h hwork hwidths hphase1 hphase2,
        phaseZero_phaseReady_after_step
          h hwork hwidths hphase1 hphase2 hrPrime⟩
      relation := StepDomain.relation_after_step h.stepDomain
      modulusPositive := h.stepDomain.modulusPositive
      modulusFits := h.stepDomain.modulusFits
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · intro hout1 _hout2
    rw [houtPhase1] at hout1
    contradiction
  · intro hterminal
    have hrPrimeZero :
        (step lengthWidth shiftWidth s).rPrime = 0 := hterminal.1
    rw [hstep] at hrPrimeZero
    dsimp only at hrPrimeZero
    omega

theorem phaseZero_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  have hstep := phaseZero_step_eq h hwork hwidths hphase1 hphase2
  have hwindow := phaseZero_nextWindow h hphase1 hphase2 hrPrime
  rcases phaseZero_liveFacts h hphase1 hphase2 hrPrime with
    ⟨_hq, hlenQ, _hshiftBound, hcomparison⟩
  refine
    { stepDomain := phaseZero_stepDomain_after_step
        h hwork hwidths hphase1 hphase2 hrPrime
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · unfold EarlyCoefficientOrder
    rw [hstep]
    dsimp only
    intro _houtPhase1 _houtRPrime
    exact h.earlyCoefficientOrder hphase1 hrPrime
  · unfold PhaseOneReachable
    rw [hstep]
    dsimp only
    intro _houtPhase1 _houtPhase2
    constructor
    · omega
    · intro _houtLenQZero
      simpa using hcomparison
  · unfold LateCoefficientOrder
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2 _houtR
    rw [hphase1] at houtPhase1
    contradiction
  · unfold NormalizedFirstDivisor
    rw [hstep]
    dsimp only
    exact h.normalizedFirstDivisor
  · unfold PhaseFourLowerBound
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2
    rw [hphase1] at houtPhase1
    contradiction
  · unfold PositiveLiveCoefficient
    rw [hstep]
    dsimp only
    exact h.positiveLiveCoefficient

theorem phaseZero_remainderEndpointFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hrPrime : 0 < s.rPrime) :
    let left := s.lenT + 1
    let right := n + 1 - s.shift
    left ≤ right ∧ right < workWidth n := by
  have hlength := phaseZero_length_shift_le h hphase1 hphase2 hrPrime
  simp only [workWidth]
  omega

theorem phaseOne_remainderEndpointFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    left ≤ right ∧ right < workWidth n ∧
      s.lenRPrime ≤ right - left := by
  have hwindow := phaseOne_window h hphase1 hphase2
  have hshift := (phaseOne_stateFacts h hphase1 hphase2).2.1
  omega

theorem phaseOne_lenQ_noWrap
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    s.lenQ + 1 < 2 ^ lengthWidth := by
  have hwindow := phaseOne_window h hphase1 hphase2
  omega

theorem phaseOne_nextCounter
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    nextCounter lengthWidth s.lenQ = s.lenQ + 1 := by
  exact nextCounter_eq_add_one
    (phaseOne_lenQ_noWrap h hwork hphase1 hphase2)

theorem phaseOne_previousCounter
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    previousCounter shiftWidth s.shift = s.shift - 1 := by
  exact previousCounter_eq_sub_one
    (phaseOne_stateFacts h hphase1 hphase2).2.1
    h.stepDomain.valid.1.2.2.2.2.2.1

theorem phaseOne_quotientLength_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let take := decide (shifted s.rPrime k ≤ s.r)
    s.lenQ + 1 = bitLength
      ((if take then s.q + 2 ^ k else s.q) >>> k) := by
  dsimp only
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      hq, hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  apply quotientExtension_bitLength
    (take := decide
      (shifted s.rPrime (s.shift - 1) ≤ s.r))
    (phaseOne_stateFacts h hphase1 hphase2).2.1 hq hlenQ
  intro hlenQZero
  exact decide_eq_true
    (phaseOne_firstBit h hphase1 hphase2 hlenQZero)

theorem phaseOne_remainder_after_step_lt_shifted
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let d := shifted s.rPrime k
    let take := decide (d ≤ s.r)
    (if take then s.r - d else s.r) < d := by
  dsimp only
  have hindex : s.shift - 1 + 1 = s.shift := by
    exact Nat.sub_add_cancel
      (phaseOne_stateFacts h hphase1 hphase2).2.1
  have hready := h.stepDomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hremainder :
      s.r < shifted s.rPrime (s.shift - 1 + 1) := by
    simpa [hindex] using hready.2.2.2.2
  rw [shifted_succ] at hremainder
  by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
  · simp [htake]
    omega
  · have hlt : s.r < shifted s.rPrime (s.shift - 1) :=
      Nat.lt_of_not_ge htake
    simp [htake, hlt]

theorem phaseOne_remainderFit_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let d := shifted s.rPrime k
    let take := decide (d ≤ s.r)
    (if take then s.r - d else s.r) <
      2 ^ (workWidth n - (s.lenT + 1 + (s.lenQ + 1))) := by
  dsimp only
  have htrial := phaseOne_remainder_after_step_lt_shifted h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      _hq, _hlenQ, _hrFit, _htPrimeFit, hrPrimeFit⟩
  have htrialFit := shifted_lt_two_pow_add
    (k := s.shift - 1) hrPrimeFit
  have hexponent :
      s.lenRPrime + (s.shift - 1) ≤
        workWidth n - (s.lenT + 1 + (s.lenQ + 1)) := by
    have hwindow := phaseOne_window h hphase1 hphase2
    have hshift := (phaseOne_stateFacts h hphase1 hphase2).2.1
    omega
  exact htrial.trans <| htrialFit.trans_le <|
    Nat.pow_le_pow_right (by omega) hexponent

theorem phaseOne_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    step lengthWidth shiftWidth s =
      { s with
        q := if shifted s.rPrime (s.shift - 1) ≤ s.r then
          s.q + 2 ^ (s.shift - 1) else s.q
        r := if shifted s.rPrime (s.shift - 1) ≤ s.r then
          s.r - shifted s.rPrime (s.shift - 1) else s.r
        lenQ := s.lenQ + 1
        shift := s.shift - 1
        phase1 := decide (s.shift - 1 = 0)
        phase2 := decide (s.shift - 1 ≠ 0)
        sign := false } := by
  simp [step, hphase1, hphase2,
    phaseOne_previousCounter h hphase1 hphase2,
    phaseOne_nextCounter h hwork hphase1 hphase2]

theorem phaseOne_packed_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    Packed n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  rw [phaseOne_step_eq h hwork hphase1 hphase2]
  unfold Packed
  dsimp only
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, hlenTFit, _hlenQFit, hlenRPrimeFit,
      hshiftFit, _hallocation, hwork2Allocation, htFit,
      hq, _hlenQ, _hrFit, htPrimeFit, hrPrimeFit⟩
  have hqk : s.q % 2 ^ (s.shift - 1) = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact (Nat.pow_dvd_pow 2 (Nat.sub_le s.shift 1)).trans
      (Nat.dvd_of_mod_eq_zero hq)
  have hqNext :
      (if shifted s.rPrime (s.shift - 1) ≤ s.r then
          s.q + 2 ^ (s.shift - 1) else s.q) %
        2 ^ (s.shift - 1) = 0 := by
    by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
    · simp [htake, hqk]
    · simp [htake, hqk]
  refine ⟨hlenT, hlenRPrime,
    hlenTFit,
    phaseOne_lenQ_noWrap h hwork hphase1 hphase2,
    hlenRPrimeFit,
    ?_, ?_, hwork2Allocation, htFit, hqNext, ?_, ?_,
    htPrimeFit, hrPrimeFit⟩
  · omega
  · have hwindow := phaseOne_window h hphase1 hphase2
    have hshift := (phaseOne_stateFacts h hphase1 hphase2).2.1
    omega
  · simpa using phaseOne_quotientLength_after_step h hphase1 hphase2
  · simpa using phaseOne_remainderFit_after_step h hphase1 hphase2

theorem phaseOne_work1_after_quotientInsertion
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    let k := s.shift - 1
    let left := s.lenT + 1 + s.lenQ
    let right := workWidth n - s.shift
    let width := right - left + 1
    let take := shifted s.rPrime k ≤ s.r
    let resultWord :=
      if take then s.r >>> k - s.rPrime else s.r >>> k
    let takeBit := if take then 1 else 0
    writeField
        (writeField (encodeWork1 n s % 2 ^ workWidth n)
          left width (reverseBits width resultWord))
        left 1 takeBit =
      encodeWork1 n (step lengthWidth shiftWidth s) %
        2 ^ workWidth n := by
  dsimp only
  let k := s.shift - 1
  let left := s.lenT + 1 + s.lenQ
  let width := workWidth n - s.shift - left + 1
  let take := shifted s.rPrime k ≤ s.r
  let newR := if take then s.r - shifted s.rPrime k else s.r
  let base := s.t |||
    reverseBits s.lenQ (s.q >>> s.shift) <<< (s.lenT + 1)
  have hwindow := phaseOne_window h hphase1 hphase2
  have hshiftPos := (phaseOne_stateFacts h hphase1 hphase2).2.1
  have hk : k + 1 = s.shift := by
    dsimp only [k]
    omega
  have hwidth : 0 < width := by
    dsimp only [width, left]
    omega
  have holdWidth :
      workWidth n - left = width + k := by
    dsimp only [width, left, k]
    omega
  have hnewWidth :
      workWidth n - (s.lenT + 1 + (s.lenQ + 1)) =
        width - 1 + k := by
    dsimp only [width, left, k]
    omega
  have hnewOffset :
      s.lenT + 1 + (s.lenQ + 1) = left + 1 := by
    dsimp only [left]
    omega
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht, hq,
      _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hbase : base < 2 ^ left := by
    have ht' : s.t < 2 ^ left :=
      ht.trans_le (Nat.pow_le_pow_right (by omega) (by
        dsimp only [left]
        omega))
    have hq' := shiftLeft_lt_two_pow (offset := s.lenT + 1)
      (reverseBits_lt s.lenQ (s.q >>> s.shift))
    have hq'' :
        reverseBits s.lenQ (s.q >>> s.shift) <<< (s.lenT + 1) <
          2 ^ left := by
      simpa [left, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hq'
    exact Nat.or_lt_two_pow ht' hq''
  have hresult :
      (if take then s.r >>> k - s.rPrime else s.r >>> k) =
        newR >>> k := by
    by_cases htake : shifted s.rPrime k ≤ s.r
    · simp [take, newR, htake, sub_shifted_shiftRight htake]
    · simp [take, newR, htake]
  have hlow : s.r % 2 ^ k = newR % 2 ^ k := by
    by_cases htake : shifted s.rPrime k ≤ s.r
    · simpa [take, newR, htake] using
        (sub_shifted_mod htake).symm
    · simp [take, newR, htake]
  have hqk : s.q % 2 ^ (k + 1) = 0 := by
    simpa [hk] using hq
  have hquotient :
      reverseBits (s.lenQ + 1)
          ((if take then s.q + 2 ^ k else s.q) >>> k) =
        reverseBits s.lenQ (s.q >>> s.shift) |||
          (if take then 1 else 0) <<< s.lenQ := by
    simpa [take, hk] using
      (reverseBits_quotientExtension
        (width := s.lenQ) (take := decide take) hqk)
  have holdFit := encodeWork1_lt ht hallocation
  have holdEncoding :
      encodeWork1 n s % 2 ^ workWidth n =
        base ||| reverseBits (width + k) s.r <<< left := by
    rw [Nat.mod_eq_of_lt holdFit]
    simp only [encodeWork1]
    rw [holdWidth]
  have hlayout := writeReversedPrefixAndBoundary
    base s.r newR left width k (decide take) hbase hwidth hlow
  simp only [decide_eq_true_eq] at hlayout
  have hshiftBit :
      ((if take then 1 else 0) <<< s.lenQ) <<< (s.lenT + 1) =
        (if take then 1 else 0) <<< left := by
    simp only [Nat.shiftLeft_eq]
    rw [show left = s.lenQ + (s.lenT + 1) by
      dsimp only [left]
      omega, pow_add]
    ring
  have hnewEncoding :
      encodeWork1 n (step lengthWidth shiftWidth s) =
        base ||| (if take then 1 else 0) <<< left |||
          reverseBits (width - 1 + k) newR <<< (left + 1) := by
    rw [phaseOne_step_eq h hwork hphase1 hphase2]
    simp only [encodeWork1]
    change s.t |||
        reverseBits (s.lenQ + 1)
            ((if take then s.q + 2 ^ k else s.q) >>> k) <<<
              (s.lenT + 1) |||
          reverseBits
              (workWidth n - (s.lenT + 1 + (s.lenQ + 1))) newR <<<
            (s.lenT + 1 + (s.lenQ + 1)) = _
    rw [hquotient, shiftLeft_or, hshiftBit, hnewWidth, hnewOffset]
    dsimp only [base]
    ac_rfl
  rcases phaseOne_packed_after_step h hwork hphase1 hphase2 with
    ⟨_hlenT', _hlenRPrime', _hlenTFit', _hlenQFit',
      _hlenRPrimeFit', _hshiftFit', hallocation',
      _hwork2Allocation', ht', _hq', _hlenQ', _hrFit',
      _htPrimeFit', _hrPrimeFit'⟩
  have hnewFit := encodeWork1_lt ht' hallocation'
  calc
    writeField
          (writeField (encodeWork1 n s % 2 ^ workWidth n)
            left width
            (reverseBits width
              (if take then s.r >>> k - s.rPrime else s.r >>> k)))
          left 1 (if take then 1 else 0) =
        base ||| (if take then 1 else 0) <<< left |||
          reverseBits (width - 1 + k) newR <<< (left + 1) := by
      rw [holdEncoding, hresult]
      exact hlayout
    _ = encodeWork1 n (step lengthWidth shiftWidth s) :=
      hnewEncoding.symm
    _ = encodeWork1 n (step lengthWidth shiftWidth s) %
        2 ^ workWidth n := by
      rw [Nat.mod_eq_of_lt hnewFit]

theorem phaseOne_phaseReady_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    PhaseReady n (step lengthWidth shiftWidth s) := by
  rw [phaseOne_step_eq h hwork hphase1 hphase2]
  have hrPrimePos := (phaseOne_stateFacts h hphase1 hphase2).1
  have hshiftBound := (phaseOne_stateFacts h hphase1 hphase2).2.2
  have hremainder := phaseOne_remainder_after_step_lt_shifted h hphase1 hphase2
  have hremainderProp :
      (if shifted s.rPrime (s.shift - 1) ≤ s.r then
          s.r - shifted s.rPrime (s.shift - 1) else s.r) <
        shifted s.rPrime (s.shift - 1) := by
    simpa only [decide_eq_true_eq] using hremainder
  have hcoefficient := phaseOne_tPrime_lt_t h hphase1 hphase2
  by_cases hk : s.shift - 1 = 0
  · have hremainderZero := hremainderProp
    simp [hk, shifted] at hremainderZero
    simp [PhaseReady, hk, shifted, hrPrimePos, hremainderZero,
      hcoefficient, workWidth]
  · have hkpos : 0 < s.shift - 1 := Nat.pos_of_ne_zero hk
    have hkbound : s.shift - 1 < workWidth n := by omega
    simp [PhaseReady, hk, hrPrimePos, hkpos, hkbound, hremainderProp]

theorem phaseOne_not_phaseFour_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    ¬((step lengthWidth shiftWidth s).phase1 = true ∧
      (step lengthWidth shiftWidth s).phase2 = true) := by
  rw [phaseOne_step_eq h hwork hphase1 hphase2]
  dsimp only
  by_cases hk : s.shift - 1 = 0 <;> simp [hk]

theorem phaseOne_stepDomain_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    StepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  refine
    { valid := ⟨phaseOne_packed_after_step h hwork hphase1 hphase2,
        phaseOne_phaseReady_after_step h hwork hphase1 hphase2⟩
      relation := StepDomain.relation_after_step h.stepDomain
      modulusPositive := h.stepDomain.modulusPositive
      modulusFits := h.stepDomain.modulusFits
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · intro hout1 hout2
    exact (phaseOne_not_phaseFour_after_step
      h hwork hphase1 hphase2 ⟨hout1, hout2⟩).elim
  · intro hterminal
    have hrPrimeZero :
        (step lengthWidth shiftWidth s).rPrime = 0 := hterminal.1
    have hrPrimeSame :
        (step lengthWidth shiftWidth s).rPrime = s.rPrime := by
      rw [phaseOne_step_eq h hwork hphase1 hphase2]
    rw [hrPrimeSame] at hrPrimeZero
    have hrPrimePos :=
      (phaseOne_stateFacts h hphase1 hphase2).1
    omega

theorem phaseOne_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  refine
    { stepDomain := phaseOne_stepDomain_after_step
        h hwork hphase1 hphase2
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · unfold EarlyCoefficientOrder
    rw [phaseOne_step_eq h hwork hphase1 hphase2]
    dsimp only
    intro _houtPhase1 _houtRPrime
    exact phaseOne_tPrime_lt_t h hphase1 hphase2
  · unfold PhaseOneReachable
    rw [phaseOne_step_eq h hwork hphase1 hphase2]
    dsimp only
    intro _houtPhase1 _houtPhase2
    constructor
    · have hwindow := phaseOne_window h hphase1 hphase2
      have hshift := (phaseOne_stateFacts h hphase1 hphase2).2.1
      omega
    · intro hlenQZero
      omega
  · unfold LateCoefficientOrder
    intro hout1 hout2 _houtR
    exact (phaseOne_not_phaseFour_after_step
      h hwork hphase1 hphase2 ⟨hout1, hout2⟩).elim
  · unfold NormalizedFirstDivisor
    rw [phaseOne_step_eq h hwork hphase1 hphase2]
    dsimp only
    exact h.normalizedFirstDivisor
  · unfold PhaseFourLowerBound
    intro hout1 hout2
    exact (phaseOne_not_phaseFour_after_step
      h hwork hphase1 hphase2 ⟨hout1, hout2⟩).elim
  · unfold PositiveLiveCoefficient
    rw [phaseOne_step_eq h hwork hphase1 hphase2]
    dsimp only
    exact h.positiveLiveCoefficient

theorem phaseTwo_stateFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.sign = false ∧ 0 < s.rPrime ∧ 0 < s.lenQ ∧
      s.shift < workWidth n ∧ s.r < s.rPrime ∧
      s.tPrime < shifted s.t s.shift := by
  have hready := h.stepDomain.valid.2
  simpa [PhaseReady, hphase1, hphase2] using hready

theorem phaseTwo_t_pos
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    0 < s.t := by
  have hlt :=
    (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.2
  have hshifted : 0 < shifted s.t s.shift := by omega
  by_contra hnot
  have ht : s.t = 0 := Nat.eq_zero_of_not_pos hnot
  simp [shifted, ht] at hshifted

theorem phaseTwo_previousLenQ
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    previousCounter lengthWidth s.lenQ = s.lenQ - 1 := by
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  exact previousCounter_eq_sub_one
    (phaseTwo_stateFacts h hphase1 hphase2).2.2.1 hlenQFit

theorem phaseTwo_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    step lengthWidth shiftWidth s =
      { s with
        q := if s.q.testBit s.shift then
          s.q - 2 ^ s.shift else s.q
        tPrime := if s.q.testBit s.shift then
          s.tPrime + shifted s.t s.shift else s.tPrime
        lenQ := s.lenQ - 1
        shift := s.shift + 1
        phase2 := decide
          (s.lenQ - 1 = 0 ∧ s.lenRPrime > 0)
        sign := decide
          (s.lenQ - 1 = 0 ∧ s.lenRPrime > 0) } := by
  simp [step, hphase1, hphase2,
    phaseTwo_previousLenQ h hphase1 hphase2,
    StepDomain.increment_nextCounter
      h.stepDomain hwork hwidths hphase2]

theorem phaseTwo_shift_lt_n
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.shift < n := by
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      hq, hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hfacts := phaseTwo_stateFacts h hphase1 hphase2
  have hxPos : 0 < s.q >>> s.shift := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : s.lenQ = 0 := by
      rw [hlenQ, hz]
      simp [bitLength]
    omega
  have hqeq : s.q = 2 ^ s.shift * (s.q >>> s.shift) := by
    calc
      s.q = 2 ^ s.shift * (s.q / 2 ^ s.shift) +
          s.q % 2 ^ s.shift :=
        (Nat.div_add_mod s.q (2 ^ s.shift)).symm
      _ = 2 ^ s.shift * (s.q >>> s.shift) := by
        simp [hq, Nat.shiftRight_eq_div_pow]
  have htPos := phaseTwo_t_pos h hphase1 hphase2
  have hqProduct : s.q * s.rPrime * s.t < 2 ^ n := by
    have hrel := h.stepDomain.relation
    unfold Relation at hrel
    have hle : s.q * s.rPrime * s.t ≤ p := by omega
    exact hle.trans_lt h.stepDomain.modulusFits
  have hpow : 2 ^ s.shift < 2 ^ n := by
    calc
      2 ^ s.shift ≤ s.q := by
        rw [hqeq]
        exact Nat.le_mul_of_pos_right _ hxPos
      _ ≤ s.q * s.rPrime * s.t := by
        have hmul : 0 < s.rPrime * s.t :=
          Nat.mul_pos hfacts.2.1 htPos
        simpa [Nat.mul_assoc] using
          Nat.le_mul_of_pos_right s.q hmul
      _ < 2 ^ n := hqProduct
  exact (Nat.pow_lt_pow_iff_right (by omega)).mp hpow

theorem phaseTwo_stored_length_sum
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.lenT + s.shift + s.lenRPrime ≤ n + 1 := by
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      hq, hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hstate := phaseTwo_stateFacts h hphase1 hphase2
  have htPos := phaseTwo_t_pos h hphase1 hphase2
  have hquotientPos : 0 < s.q >>> s.shift := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : s.lenQ = 0 := by
      rw [hlenQ, hz]
      simp [bitLength]
    omega
  have hqeq : s.q = 2 ^ s.shift * (s.q >>> s.shift) := by
    calc
      s.q = 2 ^ s.shift * (s.q / 2 ^ s.shift) +
          s.q % 2 ^ s.shift :=
        (Nat.div_add_mod s.q (2 ^ s.shift)).symm
      _ = 2 ^ s.shift * (s.q >>> s.shift) := by
        simp [hq, Nat.shiftRight_eq_div_pow]
  have hpowLe : 2 ^ s.shift ≤ s.q := by
    rw [hqeq]
    exact Nat.le_mul_of_pos_right _ hquotientPos
  have hqProduct : s.q * s.rPrime * s.t < 2 ^ n := by
    have hrel := h.stepDomain.relation
    unfold Relation at hrel
    have hle : s.q * s.rPrime * s.t ≤ p := by omega
    exact hle.trans_lt h.stepDomain.modulusFits
  have hproduct : shifted s.t s.shift * s.rPrime < 2 ^ n := by
    have hle := Nat.mul_le_mul_right (s.rPrime * s.t) hpowLe
    have hle' : shifted s.t s.shift * s.rPrime ≤
        s.q * s.rPrime * s.t := by
      simpa [shifted, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle
    exact hle'.trans_lt hqProduct
  have hshiftedPos : 0 < shifted s.t s.shift :=
    Nat.mul_pos (Nat.two_pow_pos s.shift) htPos
  have hsum := bitLength_add_le_of_mul_lt_two_pow
    hshiftedPos hstate.2.1 hproduct
  rw [bitLength_shifted htPos s.shift, ← hlenT, ← hlenRPrime] at hsum
  omega

theorem phaseTwo_coefficientWindow
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.shift + (s.lenT + 1) ≤ workWidth n - s.lenRPrime := by
  have hsum := phaseTwo_stored_length_sum h hphase1 hphase2
  simp only [workWidth]
  omega

theorem phaseTwo_work2Coefficient
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    readField (encodeWork2 n s) 0 (s.lenT + 1) =
      s.tPrime >>> s.shift := by
  have hwindow := phaseTwo_coefficientWindow h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have horder := (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.2
  have htPrime : s.tPrime < 2 ^ (s.shift + (s.lenT + 1)) := by
    have hsmall := horder.trans (shifted_lt_two_pow_add
      (x := s.t) (k := s.shift) ht)
    exact hsmall.trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact readField_encodeWork2_coefficient hwindow htPrime

theorem phaseTwo_coefficientOperandBounds
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.tPrime >>> s.shift < s.t ∧
      s.tPrime >>> s.shift + s.t < 2 ^ (s.lenT + 1) := by
  have horder := (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.2
  have hu : s.tPrime >>> s.shift < s.t := by
    by_contra hnot
    have hle : s.t ≤ s.tPrime >>> s.shift := Nat.le_of_not_gt hnot
    have := (shifted_le_iff_le_shiftRight
      s.t s.tPrime s.shift).2 hle
    omega
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  constructor
  · exact hu
  · rw [Nat.pow_succ]
    omega

theorem phaseTwo_work2_after_coefficientAddition
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    writeField (encodeWork2 n s) 0 (s.lenT + 1)
        (s.tPrime >>> s.shift + s.t) =
      encodeWork2 n
        { s with
          tPrime := s.tPrime + shifted s.t s.shift } := by
  apply encodeWork2_add_shifted
    (phaseTwo_coefficientWindow h hphase1 hphase2)
  have horder := (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hshifted := shifted_lt_two_pow_add
    (x := s.t) (k := s.shift) ht
  calc
    s.tPrime + shifted s.t s.shift <
        shifted s.t s.shift + shifted s.t s.shift :=
      Nat.add_lt_add_right horder _
    _ < 2 ^ (s.lenT + s.shift) + 2 ^ (s.lenT + s.shift) :=
      Nat.add_lt_add hshifted hshifted
    _ = 2 ^ (s.shift + (s.lenT + 1)) := by
      rw [show s.shift + (s.lenT + 1) =
          s.lenT + s.shift + 1 by omega,
        Nat.pow_succ]
      omega

theorem phaseTwo_quotientLength_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    s.lenQ - 1 = bitLength
      ((if s.q.testBit s.shift then s.q - 2 ^ s.shift else s.q) >>>
        (s.shift + 1)) := by
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      hq, hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hxPos : 0 < s.q >>> s.shift := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : s.lenQ = 0 := by
      rw [hlenQ, hz]
      simp [bitLength]
    have hlenQPos :=
      (phaseTwo_stateFacts h hphase1 hphase2).2.2.1
    omega
  rw [clearCurrentBit_shiftRight hq, Nat.shiftRight_add]
  rw [bitLength_shiftRight_one hxPos, ← hlenQ]

theorem phaseTwo_work1_after_quotientRemoval
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    writeField (encodeWork1 n s % 2 ^ workWidth n)
        (s.lenT + s.lenQ) 1 0 =
      encodeWork1 n (step lengthWidth shiftWidth s) %
        2 ^ workWidth n := by
  let qNew := if s.q.testBit s.shift then
    s.q - 2 ^ s.shift else s.q
  let target := s.lenT + s.lenQ
  let oldRemainderWidth :=
    workWidth n - (s.lenT + 1 + s.lenQ)
  let low := s.t |||
    reverseBits (s.lenQ - 1) (qNew >>> (s.shift + 1)) <<<
      (s.lenT + 1) |||
    reverseBits oldRemainderWidth s.r <<<
      (s.lenT + 1 + s.lenQ)
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht, hq,
      _hlenQ, hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hlenQPos :=
    (phaseTwo_stateFacts h hphase1 hphase2).2.2.1
  have holdFit := encodeWork1_lt ht hallocation
  have hnewFit :
      encodeWork1 n (step lengthWidth shiftWidth s) <
        2 ^ workWidth n := by
    rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
    apply encodeWork1_lt
    · exact ht
    · dsimp only
      omega
  have hquotient :
      reverseBits s.lenQ (s.q >>> s.shift) =
        reverseBits (s.lenQ - 1) (qNew >>> (s.shift + 1)) |||
          (if s.q.testBit s.shift then 1 else 0) <<<
            (s.lenQ - 1) := by
    dsimp only [qNew]
    rw [clearCurrentBit_shiftRight hq]
    exact reverseBits_currentQuotientDecomposition hlenQPos
  have hselectedShift :
      ((if s.q.testBit s.shift then 1 else 0) <<<
          (s.lenQ - 1)) <<< (s.lenT + 1) =
        (if s.q.testBit s.shift then 1 else 0) <<< target := by
    dsimp only [target]
    simp only [Nat.shiftLeft_eq]
    rw [show s.lenT + s.lenQ =
        (s.lenQ - 1) + (s.lenT + 1) by omega, pow_add]
    ring
  have holdEncoding :
      encodeWork1 n s =
        low ||| (if s.q.testBit s.shift then 1 else 0) <<< target := by
    simp only [encodeWork1]
    rw [hquotient, shiftLeft_or, hselectedShift]
    dsimp only [low, oldRemainderWidth]
    ac_rfl
  have hnewRemainderWidth :
      workWidth n - (s.lenT + 1 + (s.lenQ - 1)) =
        oldRemainderWidth + 1 := by
    dsimp only [oldRemainderWidth]
    omega
  have hnewRemainderOffset :
      s.lenT + 1 + (s.lenQ - 1) = target := by
    dsimp only [target]
    omega
  have holdRemainderOffset :
      s.lenT + 1 + s.lenQ = target + 1 := by
    dsimp only [target]
    omega
  have hnewRemainder :
      reverseBits
          (workWidth n - (s.lenT + 1 + (s.lenQ - 1))) s.r <<<
          (s.lenT + 1 + (s.lenQ - 1)) =
        reverseBits oldRemainderWidth s.r <<<
          (s.lenT + 1 + s.lenQ) := by
    rw [hnewRemainderWidth, reverseBits_succ_of_lt hrFit,
      hnewRemainderOffset, holdRemainderOffset]
    simp only [Nat.shiftLeft_eq, pow_succ]
    have hwidthEq :
        workWidth n - (target + 1) = oldRemainderWidth := by
      dsimp only [target, oldRemainderWidth]
      omega
    rw [hwidthEq]
    ring
  have hnewEncoding :
      encodeWork1 n (step lengthWidth shiftWidth s) = low := by
    rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
    simp only [encodeWork1]
    change s.t |||
        reverseBits (s.lenQ - 1) (qNew >>> (s.shift + 1)) <<<
            (s.lenT + 1) |||
          reverseBits
              (workWidth n - (s.lenT + 1 + (s.lenQ - 1))) s.r <<<
            (s.lenT + 1 + (s.lenQ - 1)) = low
    rw [hnewRemainder]
  have htTarget : s.t.testBit target = false := by
    apply Nat.testBit_lt_two_pow
    exact ht.trans_le (Nat.pow_le_pow_right (by omega) (by
      dsimp only [target]
      omega))
  have hquotientStart : s.lenT + 1 ≤ target := by
    dsimp only [target]
    omega
  have hquotientOutside :
      ¬target - (s.lenT + 1) < s.lenQ - 1 := by
    dsimp only [target]
    omega
  have hremainderBefore :
      ¬s.lenT + 1 + s.lenQ ≤ target := by
    dsimp only [target]
    omega
  have htargetLow : low.testBit target = false := by
    simp only [low, Nat.testBit_or, Nat.testBit_shiftLeft, htTarget,
      Bool.false_or, testBit_reverseBits]
    simp [hquotientStart, hquotientOutside, hremainderBefore]
  rw [Nat.mod_eq_of_lt holdFit, Nat.mod_eq_of_lt hnewFit,
    holdEncoding, hnewEncoding]
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b = target
  · subst b
    rw [testBit_writeField_inside (Nat.le_refl _) (by omega),
      Nat.zero_testBit, htargetLow]
  · rw [testBit_writeField_outside (by omega), Nat.testBit_or]
    cases hbit : s.q.testBit s.shift
    · simp
    · simp only [if_true, Nat.one_shiftLeft]
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hb), Bool.or_false]

theorem phaseTwo_finalQuotientFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (hfinal : s.lenQ - 1 = 0) :
    s.lenQ = 1 ∧ s.q >>> s.shift = 1 ∧
      s.q.testBit s.shift = true := by
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      _hq, hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hlenQPos := (phaseTwo_stateFacts h hphase1 hphase2).2.2.1
  have hlenQOne : s.lenQ = 1 := by omega
  have htail : s.q >>> s.shift = 1 := by
    apply bitLength_eq_one_iff.mp
    rw [← hlenQ]
    exact hlenQOne
  exact ⟨hlenQOne, htail, finalQuotientBit_true (by
    rw [htail]
    simp [bitLength, Nat.log2_eq_log_two, Nat.log_one_right])⟩

theorem phaseTwo_coefficient_lt_nextShift
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    (if s.q.testBit s.shift then
        s.tPrime + shifted s.t s.shift else s.tPrime) <
      shifted s.t (s.shift + 1) := by
  have hlt :=
    (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.2
  rw [shifted_succ]
  cases hbit : s.q.testBit s.shift <;> simp <;> omega

theorem phaseTwo_coefficientFit_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    (if s.q.testBit s.shift then
        s.tPrime + shifted s.t s.shift else s.tPrime) <
      2 ^ (workWidth n - s.lenRPrime) := by
  let tNew := if s.q.testBit s.shift then
    s.tPrime + shifted s.t s.shift else s.tPrime
  have hrel := StepDomain.relation_after_step h.stepDomain
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2] at hrel
  unfold Relation at hrel
  dsimp only at hrel
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hrPrime := (phaseTwo_stateFacts h hphase1 hphase2).2.1
  by_cases htNew : tNew = 0
  · simp [tNew, htNew]
  · have htNewPos : 0 < tNew := Nat.pos_of_ne_zero htNew
    have hle : s.rPrime * tNew ≤ p := by
      dsimp [tNew]
      omega
    have hproduct : s.rPrime * tNew < 2 ^ n :=
      hle.trans_lt h.stepDomain.modulusFits
    have hsum := bitLength_add_le_of_mul_lt_two_pow
      hrPrime htNewPos hproduct
    rw [← hlenRPrime] at hsum
    have hlength :
        bitLength tNew ≤ workWidth n - s.lenRPrime := by
      simp only [workWidth]
      omega
    exact (lt_two_pow_bitLength tNew).trans_le
      (Nat.pow_le_pow_right (by omega) hlength)

theorem phaseTwo_packed_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    Packed n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  unfold Packed
  dsimp only
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      _hshiftFit, hallocation, hwork2Allocation, htFit,
      hq, _hlenQ, hrFit, _htPrimeFit, hrPrimeFit⟩
  have hrExpanded :
      s.r < 2 ^ (workWidth n -
        (s.lenT + 1 + (s.lenQ - 1))) := by
    have hexponent :
        workWidth n - (s.lenT + 1 + s.lenQ) ≤
          workWidth n - (s.lenT + 1 + (s.lenQ - 1)) := by
      omega
    exact hrFit.trans_le
      (Nat.pow_le_pow_right (by omega) hexponent)
  refine ⟨hlenT, hlenRPrime, hlenTFit, ?_, hlenRPrimeFit,
    StepDomain.increment_noWrap h.stepDomain hwork hwidths hphase2,
    ?_, hwork2Allocation, htFit,
    clearCurrentBit_mod hq,
    phaseTwo_quotientLength_after_step h hphase1 hphase2,
    hrExpanded,
    phaseTwo_coefficientFit_after_step
      h hwork hwidths hphase1 hphase2,
    hrPrimeFit⟩
  · omega
  · omega

theorem phaseTwo_phaseReady_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    PhaseReady n (step lengthWidth shiftWidth s) := by
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  rcases phaseTwo_stateFacts h hphase1 hphase2 with
    ⟨_hsign, hrPrime, hlenQ, _hshift, hrOrder, _htOrder⟩
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      hq, hlenQValue, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hlenRPrimePos : 0 < s.lenRPrime := by
    rw [hlenRPrime]
    exact bitLength_pos hrPrime
  have hshiftBound : s.shift + 1 < workWidth n := by
    have := phaseTwo_shift_lt_n h hphase1 hphase2
    simp only [workWidth]
    omega
  have hcoefficient :=
    phaseTwo_coefficient_lt_nextShift h hphase1 hphase2
  by_cases hfinal : s.lenQ = 1
  · have hlenQZero : s.lenQ - 1 = 0 := by omega
    have hlength : bitLength (s.q >>> s.shift) = 1 := by
      rw [← hlenQValue]
      exact hfinal
    have hbit := finalQuotientBit_true hlength
    have hqZero := clearFinalQuotientBit_zero hq hlength
    have hqZero' : s.q - 2 ^ s.shift = 0 := by
      simpa [hbit] using hqZero
    have hcoefficient' :
        s.tPrime + shifted s.t s.shift <
          shifted s.t (s.shift + 1) := by
      simpa [hbit] using hcoefficient
    simp [PhaseReady, hphase1, hfinal,
      hlenRPrimePos, hbit, hqZero', hrPrime,
      hshiftBound, hrOrder, hcoefficient']
  · have hlenQPos : 0 < s.lenQ - 1 := by omega
    have hlenQNe : s.lenQ - 1 ≠ 0 := Nat.ne_of_gt hlenQPos
    simp [PhaseReady, hphase1, hlenQNe,
      hlenRPrimePos, hrPrime, hshiftBound, hrOrder, hcoefficient]
    omega

theorem phaseTwo_final_of_phaseFour_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (houtPhase2 :
      (step lengthWidth shiftWidth s).phase2 = true) :
    s.lenQ - 1 = 0 := by
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2] at houtPhase2
  dsimp only at houtPhase2
  exact (of_decide_eq_true houtPhase2).1

theorem coefficient_le_shifted (t shift : Nat) :
    t ≤ shifted t shift := by
  simpa [shifted, Nat.mul_comm] using
    Nat.le_mul_of_pos_right t (Nat.two_pow_pos shift)

theorem normalizedFirstDivisor_finalCoefficient
    {p : Nat} {s : State}
    (hrelation : Relation p s)
    (hnormalized : NormalizedFirstDivisor p s)
    (ht : 0 < s.t) (hremainder : s.r < s.rPrime)
    (hquotient : s.q >>> s.shift = 1) :
    s.t < s.tPrime + shifted s.t s.shift := by
  by_cases htPrime : 0 < s.tPrime
  · have hle := coefficient_le_shifted s.t s.shift
    omega
  · have htPrimeZero : s.tPrime = 0 := Nat.eq_zero_of_not_pos htPrime
    by_cases hshift : s.shift = 0
    · have hq : s.q = 1 := by
        simpa [hshift] using hquotient
      have hnormalized' := hnormalized htPrimeZero
      have hrelation' := hrelation
      unfold Relation at hrelation'
      simp [htPrimeZero, hq] at hrelation'
      have htwice :
          s.rPrime * s.t + s.rPrime * s.t ≤ p := by
        calc
          s.rPrime * s.t + s.rPrime * s.t =
              2 * s.rPrime * s.t := by ring
          _ ≤ p := hnormalized'
      have hproducts : s.rPrime * s.t ≤ s.r * s.t := by
        omega
      have horder : s.rPrime ≤ s.r :=
        Nat.le_of_mul_le_mul_right hproducts ht
      omega
    · have hpow : 1 < 2 ^ s.shift :=
        Nat.one_lt_two_pow hshift
      have hstrict : s.t < shifted s.t s.shift := by
        unfold shifted
        have := Nat.mul_lt_mul_of_pos_right hpow ht
        simpa using this
      omega

theorem phaseTwo_coefficientOrder_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (houtPhase2 :
      (step lengthWidth shiftWidth s).phase2 = true) :
    (step lengthWidth shiftWidth s).t ≤
      (step lengthWidth shiftWidth s).tPrime := by
  have hfinal := phaseTwo_final_of_phaseFour_after_step
    h hwork hwidths hphase1 hphase2 houtPhase2
  have hbit :=
    (phaseTwo_finalQuotientFacts h hphase1 hphase2 hfinal).2.2
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  dsimp only
  simp [hbit]
  exact (coefficient_le_shifted s.t s.shift).trans
    (Nat.le_add_left _ _)

theorem phaseTwo_normalizedFirstDivisor_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    NormalizedFirstDivisor p (step lengthWidth shiftWidth s) := by
  unfold NormalizedFirstDivisor
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  dsimp only
  intro hzero
  apply h.normalizedFirstDivisor
  cases hbit : s.q.testBit s.shift
  · simpa [hbit] using hzero
  · simp [hbit] at hzero
    omega

theorem phaseTwo_lateCoefficientOrder_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    LateCoefficientOrder (step lengthWidth shiftWidth s) := by
  unfold LateCoefficientOrder
  intro _houtPhase1 houtPhase2 _houtR
  have hfinal := phaseTwo_final_of_phaseFour_after_step
    h hwork hwidths hphase1 hphase2 houtPhase2
  rcases phaseTwo_finalQuotientFacts h hphase1 hphase2 hfinal with
    ⟨_hlenQ, hquotient, hbit⟩
  have hstrict := normalizedFirstDivisor_finalCoefficient
    h.stepDomain.relation h.normalizedFirstDivisor
    (phaseTwo_t_pos h hphase1 hphase2)
    (phaseTwo_stateFacts h hphase1 hphase2).2.2.2.2.1
    hquotient
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  dsimp only
  simpa [hbit] using hstrict

theorem phaseTwo_phaseFourLowerBound_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    PhaseFourLowerBound (step lengthWidth shiftWidth s) := by
  unfold PhaseFourLowerBound
  intro _houtPhase1 houtPhase2
  have hfinal := phaseTwo_final_of_phaseFour_after_step
    h hwork hwidths hphase1 hphase2 houtPhase2
  have hbit :=
    (phaseTwo_finalQuotientFacts h hphase1 hphase2 hfinal).2.2
  rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  dsimp only
  have hindex : s.shift + 1 - 1 = s.shift := by omega
  simp [hbit, hindex]

theorem phaseTwo_stepDomain_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    StepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  refine
    { valid := ⟨phaseTwo_packed_after_step
          h hwork hwidths hphase1 hphase2,
        phaseTwo_phaseReady_after_step
          h hwork hwidths hphase1 hphase2⟩
      relation := StepDomain.relation_after_step h.stepDomain
      modulusPositive := h.stepDomain.modulusPositive
      modulusFits := h.stepDomain.modulusFits
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · intro _houtPhase1 houtPhase2
    exact phaseTwo_coefficientOrder_after_step
      h hwork hwidths hphase1 hphase2 houtPhase2
  · intro hterminal
    have hrPrimeZero :
        (step lengthWidth shiftWidth s).rPrime = 0 := hterminal.1
    rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2] at hrPrimeZero
    dsimp only at hrPrimeZero
    have hrPrime := (phaseTwo_stateFacts h hphase1 hphase2).2.1
    omega

theorem phaseTwo_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  have hstep := phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  refine
    { stepDomain := phaseTwo_stepDomain_after_step
        h hwork hwidths hphase1 hphase2
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder :=
        phaseTwo_lateCoefficientOrder_after_step
          h hwork hwidths hphase1 hphase2
      normalizedFirstDivisor :=
        phaseTwo_normalizedFirstDivisor_after_step
          h hwork hwidths hphase1 hphase2
      phaseFourLowerBound :=
        phaseTwo_phaseFourLowerBound_after_step
          h hwork hwidths hphase1 hphase2
      positiveLiveCoefficient := ?_ }
  · unfold EarlyCoefficientOrder
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtRPrime
    rw [hphase1] at houtPhase1
    contradiction
  · unfold PhaseOneReachable
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2
    rw [hphase1] at houtPhase1
    contradiction
  · unfold PositiveLiveCoefficient
    rw [hstep]
    dsimp only
    exact h.positiveLiveCoefficient

theorem shifted_mono_right {x first last : Nat}
    (h : first ≤ last) : shifted x first ≤ shifted x last := by
  unfold shifted
  exact Nat.mul_le_mul_right x
    (Nat.pow_le_pow_right (by omega) h)

theorem phaseFour_stateFacts
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    0 < s.rPrime ∧ s.q = 0 ∧ s.lenQ = 0 ∧
      0 < s.shift ∧ s.shift < workWidth n ∧
      s.r < s.rPrime ∧
      s.sign = decide (s.tPrime < shifted s.t s.shift) := by
  have hready := h.stepDomain.valid.2
  simpa [PhaseReady, hphase1, hphase2] using hready

theorem phaseFour_coefficientIntervalFit
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    s.lenT + 1 + s.lenRPrime + s.shift ≤ workWidth n := by
  have hfacts := phaseFour_stateFacts h hphase1 hphase2
  have htPos := h.positiveLiveCoefficient hfacts.1
  have hlower := h.phaseFourLowerBound hphase1 hphase2
  have hlength := bitLength_mono hlower
  rw [bitLength_shifted htPos (s.shift - 1),
    ← h.stepDomain.valid.1.1] at hlength
  have hsum := (StepDomain.phaseFour_length_core
    h.stepDomain hphase1 hphase2).2.2.2
  simp only [workWidth]
  omega

theorem phaseFour_work1Coefficient
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    readField (encodeWork1 n s) 0
        (workWidth n - s.lenRPrime - s.shift) = s.t := by
  have hfacts := phaseFour_stateFacts h hphase1 hphase2
  have hfit := phaseFour_coefficientIntervalFit h hphase1 hphase2
  have hr := StepDomain.phaseFour_r_length_le
    h.stepDomain hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, ht,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  apply readField_encodeWork1_coefficient_padding hfacts.2.2.1 ht
  · omega
  · omega

theorem phaseFour_work2Coefficient
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    readField (encodeWork2 n s) 0
        (workWidth n - s.lenRPrime - s.shift) =
      s.tPrime >>> s.shift := by
  have hfit := phaseFour_coefficientIntervalFit h hphase1 hphase2
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hallocation, _hwork2Allocation, _ht,
      _hq, _hlenQ, _hrFit, htPrime, _hrPrimeFit⟩
  apply readField_encodeWork2_coefficient
  · omega
  · have hexponent :
        s.shift + (workWidth n - s.lenRPrime - s.shift) =
          workWidth n - s.lenRPrime := by
      omega
    rw [hexponent]
    exact htPrime

theorem phaseFour_previousCounter
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    previousCounter shiftWidth s.shift = s.shift - 1 := by
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      hshiftFit, _hallocation, _hwork2Allocation, _htFit,
      _hq, _hlenQ, _hrFit, _htPrimeFit, _hrPrimeFit⟩
  exact previousCounter_eq_sub_one
    (phaseFour_stateFacts h hphase1 hphase2).2.2.2.1
    hshiftFit

theorem phaseFour_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    step lengthWidth shiftWidth s =
      if s.shift - 1 = 0 then
        { s with
          t := s.tPrime
          q := 0
          r := s.rPrime
          tPrime := s.t
          rPrime := s.r
          lenT := bitLength s.tPrime
          lenQ := 0
          lenRPrime := bitLength s.r
          shift := 0
          phase1 := false
          phase2 := false
          iter := !s.iter
          sign := false }
      else
        { s with shift := s.shift - 1, sign := false } := by
  simp [step, hphase1, hphase2,
    phaseFour_previousCounter h hphase1 hphase2]

theorem phaseFour_swap_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    step lengthWidth shiftWidth s =
      { s with
        t := s.tPrime
        q := 0
        r := s.rPrime
        tPrime := s.t
        rPrime := s.r
        lenT := bitLength s.tPrime
        lenQ := 0
        lenRPrime := bitLength s.r
        shift := 0
        phase1 := false
        phase2 := false
        iter := !s.iter
        sign := false } := by
  rw [phaseFour_step_eq h hphase1 hphase2]
  simp [hswap]

theorem phaseFour_decrement_step_eq
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    step lengthWidth shiftWidth s =
      { s with shift := s.shift - 1, sign := false } := by
  rw [phaseFour_step_eq h hphase1 hphase2]
  simp [hdecrement]

theorem phaseFour_decrement_packed_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    Packed n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  rw [phaseFour_decrement_step_eq h hphase1 hphase2 hdecrement]
  unfold Packed
  dsimp only
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      hshiftFit, hallocation, hwork2Allocation, htFit,
      _hq, _hlenQValue, hrFit, htPrimeFit, hrPrimeFit⟩
  rcases phaseFour_stateFacts h hphase1 hphase2 with
    ⟨_hrPrime, hq, hlenQ, _hshiftPos, _hshiftBound,
      _hrOrder, _hsign⟩
  refine ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit,
    hlenRPrimeFit, ?_, hallocation, hwork2Allocation,
    htFit, ?_, ?_, hrFit, htPrimeFit, hrPrimeFit⟩
  · omega
  · simp [hq]
  · simp [hq, hlenQ, bitLength]

theorem phaseFour_decrement_phaseReady_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    PhaseReady n (step lengthWidth shiftWidth s) := by
  rw [phaseFour_decrement_step_eq h hphase1 hphase2 hdecrement]
  rcases phaseFour_stateFacts h hphase1 hphase2 with
    ⟨hrPrime, hq, hlenQ, hshiftPos, hshiftBound,
      hrOrder, _hsign⟩
  have hnextPos : 0 < s.shift - 1 := Nat.pos_of_ne_zero hdecrement
  have hnextBound : s.shift - 1 < workWidth n := by omega
  have hlower := h.phaseFourLowerBound hphase1 hphase2
  simp [PhaseReady, hphase1, hphase2, hrPrime, hq, hlenQ,
    hnextPos, hnextBound, hrOrder, hlower]

theorem phaseFour_decrement_stepDomain_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    StepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  refine
    { valid := ⟨phaseFour_decrement_packed_after_step
          h hphase1 hphase2 hdecrement,
        phaseFour_decrement_phaseReady_after_step
          h hphase1 hphase2 hdecrement⟩
      relation := StepDomain.relation_after_step h.stepDomain
      modulusPositive := h.stepDomain.modulusPositive
      modulusFits := h.stepDomain.modulusFits
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · intro _houtPhase1 _houtPhase2
    rw [phaseFour_decrement_step_eq
      h hphase1 hphase2 hdecrement]
    dsimp only
    exact h.stepDomain.coefficientOrder hphase1 hphase2
  · intro hterminal
    have hrPrimeZero :
        (step lengthWidth shiftWidth s).rPrime = 0 := hterminal.1
    rw [phaseFour_decrement_step_eq
      h hphase1 hphase2 hdecrement] at hrPrimeZero
    dsimp only at hrPrimeZero
    have hrPrime := (phaseFour_stateFacts h hphase1 hphase2).1
    omega

theorem phaseFour_decrement_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hdecrement : s.shift - 1 ≠ 0) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  have hstep := phaseFour_decrement_step_eq
    h hphase1 hphase2 hdecrement
  refine
    { stepDomain := phaseFour_decrement_stepDomain_after_step
        h hphase1 hphase2 hdecrement
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · unfold EarlyCoefficientOrder
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtRPrime
    rw [hphase1] at houtPhase1
    contradiction
  · unfold PhaseOneReachable
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2
    rw [hphase1] at houtPhase1
    contradiction
  · unfold LateCoefficientOrder
    rw [hstep]
    dsimp only
    exact h.lateCoefficientOrder
  · unfold NormalizedFirstDivisor
    rw [hstep]
    dsimp only
    intro htPrimeZero
    have htPrime := StepDomain.phaseFour_tPrime_pos
      h.stepDomain hphase1 hphase2
    omega
  · unfold PhaseFourLowerBound
    rw [hstep]
    dsimp only
    intro _houtPhase1 _houtPhase2
    have hlower := h.phaseFourLowerBound hphase1 hphase2
    exact (shifted_mono_right (Nat.sub_le (s.shift - 1) 1)).trans
      hlower
  · unfold PositiveLiveCoefficient
    rw [hstep]
    dsimp only
    exact h.positiveLiveCoefficient

theorem phaseFour_run_countdown
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hsteps : steps ≤ s.shift - 1) :
    let out := run lengthWidth shiftWidth steps s
    ReachableStepDomain p n lengthWidth shiftWidth out ∧
      out =
        { s with
          shift := s.shift - steps
          sign := if steps = 0 then s.sign else false } := by
  induction steps generalizing s with
  | zero =>
      simp [run, h]
  | succ steps ih =>
      have hdecrement : s.shift - 1 ≠ 0 := by omega
      have hstep := phaseFour_decrement_step_eq
        h hphase1 hphase2 hdecrement
      have hnext := phaseFour_decrement_reachable_after_step
        h hphase1 hphase2 hdecrement
      have hnextPhase1 :
          (step lengthWidth shiftWidth s).phase1 = true := by
        rw [hstep]
        exact hphase1
      have hnextPhase2 :
          (step lengthWidth shiftWidth s).phase2 = true := by
        rw [hstep]
        exact hphase2
      have hnextSteps :
          steps ≤ (step lengthWidth shiftWidth s).shift - 1 := by
        rw [hstep]
        dsimp only
        omega
      have hout := ih hnext hnextPhase1 hnextPhase2 hnextSteps
      constructor
      · exact hout.1
      · rw [run]
        rw [hout.2, hstep]
        cases s
        simp_all [Nat.sub_sub]
        omega

theorem phaseFour_countdown_to_one
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    let out := run lengthWidth shiftWidth (s.shift - 1) s
    ReachableStepDomain p n lengthWidth shiftWidth out ∧
      out.phase1 = true ∧ out.phase2 = true ∧
      out.shift = 1 ∧ out.lenRPrime = s.lenRPrime ∧
      out =
        { s with
          shift := 1
          sign := if s.shift = 1 then s.sign else false } := by
  have hshift := (phaseFour_stateFacts h hphase1 hphase2).2.2.2.1
  have hout := phaseFour_run_countdown h hphase1 hphase2
    (steps := s.shift - 1) (Nat.le_refl _)
  refine ⟨hout.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout.2]
    exact hphase1
  · rw [hout.2]
    exact hphase2
  · rw [hout.2]
    dsimp only
    omega
  · rw [hout.2]
  · rw [hout.2]
    have hremaining : s.shift - (s.shift - 1) = 1 := by omega
    by_cases hshiftOne : s.shift = 1
    · simp [hshiftOne]
    · have hsub : s.shift - 1 ≠ 0 := by omega
      simp [hremaining, hshiftOne, hsub]

theorem phaseFour_swap_shift_eq_one
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) : s.shift = 1 := by
  have hshift := (phaseFour_stateFacts h hphase1 hphase2).2.2.2.1
  omega

theorem phaseFour_swap_packed_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    Packed n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  rw [phaseFour_swap_step_eq h hphase1 hphase2 hswap]
  unfold Packed
  dsimp only
  rcases StepDomain.phaseFour_length_core
      h.stepDomain hphase1 hphase2 with
    ⟨htPrimePos, hlenTLe, hlenRLe, hlengthSum⟩
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, hlenRPrimeFit,
      _hshiftFit, _hallocation, hwork2Allocation, htFit,
      _hq, _hlenQValue, _hrFit, _htPrimeFit, hrPrimeFit⟩
  have hlenTPrimeFit : bitLength s.tPrime < 2 ^ lengthWidth := by
    apply Nat.lt_of_lt_of_le _ (Nat.le_of_lt hwork)
    simp only [workWidth]
    omega
  have hlenRFit : bitLength s.r < 2 ^ lengthWidth :=
    hlenRLe.trans_lt hlenRPrimeFit
  have hallocation : bitLength s.tPrime + 1 ≤ workWidth n := by
    simp only [workWidth]
    omega
  have hwork2 : bitLength s.r ≤ workWidth n :=
    hlenRLe.trans hwork2Allocation
  have hrPrimeExponent :
      s.lenRPrime ≤ workWidth n - (bitLength s.tPrime + 1) := by
    simp only [workWidth]
    omega
  have htExponent :
      s.lenT ≤ workWidth n - bitLength s.r := by
    simp only [workWidth]
    omega
  refine ⟨rfl, rfl, hlenTPrimeFit, Nat.two_pow_pos _,
    hlenRFit, Nat.two_pow_pos _, hallocation, hwork2,
    lt_two_pow_bitLength s.tPrime, ?_, ?_, ?_, ?_,
    lt_two_pow_bitLength s.r⟩
  · simp
  · simp [bitLength]
  · exact hrPrimeFit.trans_le
      (Nat.pow_le_pow_right (by omega) hrPrimeExponent)
  · exact htFit.trans_le
      (Nat.pow_le_pow_right (by omega) htExponent)

theorem phaseFour_swap_phaseReady_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    PhaseReady n (step lengthWidth shiftWidth s) := by
  rw [phaseFour_swap_step_eq h hphase1 hphase2 hswap]
  have hrOrder :=
    (phaseFour_stateFacts h hphase1 hphase2).2.2.2.2.2.1
  by_cases hr : s.r = 0
  · simp [PhaseReady, hr]
  · have hrPos : 0 < s.r := Nat.pos_of_ne_zero hr
    have hwork : 0 < workWidth n := by simp [workWidth]
    have hle : shifted s.r 0 ≤ s.rPrime := by
      simpa [shifted] using Nat.le_of_lt hrOrder
    simp [PhaseReady, hr, hrPos, hwork, hle]

theorem phaseFour_swap_stepDomain_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    StepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  refine
    { valid := ⟨phaseFour_swap_packed_after_step
          h hwork hphase1 hphase2 hswap,
        phaseFour_swap_phaseReady_after_step
          h hphase1 hphase2 hswap⟩
      relation := StepDomain.relation_after_step h.stepDomain
      modulusPositive := h.stepDomain.modulusPositive
      modulusFits := h.stepDomain.modulusFits
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · intro houtPhase1 _houtPhase2
    rw [phaseFour_swap_step_eq h hphase1 hphase2 hswap] at houtPhase1
    contradiction
  · intro _hterminal
    have hshiftOne := phaseFour_swap_shift_eq_one
      h hphase1 hphase2 hswap
    have hshiftFit := h.stepDomain.valid.1.2.2.2.2.2.1
    rw [hshiftOne] at hshiftFit
    rw [phaseFour_swap_step_eq h hphase1 hphase2 hswap]
    dsimp only
    exact hshiftFit

theorem phaseFour_swap_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hswap : s.shift - 1 = 0) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  have hstep := phaseFour_swap_step_eq h hphase1 hphase2 hswap
  refine
    { stepDomain := phaseFour_swap_stepDomain_after_step
        h hwork hphase1 hphase2 hswap
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · unfold EarlyCoefficientOrder
    rw [hstep]
    dsimp only
    intro _houtPhase1 hr
    exact h.lateCoefficientOrder hphase1 hphase2 hr
  · unfold PhaseOneReachable
    rw [hstep]
    dsimp only
    intro _houtPhase1 houtPhase2
    contradiction
  · unfold LateCoefficientOrder
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2 _houtR
    contradiction
  · unfold NormalizedFirstDivisor
    rw [hstep]
    dsimp only
    intro htZero
    have ht := h.positiveLiveCoefficient
      (phaseFour_stateFacts h hphase1 hphase2).1
    omega
  · unfold PhaseFourLowerBound
    rw [hstep]
    dsimp only
    intro houtPhase1 _houtPhase2
    contradiction
  · unfold PositiveLiveCoefficient
    rw [hstep]
    dsimp only
    intro _hr
    exact StepDomain.phaseFour_tPrime_pos
      h.stepDomain hphase1 hphase2

theorem phaseFour_reachable_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  by_cases hswap : s.shift - 1 = 0
  · exact phaseFour_swap_reachable_after_step
      h hwork hphase1 hphase2 hswap
  · exact phaseFour_decrement_reachable_after_step
      h hphase1 hphase2 hswap

theorem reachable_after_step_of_not_terminal
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ¬ Terminal s) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (step lengthWidth shiftWidth s) := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz)
    exact phaseZero_reachable_after_step
      h hwork hwidths hphase1 hphase2 hrPrime
  · exact phaseOne_reachable_after_step h hwork hphase1 hphase2
  · exact phaseTwo_reachable_after_step
      h hwork hwidths hphase1 hphase2
  · exact phaseFour_reachable_after_step h hwork hphase1 hphase2

end ReachableStepDomain
end Euclid
end VQ
