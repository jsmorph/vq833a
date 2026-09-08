import VQ.Euclid.StepDomain

namespace VQ
namespace Euclid

def normalizedInput (p a : Nat) : Nat :=
  if p / 2 < a then p - a else a

def initialIter (p a : Nat) : Bool :=
  decide (p / 2 < a)

def preprocessedState (p a : Nat) : State :=
  let x := normalizedInput p a
  { t := 1
    q := 0
    r := p
    tPrime := 0
    rPrime := x
    lenT := 1
    lenQ := 0
    lenRPrime := bitLength x
    shift := 0
    phase1 := false
    phase2 := false
    iter := initialIter p a
    sign := false }

def zeroPreparedState (p : Nat) : State :=
  { preprocessedState p 0 with iter := true }

theorem zeroPreparedState_terminal (p : Nat) :
    Terminal (zeroPreparedState p) := by
  simp [Terminal, zeroPreparedState, preprocessedState, normalizedInput,
    initialIter, bitLength]

theorem zeroPreparedState_packed
    {p n lengthWidth shiftWidth : Nat}
    (hpfit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    Packed n lengthWidth shiftWidth (zeroPreparedState p) := by
  have hlenTFit : 1 < 2 ^ lengthWidth := by
    have hwidth : 1 < workWidth n := by simp [workWidth]
    omega
  have hrFit : p < 2 ^ (workWidth n - (1 + 1 + 0)) := by
    have hexponent : n ≤ workWidth n - (1 + 1 + 0) := by
      simp [workWidth]
    exact hpfit.trans_le
      (Nat.pow_le_pow_right (by omega) hexponent)
  unfold Packed zeroPreparedState preprocessedState
  dsimp only
  refine ⟨?_, ?_, hlenTFit, Nat.two_pow_pos _, Nat.two_pow_pos _,
    Nat.two_pow_pos _, ?_, ?_, ?_, ?_, ?_, hrFit,
    Nat.two_pow_pos _, Nat.two_pow_pos _⟩ <;>
    simp [normalizedInput, bitLength, workWidth,
      Nat.log2_eq_log_two, Nat.log_one_right]

theorem normalizedInput_twice_le (p a : Nat) :
    2 * normalizedInput p a ≤ p := by
  unfold normalizedInput
  by_cases h : p / 2 < a <;> simp [h] <;> omega

theorem normalizedInput_pos {p a : Nat}
    (ha0 : 0 < a) (ha : a < p) :
    0 < normalizedInput p a := by
  unfold normalizedInput
  by_cases h : p / 2 < a <;> simp [h] <;> omega

theorem normalizedInput_lt {p a : Nat}
    (ha0 : 0 < a) (ha : a < p) :
    normalizedInput p a < p := by
  unfold normalizedInput
  by_cases h : p / 2 < a <;> simp [h] <;> omega

theorem preprocessedState_packed
    {p n lengthWidth shiftWidth a : Nat}
    (hpfit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    Packed n lengthWidth shiftWidth (preprocessedState p a) := by
  have hxPos : 0 < normalizedInput p a := normalizedInput_pos ha0 ha
  have hxFit : normalizedInput p a < 2 ^ n :=
    (normalizedInput_lt ha0 ha).trans hpfit
  have hlenX : bitLength (normalizedInput p a) ≤ n :=
    bitLength_le_of_lt_two_pow hxFit
  have hlenTFit : 1 < 2 ^ lengthWidth := by
    have hwidth : 1 < workWidth n := by simp [workWidth]
    omega
  have hlenRPrimeFit :
      bitLength (normalizedInput p a) < 2 ^ lengthWidth := by
    have hn : n < workWidth n := by simp [workWidth]
    omega
  have hrFit : p < 2 ^ (workWidth n - (1 + 1 + 0)) := by
    have hexponent : n ≤ workWidth n - (1 + 1 + 0) := by
      simp [workWidth]
    exact hpfit.trans_le
      (Nat.pow_le_pow_right (by omega) hexponent)
  unfold Packed preprocessedState
  dsimp only
  refine ⟨?_, rfl, hlenTFit, Nat.two_pow_pos _,
    hlenRPrimeFit, Nat.two_pow_pos _, ?_, ?_, ?_, ?_, ?_,
    hrFit, Nat.two_pow_pos _,
    lt_two_pow_bitLength (normalizedInput p a)⟩
  · simp [bitLength, Nat.log2_eq_log_two, Nat.log_one_right]
  · simp [workWidth]
  · simp [workWidth]
    omega
  · norm_num
  · simp
  · simp [bitLength]

theorem preprocessedState_phaseReady
    {p n a : Nat} (ha0 : 0 < a) (ha : a < p) :
    PhaseReady n (preprocessedState p a) := by
  have hxPos := normalizedInput_pos ha0 ha
  have hxLe : normalizedInput p a ≤ p :=
    Nat.le_of_lt (normalizedInput_lt ha0 ha)
  simp [PhaseReady, preprocessedState, hxPos, shifted, workWidth,
    hxLe]

theorem preprocessedState_stepDomain
    {p n lengthWidth shiftWidth a : Nat}
    (hpfit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    StepDomain p n lengthWidth shiftWidth
      (preprocessedState p a) := by
  have hp : 0 < p := ha0.trans ha
  refine
    { valid := ⟨preprocessedState_packed hpfit hwork ha0 ha,
        preprocessedState_phaseReady ha0 ha⟩
      relation := ?_
      modulusPositive := hp
      modulusFits := hpfit
      coefficientOrder := ?_
      terminalNoWrap := ?_ }
  · simp [Relation, preprocessedState]
  · intro hphase1 _hphase2
    simp [preprocessedState] at hphase1
  · intro hterminal
    have hxPos := normalizedInput_pos ha0 ha
    have hxZero : normalizedInput p a = 0 := by
      simpa [Terminal, preprocessedState] using hterminal.1
    omega

theorem preprocessedState_reachable
    {p n lengthWidth shiftWidth a : Nat}
    (hpfit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    ReachableStepDomain p n lengthWidth shiftWidth
      (preprocessedState p a) := by
  refine
    { stepDomain := preprocessedState_stepDomain hpfit hwork ha0 ha
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · simp [EarlyCoefficientOrder, preprocessedState,
      normalizedInput_pos ha0 ha]
  · simp [PhaseOneReachable, preprocessedState]
  · simp [LateCoefficientOrder, preprocessedState]
  · unfold NormalizedFirstDivisor
    simp [preprocessedState, normalizedInput_twice_le]
  · simp [PhaseFourLowerBound, preprocessedState]
  · simp [PositiveLiveCoefficient, preprocessedState]

end Euclid
end VQ
