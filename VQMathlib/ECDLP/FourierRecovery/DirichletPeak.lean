import VQMathlib.ECDLP.FourierRecovery.Rounding
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace VQ.Tests.ECDLPFourierRecovery

open Finset

noncomputable def phaseRoot (delta : Real) : Complex :=
  Complex.exp (Complex.I * (2 * Real.pi * delta))

noncomputable def dirichletAmplitude (N : Nat) (delta : Real) : Complex :=
  (N : Complex)⁻¹ * ∑ x ∈ Finset.range N,
    Complex.exp (Complex.I * (2 * Real.pi * (x : Real) * delta))

noncomputable def dirichletProbability (N : Nat) (delta : Real) : Real :=
  ‖dirichletAmplitude N delta‖ ^ 2

noncomputable def frequencyOffset (N q j t : Nat) : Real :=
  (j : Real) / (N : Real) - (t : Real) / (q : Real)

noncomputable def fourierPeakAmplitude (N q j t : Nat) : Complex :=
  dirichletAmplitude N (frequencyOffset N q j t)

noncomputable def fourierPeakProbability (N q j t : Nat) : Real :=
  ‖fourierPeakAmplitude N q j t‖ ^ 2

theorem fourierPeakAmplitude_eq_exponential_sum (N q j t : Nat) :
    fourierPeakAmplitude N q j t =
      (N : Complex)⁻¹ * ∑ x ∈ Finset.range N,
        Complex.exp (Complex.I *
          (2 * Real.pi * (x : Real) *
            ((j : Real) / (N : Real) - (t : Real) / (q : Real)))) := by
  unfold fourierPeakAmplitude dirichletAmplitude frequencyOffset
  push_cast
  rfl

theorem fourierPeakProbability_eq_dirichlet (N q j t : Nat) :
    fourierPeakProbability N q j t =
      dirichletProbability N (frequencyOffset N q j t) := by
  rfl

theorem phaseRoot_pow (delta : Real) (x : Nat) :
    phaseRoot delta ^ x =
      Complex.exp (Complex.I * (2 * Real.pi * (x : Real) * delta)) := by
  rw [phaseRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem dirichletAmplitude_zero {N : Nat} (hN : 0 < N) :
    dirichletAmplitude N 0 = 1 := by
  simp [dirichletAmplitude, hN.ne']

theorem dirichletAmplitude_geometric {N : Nat} {delta : Real}
    (hN : 0 < N) (hroot : phaseRoot delta ≠ 1) :
    dirichletAmplitude N delta =
      (phaseRoot delta ^ N - 1) /
        ((N : Complex) * (phaseRoot delta - 1)) := by
  rw [dirichletAmplitude]
  simp_rw [← phaseRoot_pow]
  rw [geom_sum_eq hroot]
  have hNc : (N : Complex) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNc]

theorem norm_phaseRoot_sub_one (delta : Real) :
    ‖phaseRoot delta - 1‖ = 2 * |Real.sin (Real.pi * delta)| := by
  rw [phaseRoot]
  have hcast :
      (2 : Complex) * Real.pi * delta =
        ((2 * Real.pi * delta : Real) : Complex) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * delta / 2 = Real.pi * delta := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]

theorem norm_phaseRoot_pow_sub_one (N : Nat) (delta : Real) :
    ‖phaseRoot delta ^ N - 1‖ =
      2 * |Real.sin (Real.pi * (N : Real) * delta)| := by
  rw [phaseRoot_pow]
  have hcast :
      (2 : Complex) * Real.pi * (N : Real) * delta =
        ((2 * Real.pi * (N : Real) * delta : Real) : Complex) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * (N : Real) * delta / 2 =
      Real.pi * (N : Real) * delta := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]

theorem phaseRoot_ne_one_of_sin_ne_zero {delta : Real}
    (hsin : Real.sin (Real.pi * delta) ≠ 0) :
    phaseRoot delta ≠ 1 := by
  intro hroot
  have hnorm := norm_phaseRoot_sub_one delta
  rw [hroot, sub_self, norm_zero] at hnorm
  have habs : |Real.sin (Real.pi * delta)| = 0 := by linarith
  exact hsin (abs_eq_zero.mp habs)

theorem norm_dirichletAmplitude {N : Nat} {delta : Real}
    (hN : 0 < N) (hsin : Real.sin (Real.pi * delta) ≠ 0) :
    ‖dirichletAmplitude N delta‖ =
      |Real.sin (Real.pi * (N : Real) * delta)| /
        ((N : Real) * |Real.sin (Real.pi * delta)|) := by
  rw [dirichletAmplitude_geometric hN
      (phaseRoot_ne_one_of_sin_ne_zero hsin),
    Complex.norm_div, Complex.norm_mul,
    norm_phaseRoot_pow_sub_one, norm_phaseRoot_sub_one,
    Complex.norm_natCast]
  have hNc : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hsinAbs : |Real.sin (Real.pi * delta)| ≠ 0 := abs_ne_zero.mpr hsin
  norm_cast
  field_simp [hNc, hsinAbs]

theorem two_div_pi_le_norm_dirichletAmplitude {N : Nat} {delta : Real}
    (hN : 0 < N) (hdelta : |delta| ≤ 1 / (2 * (N : Real))) :
    2 / Real.pi ≤ ‖dirichletAmplitude N delta‖ := by
  by_cases hdeltaZero : delta = 0
  · subst delta
    rw [dirichletAmplitude_zero hN, norm_one]
    exact (div_le_one Real.pi_pos).2 Real.two_le_pi
  · have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hNone : (1 : Real) ≤ N := by exact_mod_cast hN
    have hdenLe : (2 : Real) ≤ 2 * (N : Real) := by
      nlinarith
    have hinvLe : 1 / (2 * (N : Real)) ≤ (1 : Real) / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdenLe
    have hdeltaLtOne : |delta| < 1 :=
      lt_of_le_of_lt (hdelta.trans hinvLe) (by norm_num)
    have hdeltaLower : -1 < delta := (abs_lt.mp hdeltaLtOne).1
    have hdeltaUpper : delta < 1 := (abs_lt.mp hdeltaLtOne).2
    have hangleLower : -Real.pi < Real.pi * delta := by
      simpa using mul_lt_mul_of_pos_left hdeltaLower Real.pi_pos
    have hangleUpper : Real.pi * delta < Real.pi := by
      simpa using mul_lt_mul_of_pos_left hdeltaUpper Real.pi_pos
    have hsin : Real.sin (Real.pi * delta) ≠ 0 := by
      intro hzero
      have hangleZero :=
        (Real.sin_eq_zero_iff_of_lt_of_lt hangleLower hangleUpper).mp hzero
      apply hdeltaZero
      exact (mul_eq_zero.mp hangleZero).resolve_left Real.pi_ne_zero
    have hangleAbs :
        |Real.pi * (N : Real) * delta| ≤ Real.pi / 2 := by
      calc
        |Real.pi * (N : Real) * delta| =
            Real.pi * (N : Real) * |delta| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
                abs_of_pos hNreal]
        _ ≤ Real.pi * (N : Real) * (1 / (2 * (N : Real))) :=
          mul_le_mul_of_nonneg_left hdelta
            (mul_nonneg Real.pi_nonneg hNreal.le)
        _ = Real.pi / 2 := by field_simp [hNreal.ne']
    have hnumerator :
        2 * (N : Real) * |delta| ≤
          |Real.sin (Real.pi * (N : Real) * delta)| := by
      calc
        2 * (N : Real) * |delta| =
            (2 / Real.pi) * |Real.pi * (N : Real) * delta| := by
              rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
                abs_of_pos hNreal]
              field_simp [Real.pi_ne_zero]
        _ ≤ |Real.sin (Real.pi * (N : Real) * delta)| :=
          Real.mul_abs_le_abs_sin hangleAbs
    have hdenominator :
        |Real.sin (Real.pi * delta)| ≤ Real.pi * |delta| := by
      calc
        |Real.sin (Real.pi * delta)| ≤ |Real.pi * delta| :=
          Real.abs_sin_le_abs
        _ = Real.pi * |delta| := by
          rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [norm_dirichletAmplitude hN hsin]
    apply (le_div_iff₀
      (mul_pos hNreal (abs_pos.mpr hsin))).2
    calc
      (2 / Real.pi) *
          ((N : Real) * |Real.sin (Real.pi * delta)|) ≤
          (2 / Real.pi) *
            ((N : Real) * (Real.pi * |delta|)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdenominator hNreal.le)
          (by positivity)
      _ = 2 * (N : Real) * |delta| := by
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * (N : Real) * delta)| := hnumerator

theorem four_div_pi_sq_le_dirichletProbability {N : Nat} {delta : Real}
    (hN : 0 < N) (hdelta : |delta| ≤ 1 / (2 * (N : Real))) :
    4 / Real.pi ^ 2 ≤ dirichletProbability N delta := by
  have hnorm := two_div_pi_le_norm_dirichletAmplitude hN hdelta
  have hsquare :
      (2 / Real.pi) ^ 2 ≤ ‖dirichletAmplitude N delta‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hnorm
  rw [dirichletProbability]
  calc
    4 / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by
      field_simp [Real.pi_ne_zero]
      norm_num
    _ ≤ ‖dirichletAmplitude N delta‖ ^ 2 := hsquare

theorem abs_frequencyOffset_peak_le {N q t : Nat}
    (hq : 0 < q) (hqN : q ≤ N) :
    |frequencyOffset N q (peak N q t) t| ≤
      1 / (2 * (N : Real)) := by
  have hN : 0 < N := hq.trans_le hqN
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hNReal : 0 < (N : Real) := by exact_mod_cast hN
  obtain ⟨hupperNat, hlowerNat⟩ := peak_distance (N := N) (q := q) (t := t) hq
  have hupperCast :
      (2 : Real) * q * peak N q t ≤ 2 * N * t + q := by
    exact_mod_cast hupperNat
  have hlowerCast :
      (2 : Real) * N * t ≤ 2 * q * peak N q t + q := by
    exact_mod_cast hlowerNat
  have hupper :
      2 * ((q : Real) * peak N q t - (N : Real) * t) ≤ q := by
    linarith
  have hlower :
      -(q : Real) ≤
        2 * ((q : Real) * peak N q t - (N : Real) * t) := by
    linarith
  have hoffset : frequencyOffset N q (peak N q t) t =
      ((q : Real) * peak N q t - (N : Real) * t) /
        ((N : Real) * q) := by
    rw [frequencyOffset]
    field_simp [hNReal.ne', hqReal.ne']
  rw [hoffset, abs_le]
  constructor
  · apply (le_div_iff₀ (mul_pos hNReal hqReal)).2
    have hscale :
        -(1 / (2 * (N : Real))) * ((N : Real) * q) =
          -(q : Real) / 2 := by
      field_simp [hNReal.ne']
    rw [hscale]
    linarith
  · apply (div_le_iff₀ (mul_pos hNReal hqReal)).2
    have hscale :
        (1 / (2 * (N : Real))) * ((N : Real) * q) =
          (q : Real) / 2 := by
      field_simp [hNReal.ne']
    rw [hscale]
    linarith

theorem four_div_pi_sq_le_peakProbability {N q t : Nat}
    (hq : 0 < q) (hqN : q ≤ N) :
    4 / Real.pi ^ 2 ≤
      fourierPeakProbability N q (peak N q t) t := by
  rw [fourierPeakProbability_eq_dirichlet]
  exact four_div_pi_sq_le_dirichletProbability
    (hq.trans_le hqN) (abs_frequencyOffset_peak_le hq hqN)

theorem fortyNine_div_121_le_four_div_pi_sq :
    (49 : Real) / 121 ≤ 4 / Real.pi ^ 2 := by
  have hpiLt : Real.pi < (22 : Real) / 7 :=
    Real.pi_lt_d4.trans (by norm_num)
  have hpiSq : Real.pi ^ 2 < ((22 : Real) / 7) ^ 2 := by
    exact pow_lt_pow_left₀ hpiLt Real.pi_nonneg (by norm_num)
  apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
  calc
    (49 / 121 : Real) * Real.pi ^ 2 ≤
        (49 / 121 : Real) * ((22 / 7 : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hpiSq.le (by norm_num)
    _ = 4 := by norm_num

theorem fortyNine_div_121_le_peakProbability {N q t : Nat}
    (hq : 0 < q) (hqN : q ≤ N) :
    (49 : Real) / 121 ≤
      fourierPeakProbability N q (peak N q t) t :=
  fortyNine_div_121_le_four_div_pi_sq.trans
    (four_div_pi_sq_le_peakProbability hq hqN)

/-- info: 'VQ.Tests.ECDLPFourierRecovery.dirichletAmplitude_geometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dirichletAmplitude_geometric

/-- info: 'VQ.Tests.ECDLPFourierRecovery.norm_dirichletAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms norm_dirichletAmplitude

/-- info: 'VQ.Tests.ECDLPFourierRecovery.four_div_pi_sq_le_dirichletProbability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms four_div_pi_sq_le_dirichletProbability

/-- info: 'VQ.Tests.ECDLPFourierRecovery.four_div_pi_sq_le_peakProbability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms four_div_pi_sq_le_peakProbability

/-- info: 'VQ.Tests.ECDLPFourierRecovery.fortyNine_div_121_le_peakProbability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fortyNine_div_121_le_peakProbability

end VQ.Tests.ECDLPFourierRecovery
