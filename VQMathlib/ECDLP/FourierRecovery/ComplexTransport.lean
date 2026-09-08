import VQMathlib.ECDLP.FourierRecovery.DirichletPeak
import VQMathlib.Algorithms.QFT
import VQMathlib.Semantics.Gate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace VQ.Tests.ECDLPFourierRecovery

open VQ.Algebra VQ.Semantics
open Finset

theorem dtoC_invSqrt2_deg {level : Nat} (hlevel : 3 ≤ level) :
    VQBridge.dtoC (Dy.invSqrt2 (deg level)) =
      1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [VQBridge.deg_eq_four_mul hlevel]
  exact VQBridge.dtoC_invSqrt2 (Nat.two_pow_pos _)

theorem dtoC_preparation_qft_normalization {level n : Nat}
    (hlevel : 3 ≤ level) :
    VQBridge.dtoC
        (Dy.invSqrt2 (deg level) ^ n *
          Dy.invSqrt2 (deg level) ^ n) =
      (((2 ^ n : Nat) : ℂ)⁻¹) := by
  rw [VQBridge.dtoC_mul (VQBridge.deg_pos level),
    VQBridge.dtoC_pow (VQBridge.deg_pos level),
    dtoC_invSqrt2_deg hlevel]
  have hbase :
      (1 / ((Real.sqrt 2 : ℝ) : ℂ)) *
          (1 / ((Real.sqrt 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ := by
    rw [one_div_mul_one_div, ← sq, VQBridge.sqrt_two_sq]
    rw [one_div]
  rw [← mul_pow, hbase, inv_pow]
  norm_cast

theorem dtoC_preparedQFTCoefficient
    {level n x j : Nat} (hlevel : 3 ≤ level)
    (hn : n + 1 ≤ level) (hj : j < 2 ^ n) :
    VQBridge.dtoC
        (Dy.invSqrt2 (deg level) ^ n *
          QFT.FourierColumn level n x j) =
      (((2 ^ n : Nat) : ℂ)⁻¹) *
        Complex.exp (Complex.I *
          (2 * Real.pi * (x : ℝ) *
            ((j : ℝ) / (2 ^ n : Nat)))) := by
  rw [QFT.FourierColumn, if_pos hj, ← Dy.mul_assoc,
    VQBridge.dtoC_mul (VQBridge.deg_pos level),
    dtoC_preparation_qft_normalization hlevel,
    VQBridge.dtoC_pow (VQBridge.deg_pos level),
    VQBridge.dtoC_phase (by omega) (by omega),
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

theorem qftCharacterSum_eq_fourierPeakAmplitude
    (N q j t : Nat) [NeZero q] :
    ∑ x ∈ Finset.range N,
        (((N : ℂ)⁻¹) *
          Complex.exp (Complex.I *
            (2 * Real.pi * (x : ℝ) *
              ((j : ℝ) / (N : ℝ))))) *
          ZMod.stdAddChar
            (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) =
      fourierPeakAmplitude N q j t := by
  rw [fourierPeakAmplitude_eq_exponential_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  calc
    (((N : ℂ)⁻¹) *
          Complex.exp (Complex.I *
            (2 * Real.pi * (x : ℝ) *
              ((j : ℝ) / (N : ℝ))))) *
        ZMod.stdAddChar
          (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) =
      ((N : ℂ)⁻¹) * Complex.exp
        (Complex.I *
            (2 * Real.pi * (x : ℝ) *
              ((j : ℝ) / (N : ℝ))) +
          2 * Real.pi * Complex.I * (-(t : ℤ) * (x : ℤ)) / q) := by
        rw [ZMod.stdAddChar_coe, mul_assoc, ← Complex.exp_add]
        push_cast
        ring_nf
    _ = ((N : ℂ)⁻¹) *
        Complex.exp (Complex.I *
          (2 * Real.pi * (x : ℝ) *
            ((j : ℝ) / (N : ℝ) - (t : ℝ) / (q : ℝ)))) := by
      congr 1
      push_cast
      ring_nf

theorem preparedQFTCharacterSum_eq_fourierPeakAmplitude
    {level n q j t : Nat} [NeZero q] (hlevel : 3 ≤ level)
    (hn : n + 1 ≤ level) (hj : j < 2 ^ n) :
    ∑ x ∈ Finset.range (2 ^ n),
        VQBridge.dtoC
            (Dy.invSqrt2 (deg level) ^ n *
              QFT.FourierColumn level n x j) *
          ZMod.stdAddChar
            (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) =
      fourierPeakAmplitude (2 ^ n) q j t := by
  calc
    ∑ x ∈ Finset.range (2 ^ n),
        VQBridge.dtoC
            (Dy.invSqrt2 (deg level) ^ n *
              QFT.FourierColumn level n x j) *
          ZMod.stdAddChar
            (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) =
      ∑ x ∈ Finset.range (2 ^ n),
          ((((2 ^ n : Nat) : ℂ)⁻¹) *
            Complex.exp (Complex.I *
              (2 * Real.pi * (x : ℝ) *
                ((j : ℝ) / ((2 ^ n : Nat) : ℝ))))) *
            ZMod.stdAddChar
              (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [dtoC_preparedQFTCoefficient hlevel hn hj]
        simp only [Complex.ofReal_natCast]
    _ = fourierPeakAmplitude (2 ^ n) q j t :=
      qftCharacterSum_eq_fourierPeakAmplitude (2 ^ n) q j t

theorem qft256CharacterSum_eq_fourierPeakAmplitude
    {level q j t : Nat} [NeZero q] (hlevel : 257 ≤ level)
    (hj : j < 2 ^ 256) :
    ∑ x ∈ Finset.range (2 ^ 256),
        VQBridge.dtoC
            (Dy.invSqrt2 (deg level) ^ 256 *
              QFT.FourierColumn level 256 x j) *
          ZMod.stdAddChar
            (((-(t : ℤ) * (x : ℤ) : ℤ)) : ZMod q) =
      fourierPeakAmplitude (2 ^ 256) q j t := by
  exact preparedQFTCharacterSum_eq_fourierPeakAmplitude
    (by omega) hlevel hj

end VQ.Tests.ECDLPFourierRecovery
