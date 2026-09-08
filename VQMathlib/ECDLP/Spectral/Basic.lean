import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open WithLp
open scoped BigOperators ComplexConjugate

namespace VQ.Tests.ECDLPSpectral

abbrev CyclicState (q : Nat) := EuclideanSpace ℂ (ZMod q)

noncomputable def invSqrtCard (q : Nat) : ℂ :=
  ((1 / Real.sqrt (q : ℝ) : ℝ) : ℂ)

noncomputable def shiftEigen (q : Nat) [NeZero q]
    (k : ZMod q) : CyclicState q :=
  toLp 2 fun t => invSqrtCard q * ZMod.stdAddChar (k * t)

noncomputable def translate (q : Nat) [NeZero q]
    (s : ZMod q) (v : CyclicState q) : CyclicState q :=
  toLp 2 fun t => v (t - s)

noncomputable def zeroBasis (q : Nat) [NeZero q] : CyclicState q :=
  PiLp.single 2 0 1

@[simp]
theorem shiftEigen_apply (q : Nat) [NeZero q] (k t : ZMod q) :
    shiftEigen q k t = invSqrtCard q * ZMod.stdAddChar (k * t) :=
  rfl

@[simp]
theorem translate_apply (q : Nat) [NeZero q]
    (s : ZMod q) (v : CyclicState q) (t : ZMod q) :
    translate q s v t = v (t - s) :=
  rfl

@[simp]
theorem zeroBasis_apply (q : Nat) [NeZero q] (t : ZMod q) :
    zeroBasis q t = if t = 0 then 1 else 0 := by
  simp [zeroBasis]

theorem invSqrtCard_conj (q : Nat) :
    conj (invSqrtCard q) = invSqrtCard q := by
  simp [invSqrtCard]

theorem invSqrtCard_mul_self {q : Nat} (hq : 0 < q) :
    invSqrtCard q * invSqrtCard q = ((q : ℂ)⁻¹) := by
  have hqReal : 0 ≤ (q : ℝ) := by positivity
  calc
    invSqrtCard q * invSqrtCard q =
        (((1 / Real.sqrt (q : ℝ)) * (1 / Real.sqrt (q : ℝ)) : ℝ) : ℂ) := by
      simp [invSqrtCard]
    _ = ((1 / (q : ℝ) : ℝ) : ℂ) := by
      rw [one_div_mul_one_div, ← sq, Real.sq_sqrt hqReal]
    _ = ((q : ℂ)⁻¹) := by
      simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem character_sum (q : Nat) [NeZero q] (a : ZMod q) :
    ∑ t : ZMod q, ZMod.stdAddChar (t * a) =
      if a = 0 then (q : ℂ) else 0 := by
  simpa using
    AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar q)

theorem conj_character_mul_character (q : Nat) [NeZero q]
    (k l t : ZMod q) :
    conj (ZMod.stdAddChar (k * t)) * ZMod.stdAddChar (l * t) =
      ZMod.stdAddChar (t * (l - k)) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

end VQ.Tests.ECDLPSpectral
