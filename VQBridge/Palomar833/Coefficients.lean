import VQBridge.Palomar833.Gates

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics VQBridge

theorem state_smul {d : Nat} (hd : 0 < d) (a : Dy d) (u : Vec d) (j : Nat) :
    state (a • u) j = dtoC a * state u j := dtoC_mul hd a (u j)

theorem inverse_sqrt_two_pow_even (n : Nat) :
    (1 / (Real.sqrt 2 : ℂ)) ^ (2 * n) = (1 / (2 : ℂ)) ^ n := by
  rw [pow_mul]
  congr 1
  have hsquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [div_pow, _root_.one_pow, hsquare]

theorem dtoC_inverse_sqrt_two {level : Nat} (hl : 3 ≤ level) :
    dtoC (Dy.invSqrt2 (deg level)) = 1 / (Real.sqrt 2 : ℂ) := by
  rw [deg_eq_four_mul hl]
  exact dtoC_invSqrt2 (Nat.two_pow_pos _)

theorem dtoC_fourier_scale {level : Nat} (hl : 3 ≤ level) (n : Nat) :
    dtoC (Dy.invSqrt2 (deg level) ^ (4 * n)) =
      1 / ((2 : ℂ) ^ n) ^ 2 := by
  rw [dtoC_pow (deg_pos level), dtoC_inverse_sqrt_two hl,
    show 4 * n = 2 * (n * 2) by omega,
    inverse_sqrt_two_pow_even, div_pow, _root_.one_pow, pow_mul]

theorem dtoC_phase_power {level k : Nat} (hl : 0 < level) (hk : k ≤ level)
    (m : Nat) :
    dtoC (phase level k ^ m) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (2 : ℂ) ^ k) := by
  rw [dtoC_pow (deg_pos level), dtoC_phase hl hk, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end Palomar833.Connection
