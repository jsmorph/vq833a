/-
The primality of the secp256k1 field prime.

The certificate proves the `Nat.Prime p` proposition used by the Mathlib curve
laws in `VQMathlib.Curve.Laws`.

The factorization tree comes from the ACL2 community-book theorem
`PRIMES::secp256k1-field-prime`, whose data was generated with Mathematica's
`FactorInteger` and `PrimitiveRoot`.  Each node names a witness and the prime
factorization of `n - 1`.  Large factors have recursive nodes, and `norm_num`
proves the small factors.  Lean's kernel checks every product, witness, and
primality claim.
-/
import VQMathlib.Curve.Prime
import Mathlib.Tactic.NormNum.Prime

namespace VQBridge
namespace Prime

open VQ.Curve

set_option maxRecDepth 40000

/-! ## Directly proved prime factors -/
theorem prime_2 : Nat.Prime 2 := by norm_num
theorem prime_3 : Nat.Prime 3 := by norm_num
theorem prime_5 : Nat.Prime 5 := by norm_num
theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_11 : Nat.Prime 11 := by norm_num
theorem prime_29 : Nat.Prime 29 := by norm_num
theorem prime_31 : Nat.Prime 31 := by norm_num
theorem prime_53 : Nat.Prime 53 := by norm_num
theorem prime_971 : Nat.Prime 971 := by norm_num
theorem prime_1373 : Nat.Prime 1373 := by norm_num
theorem prime_1627 : Nat.Prime 1627 := by norm_num
theorem prime_2621 : Nat.Prime 2621 := by norm_num
theorem prime_2657 : Nat.Prime 2657 := by norm_num
theorem prime_4423 : Nat.Prime 4423 := by norm_num
theorem prime_5323 : Nat.Prime 5323 := by norm_num
theorem prime_7723 : Nat.Prime 7723 := by norm_num
theorem prime_13441 : Nat.Prime 13441 := by norm_num
theorem prime_24809 : Nat.Prime 24809 := by norm_num
theorem prime_41201 : Nat.Prime 41201 := by norm_num
theorem prime_96557 : Nat.Prime 96557 := by norm_num
theorem prime_7240687 : Nat.Prime 7240687 := by norm_num

/-! ## Recursive certificate tree -/

theorem prime_n5 : Nat.Prime 13331831 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 13
      factors := [2, 5, 971, 1373]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_5 | exact prime_971 | exact prime_1373
      pow_one := by decide
      pow_ne := by decide }

theorem prime_n4 : Nat.Prime 173378833005251801 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 6
      factors := [2, 2, 2, 5, 5, 2621, 24809, 13331831]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_5 | exact prime_2621 | exact prime_24809 | exact prime_n5
      pow_one := by decide
      pow_ne := by decide }

theorem prime_n3 : Nat.Prime 22149492674086928081353 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 5
      factors := [2, 2, 2, 3, 5323, 173378833005251801]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_3 | exact prime_5323 | exact prime_n4
      pow_one := by decide
      pow_ne := by decide }

theorem prime_n1 : Nat.Prime 132896956044521568488119 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 6
      factors := [2, 3, 22149492674086928081353]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_3 | exact prime_n3
      pow_one := by decide
      pow_ne := by decide }

theorem prime_n7 : Nat.Prime 107590001 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 3
      factors := [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_5 | exact prime_7 | exact prime_29 | exact prime_53
      pow_one := by decide
      pow_ne := by decide }

theorem prime_n2 : Nat.Prime 255515944373312847190720520512484175977 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 3
      factors := [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_7 | exact prime_11 | exact prime_1627 | exact prime_2657 | exact prime_4423 | exact prime_41201 | exact prime_96557 | exact prime_7240687 | exact prime_n7
      pow_one := by decide
      pow_ne := by decide }

theorem prime_C : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 10
      factors := [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_3 | exact prime_5 | exact prime_29 | exact prime_31 | exact prime_7723 | exact prime_n1 | exact prime_n2
      pow_one := by decide
      pow_ne := by decide }

theorem prime_P : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 3
      factors := [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
      prod_eq := by norm_num
      factors_prime := by
        intro q hq
        fin_cases hq <;> first | exact prime_2 | exact prime_3 | exact prime_7 | exact prime_13441 | exact prime_C
      pow_one := by decide
      pow_ne := by decide }

/-- Primality of the secp256k1 field modulus. -/
theorem prime_p : Nat.Prime VQ.Curve.p := by
  show Nat.Prime (2 ^ 256 - 2 ^ 32 - 977)
  have h : (2 : Nat) ^ 256 - 2 ^ 32 - 977
      = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num
  rw [h]
  exact prime_P

instance : Fact (Nat.Prime VQ.Curve.p) := ⟨prime_p⟩

end Prime
end VQBridge
