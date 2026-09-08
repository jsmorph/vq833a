import VQMathlib.Curve.Secp256k1Order.Basic
import VQMathlib.Curve.PrimeCert
import Mathlib.Tactic.NormNum.Prime

namespace VQ.Tests.Secp256k1Order

open VQBridge.Prime

set_option maxRecDepth 40000

theorem prime_17_order : Nat.Prime 17 := by norm_num
theorem prime_41_order : Nat.Prime 41 := by norm_num
theorem prime_59_order : Nat.Prime 59 := by norm_num
theorem prime_109_order : Nat.Prime 109 := by norm_num
theorem prime_149_order : Nat.Prime 149 := by norm_num
theorem prime_293_order : Nat.Prime 293 := by norm_num
theorem prime_461_order : Nat.Prime 461 := by norm_num
theorem prime_631_order : Nat.Prime 631 := by norm_num
theorem prime_797_order : Nat.Prime 797 := by norm_num
theorem prime_4051_order : Nat.Prime 4051 := by norm_num
theorem prime_9349_order : Nat.Prime 9349 := by norm_num
theorem prime_16699_order : Nat.Prime 16699 := by norm_num
theorem prime_28181_order : Nat.Prime 28181 := by norm_num
theorem prime_85831_order : Nat.Prime 85831 := by norm_num
theorem prime_120233_order : Nat.Prime 120233 := by norm_num
theorem prime_305873_order : Nat.Prime 305873 := by norm_num
theorem prime_1627771_order : Nat.Prime 1627771 := by norm_num
theorem prime_4681609_order : Nat.Prime 4681609 := by norm_num

theorem prime_44706919_order : Nat.Prime 44706919 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 6
      factors := [2, 3, 797, 9349]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_3
          | exact prime_797_order
          | exact prime_9349_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_545358713_order : Nat.Prime 545358713 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 5
      factors := [2, 2, 2, 41, 59, 28181]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_41_order
          | exact prime_59_order
          | exact prime_28181_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_297159362677_order : Nat.Prime 297159362677 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 2
      factors := [2, 2, 3, 3, 11, 461, 1627771]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_3
          | exact prime_11
          | exact prime_461_order
          | exact prime_1627771_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_107361793816595537_order : Nat.Prime 107361793816595537 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 3
      factors := [2, 2, 2, 2, 16699, 85831, 4681609]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_16699_order
          | exact prime_85831_order
          | exact prime_4681609_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_174723607534414371449_order : Nat.Prime 174723607534414371449 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 3
      factors := [2, 2, 2, 17, 59, 4051, 120233, 44706919]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_17_order
          | exact prime_59_order
          | exact prime_4051_order
          | exact prime_120233_order
          | exact prime_44706919_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_29047611873442575647497758179_order :
    Nat.Prime 29047611873442575647497758179 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 2
      factors := [2, 293, 305873, 545358713, 297159362677]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_293_order
          | exact prime_305873_order
          | exact prime_545358713_order
          | exact prime_297159362677_order
      pow_one := by decide
      pow_ne := by decide }

theorem prime_341948486974166000522343609283189_order :
    Nat.Prime 341948486974166000522343609283189 :=
  prime_of_cert
    { one_lt := by norm_num
      witness := 2
      factors := [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_3
          | exact prime_109_order
          | exact prime_29047611873442575647497758179_order
      pow_one := by decide
      pow_ne := by decide }

theorem q_prime : Nat.Prime q := by
  unfold q
  exact prime_of_cert
    { one_lt := by norm_num
      witness := 7
      factors := [2, 2, 2, 2, 2, 2, 3, 149, 631,
        107361793816595537, 174723607534414371449,
        341948486974166000522343609283189]
      prod_eq := by norm_num
      factors_prime := by
        intro r hr
        fin_cases hr <;> first
          | exact prime_2
          | exact prime_3
          | exact prime_149_order
          | exact prime_631_order
          | exact prime_107361793816595537_order
          | exact prime_174723607534414371449_order
          | exact prime_341948486974166000522343609283189_order
      pow_one := by decide
      pow_ne := by decide }

instance : Fact (Nat.Prime q) := ⟨q_prime⟩

end VQ.Tests.Secp256k1Order
