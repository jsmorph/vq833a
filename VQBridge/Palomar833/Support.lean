import VQBridge.Palomar833.Specification
import VQ.Semantics.RegisterState

namespace Palomar833.Connection

theorem encodePoint_bounds (point : Point) :
    encodePoint point % 2 ^ 259 < 2 ^ 256 ∧ encodePoint point < 2 ^ 515 := by
  cases point with
  | zero =>
      simpa only [encodePoint, Nat.zero_mod] using
        And.intro (Nat.two_pow_pos 256) (Nat.two_pow_pos 515)
  | some x y _ =>
      have hp : p < 2 ^ 256 := VQ.Tests.Secp256k1Order.p_lt_two_pow_256
      have hx := (ZMod.val_lt x).trans hp
      have hy := (ZMod.val_lt y).trans hp
      have hx259 : x.val < 2 ^ 259 :=
        hx.trans_le (Nat.pow_le_pow_right (by decide) (by decide))
      change (x.val + 2 ^ 259 * y.val) % 2 ^ 259 < 2 ^ 256 ∧
        x.val + 2 ^ 259 * y.val < 2 ^ 515
      constructor
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx259]
        exact hx
      · simpa only [VQ.Tests.RegisterState.joinIndex, Nat.reduceAdd] using
          VQ.Tests.RegisterState.joinIndex_lt (m := 259) (s := 256) hx259 hy

theorem fourierState_support (d : Nat) (o : Outcome) {j : Nat}
    (hj : 2 ^ 256 ≤ j % 2 ^ 259 ∨ 2 ^ 515 ≤ j) : fourierState d o j = 0 := by
  have hne (point : Point) : j ≠ encodePoint point := by
    intro heq
    rw [heq] at hj
    rcases encodePoint_bounds point with ⟨hlow, hhigh⟩
    rcases hj with hj | hj
    · exact (Nat.not_le_of_lt hlow) hj
    · exact (Nat.not_le_of_lt hhigh) hj
  simp only [fourierState, ite_eq_right (hne _), mul_zero, Finset.sum_const_zero]

end Palomar833.Connection
