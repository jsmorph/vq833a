/-
Arithmetic in the secp256k1 base field.

A field element is a `Nat` below `p`, and every operation reduces modulo `p`.
This representation matches basis-state registers, which expose `Nat` values.
Kernel evaluation can then close concrete curve obligations by reduction.

Inversion is Fermat's `a ^ (p - 2)` by binary exponentiation, which makes the
sum of two points a function.  The value is unique by construction, while
primality determines whether the function agrees with the curve law stated in
`VQBridge.Curve`.  `powModAux` recurses structurally on its fuel argument so
concrete curve obligations reduce in the kernel.
-/

namespace VQ
namespace Curve

/-- The secp256k1 base field prime, `2 ^ 256 - 2 ^ 32 - 977`. -/
def p : Nat := 2 ^ 256 - 2 ^ 32 - 977

theorem p_pos : 0 < p := by decide

/-- Modular addition. -/
def add (a b : Nat) : Nat := (a + b) % p

/-- Modular subtraction.  `p - b % p` is `p` when `b` is a multiple of `p`, and
the outer reduction absorbs it. -/
def sub (a b : Nat) : Nat := (a + (p - b % p)) % p

/-- Modular multiplication. -/
def mul (a b : Nat) : Nat := a * b % p

/-- Binary exponentiation modulo `m`, structurally recursive on the fuel.

The exponent serves as its own fuel: the number of halvings needed for `e` is
at most `e` for every `e`, and the `0` case exits as soon as the exponent is
exhausted.

The modulus is a parameter because a Pratt primality certificate needs the same
computation at every prime in its tree, not only at this one. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | _ + 1, _, 0, acc => acc
  | fuel + 1, base, e, acc =>
      powModAux m fuel (base * base % m) (e / 2)
        (if e % 2 = 1 then acc * base % m else acc)

/-- `a ^ e` modulo `m`. -/
def powModOf (m a e : Nat) : Nat := powModAux m e (a % m) e 1 % m

/-- The exponentiation loop computes what it claims, given enough fuel.

Stated with the reduction on the left because the two base cases return the
accumulator unreduced.  The hypothesis is what the caller supplies by passing
the exponent as its own fuel. -/
theorem powModAux_mod (m : Nat) (fuel : Nat) : ∀ base e acc : Nat, e < 2 ^ fuel →
    powModAux m fuel base e acc % m = acc * base ^ e % m := by
  induction fuel with
  | zero =>
      intro base e acc he
      have he0 : e = 0 := by simpa using he
      subst he0
      simp [powModAux]
  | succ fuel ih =>
      intro base e acc he
      match e with
      | 0 => simp [powModAux]
      | e + 1 =>
          have hm : (e + 1) / 2 < 2 ^ fuel := by
            have h2 : e + 1 < 2 ^ fuel * 2 := by simpa [Nat.pow_succ] using he
            omega
          have hsq : (base * base) ^ ((e + 1) / 2) = base ^ (2 * ((e + 1) / 2)) := by
            rw [Nat.pow_mul, Nat.pow_two]
          have hbase : (base * base % m) ^ ((e + 1) / 2) % m
              = base ^ (2 * ((e + 1) / 2)) % m := by
            rw [← Nat.pow_mod, hsq]
          show powModAux m fuel (base * base % m) ((e + 1) / 2)
              (if (e + 1) % 2 = 1 then acc * base % m else acc) % m = _
          rw [ih _ _ _ hm, Nat.mul_mod, hbase, ← Nat.mul_mod]
          rcases Nat.mod_two_eq_zero_or_one (e + 1) with h | h
          · rw [if_neg (by omega)]
            have h0 : 2 * ((e + 1) / 2) = e + 1 := by omega
            rw [h0]
          · rw [if_pos h]
            obtain ⟨k, hk⟩ : ∃ k, e + 1 = 2 * k + 1 := ⟨(e + 1) / 2, by omega⟩
            have hk2 : (e + 1) / 2 = k := by omega
            rw [Nat.mod_mul_mod, hk2, hk, Nat.pow_succ]
            congr 1
            ac_rfl

theorem powModOf_eq (m a e : Nat) : powModOf m a e = a ^ e % m := by
  have h : e < 2 ^ e := Nat.lt_two_pow_self
  rw [powModOf, powModAux_mod m e _ _ _ h, Nat.one_mul, ← Nat.pow_mod]

theorem powModOf_lt {m : Nat} (hm : 0 < m) (a e : Nat) : powModOf m a e < m :=
  Nat.mod_lt _ hm

/-- `a ^ e` modulo `p`. -/
def powMod (a e : Nat) : Nat := powModOf p a e

/-- The multiplicative inverse from Fermat's little theorem.  The definition
sends zero to zero, matching Mathlib's `ZMod` inverse convention. -/
def inv (a : Nat) : Nat := powMod a (p - 2)

/-- `powMod` computes `a ^ e` modulo `p`. -/
theorem powMod_eq (a e : Nat) : powMod a e = a ^ e % p := powModOf_eq p a e

theorem inv_zero : inv 0 = 0 := by
  rw [inv, powMod_eq, Nat.zero_pow (show 0 < p - 2 by decide), Nat.zero_mod]

/-! ## Modular arithmetic

The assembly's algebra runs in these terms, so the ring laws are stated once
here.  Each is a rewrite of `%` past an operation, which core Lean's
`Nat.mod_mul_mod`, `Nat.mul_mod_mod`, `Nat.mod_add_mod`, and `Nat.add_mod_mod`
supply, followed by the corresponding law on `Nat`.

The multiplicative inverse is absent from this list.  `inv a` is `a ^ (p - 2)`,
and Fermat's little theorem proves its inverse law when `p` is prime.  The
assembly takes `InverseLaw` as a hypothesis, and `VQBridge.Curve` discharges it
from the bridge's `Nat.Prime p` hypothesis. -/

theorem add_comm (a b : Nat) : add a b = add b a := by
  show (a + b) % p = (b + a) % p
  rw [Nat.add_comm]

theorem add_assoc (a b c : Nat) : add (add a b) c = add a (add b c) := by
  show ((a + b) % p + c) % p = (a + (b + c) % p) % p
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem add_zero {a : Nat} (h : a < p) : add a 0 = a := by
  show (a + 0) % p = a
  rw [Nat.add_zero, Nat.mod_eq_of_lt h]

theorem zero_add {a : Nat} (h : a < p) : add 0 a = a := by
  rw [add_comm]; exact add_zero h

theorem mul_comm (a b : Nat) : mul a b = mul b a := by
  show a * b % p = b * a % p
  rw [Nat.mul_comm]

theorem mul_assoc (a b c : Nat) : mul (mul a b) c = mul a (mul b c) := by
  show (a * b % p) * c % p = a * (b * c % p) % p
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem one_mul {a : Nat} (h : a < p) : mul 1 a = a := by
  show 1 * a % p = a
  rw [Nat.one_mul, Nat.mod_eq_of_lt h]

theorem mul_one {a : Nat} (h : a < p) : mul a 1 = a := by
  rw [mul_comm]; exact one_mul h

@[simp] theorem mul_zero (a : Nat) : mul a 0 = 0 := by
  show a * 0 % p = 0
  rw [Nat.mul_zero, Nat.zero_mod]

@[simp] theorem zero_mul (a : Nat) : mul 0 a = 0 := by
  rw [mul_comm]; exact mul_zero a

theorem mul_add (a b c : Nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  show a * ((b + c) % p) % p = (a * b % p + a * c % p) % p
  rw [Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_add]

theorem add_mul (a b c : Nat) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

/-- `add` and `mul` reduce their arguments, so a value already in range is
unchanged by reduction.  This is the form every cancellation below needs. -/
theorem mod_eq {a : Nat} (h : a < p) : a % p = a := Nat.mod_eq_of_lt h

theorem sub_self {a : Nat} (h : a < p) : sub a a = 0 := by
  show (a + (p - a % p)) % p = 0
  rw [mod_eq h, show a + (p - a) = p from by omega, Nat.mod_self]

/-- Subtraction is addition of the negation, which is the form the assembly's
constant steps use: subtracting the classical `c` is adding `p - c`. -/
theorem sub_eq_add {a b : Nat} (h : b < p) : sub a b = add a (p - b) := by
  show (a + (p - b % p)) % p = (a + (p - b)) % p
  rw [mod_eq h]

/-- Adding then subtracting the same value returns it. -/
theorem add_sub_cancel {a b : Nat} (ha : a < p) (hb : b < p) : sub (add a b) b = a := by
  show ((a + b) % p + (p - b % p)) % p = a
  rw [mod_eq hb, Nat.mod_add_mod]
  have hsplit : a + b + (p - b) = a + p := by omega
  rw [hsplit, Nat.add_mod_right, mod_eq ha]

/-- Subtracting then adding the same value returns it. -/
theorem sub_add_cancel {a b : Nat} (ha : a < p) (hb : b < p) : add (sub a b) b = a := by
  show ((a + (p - b % p)) % p + b) % p = a
  rw [mod_eq hb, Nat.mod_add_mod]
  have hsplit : a + (p - b) + b = a + p := by omega
  rw [hsplit, Nat.add_mod_right, mod_eq ha]

theorem sub_zero {a : Nat} (ha : a < p) : sub a 0 = a := by
  show (a + (p - 0 % p)) % p = a
  rw [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, mod_eq ha]

theorem add_then_sub (a b c : Nat) (hc : c < p) :
    sub (add a b) c = add (sub a c) b := by
  calc
    sub (add a b) c = add (add a b) (p - c) := sub_eq_add hc
    _ = add a (add b (p - c)) := add_assoc _ _ _
    _ = add a (add (p - c) b) := congrArg (add a) (add_comm _ _)
    _ = add (add a (p - c)) b := (add_assoc _ _ _).symm
    _ = add (sub a c) b := by rw [sub_eq_add hc]

/-- Two subtractions collapse into one. -/
theorem sub_sub {a b c : Nat} (hb : b < p) (hc : c < p) :
    sub (sub a b) c = sub a (add b c) := by
  show ((a + (p - b % p)) % p + (p - c % p)) % p = (a + (p - (b + c) % p % p)) % p
  rw [mod_eq hb, mod_eq hc, Nat.mod_mod, Nat.mod_add_mod]
  by_cases h : b + c < p
  · rw [mod_eq h, show a + (p - b) + (p - c) = a + (p - (b + c)) + p from by omega,
      Nat.add_mod_right]
  · have hlt : b + c - p < p := by omega
    have heq : b + c = (b + c - p) + p := by omega
    have hbc : (b + c) % p = b + c - p := by
      have h1 : (b + c) % p = ((b + c - p) + p) % p := congrArg (· % p) heq
      rw [h1, Nat.add_mod_right, mod_eq hlt]
    rw [hbc, show a + (p - b) + (p - c) = a + (p - (b + c - p)) from by omega]

/-! ## Negation -/

/-- Modular negation. -/
def neg (a : Nat) : Nat := sub 0 a

theorem neg_eq {a : Nat} (h : a < p) : neg a = (p - a) % p := by
  show (0 + (p - a % p)) % p = (p - a) % p
  rw [mod_eq h, Nat.zero_add]

theorem neg_lt (a : Nat) : neg a < p := Nat.mod_lt _ p_pos

/-- Subtracting a classical value is adding its negation.  The assembly's
constant steps use this: the constant is `neg ax`, which is zero when `ax` is,
where `p - ax` would be `p` and fail the specification's `c < m`. -/
theorem add_neg_eq_sub {a b : Nat} (hb : b < p) : (a + neg b) % p = sub a b := by
  rw [neg_eq hb]
  show (a + (p - b) % p) % p = (a + (p - b % p)) % p
  rw [Nat.add_mod_mod, mod_eq hb]

/-- The reduced representative of a difference, in the form produced by a
subtractor specification. -/
theorem sub_eq_mod {a b : Nat} (hb : b < p) : (a + (p - b)) % p = sub a b := by
  show _ = (a + (p - b % p)) % p
  rw [mod_eq hb]

/-- Two subtractions in opposite directions cancel. -/
theorem add_sub_sub {a b : Nat} (ha : a < p) (hb : b < p) :
    add (sub b a) (sub a b) = 0 := by
  show ((b + (p - a % p)) % p + (a + (p - b % p)) % p) % p = 0
  rw [mod_eq ha, mod_eq hb, Nat.mod_add_mod, Nat.add_mod_mod,
    show b + (p - a) + (a + (p - b)) = p + p from by omega,
    Nat.add_mod_right, Nat.mod_self]

/-- Negating a difference exchanges its operands.  This is step 15 of the
assembly, where the register holds `ax - x₃` and has to end holding `x₃ - ax`. -/
theorem neg_sub {a b : Nat} (ha : a < p) (hb : b < p) : neg (sub a b) = sub b a := by
  have hab : sub a b < p := Nat.mod_lt _ p_pos
  have hba : sub b a < p := Nat.mod_lt _ p_pos
  have hn : neg (sub a b) < p := Nat.mod_lt _ p_pos
  have h1 : add (neg (sub a b)) (sub a b) = 0 := sub_add_cancel p_pos hab
  have h2 : add (sub b a) (sub a b) = 0 := add_sub_sub ha hb
  calc neg (sub a b) = sub (add (neg (sub a b)) (sub a b)) (sub a b) :=
        (add_sub_cancel hn hab).symm
    _ = sub 0 (sub a b) := by rw [h1]
    _ = sub (add (sub b a) (sub a b)) (sub a b) := by rw [h2]
    _ = sub b a := add_sub_cancel hba hab

/-- A difference of distinct reduced values is nonzero. -/
theorem sub_ne_zero_of_ne {a b : Nat} (ha : a < p) (hb : b < p) (h : a ≠ b) : sub a b ≠ 0 := by
  intro h0
  have hc := sub_add_cancel ha hb
  rw [h0, zero_add hb] at hc
  exact h hc.symm

/-! ## Fermat inversion

`inv a` is `a ^ (p - 2)`, so that it inverts is Fermat's little theorem and needs
`p` prime.  Every theorem that uses the inverse law takes it as an argument,
which exposes the assumption in the statement.  `VQBridge.Curve.inverseLaw`
discharges the law from the bridge's `Nat.Prime p` hypothesis. -/

/-- Away from zero, `inv` is a multiplicative inverse. -/
def InverseLaw : Prop := ∀ a, a < p → a ≠ 0 → mul (inv a) a = 1

/-- Cancelling an inverse against the value it inverts. -/
theorem mul_inv_cancel (hlaw : InverseLaw) {a b : Nat}
    (hb : b < p) (ha : a < p) (ha0 : a ≠ 0) : mul (mul b (inv a)) a = b := by
  rw [mul_assoc, hlaw a ha ha0, mul_one hb]

/-- The other association, which is the form step 13 meets: the inverse arrives
on the left. -/
theorem inv_mul_cancel (hlaw : InverseLaw) {a b : Nat}
    (hb : b < p) (ha : a < p) (ha0 : a ≠ 0) : mul (inv a) (mul b a) = b := by
  rw [mul_comm b a, ← mul_assoc, hlaw a ha ha0, one_mul hb]

end Curve
end VQ
