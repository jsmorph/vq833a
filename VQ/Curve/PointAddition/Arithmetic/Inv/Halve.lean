import VQ.Curve.PointAddition.Arithmetic.Inv.Round

/-!
# Modular halving

The correction divides by two `k` times.  Halving modulo an odd `p` is exact
when the value is even and adds the modulus first when it is odd, which makes it
even.  Doubling the result returns the value, or the value plus the modulus, so
halving is multiplication by the inverse of two.

Cancelling that two needs only that `p` is odd: if `p` divides `2 m` and `p` is
odd then `p` divides `m`, because the quotient cannot be odd against an even
product.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

/-- Halve modulo `p`. -/
def mhalve (p a : Nat) : Nat := if a % 2 = 0 then a / 2 else (a + p) / 2

/-- The output of modular halving determines the input parity.  With `p` odd
and `a < p`, an even `a` halves to below `(p + 1) / 2`, while an odd `a`
halves to at least that threshold.  These ranges identify the branch and allow
one control wire to serve every halving. -/
theorem mhalve_gt {p a : Nat} (hp : p % 2 = 1) (ha : a < p) :
    ((p - 1) / 2 < mhalve p a) ↔ a % 2 = 1 := by
  unfold mhalve
  by_cases h : a % 2 = 0
  · rw [if_pos h]
    constructor
    · intro hlt; omega
    · intro hodd; omega
  · rw [if_neg h]
    have hodd : a % 2 = 1 := by omega
    constructor
    · intro _; exact hodd
    · intro _; omega

/-- Doubling undoes it, up to the modulus. -/
theorem mhalve_two {p a : Nat} (hp : p % 2 = 1) :
    2 * mhalve p a = a ∨ 2 * mhalve p a = a + p := by
  unfold mhalve
  by_cases h : a % 2 = 0
  · rw [if_pos h]; left; omega
  · rw [if_neg h]; right; omega

/-- It stays in range. -/
theorem mhalve_lt {p a : Nat} (hp : p % 2 = 1) (h : a < p) : mhalve p a < p := by
  unfold mhalve
  by_cases he : a % 2 = 0
  · rw [if_pos he]; omega
  · rw [if_neg he]; omega

/-! ## Congruence as divisibility

Two values agree modulo `p` exactly when `p` divides their difference.  Both
directions are needed: one to turn the halving's congruence into a divisibility,
the other to turn it back. -/

theorem dvd_sub_of_mod_eq {p a b : Nat} (hab : b ≤ a) (h : a % p = b % p) : p ∣ (a - b) := by
  have ha := Nat.div_add_mod a p
  have hb := Nat.div_add_mod b p
  have hle : b / p ≤ a / p := Nat.div_le_div_right hab
  refine ⟨a / p - b / p, ?_⟩
  have e : p * (a / p - b / p) = p * (a / p) - p * (b / p) := by rw [Nat.mul_sub]
  omega

theorem mod_eq_of_dvd_sub {p a b : Nat} (hab : b ≤ a) (h : p ∣ (a - b)) : a % p = b % p := by
  obtain ⟨c, hc⟩ := h
  have e : a = b + p * c := by omega
  rw [e, Nat.add_mul_mod_self_left]

/-- An odd modulus divides a doubled value only by dividing the value. -/
theorem dvd_of_two_mul {p m : Nat} (hp : p % 2 = 1) (h : p ∣ 2 * m) : p ∣ m := by
  obtain ⟨t, ht⟩ := h
  have ht2 : t % 2 = 0 := by
    have hm : (p * t) % 2 = 0 := by rw [← ht]; omega
    rw [Nat.mul_mod, hp, Nat.one_mul] at hm
    omega
  obtain ⟨t', rfl⟩ : ∃ t', t = 2 * t' := ⟨t / 2, by omega⟩
  have e : p * (2 * t') = 2 * (p * t') := by rw [Nat.mul_left_comm]
  exact ⟨t', by omega⟩

/-- Cancelling a two on both sides of a congruence at an odd modulus. -/
theorem cancel_two {p a b : Nat} (hp : p % 2 = 1) (h : (2 * a) % p = (2 * b) % p) :
    a % p = b % p := by
  rcases Nat.le_total b a with hab | hab
  · have hd : p ∣ 2 * a - 2 * b := dvd_sub_of_mod_eq (by omega) h
    have he : 2 * a - 2 * b = 2 * (a - b) := by omega
    rw [he] at hd
    exact mod_eq_of_dvd_sub hab (dvd_of_two_mul hp hd)
  · have hd : p ∣ 2 * b - 2 * a := dvd_sub_of_mod_eq (by omega) h.symm
    have he : 2 * b - 2 * a = 2 * (b - a) := by omega
    rw [he] at hd
    exact (mod_eq_of_dvd_sub hab (dvd_of_two_mul hp hd)).symm

/-! ## Repeated-halving semantics

`k` halvings divide by `2 ^ k`.  The invariant runs downward: after `j` of them
the value is what the original was, divided by `2 ^ j`. -/

/-- Halve `j` times. -/
def mhalves (p : Nat) : Nat → Nat → Nat
  | 0, a => a
  | j + 1, a => mhalves p j (mhalve p a)

/-- The halve-last form, against a definition that halves first. -/
theorem mhalves_succ' {p : Nat} : ∀ (j a : Nat),
    mhalves p (j + 1) a = mhalve p (mhalves p j a)
  | 0, _ => rfl
  | j + 1, a => by
    show mhalves p (j + 1) (mhalve p a) = mhalve p (mhalves p j (mhalve p a))
    exact mhalves_succ' j (mhalve p a)

/-- Adding one to the count is one more halving at the end. -/
theorem mhalves_add_one {p : Nat} (j a : Nat) :
    mhalves p (j + 1) a = mhalve p (mhalves p j a) := mhalves_succ' j a

theorem mhalves_lt {p : Nat} (hp : p % 2 = 1) :
    ∀ (j a : Nat), a < p → mhalves p j a < p
  | 0, a, h => h
  | j + 1, a, h => mhalves_lt hp j _ (mhalve_lt hp h)

/-- Halving `j` times divides by `2 ^ j`.  The congruence states that
multiplication by `2 ^ j` restores the original residue. -/
theorem mhalves_two {p : Nat} (hp : p % 2 = 1) :
    ∀ (j a : Nat), (2 ^ j * mhalves p j a) % p = a % p
  | 0, a => by simp [mhalves]
  | j + 1, a => by
    have hstep : (2 * mhalve p a) % p = a % p := by
      rcases mhalve_two (p := p) (a := a) hp with h | h
      · rw [h]
      · rw [h, Nat.add_mod_right]
    have hih := mhalves_two hp j (mhalve p a)
    show (2 ^ (j + 1) * mhalves p j (mhalve p a)) % p = a % p
    have hpow : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    rw [hpow, Nat.mul_assoc, Nat.mul_mod, hih, ← Nat.mul_mod, ← hstep]

/-- Cancelling a whole power of two. -/
theorem cancel_pow_two {p : Nat} (hp : p % 2 = 1) : ∀ (j a b : Nat),
    (2 ^ j * a) % p = (2 ^ j * b) % p → a % p = b % p
  | 0, a, b, h => by simpa using h
  | j + 1, a, b, h => by
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
    rw [hpow] at h
    have h2 : (2 ^ j * (2 * a)) % p = (2 ^ j * (2 * b)) % p := by
      have e1 : 2 ^ j * 2 * a = 2 ^ j * (2 * a) := by rw [Nat.mul_assoc]
      have e2 : 2 ^ j * 2 * b = 2 ^ j * (2 * b) := by rw [Nat.mul_assoc]
      rw [← e1, ← e2]; exact h
    exact cancel_two hp (cancel_pow_two hp j (2 * a) (2 * b) h2)

/-- An inverse modulo `p` is unique below `p`. -/
theorem inv_unique {p x a b : Nat} (ha : a < p) (hb : b < p)
    (h1 : (x * a) % p = 1 % p) (h2 : (x * b) % p = 1 % p) : a = b := by
  have e1 : (a * (x * b)) % p = a % p := by
    rw [Nat.mul_mod, h2, ← Nat.mul_mod, Nat.mul_one]
  have e2 : (b * (x * a)) % p = b % p := by
    rw [Nat.mul_mod, h1, ← Nat.mul_mod, Nat.mul_one]
  have e3 : a * (x * b) = b * (x * a) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a x, Nat.mul_comm b x,
      Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm b a]
  rw [e3, e2] at e1
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] at e1
  omega

/-! ## Almost-inverse correction

The chain leaves `r` with `x r + 2 ^ k` zero modulo `p`.  Reducing and negating
gives `a` with `x a` congruent to `2 ^ k`, and `k` halvings then give a value
whose product with `x` is one. -/

/-- The correction inverts. -/
theorem fix_inverts {p x r k : Nat} (hp : p % 2 = 1) (hpp : 0 < p)
    (halm : (x * r + 2 ^ k) % p = 0) (hr : r < p) (hr0 : 0 < r) :
    (x * mhalves p k (p - r)) % p = 1 % p := by
  have hlt : p - r < p := by omega
  -- `x (p - r)` is congruent to `2 ^ k`.
  have hneg : (x * (p - r)) % p = (2 ^ k) % p := by
    have hexp : x * (p - r) + (x * r + 2 ^ k) = x * p + 2 ^ k := by
      have : x * (p - r) + x * r = x * p := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    have h1 : (x * (p - r) + (x * r + 2 ^ k)) % p = (x * (p - r)) % p := by
      rw [Nat.add_mod, halm, Nat.add_zero, Nat.mod_mod_of_dvd _ (Nat.dvd_refl p)]
    have h2 : (x * p + 2 ^ k) % p = (2 ^ k) % p := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [hexp] at h1
    rw [← h1, h2]
  -- The halvings divide by `2 ^ k`.
  have hhalf := mhalves_two (p := p) hp k (p - r)
  -- Multiply the two together and cancel.
  have hmul : (2 ^ k * (x * mhalves p k (p - r))) % p = (2 ^ k * 1) % p := by
    have e : 2 ^ k * (x * mhalves p k (p - r)) = x * (2 ^ k * mhalves p k (p - r)) := by
      rw [Nat.mul_left_comm]
    rw [e, Nat.mul_mod, hhalf, ← Nat.mul_mod, hneg, Nat.mul_one]
  exact cancel_pow_two hp k _ 1 hmul

end VQ.Curve.PointAddition.Arithmetic.Inv
