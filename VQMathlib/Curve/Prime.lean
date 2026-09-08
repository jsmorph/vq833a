/-
Primality by Pratt certificate.

`VQMathlib.Curve.PrimeCert` uses these generic Pratt-certificate definitions and
proofs to establish primality of the secp256k1 field modulus.

The proof uses Mathlib's `lucas_primality`: if `a ^ (n - 1) = 1` in `ZMod n` and
`a ^ ((n - 1) / q) ≠ 1` for every prime `q` dividing `n - 1`, then `n` is prime.
A certificate supplies a witness, the prime factorization of `n - 1`, and a
recursive certificate for each factor.

Every arithmetic obligation is discharged in `Nat` by `VQ.Curve.powModOf`, which
is structurally recursive and reduces in the kernel.  `natCast_powModOf` moves
the result into `ZMod n`, and `natCast_inj_of_lt` carries a bounded equality back.
-/
import VQ.Curve.Field
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic

namespace VQBridge
namespace Prime

open VQ.Curve

/-! ## Nat and `ZMod n`

Both directions of the bridge, so that every computation happens where the kernel
can do it. -/

theorem natCast_inj_of_lt {n u v : Nat} [NeZero n] (hu : u < n) (hv : v < n)
    (h : (u : ZMod n) = (v : ZMod n)) : u = v := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hu, ZMod.val_cast_of_lt hv] at h'

theorem natCast_powModOf (n a e : Nat) :
    ((powModOf n a e : Nat) : ZMod n) = ((a : ZMod n)) ^ e := by
  rw [powModOf_eq, ZMod.natCast_mod]
  push_cast
  ring

/-- A power that reduces to one in `Nat` is one in `ZMod n`. -/
theorem pow_eq_one_of {n a e : Nat} (h : powModOf n a e = 1) :
    ((a : ZMod n)) ^ e = 1 := by
  rw [← natCast_powModOf, h, Nat.cast_one]

/-- A power that does not reduce to one in `Nat` is not one in `ZMod n`. -/
theorem pow_ne_one_of {n a e : Nat} (hn : 1 < n) (h : powModOf n a e ≠ 1) :
    ((a : ZMod n)) ^ e ≠ 1 := by
  have : NeZero n := ⟨by omega⟩
  rw [← natCast_powModOf]
  intro hc
  refine h (natCast_inj_of_lt (powModOf_lt (by omega) a e) hn ?_)
  rw [hc, Nat.cast_one]

/-! ## Prime divisors of the factor product

A prime dividing a product of primes occurs in the factor list, reducing the
quantifier in `lucas_primality` to a finite check. -/

theorem prime_mem_of_dvd_prod : ∀ (qs : List Nat), (∀ q ∈ qs, Nat.Prime q) →
    ∀ {r : Nat}, Nat.Prime r → r ∣ qs.prod → r ∈ qs := by
  intro qs
  induction qs with
  | nil =>
    intro _ r hr hd
    rw [List.prod_nil] at hd
    exact absurd (Nat.eq_one_of_dvd_one hd) hr.ne_one
  | cons q qs ih =>
    intro hq r hr hd
    rw [List.prod_cons] at hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr (hq q List.mem_cons_self)).mp h
      subst hrq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem q (ih (fun x hx => hq x (List.mem_cons_of_mem q hx)) hr h)

/-! ## Pratt certificate -/

/-- A Pratt certificate for `n`: a witness, the prime factorisation of `n - 1`,
and the two power conditions, all as `Nat` computations. -/
structure Cert (n : Nat) where
  one_lt : 1 < n
  witness : Nat
  factors : List Nat
  prod_eq : n - 1 = factors.prod
  factors_prime : ∀ q ∈ factors, Nat.Prime q
  pow_one : powModOf n witness (n - 1) = 1
  pow_ne : ∀ q ∈ factors, powModOf n witness ((n - 1) / q) ≠ 1

/-- A valid Pratt certificate proves primality. -/
theorem prime_of_cert {n : Nat} (c : Cert n) : Nat.Prime n := by
  refine lucas_primality n (c.witness : ZMod n) (pow_eq_one_of c.pow_one) ?_
  intro q hq hd
  refine pow_ne_one_of c.one_lt (c.pow_ne q ?_)
  exact prime_mem_of_dvd_prod c.factors c.factors_prime hq (c.prod_eq ▸ hd)

end Prime
end VQBridge
