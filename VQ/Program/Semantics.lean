/-
The denotation of a program: measurement, reset, and classical control.

A program denotes a list of branches.  Each branch carries the string of
measurement outcomes that produced it, the classical register it left behind,
and a subnormalised pure state.  The probability of the branch is the squared
norm of that state.  Measuring wire `q` with outcome `b` projects onto that
outcome, which zeroes components and stays inside `Dy d`, so `Vec`, `absSq`, and
`prob` carry over unchanged.  The branch list retains every measurement outcome
and its subnormalised pure state, which suffices for exact measurement, reset,
and feed-forward semantics.

Classical control can make branch arms perform different numbers of
measurements, so reachable outcome strings depend on earlier outcomes.  A total
function would require an index type containing unreachable strings and would
force normalization to sum over that larger type.  A list enumerates the exact
branch distribution, while a function-indexed family would also inherit the
poor kernel reduction of the closure-based state representation documented in
`VQ/Semantics/Eval.lean`.

`runOps` is structurally recursive through `Op.rec`, which carries a motive for
`Op` and one for `List Op` because `Op` nests the list.  `opInduction` packages
that pair as a single principle, and every proof that has to inspect a `branch`
uses it.  The recursion is structural, so a concrete program reduces in the
kernel and `Tests/ProgramSemantics.lean` decides its branches.

`reset` represents both measurement outcomes as branches and discards the
recorded outcome.  Combining them into one pure-state branch would lose
probability and require density-matrix semantics.  The pair of branches is the
ensemble written out.  The measurement string records the outcome, while the
classical register remains unchanged.

The semantics is total.  An ill-formed gate denotes the zero map, and measuring
an unavailable wire reports outcome zero with certainty.  Theorems state
well-formedness as a hypothesis.  `totalProb_runOps` uses the gate condition and
the reset wire bound, independent of the classical register.

The supporting lemmas establish conjugation and halving facts for `Dy d`,
block-sum identities for states, and norm preservation for primitive gates.
`normSq_gateVec` states unitarity as squared-norm preservation inside the exact
amplitude ring.  `VQMathlib/Semantics/Normalize.lean` proves the corresponding
complex circuit statement through Mathlib.
-/
import VQ.Program.Syntax
import VQ.Circuit.Library
import VQ.Semantics.Probability
import VQ.Algebra.GrindRing

namespace VQ
namespace Semantics

open Algebra

variable {d : Nat}

/-! ## Amplitudes -/

theorem conj_neg (x : Dy d) : Dy.conj (-x) = -Dy.conj x := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.neg_mk, Dy.conj_mk, Dy.conj_mk, Cyc.conj_neg, Dy.neg_mk]

theorem conj_sub (x y : Dy d) : Dy.conj (x - y) = Dy.conj x - Dy.conj y := by
  rw [Dy.sub_eq_add_neg, Dy.conj_add, conj_neg, Dy.sub_eq_add_neg]

theorem conj_pow (x : Dy d) (n : Nat) : Dy.conj (x ^ n) = Dy.conj x ^ n := by
  induction n with
  | zero => exact Dy.conj_one
  | succ n ih => rw [Dy.pow_succ, Dy.conj_mul, ih, Dy.pow_succ]

theorem conj_half (x : Dy d) : Dy.conj (Dy.half x) = Dy.half (Dy.conj x) := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.half_mk, Dy.conj_mk, Dy.conj_mk, Dy.half_mk]

theorem mul_pow (x y : Dy d) (n : Nat) : (x * y) ^ n = x ^ n * y ^ n := by
  induction n with
  | zero => exact (Dy.one_mul _).symm
  | succ n ih =>
    rw [Dy.pow_succ, Dy.pow_succ, Dy.pow_succ, ih]
    grind

theorem one_pow (n : Nat) : (Dy.one d) ^ n = Dy.one d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Dy.pow_succ, ih, Dy.mul_one]

theorem half_add (x y : Dy d) : Dy.half (x + y) = Dy.half x + Dy.half y := by
  refine Dy.ind (fun a m => ?_) x
  refine Dy.ind (fun b n => ?_) y
  rw [Dy.mk_add_mk, Dy.half_mk, Dy.half_mk, Dy.half_mk, Dy.mk_add_mk]
  refine Dy.sound ?_
  rw [Cyc.scale_add, Cyc.scale_add, Cyc.scale_scale, Cyc.scale_scale, Cyc.scale_scale,
    Cyc.scale_scale, show m + 1 + (n + 1) + n = m + n + 1 + (n + 1) from by omega,
    show m + 1 + (n + 1) + m = m + n + 1 + (m + 1) from by omega]

/-- Multiplication by two is injective because the ring is a localisation at
two.  A pairing argument may therefore halve both sides of a sum. -/
theorem add_self_cancel {x y : Dy d} (h : x + x = y + y) : x = y := by
  have hx : Dy.half (x + x) = x := by rw [half_add, Dy.half_add_half]
  have hy : Dy.half (y + y) = y := by rw [half_add, Dy.half_add_half]
  rw [← hx, ← hy, h]

theorem half_ofInt_two : Dy.half (Dy.ofInt d 2) = Dy.one d := by
  rw [Dy.ofInt, Dy.ofCyc, Dy.half_mk, Dy.one_eq]
  refine Dy.sound ?_
  rw [Cyc.scale_zero_exp, Cyc.scale_one_exp]
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  rw [Cyc.coeff_add, Cyc.coeff_one hi, Cyc.coeff_ofInt 2 hi]
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]; omega
  · rw [if_neg h0, if_neg h0]; omega

/-! ## Conjugation of the roots of unity -/

/-- `conj (ζ ^ a) = -ζ ^ (d - a)`, which is `ζ ^ (-a)` written inside the ring:
`ζ ^ d = -1`, so the inverse of a power is the complementary power with a
sign. -/
theorem conj_zeta_pow {a : Nat} (h1 : 1 ≤ a) (ha : a < d) :
    Cyc.conj (Cyc.zeta d ^ a) = -(Cyc.zeta d ^ (d - a)) := by
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  rw [Cyc.coeff_conj _ hi, Cyc.coeff_neg,
    Cyc.coeff_zeta_pow (show d - a < d from by omega) hi]
  by_cases h0 : i = 0
  · rw [if_pos h0, Cyc.coeff_zeta_pow ha (show 0 < d from by omega), if_neg (by omega),
      if_neg (by omega)]
    omega
  · rw [if_neg h0, Cyc.coeff_zeta_pow ha (show d - i < d from by omega)]
    by_cases hia : i = d - a
    · rw [if_pos hia, if_pos (by omega)]
    · rw [if_neg hia, if_neg (by omega)]

theorem dy_conj_zeta_pow {a : Nat} (h1 : 1 ≤ a) (ha : a < d) :
    Dy.conj (Dy.zeta d ^ a) = -(Dy.zeta d ^ (d - a)) := by
  rw [Dy.zeta, ← Dy.ofCyc_pow, Dy.ofCyc, Dy.conj_mk, conj_zeta_pow h1 ha, ← Dy.ofCyc,
    Dy.ofCyc_neg, Dy.ofCyc_pow]

theorem zeta_mul_conj (hd : 1 < d) : Dy.zeta d * Dy.conj (Dy.zeta d) = Dy.one d := by
  have h : Dy.zeta d ^ 1 = Dy.zeta d := by rw [Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]
  rw [← h, dy_conj_zeta_pow (Nat.le_refl 1) hd, Dy.mul_neg, ← Dy.pow_add,
    show 1 + (d - 1) = d from by omega, Dy.zeta_pow_d, Dy.neg_neg]

/-! ## Squared moduli -/

theorem absSq_zero : absSq (Dy.zero d) = Dy.zero d := Dy.zero_mul _

theorem absSq_one : absSq (Dy.one d) = Dy.one d := by rw [absSq, Dy.conj_one, Dy.one_mul]

theorem absSq_neg (x : Dy d) : absSq (-x) = absSq x := by
  rw [absSq, absSq, conj_neg, Dy.mul_neg, Dy.neg_mul, Dy.neg_neg]

theorem absSq_mul (x y : Dy d) : absSq (x * y) = absSq x * absSq y := by
  rw [absSq, absSq, absSq, Dy.conj_mul]
  grind

theorem absSq_zeta_pow (hd : 1 < d) (k : Nat) : absSq (Dy.zeta d ^ k) = Dy.one d := by
  rw [absSq, conj_pow, ← mul_pow, zeta_mul_conj hd, one_pow]

/-- Every gate phase has modulus one.  Diagonal gates built from these phases
are isometries. -/
theorem absSq_phase {level k : Nat} (hl : 1 < deg level) :
    absSq (phase level k) = Dy.one (deg level) := absSq_zeta_pow hl _

theorem absSq_phaseInv {level k : Nat} (hl : 1 < deg level) :
    absSq (phaseInv level k) = Dy.one (deg level) := absSq_zeta_pow hl _

/-! ## The square root of two -/

theorem conj_sqrt2 {e : Nat} (he : 4 * e = d) (h0 : 0 < e) :
    Dy.conj (Dy.sqrt2 d) = Dy.sqrt2 d := by
  have hq : d / 4 = e := by omega
  rw [Dy.sqrt2, hq, Dy.ofCyc, Dy.conj_mk, Cyc.sub_eq_add_neg, Cyc.conj_add, Cyc.conj_neg,
    conj_zeta_pow (by omega) (show e < d from by omega),
    conj_zeta_pow (by omega) (show 3 * e < d from by omega),
    show d - e = 3 * e from by omega, show d - 3 * e = e from by omega]
  congr 1
  rw [Cyc.neg_neg, Cyc.add_comm]

theorem conj_invSqrt2 {e : Nat} (he : 4 * e = d) (h0 : 0 < e) :
    Dy.conj (Dy.invSqrt2 d) = Dy.invSqrt2 d := by
  rw [Dy.invSqrt2, conj_half, conj_sqrt2 he h0]

/-- `|1/√2|² = 1/2`, the one amplitude fact the Hadamard case needs. -/
theorem absSq_invSqrt2 {e : Nat} (he : 4 * e = d) (h0 : 0 < e) :
    absSq (Dy.invSqrt2 d) = Dy.half (Dy.one d) := by
  rw [absSq, conj_invSqrt2 he h0, Dy.invSqrt2, Dy.half_mul, Dy.mul_comm, Dy.half_mul,
    Dy.sqrt2_mul_sqrt2 he, half_ofInt_two]

/-- At level three and above, the degree is a multiple of four and the ring
contains `1/√2`. -/
theorem four_dvd_deg {level : Nat} (hl : 3 ≤ level) : 4 * (2 ^ (level - 3)) = deg level := by
  have h : level - 1 = 2 + (level - 3) := by omega
  show 4 * 2 ^ (level - 3) = 2 ^ (level - 1)
  rw [h, Nat.pow_add]

/-! ## Block sums -/

theorem dsum_split (a b : Nat) (f : Nat → Dy d) :
    dsum (a + b) f = dsum a f + dsum b (fun i => f (a + i)) := by
  induction b with
  | zero => exact (Dy.add_zero _).symm
  | succ b ih =>
    show dsum (a + b + 1) f = _
    rw [dsum_succ, ih, dsum_succ, Dy.add_assoc]

theorem xor_two_pow_cancel (i k : Nat) : (i ^^^ 2 ^ k) ^^^ 2 ^ k = i := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Flipping a clear wire `q` adds `2 ^ q` to the basis index. -/
theorem xor_two_pow_of_lt {k i : Nat} (h : i < 2 ^ k) : i ^^^ 2 ^ k = 2 ^ k + i := by
  have hb : i.testBit k = false := Nat.testBit_lt_two_pow h
  rw [show (2:Nat) ^ k + i = 2 ^ k * 1 + i from by omega, Nat.two_pow_add_eq_or_of_lt h 1,
    Nat.mul_one]
  refine Nat.eq_of_testBit_eq (fun j => ?_)
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases hj : j = k
  · subst hj
    rw [Nat.testBit_two_pow_self, hb]
    simp
  · rw [Nat.testBit_two_pow_of_ne (fun he => hj he.symm)]
    simp

/--
A block sum is unchanged by flipping wire `q` of the index.

Wire `q` lies below the width, so the flip is a bijection of the block onto
itself.  The induction splits the block at its top bit: at that bit the flip
exchanges the two halves, and below it the flip acts on each half separately.
-/
theorem dsum_flip {q : Nat} : ∀ {w : Nat}, q < w → ∀ f : Nat → Dy d,
    dsum (2 ^ w) (fun i => f (i ^^^ 2 ^ q)) = dsum (2 ^ w) f := by
  intro w
  induction w with
  | zero => intro h; omega
  | succ k ih =>
    intro hq f
    have hsplit : (2:Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hsplit, dsum_split, dsum_split]
    by_cases hk : q = k
    · subst hk
      conv => rhs; rw [Dy.add_comm]
      congr 1
      · exact dsum_congr (fun i hi => by rw [xor_two_pow_of_lt hi])
      · refine dsum_congr (fun i hi => ?_)
        show f ((2 ^ q + i) ^^^ 2 ^ q) = f i
        rw [← xor_two_pow_of_lt hi, xor_two_pow_cancel]
    · have hq' : q < k := by omega
      have hpow : (2:Nat) ^ q < 2 ^ k := Nat.pow_lt_pow_of_lt (by omega) hq'
      congr 1
      · exact ih hq' f
      · have key : ∀ i, i < 2 ^ k → (2 ^ k + i) ^^^ 2 ^ q = 2 ^ k + (i ^^^ 2 ^ q) := by
          intro i hi
          rw [← xor_two_pow_of_lt hi, Nat.xor_assoc, Nat.xor_comm (2 ^ k), ← Nat.xor_assoc,
            xor_two_pow_of_lt (Nat.xor_lt_two_pow hi hpow)]
        calc dsum (2 ^ k) (fun i => f ((2 ^ k + i) ^^^ 2 ^ q))
            = dsum (2 ^ k) (fun i => (fun j => f (2 ^ k + j)) (i ^^^ 2 ^ q)) :=
              dsum_congr (fun i hi => by rw [key i hi])
          _ = dsum (2 ^ k) (fun i => f (2 ^ k + i)) := ih hq' (fun j => f (2 ^ k + j))

/--
Two block sums agree when they agree pair by pair across wire `q`.

Adding the sum to its own image under the flip doubles it, so an identity that
holds only after pairing an index with its partner still determines the sum.
The halving is `add_self_cancel`, which is available because the amplitude ring
is a localisation at two.
-/
theorem dsum_pair {q w : Nat} (hq : q < w) {F G : Nat → Dy d}
    (h : ∀ i, i < 2 ^ w → F i + F (i ^^^ 2 ^ q) = G i + G (i ^^^ 2 ^ q)) :
    dsum (2 ^ w) F = dsum (2 ^ w) G := by
  refine add_self_cancel ?_
  calc dsum (2 ^ w) F + dsum (2 ^ w) F
      = dsum (2 ^ w) F + dsum (2 ^ w) (fun i => F (i ^^^ 2 ^ q)) := by rw [dsum_flip hq]
    _ = dsum (2 ^ w) (fun i => F i + F (i ^^^ 2 ^ q)) := (dsum_add _ _ _).symm
    _ = dsum (2 ^ w) (fun i => G i + G (i ^^^ 2 ^ q)) := dsum_congr h
    _ = dsum (2 ^ w) G + dsum (2 ^ w) (fun i => G (i ^^^ 2 ^ q)) := dsum_add _ _ _
    _ = dsum (2 ^ w) G + dsum (2 ^ w) G := by rw [dsum_flip hq]

/-! ## The squared norm of a state -/

/-- The total weight of a state over the first `n` basis indices.  On a state
this is the probability that some outcome occurs, and on a branch of a program
it is the probability of that branch. -/
def normSq (n : Nat) (u : Vec d) : Dy d := dsum n (fun i => absSq (u i))

theorem normSq_zero (n : Nat) : normSq n (Vec.zero d) = Dy.zero d :=
  dsum_eq_zero (fun _ _ => absSq_zero)

theorem normSq_congr {n : Nat} {u v : Vec d} (h : ∀ i, i < n → u i = v i) :
    normSq n u = normSq n v := dsum_congr (fun i hi => by rw [h i hi])

theorem normSq_smul (n : Nat) (a : Dy d) (u : Vec d) :
    normSq n (a • u) = absSq a * normSq n u := by
  rw [normSq, normSq, dsum_mul_left]
  exact dsum_congr (fun i _ => absSq_mul a (u i))

/-! ## Every gate preserves the norm

A well-formed gate is unitary, and on a state supported by the register that is
the statement that its squared norm does not change.  The proof is by gate, and
three arguments cover the twelve: a diagonal gate multiplies by a phase of
modulus one, a permutation gate reindexes the block, and the Hadamard pairs each
index with its partner across the wire it acts on.  The proof acts directly on
states and requires neither `MatEq` nor matrix multiplication.
-/

theorem one_lt_deg {level : Nat} (hl : 2 ≤ level) : 1 < deg level := by
  show 1 < 2 ^ (level - 1)
  have h : (2:Nat) ^ 1 ≤ 2 ^ (level - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem absSq_invSqrt2_deg {level : Nat} (hl : 3 ≤ level) :
    absSq (Dy.invSqrt2 (deg level)) = Dy.half (Dy.one (deg level)) :=
  absSq_invSqrt2 (four_dvd_deg hl) (Nat.two_pow_pos _)

/-- Two Hadamard outputs recombine into the two inputs.  The cross terms cancel
between the sum and the difference, and `|1/√2|² = 1/2` halves what is left. -/
theorem absSq_pair {s : Dy d} (hs : absSq s = Dy.half (Dy.one d)) (a b : Dy d) :
    absSq (s * (a + b)) + absSq (s * (a - b)) = absSq a + absSq b := by
  have hring : absSq (a + b) + absSq (a - b) = (absSq a + absSq b) + (absSq a + absSq b) := by
    simp only [absSq, Dy.conj_add, conj_sub]
    grind
  rw [absSq_mul, absSq_mul, hs, ← Dy.left_distrib, hring, Dy.half_mul, Dy.one_mul, half_add,
    Dy.half_add_half]

theorem normSq_diagVec {q n : Nat} {a : Dy d} (ha : absSq a = Dy.one d) (u : Vec d) :
    normSq n (diagVec q a u) = normSq n u := by
  refine dsum_congr (fun i _ => ?_)
  show absSq (if i.testBit q then a * u i else u i) = absSq (u i)
  by_cases hb : i.testBit q = true
  · rw [if_pos hb, absSq_mul, ha, Dy.one_mul]
  · rw [if_neg hb]

theorem normSq_cczVec {a b c n : Nat} (u : Vec d) :
    normSq n (cczVec a b c u) = normSq n u := by
  refine dsum_congr (fun i _ => ?_)
  show absSq (if i.testBit a && i.testBit b && i.testBit c then -u i else u i) = absSq (u i)
  by_cases hb : i.testBit a && i.testBit b && i.testBit c
  · rw [if_pos hb, absSq_neg]
  · rw [if_neg hb]

theorem normSq_flipVec {q w : Nat} (hq : q < w) (u : Vec d) :
    normSq (2 ^ w) (flipVec q u) = normSq (2 ^ w) u := by
  show dsum (2 ^ w) (fun i => absSq (u (i ^^^ (1 <<< q)))) = dsum (2 ^ w) (fun i => absSq (u i))
  simp only [Nat.one_shiftLeft]
  exact dsum_flip hq (fun i => absSq (u i))

theorem normSq_yVec {q w : Nat} (hq : q < w) {a : Dy d} (ha : absSq a = Dy.one d) (u : Vec d) :
    normSq (2 ^ w) (yVec q a u) = normSq (2 ^ w) u := by
  have h1 : normSq (2 ^ w) (yVec q a u) = dsum (2 ^ w) (fun i => absSq (u (i ^^^ 2 ^ q))) := by
    refine dsum_congr (fun i _ => ?_)
    show absSq ((if i.testBit q then a else -a) * u (i ^^^ (1 <<< q))) = _
    rw [absSq_mul, Nat.one_shiftLeft]
    by_cases hb : i.testBit q = true
    · rw [if_pos hb, ha, Dy.one_mul]
    · rw [if_neg hb, absSq_neg, ha, Dy.one_mul]
  rw [h1]
  exact dsum_flip hq (fun i => absSq (u i))

theorem normSq_cxVec {a b w : Nat} (hbw : b < w) (hab : a ≠ b) (u : Vec d) :
    normSq (2 ^ w) (cxVec a b u) = normSq (2 ^ w) u := by
  refine dsum_pair hbw (fun i _ => ?_)
  have hflip : (i ^^^ 2 ^ b).testBit a = i.testBit a := by
    have h := testBit_xor_of_ne hab i
    rwa [Nat.one_shiftLeft] at h
  show absSq (u (cxIndex a b i)) + absSq (u (cxIndex a b (i ^^^ 2 ^ b)))
      = absSq (u i) + absSq (u (i ^^^ 2 ^ b))
  simp only [cxIndex, Nat.one_shiftLeft, hflip]
  by_cases hbit : i.testBit a = true
  · rw [if_pos hbit, if_pos hbit, xor_two_pow_cancel, Dy.add_comm]
  · rw [if_neg hbit, if_neg hbit]

theorem normSq_hVec {q w : Nat} (hq : q < w)
    (hs : absSq (Dy.invSqrt2 d) = Dy.half (Dy.one d)) (u : Vec d) :
    normSq (2 ^ w) (hVec q u) = normSq (2 ^ w) u := by
  have key : ∀ j : Nat, j.testBit q = false →
      absSq (hVec q u j) + absSq (hVec q u (j ^^^ 2 ^ q))
        = absSq (u j) + absSq (u (j ^^^ 2 ^ q)) := by
    intro j hj
    have hxj : (j ^^^ 2 ^ q).testBit q = true := by
      rw [← Nat.one_shiftLeft, testBit_xor_self, hj]
      rfl
    have e1 : hVec q u j = Dy.invSqrt2 d * (u j + u (j ^^^ 2 ^ q)) := by
      show Dy.invSqrt2 d * (if j.testBit q then u (j ^^^ (1 <<< q)) - u j
          else u j + u (j ^^^ (1 <<< q))) = _
      rw [if_neg (by rw [hj]; exact Bool.noConfusion), Nat.one_shiftLeft]
    have e2 : hVec q u (j ^^^ 2 ^ q) = Dy.invSqrt2 d * (u j - u (j ^^^ 2 ^ q)) := by
      show Dy.invSqrt2 d * (if (j ^^^ 2 ^ q).testBit q
          then u ((j ^^^ 2 ^ q) ^^^ (1 <<< q)) - u (j ^^^ 2 ^ q)
          else u (j ^^^ 2 ^ q) + u ((j ^^^ 2 ^ q) ^^^ (1 <<< q))) = _
      rw [if_pos hxj, Nat.one_shiftLeft, xor_two_pow_cancel]
    rw [e1, e2, absSq_pair hs]
  refine dsum_pair hq (fun i _ => ?_)
  by_cases hb : i.testBit q = true
  · have hb' : (i ^^^ 2 ^ q).testBit q = false := by
      rw [← Nat.one_shiftLeft, testBit_xor_self, hb]
      rfl
    have h2 := key (i ^^^ 2 ^ q) hb'
    rw [xor_two_pow_cancel] at h2
    rw [Dy.add_comm (absSq (hVec q u i)), h2, Dy.add_comm]
  · exact key i (Bool.eq_false_iff.mpr hb)

/-- A well-formed gate preserves the squared norm of every state.  An ill-formed
one does not: it denotes the zero map, which is why every statement below carries
well-formedness. -/
theorem normSq_gateVec (level w : Nat) {g : Gate} (hg : g.wellFormedAt level w = true)
    (u : Vec (deg level)) :
    normSq (2 ^ w) (gateVec level w g u) = normSq (2 ^ w) u := by
  rw [gateVec_of_wf hg]
  cases g with
  | x q =>
    simp only [Gate.wellFormedAt, decide_eq_true_eq] at hg
    exact normSq_flipVec hg u
  | h q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_hVec (by omega) (absSq_invSqrt2_deg (by omega)) u
  | y q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_yVec (by omega) (absSq_phase (one_lt_deg (by omega))) u
  | z q => exact normSq_diagVec (by rw [absSq_neg, absSq_one]) u
  | s q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phase (one_lt_deg (by omega))) u
  | sdg q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phaseInv (one_lt_deg (by omega))) u
  | t q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phase (one_lt_deg (by omega))) u
  | tdg q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phaseInv (one_lt_deg (by omega))) u
  | p k q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phase (one_lt_deg (by omega))) u
  | pdg k q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact normSq_diagVec (absSq_phaseInv (one_lt_deg (by omega))) u
  | cx a b =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hg
    exact normSq_cxVec (by omega) (by omega) u
  | ccz a b c => exact normSq_cczVec u

/-! ## Operation denotation -/

/--
One branch of a program's execution: the measurement record, the classical
register, and a subnormalised state.

`outcomes` carries every measurement outcome, most recent first, including the
ones a `reset` discards.  `creg` carries what the program can read: bit `c` is
classical bit `c`.  The two differ because a `reset` measures without recording
and because a later measurement may overwrite a classical bit, so the register
alone does not identify a branch.
-/
structure Branch (d : Nat) where
  outcomes : List Bool
  creg : Nat
  state : Vec d
  input : Nat := 0

/-- Set bit `c` of `n` to `b`.  Clearing is an exclusive-or with the bit's own
value, since `Nat` has no complement.  This writes the classical register below
and, in the uncompute theorem, a basis index. -/
def writeBit (n c : Nat) (b : Bool) : Nat :=
  if b then n ||| (1 <<< c) else n ^^^ (n &&& (1 <<< c))

def invertBit (n c : Nat) : Nat := n ^^^ (1 <<< c)

theorem testBit_writeBit (n c : Nat) (b : Bool) : (writeBit n c b).testBit c = b := by
  cases b with
  | true => simp [writeBit, Nat.testBit_or, Nat.one_shiftLeft]
  | false => simp [writeBit, Nat.testBit_xor, Nat.testBit_and, Nat.one_shiftLeft]

/-- Projection onto outcome `b` of wire `q`: keep the components where wire `q`
reads `b` and zero the rest.  This componentwise operation remains a pure-state
vector. -/
def projVec (q : Nat) (b : Bool) (u : Vec d) : Vec d :=
  fun i => if i.testBit q = b then u i else Dy.zero d

mutual
/--
The branches an operation produces.

`measure` splits into the two projections and records the outcome.  `reset` is a
measurement whose outcome is discarded, so it splits in the same way and the
outcome-one branch is flipped back to `|0⟩`.  Writing it as one branch would lose
probability, and writing it as a channel would need a density matrix.  `branch`
reads the classical register, which no state depends on, so it selects an arm
rather than superposing them.
-/
def runOp (level w : Nat) : Op → Branch (deg level) → List (Branch (deg level))
  | .gate g, b => [{ b with state := gateVec level w g b.state }]
  | .measure q c, b =>
      [ { outcomes := false :: b.outcomes, creg := writeBit b.creg c false,
          state := projVec q false b.state, input := b.input }
      , { outcomes := true :: b.outcomes, creg := writeBit b.creg c true,
          state := projVec q true b.state, input := b.input } ]
  | .reset q, b =>
      [ { outcomes := false :: b.outcomes, creg := b.creg,
          state := projVec q false b.state, input := b.input }
      , { outcomes := true :: b.outcomes, creg := b.creg,
          state := flipVec q (projVec q true b.state), input := b.input } ]
  | .store c value, b => [{ b with creg := writeBit b.creg c value }]
  | .invert c, b => [{ b with creg := invertBit b.creg c }]
  | .branch c t e, b =>
      if c.read b.input b.creg then runOps level w t b else runOps level w e b

/-- The branches produced by an operation list.  Each operation runs on every
branch produced by the preceding operations, as expressed by `flatMap`. -/
def runOps (level w : Nat) : List Op → Branch (deg level) → List (Branch (deg level))
  | [], b => [b]
  | o :: rest, b => (runOp level w o b).flatMap (runOps level w rest)
end

theorem runOp_gate (level w : Nat) (g : Gate) (b : Branch (deg level)) :
    runOp level w (.gate g) b = [{ b with state := gateVec level w g b.state }] := rfl

theorem runOp_measure (level w q c : Nat) (b : Branch (deg level)) :
    runOp level w (.measure q c) b =
      [ { outcomes := false :: b.outcomes, creg := writeBit b.creg c false,
          state := projVec q false b.state, input := b.input }
      , { outcomes := true :: b.outcomes, creg := writeBit b.creg c true,
          state := projVec q true b.state, input := b.input } ] := rfl

theorem runOp_reset (level w q : Nat) (b : Branch (deg level)) :
    runOp level w (.reset q) b =
      [ { outcomes := false :: b.outcomes, creg := b.creg,
          state := projVec q false b.state, input := b.input }
      , { outcomes := true :: b.outcomes, creg := b.creg,
          state := flipVec q (projVec q true b.state), input := b.input } ] := rfl

theorem runOp_store (level w c : Nat) (value : Bool) (b : Branch (deg level)) :
    runOp level w (.store c value) b = [{ b with creg := writeBit b.creg c value }] := rfl

theorem runOp_invert (level w c : Nat) (b : Branch (deg level)) :
    runOp level w (.invert c) b = [{ b with creg := invertBit b.creg c }] := rfl

theorem runOp_branch (level w : Nat) (c : CRef) (t e : List Op) (b : Branch (deg level)) :
    runOp level w (.branch c t e) b =
      if c.read b.input b.creg then runOps level w t b else runOps level w e b := rfl

theorem runOps_nil (level w : Nat) (b : Branch (deg level)) : runOps level w [] b = [b] := rfl

theorem runOps_cons (level w : Nat) (o : Op) (os : List Op) (b : Branch (deg level)) :
    runOps level w (o :: os) b = (runOp level w o b).flatMap (runOps level w os) := rfl

/--
Mutual induction over an operation and an operation list.

`Op` nests `List Op`, so its recursor carries a motive for each, and the list
half follows from the operation half by ordinary list induction.  Every proof
below that has to look inside a `branch` goes through this.
-/
theorem opInduction {P : Op → Prop} {Q : List Op → Prop}
    (hgate : ∀ g, P (.gate g)) (hmeasure : ∀ q c, P (.measure q c))
    (hreset : ∀ q, P (.reset q)) (hstore : ∀ c value, P (.store c value))
    (hinvert : ∀ c, P (.invert c))
    (hbranch : ∀ c t e, Q t → Q e → P (.branch c t e))
    (hnil : Q []) (hcons : ∀ o os, P o → Q os → Q (o :: os)) :
    (∀ o, P o) ∧ (∀ os, Q os) := by
  have h1 : ∀ o, P o :=
    fun o => Op.rec (motive_1 := P) (motive_2 := Q) hgate hmeasure hreset hstore hinvert
      hbranch hnil hcons o
  refine ⟨h1, fun os => ?_⟩
  induction os with
  | nil => exact hnil
  | cons o os ih => exact hcons o os (h1 o) ih

/-! ## Composition -/

/-- The operations of the first list run first, and each branch they leave runs
the second.  This is the program counterpart of `runGates_append`. -/
theorem runOps_append (level w : Nat) (a b : List Op) (br : Branch (deg level)) :
    runOps level w (a ++ b) br = (runOps level w a br).flatMap (runOps level w b) := by
  induction a generalizing br with
  | nil => rw [List.nil_append, runOps_nil, List.flatMap_singleton]
  | cons o rest ih =>
    have hfun : runOps level w (rest ++ b)
        = fun x => List.flatMap (runOps level w b) (runOps level w rest x) := funext ih
    rw [List.cons_append, runOps_cons, runOps_cons, List.flatMap_assoc, hfun]

/-! ## Support -/

theorem wfVec_projVec {n q : Nat} {u : Vec d} (v : Bool) (hu : WFVec n u) :
    WFVec n (projVec q v u) := by
  intro i hi
  show (if i.testBit q = v then u i else Dy.zero d) = Dy.zero d
  by_cases hb : i.testBit q = v
  · rw [if_pos hb]; exact hu i hi
  · rw [if_neg hb]

theorem two_pow_le_of_testBit {x q : Nat} (h : x.testBit q = true) : 2 ^ q ≤ x := by
  refine Nat.le_of_not_lt (fun hc => ?_)
  rw [Nat.testBit_lt_two_pow hc] at h
  exact Bool.noConfusion h

/-- The outcome-one branch of a reset stays inside the register whatever wire it
names.  Flipping a wire above the width would leave the register, but the
projection has already zeroed everything the flip could carry across. -/
theorem wfVec_resetVec {w q : Nat} {u : Vec d} (hu : WFVec (2 ^ w) u) :
    WFVec (2 ^ w) (flipVec q (projVec q true u)) := by
  intro i hi
  show (if (i ^^^ (1 <<< q)).testBit q = true then u (i ^^^ (1 <<< q)) else Dy.zero d)
      = Dy.zero d
  by_cases hb : (i ^^^ (1 <<< q)).testBit q = true
  · rw [if_pos hb]
    refine hu _ ?_
    by_cases hq : q < w
    · exact two_pow_le_xor hq hi
    · have h1 : (2:Nat) ^ q ≤ i ^^^ (1 <<< q) := by
        have h2 := two_pow_le_of_testBit hb
        rwa [Nat.one_shiftLeft] at h2 ⊢
      have h3 : (2:Nat) ^ w ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  · rw [if_neg hb]

/-- Every branch of a program stays inside the register the width declares. -/
theorem wfVec_runOp_runOps (level w : Nat) :
    (∀ o : Op, ∀ b : Branch (deg level), WFVec (2 ^ w) b.state →
        ∀ b' ∈ runOp level w o b, WFVec (2 ^ w) b'.state) ∧
    (∀ os : List Op, ∀ b : Branch (deg level), WFVec (2 ^ w) b.state →
        ∀ b' ∈ runOps level w os b, WFVec (2 ^ w) b'.state) := by
  refine opInduction (fun g b hb b' hm => ?_) (fun q c b hb b' hm => ?_)
    (fun q b hb b' hm => ?_) (fun c value b hb b' hm => ?_) (fun c b hb b' hm => ?_)
    (fun c t e ht he b hb b' hm => ?_) (fun b hb b' hm => ?_)
    (fun o os ho hos b hb b' hm => ?_)
  · rw [runOp_gate, List.mem_singleton] at hm
    subst hm
    exact wfVec_gateVec level w g hb
  · rw [runOp_measure] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact wfVec_projVec false hb
    · exact wfVec_projVec true hb
  · rw [runOp_reset] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact wfVec_projVec false hb
    · exact wfVec_resetVec hb
  · rw [runOp_store, List.mem_singleton] at hm
    subst hm
    exact hb
  · rw [runOp_invert, List.mem_singleton] at hm
    subst hm
    exact hb
  · rw [runOp_branch] at hm
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc] at hm
      exact ht b hb b' hm
    · rw [if_neg hc] at hm
      exact he b hb b' hm
  · rw [runOps_nil, List.mem_singleton] at hm
    subst hm
    exact hb
  · rw [runOps_cons, List.mem_flatMap] at hm
    obtain ⟨x, hx, hb'⟩ := hm
    exact hos x (ho b hb x hx) b' hb'

theorem wfVec_runOps (level w : Nat) (os : List Op) {b : Branch (deg level)}
    (hb : WFVec (2 ^ w) b.state) {b' : Branch (deg level)} (hm : b' ∈ runOps level w os b) :
    WFVec (2 ^ w) b'.state := (wfVec_runOp_runOps level w).2 os b hb b' hm

theorem input_runOp_runOps (level w : Nat) :
    (∀ o : Op, ∀ b b' : Branch (deg level), b' ∈ runOp level w o b →
      b'.input = b.input) ∧
    (∀ os : List Op, ∀ b b' : Branch (deg level), b' ∈ runOps level w os b →
      b'.input = b.input) := by
  refine opInduction (fun g b b' hm => ?_) (fun q c b b' hm => ?_)
    (fun q b b' hm => ?_) (fun c value b b' hm => ?_) (fun c b b' hm => ?_)
    (fun c t e ht he b b' hm => ?_) (fun b b' hm => ?_)
    (fun o os ho hos b b' hm => ?_)
  · simpa [runOp_gate] using congrArg Branch.input (List.mem_singleton.mp hm)
  · rw [runOp_measure] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> rfl
  · rw [runOp_reset] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> rfl
  · simpa [runOp_store] using congrArg Branch.input (List.mem_singleton.mp hm)
  · simpa [runOp_invert] using congrArg Branch.input (List.mem_singleton.mp hm)
  · rw [runOp_branch] at hm
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc] at hm
      exact ht b b' hm
    · rw [if_neg hc] at hm
      exact he b b' hm
  · rw [runOps_nil, List.mem_singleton] at hm
    exact congrArg Branch.input hm
  · rw [runOps_cons, List.mem_flatMap] at hm
    obtain ⟨x, hx, hb'⟩ := hm
    exact (hos x b' hb').trans (ho b x hx)

theorem input_runOps (level w : Nat) (os : List Op) {b b' : Branch (deg level)}
    (hm : b' ∈ runOps level w os b) : b'.input = b.input :=
  (input_runOp_runOps level w).2 os b b' hm

/-! ## Linearity -/

/-- A branch with its state scaled.  The measurement record and classical
register remain fixed.  This invariance preserves branch structure under state
scaling. -/
def smulBranch (a : Dy d) (b : Branch d) : Branch d := { b with state := a • b.state }

theorem projVec_smul (q : Nat) (v : Bool) (a : Dy d) (u : Vec d) :
    projVec q v (a • u) = a • projVec q v u := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q = v then a * u i else Dy.zero d) = a * (if i.testBit q = v then u i else _)
  by_cases hb : i.testBit q = v
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, Dy.mul_zero]

/-- Scaling the input scales every branch.  The list of branches is the same
list, because classical control reads the register and not the state. -/
theorem runOps_smul (level w : Nat) :
    (∀ o : Op, ∀ (a : Dy (deg level)) (b : Branch (deg level)),
        runOp level w o (smulBranch a b) = (runOp level w o b).map (smulBranch a)) ∧
    (∀ os : List Op, ∀ (a : Dy (deg level)) (b : Branch (deg level)),
        runOps level w os (smulBranch a b) = (runOps level w os b).map (smulBranch a)) := by
  refine opInduction (fun g a b => ?_) (fun q c a b => ?_) (fun q a b => ?_)
    (fun c value a b => ?_) (fun c a b => ?_) (fun c t e ht he a b => ?_)
    (fun a b => rfl) (fun o os ho hos a b => ?_)
  · simp only [runOp_gate, smulBranch, gateVec_smul, List.map_cons, List.map_nil]
  · simp only [runOp_measure, smulBranch, projVec_smul, List.map_cons, List.map_nil]
  · simp only [runOp_reset, smulBranch, projVec_smul, flipVec_smul, List.map_cons, List.map_nil]
  · rfl
  · rfl
  · rw [runOp_branch, runOp_branch]
    show (if c.read b.input b.creg then _ else _) = _
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc, if_pos hc, ht]
    · rw [if_neg hc, if_neg hc, he]
  · have hfun : (fun x => runOps level w os (smulBranch a x))
        = fun x => (runOps level w os x).map (smulBranch a) := funext (fun x => hos a x)
    rw [runOps_cons, runOps_cons, ho, List.flatMap_map, List.map_flatMap, hfun]

/-- The zero state is a fixed point: every branch of a program run on it is
zero.  This is the program counterpart of `runGates_zero`. -/
theorem runOps_zero_state (level w : Nat) (os : List Op) (rec : List Bool) (n input : Nat)
    {b' : Branch (deg level)}
    (hm : b' ∈ runOps level w os (Branch.mk rec n (Vec.zero (deg level)) input)) :
    b'.state = Vec.zero (deg level) := by
  have hsm : smulBranch (Dy.zero (deg level))
      (Branch.mk rec n (Vec.zero (deg level)) input)
      = Branch.mk rec n (Vec.zero (deg level)) input := by
    show Branch.mk rec n (Dy.zero (deg level) • Vec.zero (deg level)) input = _
    rw [Vec.smul_zero]
  rw [← hsm, (runOps_smul level w).2] at hm
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
  exact Vec.ext (fun i => Dy.zero_mul _)

/-! ## Branch-list shape

The classical register and the measurement record a branch carries do not depend
on the state, since the only thing that reads the register is `branch` and the
only thing that writes it is `measure`.  Computing them without a state is what
lets the two runs in an additivity statement be compared position by position.
-/

mutual
/-- The input, measurement record, and mutable register an operation produces,
with no quantum state. -/
def opShape : Op → List Bool → Nat → Nat → List (List Bool × Nat × Nat)
  | .gate _, rec, n, input => [(rec, n, input)]
  | .measure _ c, rec, n, input =>
      [(false :: rec, writeBit n c false, input),
       (true :: rec, writeBit n c true, input)]
  | .reset _, rec, n, input => [(false :: rec, n, input), (true :: rec, n, input)]
  | .store c value, rec, n, input => [(rec, writeBit n c value, input)]
  | .invert c, rec, n, input => [(rec, invertBit n c, input)]
  | .branch c t e, rec, n, input =>
      if c.read input n then opsShape t rec n input else opsShape e rec n input

def opsShape : List Op → List Bool → Nat → Nat → List (List Bool × Nat × Nat)
  | [], rec, n, input => [(rec, n, input)]
  | o :: rest, rec, n, input =>
      (opShape o rec n input).flatMap (fun p => opsShape rest p.1 p.2.1 p.2.2)
end

/-- The classical part of a branch list. -/
def shape (bs : List (Branch d)) : List (List Bool × Nat × Nat) :=
  bs.map (fun b => (b.outcomes, b.creg, b.input))

theorem shape_runOps (level w : Nat) :
    (∀ o : Op, ∀ (rec : List Bool) (n input : Nat) (u : Vec (deg level)),
        shape (runOp level w o (Branch.mk rec n u input)) = opShape o rec n input) ∧
    (∀ os : List Op, ∀ (rec : List Bool) (n input : Nat) (u : Vec (deg level)),
        shape (runOps level w os (Branch.mk rec n u input)) = opsShape os rec n input) := by
  refine opInduction (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun c t e ht he rec n input u => ?_) (fun _ _ _ _ => rfl)
    (fun o os ho hos rec n input u => ?_)
  · show shape (if c.read input n then runOps level w t (Branch.mk rec n u input)
        else runOps level w e (Branch.mk rec n u input))
      = if c.read input n then opsShape t rec n input else opsShape e rec n input
    by_cases hc : c.read input n = true
    · rw [if_pos hc, if_pos hc]
      exact ht rec n input u
    · rw [if_neg hc, if_neg hc]
      exact he rec n input u
  · have hfun : (fun b : Branch (deg level) => shape (runOps level w os b))
        = fun b => opsShape os b.outcomes b.creg b.input :=
      funext (fun b => hos b.outcomes b.creg b.input b.state)
    show shape (List.flatMap (runOps level w os)
        (runOp level w o (Branch.mk rec n u input)))
        = List.flatMap (fun p => opsShape os p.1 p.2.1 p.2.2) (opShape o rec n input)
    rw [shape, List.map_flatMap]
    show List.flatMap (fun b => shape (runOps level w os b))
        (runOp level w o (Branch.mk rec n u input)) = _
    rw [hfun, ← ho rec n input u, shape, List.flatMap_map]

theorem length_runOps (level w : Nat) (os : List Op) (b : Branch (deg level)) :
    (runOps level w os b).length = (opsShape os b.outcomes b.creg b.input).length := by
  have h := congrArg List.length
    ((shape_runOps level w).2 os b.outcomes b.creg b.input b.state)
  rwa [shape, List.length_map] at h

/-! ## Additivity -/

/-- Two branches added state by state.  It is used only where the two agree on
the classical part, which `shape_runOps` supplies. -/
def addBranch (p q : Branch d) : Branch d := { p with state := p.state + q.state }

theorem projVec_add (q : Nat) (v : Bool) (u₁ u₂ : Vec d) :
    projVec q v (u₁ + u₂) = projVec q v u₁ + projVec q v u₂ := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q = v then u₁ i + u₂ i else Dy.zero d)
      = (if i.testBit q = v then u₁ i else Dy.zero d)
        + (if i.testBit q = v then u₂ i else Dy.zero d)
  by_cases hb : i.testBit q = v
  · rw [if_pos hb, if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, if_neg hb, Dy.add_zero]

/-- Running an operation list on a list of branches added state by state is the
same as running it on each and adding.  This is the step the induction below
takes at a cons, and it is where the shape lemma is needed: `zipWith` splits
across an append only when the pieces have equal lengths. -/
theorem flatMap_zipWith (level w : Nat) (os : List Op)
    (hadd : ∀ (rec : List Bool) (n input : Nat) (u v : Vec (deg level)),
      runOps level w os (Branch.mk rec n (u + v) input)
        = List.zipWith addBranch (runOps level w os (Branch.mk rec n u input))
            (runOps level w os (Branch.mk rec n v input))) :
    ∀ L M : List (Branch (deg level)), shape L = shape M →
      List.flatMap (runOps level w os) (List.zipWith addBranch L M)
        = List.zipWith addBranch (List.flatMap (runOps level w os) L)
            (List.flatMap (runOps level w os) M) := by
  intro L
  induction L with
  | nil => intro M _; rfl
  | cons p ps ih =>
    intro M hs
    cases M with
    | nil => simp [shape] at hs
    | cons q qs =>
      simp only [shape, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
      obtain ⟨⟨hrec, hcreg, hinput⟩, hrest⟩ := hs
      have hq : q = Branch.mk p.outcomes p.creg q.state p.input := by
        rw [hrec, hcreg, hinput]
      have hlen : (runOps level w os p).length = (runOps level w os q).length := by
        rw [length_runOps, length_runOps, hrec, hcreg, hinput]
      have hpq : runOps level w os (addBranch p q)
          = List.zipWith addBranch (runOps level w os p) (runOps level w os q) := by
        have h := hadd p.outcomes p.creg p.input p.state q.state
        rw [← hq] at h
        exact h
      rw [List.zipWith_cons_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
        List.zipWith_append hlen, hpq, ih qs hrest]

/-- Adding two inputs adds the branches position by position.  The branch list
is the same list, because classical control reads the register and not the
state.  This is the program counterpart of `runGates_add`. -/
theorem runOps_add (level w : Nat) :
    (∀ o : Op, ∀ (rec : List Bool) (n input : Nat) (u v : Vec (deg level)),
        runOp level w o (Branch.mk rec n (u + v) input)
          = List.zipWith addBranch (runOp level w o (Branch.mk rec n u input))
              (runOp level w o (Branch.mk rec n v input))) ∧
    (∀ os : List Op, ∀ (rec : List Bool) (n input : Nat) (u v : Vec (deg level)),
        runOps level w os (Branch.mk rec n (u + v) input)
          = List.zipWith addBranch (runOps level w os (Branch.mk rec n u input))
              (runOps level w os (Branch.mk rec n v input))) := by
  refine opInduction (fun g rec n input u v => ?_) (fun q c rec n input u v => ?_)
    (fun q rec n input u v => ?_) (fun c value rec n input u v => ?_)
    (fun c rec n input u v => ?_) (fun c t e ht he rec n input u v => ?_)
    (fun _ _ _ _ _ => rfl) (fun o os ho hos rec n input u v => ?_)
  · simp only [runOp_gate, gateVec_add, List.zipWith_cons_cons, List.zipWith_nil_left, addBranch]
  · simp only [runOp_measure, projVec_add, List.zipWith_cons_cons, List.zipWith_nil_left,
      addBranch]
  · simp only [runOp_reset, projVec_add, flipVec_add, List.zipWith_cons_cons,
      List.zipWith_nil_left, addBranch]
  · rfl
  · rfl
  · show (if c.read input n then runOps level w t (Branch.mk rec n (u + v) input)
        else runOps level w e (Branch.mk rec n (u + v) input))
      = List.zipWith addBranch
          (if c.read input n then runOps level w t (Branch.mk rec n u input)
            else runOps level w e (Branch.mk rec n u input))
          (if c.read input n then runOps level w t (Branch.mk rec n v input)
            else runOps level w e (Branch.mk rec n v input))
    by_cases hc : c.read input n = true
    · rw [if_pos hc, if_pos hc, if_pos hc, ht]
    · rw [if_neg hc, if_neg hc, if_neg hc, he]
  · have hshape : shape (runOp level w o (Branch.mk rec n u input))
        = shape (runOp level w o (Branch.mk rec n v input)) := by
      rw [(shape_runOps level w).1 o rec n input u,
        (shape_runOps level w).1 o rec n input v]
    rw [runOps_cons, runOps_cons, runOps_cons, ho, flatMap_zipWith level w os hos _ _ hshape]

/-! ## Branch probabilities -/

/-- The probability of a branch: the squared norm of its subnormalised state. -/
def branchProb (w : Nat) (b : Branch d) : Dy d := normSq (2 ^ w) b.state

/-- The probability that the program takes some branch of the given list. -/
def totalProb (w : Nat) : List (Branch d) → Dy d
  | [] => Dy.zero d
  | b :: bs => branchProb w b + totalProb w bs

theorem totalProb_nil (w : Nat) : totalProb w ([] : List (Branch d)) = Dy.zero d := rfl

theorem totalProb_cons (w : Nat) (b : Branch d) (bs : List (Branch d)) :
    totalProb w (b :: bs) = branchProb w b + totalProb w bs := rfl

theorem totalProb_append (w : Nat) (l₁ l₂ : List (Branch d)) :
    totalProb w (l₁ ++ l₂) = totalProb w l₁ + totalProb w l₂ := by
  induction l₁ with
  | nil => exact (Dy.zero_add _).symm
  | cons b bs ih => rw [List.cons_append, totalProb_cons, ih, totalProb_cons, Dy.add_assoc]

/-- The two outcomes of a measurement partition the state, so their
probabilities add up to what was there before.  Every index contributes to
exactly one of the two projections. -/
theorem normSq_proj_add (n q : Nat) (u : Vec d) :
    normSq n (projVec q false u) + normSq n (projVec q true u) = normSq n u := by
  rw [normSq, normSq, normSq, ← dsum_add]
  refine dsum_congr (fun i _ => ?_)
  show absSq (if i.testBit q = false then u i else Dy.zero d)
      + absSq (if i.testBit q = true then u i else Dy.zero d) = absSq (u i)
  cases hb : i.testBit q
  · show absSq (u i) + absSq (Dy.zero d) = absSq (u i)
    rw [absSq_zero, Dy.add_zero]
  · show absSq (Dy.zero d) + absSq (u i) = absSq (u i)
    rw [absSq_zero, Dy.zero_add]

theorem opWellFormed_gate (level w iw cw : Nat) (g : Gate) :
    Program.opWellFormed level w iw cw (.gate g) = g.wellFormedAt level w := rfl

theorem opsWellFormed_cons (level w iw cw : Nat) (o : Op) (os : List Op) :
    Program.opsWellFormed level w iw cw (o :: os)
      = (Program.opWellFormed level w iw cw o &&
        Program.opsWellFormed level w iw cw os) := rfl

/-- Running an operation list on every branch of a list adds nothing and loses
nothing, given that it preserves the probability of one branch.  This is the
step the induction below takes at a cons. -/
theorem totalProb_flatMap (level w : Nat) (os : List Op) (L : List (Branch (deg level)))
    (hL : ∀ b ∈ L, WFVec (2 ^ w) b.state)
    (hQ : ∀ b : Branch (deg level), WFVec (2 ^ w) b.state →
        totalProb w (runOps level w os b) = branchProb w b) :
    totalProb w (L.flatMap (runOps level w os)) = totalProb w L := by
  induction L with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatMap_cons, totalProb_append, hQ b (hL b (by simp)), totalProb_cons,
      ih (fun x hx => hL x (by simp [hx]))]

/--
A well-formed program's branch probabilities sum to the norm of its input.

The gate case is unitarity, the measurement and reset cases are the partition of
the state by the outcome, and the branch case runs one arm.  Two conjuncts of
well-formedness are consumed: an ill-formed gate denotes the zero map, which
loses all the probability, and the reset case reads the flip back through
`normSq_flipVec`, which needs the wire.  The classical bounds are not used.  A
measurement of a wire the register does not have reports outcome zero with
certainty, which keeps the probability rather than losing it.
-/
theorem totalProb_runOps (level w iw cw : Nat) :
    (∀ o : Op, Program.opWellFormed level w iw cw o = true → ∀ b : Branch (deg level),
        WFVec (2 ^ w) b.state → totalProb w (runOp level w o b) = branchProb w b) ∧
    (∀ os : List Op, Program.opsWellFormed level w iw cw os = true →
      ∀ b : Branch (deg level),
        WFVec (2 ^ w) b.state → totalProb w (runOps level w os b) = branchProb w b) := by
  refine opInduction (fun g hwf b hb => ?_) (fun q c hwf b hb => ?_) (fun q hwf b hb => ?_)
    (fun c value hwf b hb => ?_) (fun c hwf b hb => ?_)
    (fun c t e ht he hwf b hb => ?_) (fun hwf b hb => ?_)
    (fun o os ho hos hwf b hb => ?_)
  · rw [runOp_gate, totalProb_cons, totalProb_nil, Dy.add_zero]
    exact normSq_gateVec level w hwf b.state
  · rw [runOp_measure, totalProb_cons, totalProb_cons, totalProb_nil, Dy.add_zero]
    exact normSq_proj_add (2 ^ w) q b.state
  · rw [runOp_reset, totalProb_cons, totalProb_cons, totalProb_nil, Dy.add_zero]
    have hq : q < w := by
      simp only [Program.opWellFormed, decide_eq_true_eq] at hwf
      exact hwf
    show normSq (2 ^ w) (projVec q false b.state)
        + normSq (2 ^ w) (flipVec q (projVec q true b.state)) = _
    rw [normSq_flipVec hq]
    exact normSq_proj_add (2 ^ w) q b.state
  · rw [runOp_store, totalProb_cons, totalProb_nil, Dy.add_zero]
    rfl
  · rw [runOp_invert, totalProb_cons, totalProb_nil, Dy.add_zero]
    rfl
  · simp only [Program.opWellFormed, Bool.and_eq_true] at hwf
    rw [runOp_branch]
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc]
      exact ht hwf.1.2 b hb
    · rw [if_neg hc]
      exact he hwf.2 b hb
  · rw [runOps_nil, totalProb_cons, totalProb_nil, Dy.add_zero]
  · rw [opsWellFormed_cons, Bool.and_eq_true] at hwf
    rw [runOps_cons,
      totalProb_flatMap level w os _
        (fun x hx => (wfVec_runOp_runOps level w).1 o b hb x hx) (hos hwf.2)]
    exact ho hwf.1 b hb

/-! ## Program denotation -/

/-- The denotation of a program on an input state: the family of subnormalised
states indexed by the measurement record, with the classical register each one
ends with. -/
def runProgram (level : Nat) (p : Program) (input : Nat) (u : Vec (deg level)) :
    List (Branch (deg level)) :=
  runOps level p.width p.ops { outcomes := [], creg := 0, state := u, input := input }

theorem input_runProgram (level : Nat) (p : Program) (input : Nat) (u : Vec (deg level))
    {b : Branch (deg level)} (hb : b ∈ runProgram level p input u) : b.input = input :=
  input_runOps level p.width p.ops hb

theorem totalProb_runProgram (level : Nat) (p : Program) (hp : p.wellFormed level = true)
    (input : Nat) {u : Vec (deg level)} (hu : WFVec (2 ^ p.width) u) :
    totalProb p.width (runProgram level p input u) = normSq (2 ^ p.width) u :=
  (totalProb_runOps level p.width p.inputBits p.cbits).2 p.ops hp _ hu

theorem normSq_basis {n j : Nat} (hj : j < n) : normSq n (basis j : Vec d) = Dy.one d := by
  rw [normSq, dsum_eq_single hj (fun i _ hij => by rw [basis_of_ne hij, absSq_zero]), basis_self,
    absSq_one]

/-- The branch probabilities of a well-formed program run on a basis state sum
to one.  Each branch's squared norm therefore defines its probability. -/
theorem totalProb_basis (level : Nat) (p : Program) (hp : p.wellFormed level = true)
    (input : Nat) {inp : Nat} (hinp : inp < 2 ^ p.width) :
    totalProb p.width (runProgram level p input (basis inp)) = Dy.one (deg level) := by
  rw [totalProb_runProgram level p hp input (wfVec_basis hinp), normSq_basis hinp]

/-! ## Programs that only run gates -/

theorem flatMap_singleton_id {α : Type} (L : List α) : L.flatMap (fun x => [x]) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, ih]; rfl

theorem runOps_singleton (level w : Nat) (o : Op) (br : Branch (deg level)) :
    runOps level w [o] br = runOp level w o br := by
  rw [runOps_cons]
  exact flatMap_singleton_id _

/-- A list of gate operations leaves one branch, carrying the circuit's state.
Nothing branches, so the measurement record and the classical register are
untouched. -/
theorem runOps_gates (level w : Nat) (gs : List Gate) (br : Branch (deg level)) :
    runOps level w (gs.map Op.gate) br
      = [{ br with state := runGates level w gs br.state }] := by
  induction gs generalizing br with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, runOps_cons, runOp_gate, List.flatMap_singleton, ih]
    rfl

/-- The admitted Clifford sequence `X Z X Z` is global negation. -/
theorem runGates_globalNeg {level w q : Nat} (hl : 1 ≤ level) (hq : q < w)
    (u : Vec (deg level)) :
    runGates level w [.x q, .z q, .x q, .z q] u = -u := by
  have hx : (Gate.x q).wellFormedAt level w = true := by
    simp [Gate.wellFormedAt, hq]
  have hz : (Gate.z q).wellFormedAt level w = true := by
    simp [Gate.wellFormedAt, hq, hl]
  simp only [runGates_cons, runGates_nil]
  rw [gateVec_of_wf hz, gateVec_of_wf hx, gateVec_of_wf hz, gateVec_of_wf hx]
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then -Dy.one (deg level) *
      (if (i ^^^ (1 <<< q)).testBit q then
        -Dy.one (deg level) * u ((i ^^^ (1 <<< q)) ^^^ (1 <<< q))
      else u ((i ^^^ (1 <<< q)) ^^^ (1 <<< q)))
    else if (i ^^^ (1 <<< q)).testBit q then
      -Dy.one (deg level) * u ((i ^^^ (1 <<< q)) ^^^ (1 <<< q))
    else u ((i ^^^ (1 <<< q)) ^^^ (1 <<< q))) = -u i
  rw [xor_cancel, testBit_xor_self]
  by_cases hb : i.testBit q = true
  · simp [hb, Dy.neg_mul, Dy.one_mul]
  · simp [hb, Dy.neg_mul, Dy.one_mul]

theorem runOps_globalNeg {level w q : Nat} (hl : 1 ≤ level) (hq : q < w)
    (b : Branch (deg level)) :
    runOps level w (Op.globalNeg q) b = [{ b with state := -b.state }] := by
  rw [Op.globalNeg]
  change runOps level w ([.x q, .z q, .x q, .z q].map Op.gate) b = _
  rw [runOps_gates, runGates_globalNeg hl hq]

/-- A unitary circuit read as a program denotes what the circuit denotes.  This
is what keeps the two semantics from drifting. -/
theorem runProgram_ofCircuit (level : Nat) (cir : Circuit) (u : Vec (deg level)) :
    runProgram level (Program.ofCircuit cir) 0 u
      = [{ outcomes := [], creg := 0, state := run level cir u, input := 0 }] :=
  runOps_gates level cir.width cir.gates _

/-! ## Controlled-Z as a conjugated CNOT -/

theorem invSqrt2_sq_two {e : Nat} (he : 4 * e = d) (h0 : 0 < e) :
    Dy.invSqrt2 d * Dy.invSqrt2 d + Dy.invSqrt2 d * Dy.invSqrt2 d = 1 := by
  have h : Dy.invSqrt2 d * Dy.invSqrt2 d = Dy.half (Dy.one d) := by
    have h2 := absSq_invSqrt2 he h0
    rwa [absSq, conj_invSqrt2 he h0] at h2
  rw [h, Dy.half_add_half]
  rfl

/--
`h b; cx a b; h b` is controlled-Z, on an arbitrary state.

Wire `a` is untouched by the Hadamards, so the pair `i` and `i ^^^ (1 <<< b)`
carries the computation: with `a` clear the CNOT is the identity and the two
Hadamards cancel, and with `a` set the CNOT is an `x` on wire `b` and `h x h` is
`z`.
-/
theorem hVec_cxVec_hVec {e : Nat} (he : 4 * e = d) (h0 : 0 < e) {a b : Nat} (hab : a ≠ b)
    (u : Vec d) :
    hVec b (cxVec a b (hVec b u))
      = fun i => if i.testBit a && i.testBit b then -u i else u i := by
  have hs := invSqrt2_sq_two he h0
  refine Vec.ext (fun i => ?_)
  have hcancel : (i ^^^ (1 <<< b)) ^^^ (1 <<< b) = i := xor_cancel i b
  have hta : (i ^^^ (1 <<< b)).testBit a = i.testBit a := testBit_xor_of_ne hab i
  have htb : (i ^^^ (1 <<< b)).testBit b = !i.testBit b := testBit_xor_self i b
  cases hA : i.testBit a <;> cases hB : i.testBit b <;>
    simp only [hVec, cxVec, cxIndex, hcancel, hta, htb, hA, hB, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
    grind

/-! ## Gidney's measurement-based uncompute -/

theorem testBit_writeBit_of_ne {n c r : Nat} (h : r ≠ c) (b : Bool) :
    (writeBit n c b).testBit r = n.testBit r := by
  cases b with
  | true =>
    simp [writeBit, Nat.testBit_or, Nat.one_shiftLeft,
      Nat.testBit_two_pow_of_ne (fun he => h he.symm)]
  | false =>
    simp [writeBit, Nat.testBit_xor, Nat.testBit_and, Nat.one_shiftLeft,
      Nat.testBit_two_pow_of_ne (fun he => h he.symm)]

theorem writeBit_self {n c : Nat} {b : Bool} (h : n.testBit c = b) : writeBit n c b = n := by
  refine Nat.eq_of_testBit_eq (fun r => ?_)
  by_cases hr : r = c
  · subst hr; rw [testBit_writeBit, h]
  · rw [testBit_writeBit_of_ne hr]

theorem writeBit_xor (i c : Nat) (b : Bool) :
    writeBit (i ^^^ (1 <<< c)) c b = writeBit i c b := by
  refine Nat.eq_of_testBit_eq (fun r => ?_)
  by_cases hr : r = c
  · subst hr; rw [testBit_writeBit, testBit_writeBit]
  · rw [testBit_writeBit_of_ne hr, testBit_writeBit_of_ne hr, testBit_xor_of_ne hr]

/-- Wire `c` holds the AND of wires `a` and `b`: every component where it does
not is zero.  This is the state a temporary AND leaves behind, and it is the
hypothesis the uncompute needs. -/
def AndAncilla (a b c : Nat) (u : Vec d) : Prop :=
  ∀ i, i.testBit c ≠ (i.testBit a && i.testBit b) → u i = Dy.zero d

/-- The data carried by the register, read with wire `c` set to the value
forced by the AND.  The result is independent of wire `c` in the input index,
so the ancilla factors from the data state. -/
def andData (a b c : Nat) (u : Vec d) : Vec d :=
  fun i => u (writeBit i c (i.testBit a && i.testBit b))

/-- `v` with wire `c` held in `|0⟩`. -/
def ancillaZero (c : Nat) (v : Vec d) : Vec d :=
  fun i => if i.testBit c then Dy.zero d else v i

/-- Gidney's uncompute of a temporary AND: a Hadamard on the ancilla, a
measurement of it, and a controlled-Z on the two inputs when the outcome is
one.  The `cz` is Clifford, which is the saving: uncomputing the same ancilla
unitarily costs a second `ccz`. -/
def andUncompute (a b c m : Nat) : List Op :=
  [Op.gate (Gate.h c), Op.measure c m,
   Op.branch (.localBit m) ((Circuit.cz a b).map Op.gate) []]

theorem andData_xor {a b c : Nat} (hac : a ≠ c) (hbc : b ≠ c) (u : Vec d) (i : Nat) :
    andData a b c u (i ^^^ (1 <<< c)) = andData a b c u i := by
  show u (writeBit (i ^^^ (1 <<< c)) c _) = u (writeBit i c _)
  rw [testBit_xor_of_ne hac i, testBit_xor_of_ne hbc i, writeBit_xor]

/-- The input written through its data: the amplitude is the data where wire `c`
agrees with the AND and zero everywhere else. -/
theorem eq_andData {a b c : Nat} {u : Vec d} (hu : AndAncilla a b c u) (j : Nat) :
    u j = if j.testBit c = (j.testBit a && j.testBit b) then andData a b c u j
      else Dy.zero d := by
  by_cases h : j.testBit c = (j.testBit a && j.testBit b)
  · rw [if_pos h]
    show u j = u (writeBit j c _)
    rw [writeBit_self h]
  · rw [if_neg h]
    exact hu j h

/--
The Hadamard on the ancilla leaves the data with a sign that records the AND.

Both components of wire `c` carry the same data amplitude, and the one where the
wire reads one carries `(-1)` to the AND.  That sign is what the correction
cancels.
-/
theorem hVec_andAncilla {a b c : Nat} (hac : a ≠ c) (hbc : b ≠ c) {u : Vec d}
    (hu : AndAncilla a b c u) (i : Nat) :
    hVec c u i = Dy.invSqrt2 d *
      (if i.testBit c && (i.testBit a && i.testBit b) then -andData a b c u i
        else andData a b c u i) := by
  have h1 : u i = if i.testBit c = (i.testBit a && i.testBit b) then andData a b c u i
      else Dy.zero d := eq_andData hu i
  have h2 : u (i ^^^ (1 <<< c)) = if (!i.testBit c) = (i.testBit a && i.testBit b)
      then andData a b c u i else Dy.zero d := by
    have h := eq_andData hu (i ^^^ (1 <<< c))
    rwa [testBit_xor_of_ne hac i, testBit_xor_of_ne hbc i, testBit_xor_self i c,
      andData_xor hac hbc u i] at h
  show Dy.invSqrt2 d * (if i.testBit c then u (i ^^^ (1 <<< c)) - u i
      else u i + u (i ^^^ (1 <<< c))) = _
  cases hc : i.testBit c
  · cases ht : i.testBit a && i.testBit b
    · rw [hc, ht] at h1 h2
      rw [h1, h2]
      show Dy.invSqrt2 d * (andData a b c u i + Dy.zero d) = Dy.invSqrt2 d * andData a b c u i
      rw [Dy.add_zero]
    · rw [hc, ht] at h1 h2
      rw [h1, h2]
      show Dy.invSqrt2 d * (Dy.zero d + andData a b c u i) = Dy.invSqrt2 d * andData a b c u i
      rw [Dy.zero_add]
  · cases ht : i.testBit a && i.testBit b
    · rw [hc, ht] at h1 h2
      rw [h1, h2]
      show Dy.invSqrt2 d * (andData a b c u i - Dy.zero d) = Dy.invSqrt2 d * andData a b c u i
      rw [sub_zero]
    · rw [hc, ht] at h1 h2
      rw [h1, h2]
      show Dy.invSqrt2 d * (Dy.zero d - andData a b c u i)
          = Dy.invSqrt2 d * -andData a b c u i
      rw [Dy.sub_eq_add_neg, Dy.zero_add]

/--
Gidney's uncompute, as an equality of branch lists.

The two outcome branches differ only by an `x` on wire `c`.  Both leave the data
register in the same state, with the ancilla in a basis state, so discarding the
ancilla requires no partial trace.  The correction cancels the outcome-one
branch's input-dependent `(-1)` phase.
-/
theorem runOps_andUncompute {level w a b c m : Nat} (hl : 3 ≤ level)
    (haw : a < w) (hbw : b < w) (hcw : c < w) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u : Vec (deg level)} (hu : AndAncilla a b c u) (rec : List Bool) (n input : Nat) :
    runOps level w (andUncompute a b c m)
      { outcomes := rec, creg := n, state := u, input := input }
      = [ { outcomes := false :: rec, creg := writeBit n m false,
            state := ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u), input := input }
        , { outcomes := true :: rec, creg := writeBit n m true,
            state := flipVec c
              (ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u)), input := input } ] := by
  have hgh : (Gate.h c).wellFormedAt level w = true := by
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hghb : (Gate.h b).wellFormedAt level w = true := by
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hgcx : (Gate.cx a b).wellFormedAt level w = true := by
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    exact ⟨⟨haw, hbw⟩, hab⟩
  have hstep : runOps level w (andUncompute a b c m)
      { outcomes := rec, creg := n, state := u, input := input }
      = [ { outcomes := false :: rec, creg := writeBit n m false,
            state := projVec c false (hVec c u), input := input }
        , { outcomes := true :: rec, creg := writeBit n m true,
            state := runGates level w (Circuit.cz a b) (projVec c true (hVec c u)),
            input := input } ] := by
    rw [andUncompute, runOps_cons, runOp_gate, gateVec_of_wf hgh, List.flatMap_singleton,
      runOps_cons, runOp_measure, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, runOps_singleton, runOps_singleton, runOp_branch, runOp_branch,
      CRef.read, CRef.read, testBit_writeBit, testBit_writeBit,
      if_neg (fun h => Bool.noConfusion h), if_pos rfl,
      runOps_nil, runOps_gates]
    rfl
  have hcz : runGates level w (Circuit.cz a b) (projVec c true (hVec c u))
      = fun i => if i.testBit a && i.testBit b then -(projVec c true (hVec c u) i)
          else projVec c true (hVec c u) i := by
    show gateVec level w (Gate.h b) (gateVec level w (Gate.cx a b)
        (gateVec level w (Gate.h b) (projVec c true (hVec c u)))) = _
    rw [gateVec_of_wf hghb, gateVec_of_wf hgcx, gateVec_of_wf hghb]
    exact hVec_cxVec_hVec (four_dvd_deg hl) (Nat.two_pow_pos _) hab _
  have e0 : projVec c false (hVec c u)
      = ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u) := by
    refine Vec.ext (fun i => ?_)
    show (if i.testBit c = false then hVec c u i else Dy.zero (deg level))
        = if i.testBit c then Dy.zero (deg level) else Dy.invSqrt2 (deg level) * andData a b c u i
    rw [hVec_andAncilla hac hbc hu i]
    cases hc : i.testBit c
    · show Dy.invSqrt2 (deg level) * (if false && _ then _ else _) = _
      rfl
    · rfl
  have e1 : runGates level w (Circuit.cz a b) (projVec c true (hVec c u))
      = flipVec c (ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u)) := by
    rw [hcz]
    refine Vec.ext (fun i => ?_)
    show (if i.testBit a && i.testBit b
        then -(if i.testBit c = true then hVec c u i else Dy.zero (deg level))
        else if i.testBit c = true then hVec c u i else Dy.zero (deg level))
      = if (i ^^^ (1 <<< c)).testBit c then Dy.zero (deg level)
        else Dy.invSqrt2 (deg level) * andData a b c u (i ^^^ (1 <<< c))
    rw [testBit_xor_self i c, andData_xor hac hbc u i, hVec_andAncilla hac hbc hu i]
    cases hc : i.testBit c
    · cases ht : i.testBit a && i.testBit b
      · rfl
      · show -Dy.zero (deg level) = Dy.zero (deg level)
        exact neg_zero
    · cases ht : i.testBit a && i.testBit b
      · rfl
      · show -(Dy.invSqrt2 (deg level) * -andData a b c u i)
            = Dy.invSqrt2 (deg level) * andData a b c u i
        rw [Dy.mul_neg, Dy.neg_neg]
  rw [hstep, e0, e1]

/--
Summing the squared data amplitudes over the half of the register where wire `c`
is clear recovers the norm of the whole state.

The AND fixes wire `c` on the support, so each pair of indices across that wire
carries one data amplitude and one zero.
-/
theorem dsum_andData {level w a b c : Nat} (hcw : c < w) (hac : a ≠ c) (hbc : b ≠ c)
    {u : Vec (deg level)} (hu : AndAncilla a b c u) :
    dsum (2 ^ w) (fun i => if i.testBit c then Dy.zero (deg level)
        else absSq (andData a b c u i)) = normSq (2 ^ w) u := by
  refine dsum_pair hcw (fun i _ => ?_)
  rw [← Nat.one_shiftLeft]
  have h1 : u i = if i.testBit c = (i.testBit a && i.testBit b) then andData a b c u i
      else Dy.zero (deg level) := eq_andData hu i
  have h2 : u (i ^^^ (1 <<< c)) = if (!i.testBit c) = (i.testBit a && i.testBit b)
      then andData a b c u i else Dy.zero (deg level) := by
    have h := eq_andData hu (i ^^^ (1 <<< c))
    rwa [testBit_xor_of_ne hac i, testBit_xor_of_ne hbc i, testBit_xor_self i c,
      andData_xor hac hbc u i] at h
  have hd : andData a b c u (i ^^^ (1 <<< c)) = andData a b c u i := andData_xor hac hbc u i
  have hcx : (i ^^^ (1 <<< c)).testBit c = !i.testBit c := testBit_xor_self i c
  rw [hd, hcx, h1, h2]
  cases hc : i.testBit c
  · cases ht : i.testBit a && i.testBit b
    · show absSq (andData a b c u i) + Dy.zero (deg level)
          = absSq (andData a b c u i) + absSq (Dy.zero (deg level))
      rw [absSq_zero]
    · show absSq (andData a b c u i) + Dy.zero (deg level)
          = absSq (Dy.zero (deg level)) + absSq (andData a b c u i)
      rw [absSq_zero, Dy.zero_add, Dy.add_zero]
  · cases ht : i.testBit a && i.testBit b
    · show Dy.zero (deg level) + absSq (andData a b c u i)
          = absSq (Dy.zero (deg level)) + absSq (andData a b c u i)
      rw [absSq_zero]
    · show Dy.zero (deg level) + absSq (andData a b c u i)
          = absSq (andData a b c u i) + absSq (Dy.zero (deg level))
      rw [absSq_zero, Dy.zero_add, Dy.add_zero]

theorem normSq_ancillaZero {level w c : Nat} (hl : 3 ≤ level) (v : Vec (deg level)) :
    normSq (2 ^ w) (ancillaZero c (Dy.invSqrt2 (deg level) • v))
      = Dy.half (dsum (2 ^ w)
          (fun i => if i.testBit c then Dy.zero (deg level) else absSq (v i))) := by
  have key : ∀ i, absSq (ancillaZero c (Dy.invSqrt2 (deg level) • v) i)
      = Dy.half (Dy.one (deg level))
        * (if i.testBit c then Dy.zero (deg level) else absSq (v i)) := by
    intro i
    show absSq (if i.testBit c then Dy.zero (deg level) else Dy.invSqrt2 (deg level) * v i)
        = Dy.half (Dy.one (deg level))
          * (if i.testBit c then Dy.zero (deg level) else absSq (v i))
    cases hc : i.testBit c
    · show absSq (Dy.invSqrt2 (deg level) * v i) = Dy.half (Dy.one (deg level)) * absSq (v i)
      rw [absSq_mul, absSq_invSqrt2_deg hl]
    · show absSq (Dy.zero (deg level))
          = Dy.half (Dy.one (deg level)) * Dy.zero (deg level)
      rw [absSq_zero, Dy.mul_zero]
  rw [normSq, dsum_congr (fun i _ => key i), ← dsum_mul_left, Dy.half_mul, Dy.one_mul]

/--
Each branch of Gidney's uncompute carries half the input's weight.

With a normalised input, each outcome has probability one half.  The measurement
result is unbiased and carries no information about the data.
-/
theorem branchProb_andUncompute {level w a b c m : Nat} (hl : 3 ≤ level)
    (haw : a < w) (hbw : b < w) (hcw : c < w) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u : Vec (deg level)} (hu : AndAncilla a b c u) (rec : List Bool) (n input : Nat) :
    (runOps level w (andUncompute a b c m)
        { outcomes := rec, creg := n, state := u, input := input }).map (branchProb w)
      = [Dy.half (normSq (2 ^ w) u), Dy.half (normSq (2 ^ w) u)] := by
  have hhalf : normSq (2 ^ w) (ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u))
      = Dy.half (normSq (2 ^ w) u) := by
    rw [normSq_ancillaZero hl, dsum_andData hcw hac hbc hu]
  rw [runOps_andUncompute hl haw hbw hcw hab hac hbc hu rec n input,
    List.map_cons, List.map_cons,
    List.map_nil]
  show [normSq (2 ^ w) (ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u)),
      normSq (2 ^ w) (flipVec c (ancillaZero c (Dy.invSqrt2 (deg level) • andData a b c u)))]
    = _
  rw [normSq_flipVec hcw, hhalf]

end Semantics
end VQ
