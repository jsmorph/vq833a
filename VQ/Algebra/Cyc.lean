/-
The cyclotomic integers ℤ[x]/(x^d + 1).

An element is a list of `d` integer coefficients.  Lists support kernel
reduction of concrete identities through `decide`, unlike the corresponding
functions out of `Fin d`.  The `length_eq` field is proof-irrelevant, so equality
of elements reduces to equality of coefficient lists.

Multiplication is negacyclic convolution: `x^d = -1` sends a product of degree
`k + d` back to degree `k` with a sign.  The proofs go through `ecoeff`, which
reads a coefficient at every degree rather than only below `d` and satisfies
`ecoeff a (n + d) = -ecoeff a n`, and through `window`, a `d`-term sum of
products `A i * B j` with `i + j` fixed.  For a pair of sequences with that
antiperiodicity the window depends only on `i + j` and not on where the range of
`i` starts, which is `window_shift`.  Associativity and the multiplicativity of
`conj` are then sums that differ by a shift of the range.
-/
import VQ.Algebra.Sum

namespace VQ
namespace Algebra

/-- An element of ℤ[x]/(x^d + 1), given by its `d` coefficients from degree zero
upwards. -/
structure Cyc (d : Nat) where
  coeffs : List Int
  length_eq : coeffs.length = d

namespace Cyc

variable {d : Nat}

/-- Coefficient of `x^i`, reading as zero at `i ≥ d`. -/
def coeff (a : Cyc d) (i : Nat) : Int := a.coeffs.getD i 0

theorem coeff_eq_zero (a : Cyc d) {i : Nat} (h : d ≤ i) : a.coeff i = 0 := by
  have hl : a.coeffs.length ≤ i := by rw [a.length_eq]; exact h
  simp [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]

theorem coeff_eq_getElem (a : Cyc d) {i : Nat} (h : i < a.coeffs.length) :
    a.coeff i = a.coeffs[i] := by
  simp [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem eq_of_coeffs {a b : Cyc d} (h : a.coeffs = b.coeffs) : a = b := by
  cases a; cases b; subst h; rfl

/-- Two elements with the same coefficients below `d` are equal.  At `d = 0` the
hypothesis is vacuous and every two elements are equal, which is right: the ring
is then the zero ring. -/
theorem eq_of_coeff {a b : Cyc d} (h : ∀ i, i < d → a.coeff i = b.coeff i) : a = b := by
  refine eq_of_coeffs (List.ext_getElem (by rw [a.length_eq, b.length_eq]) ?_)
  intro i h1 h2
  rw [← coeff_eq_getElem a h1, ← coeff_eq_getElem b h2]
  exact h i (by rw [← a.length_eq]; exact h1)

instance : DecidableEq (Cyc d) := fun a b =>
  if h : a.coeffs = b.coeffs then isTrue (eq_of_coeffs h)
  else isFalse (fun he => h (by rw [he]))

/-- The element whose `i`-th coefficient is `f i`. -/
def ofFn (d : Nat) (f : Nat → Int) : Cyc d := ⟨(List.range d).map f, by simp⟩

theorem coeff_ofFn {d i : Nat} {f : Nat → Int} (h : i < d) : (ofFn d f).coeff i = f i := by
  simp [coeff, ofFn, List.getD_eq_getElem?_getD, h]

/-- The element with the given coefficients, padded with zeros to length `d` and
truncated beyond it.

Truncation is wrong for anything that reads a coefficient list as a polynomial,
because in this ring `x^d = -1` and a coefficient at degree `d` or above has a
value.  `ofListWrapped` is the version that folds.  Use it unless the list is
known to be short. -/
def ofList (d : Nat) (l : List Int) : Cyc d := ofFn d (fun i => l.getD i 0)

theorem coeff_ofList {d i : Nat} {l : List Int} (h : i < d) :
    (ofList d l).coeff i = l.getD i 0 := coeff_ofFn h

/-! ## Cyclotomic operations -/

def zero (d : Nat) : Cyc d := ofFn d (fun _ => 0)

/-- The image of an integer. -/
def ofInt (d : Nat) (c : Int) : Cyc d := ofFn d (fun i => if i = 0 then c else 0)

def one (d : Nat) : Cyc d := ofInt d 1

def add (a b : Cyc d) : Cyc d := ofFn d (fun i => a.coeff i + b.coeff i)

def neg (a : Cyc d) : Cyc d := ofFn d (fun i => -a.coeff i)

def sub (a b : Cyc d) : Cyc d := add a (neg b)

/-- Multiplication by an integer. -/
def smul (c : Int) (a : Cyc d) : Cyc d := ofFn d (fun i => c * a.coeff i)

/-- `k - i` taken modulo `d`. -/
def subMod (d k i : Nat) : Nat := (d + k - i) % d

/-- The sign carried by the term `a i * b (k - i)` in the coefficient of `x^k`.
When `i > k` the two factors have degrees summing to `k + d`, so the term passes
once through `x^d = -1`. -/
def wrapSign (i k : Nat) : Int := if i ≤ k then 1 else -1

/-- Negacyclic convolution. -/
def mul (a b : Cyc d) : Cyc d :=
  ofFn d (fun k => sum d (fun i => wrapSign i k * a.coeff i * b.coeff (subMod d k i)))

instance : Add (Cyc d) := ⟨add⟩
instance : Neg (Cyc d) := ⟨neg⟩
instance : Sub (Cyc d) := ⟨sub⟩
instance : Mul (Cyc d) := ⟨mul⟩

def pow (a : Cyc d) : Nat → Cyc d
  | 0 => one d
  | n + 1 => pow a n * a

instance : Pow (Cyc d) Nat := ⟨pow⟩

/-- The class of `x`.  It is a primitive `2 * d`-th root of unity.  At `d = 1`
the relation `x + 1 = 0` already forces `x = -1`, which is why the coefficient
is `-1` there. -/
def zeta (d : Nat) : Cyc d :=
  ofFn d (fun i => if 1 < d then (if i = 1 then 1 else 0) else -1)

/-- The involution sending `x` to `x⁻¹`.  Since `x^d = -1`, `x⁻¹ = -x^(d-1)`,
so degree `j` moves to degree `d - j` and picks up a sign. -/
def conj (a : Cyc d) : Cyc d :=
  ofFn d (fun j => if j = 0 then a.coeff 0 else -a.coeff (d - j))

/-! ## Coefficients of the operations -/

theorem coeff_zero (i : Nat) : (zero d).coeff i = 0 := by
  by_cases h : i < d
  · rw [zero, coeff_ofFn h]
  · exact coeff_eq_zero _ (Nat.le_of_not_lt h)

theorem coeff_ofInt (c : Int) {i : Nat} (h : i < d) :
    (ofInt d c).coeff i = if i = 0 then c else 0 := coeff_ofFn h

theorem coeff_one {i : Nat} (h : i < d) : (one d).coeff i = if i = 0 then 1 else 0 :=
  coeff_ofFn h

theorem coeff_add (a b : Cyc d) (i : Nat) : (a + b).coeff i = a.coeff i + b.coeff i := by
  by_cases h : i < d
  · exact coeff_ofFn h
  · rw [coeff_eq_zero _ (Nat.le_of_not_lt h), coeff_eq_zero a (Nat.le_of_not_lt h),
      coeff_eq_zero b (Nat.le_of_not_lt h)]
    omega

theorem coeff_neg (a : Cyc d) (i : Nat) : (-a).coeff i = -a.coeff i := by
  by_cases h : i < d
  · exact coeff_ofFn h
  · rw [coeff_eq_zero _ (Nat.le_of_not_lt h), coeff_eq_zero a (Nat.le_of_not_lt h)]
    omega

theorem coeff_smul (c : Int) (a : Cyc d) (i : Nat) : (smul c a).coeff i = c * a.coeff i := by
  by_cases h : i < d
  · exact coeff_ofFn h
  · rw [coeff_eq_zero _ (Nat.le_of_not_lt h), coeff_eq_zero a (Nat.le_of_not_lt h),
      Int.mul_zero]

theorem coeff_sub (a b : Cyc d) (i : Nat) : (a - b).coeff i = a.coeff i - b.coeff i := by
  show (add a (neg b)).coeff i = _
  rw [show add a (neg b) = a + (-b) from rfl, coeff_add, coeff_neg]
  omega

theorem coeff_mul (a b : Cyc d) {k : Nat} (h : k < d) :
    (a * b).coeff k = sum d (fun i => wrapSign i k * a.coeff i * b.coeff (subMod d k i)) :=
  coeff_ofFn h

theorem coeff_conj (a : Cyc d) {j : Nat} (h : j < d) :
    (conj a).coeff j = if j = 0 then a.coeff 0 else -a.coeff (d - j) := coeff_ofFn h

theorem coeff_zeta {i : Nat} (h : i < d) :
    (zeta d).coeff i = if 1 < d then (if i = 1 then 1 else 0) else -1 := coeff_ofFn h

/-! ## Coefficients at every degree -/

/-- The sign that `x^d = -1` attaches to degree `n`: one minus sign for each
multiple of `d`. -/
def sgn (d n : Nat) : Int := if (n / d) % 2 = 0 then 1 else -1

/-- The coefficient of `x^n` in a polynomial representative, defined at every
degree.  Reducing `x^d` to `-1` gives `ecoeff a (n + d) = -ecoeff a n`, which is
the only property of it the convolution proofs use. -/
def ecoeff (a : Cyc d) (n : Nat) : Int := sgn d n * a.coeff (n % d)

theorem ecoeff_of_lt (a : Cyc d) {n : Nat} (h : n < d) : ecoeff a n = a.coeff n := by
  rw [ecoeff, sgn, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  simp

/--
The element a coefficient list denotes, read as a polynomial.

`ofList` truncates at degree `d`, which is right where the caller knows the list
is short and wrong for anything that reads a list as `Σ cⱼ xʲ`.  In this ring
`x^d = -1`, so a coefficient at degree `d` or above has a value: degree `j`
contributes `sgn d j` times `cⱼ` to degree `j % d`.

Truncation would admit inconsistent encodings.  At degree four,
`[-1, 0, 0, 0, -2]` denotes `-1 + (-2)(-1) = +1` after negacyclic folding but
denotes `-1` after truncation.  A submitted amplitude could then pass under a
different value, including a CCZ phase presented as the identity.
-/
def ofListWrapped (d : Nat) (l : List Int) : Cyc d :=
  ofFn d (fun i => sum l.length (fun j => if j % d = i then sgn d j * l.getD j 0 else 0))

theorem coeff_ofListWrapped {d i : Nat} {l : List Int} (h : i < d) :
    (ofListWrapped d l).coeff i
      = sum l.length (fun j => if j % d = i then sgn d j * l.getD j 0 else 0) :=
  coeff_ofFn h

/-- On a list no longer than the degree, folding and truncating agree: every
index is below `d`, so `j % d = j` and `sgn d j = 1`. -/
theorem ofListWrapped_eq_ofList {d : Nat} {l : List Int} (h : l.length ≤ d) :
    ofListWrapped d l = ofList d l := by
  refine eq_of_coeff (fun i hi => ?_)
  rw [coeff_ofListWrapped hi, coeff_ofList hi]
  by_cases hl : i < l.length
  · refine (sum_eq_single hl ?_).trans ?_
    · intro j hj hne
      have : j % d = j := Nat.mod_eq_of_lt (by omega)
      rw [this, if_neg hne]
    · have hid : i % d = i := Nat.mod_eq_of_lt hi
      rw [hid, if_pos rfl, sgn, Nat.div_eq_of_lt hi]
      simp
  · refine (sum_eq_zero (fun j hj => ?_)).trans ?_
    · have : j % d = j := Nat.mod_eq_of_lt (by omega)
      rw [this, if_neg (by omega)]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

theorem sgn_add_d (hd : 0 < d) (n : Nat) : sgn d (n + d) = -sgn d n := by
  rw [sgn, sgn, Nat.add_div_right n hd]
  by_cases h : (n / d) % 2 = 0
  · rw [if_pos h, if_neg (show ¬((n / d + 1) % 2 = 0) from by omega)]
  · rw [if_neg h, if_pos (show (n / d + 1) % 2 = 0 from by omega)]
    decide

theorem ecoeff_add_d (a : Cyc d) (n : Nat) : ecoeff a (n + d) = -ecoeff a n := by
  cases d with
  | zero =>
    have hz : ∀ i, a.coeff i = 0 := fun i => coeff_eq_zero a (Nat.zero_le i)
    simp [ecoeff, hz]
  | succ e =>
    rw [ecoeff, ecoeff, Nat.add_mod_right, sgn_add_d (Nat.succ_pos e), Int.neg_mul]

theorem ecoeff_add_two_d (a : Cyc d) (n : Nat) : ecoeff a (n + 2 * d) = ecoeff a n := by
  rw [show n + 2 * d = n + d + d from by omega, ecoeff_add_d, ecoeff_add_d, Int.neg_neg]

/-! ## The convolution window -/

/-- `window d A B p q = ∑_{m<d} A (p + m) * B (q + d - m)`.  Every term is a
product `A i * B j` with `i + j = p + q + d`, and `i` runs over the `d`
consecutive values starting at `p`.  When `A` and `B` both satisfy
`F (n + d) = -F n`, moving the range of `i` by one leaves the value unchanged,
so the window depends only on `p + q`. -/
def window (d : Nat) (A B : Nat → Int) (p q : Nat) : Int :=
  sum d (fun m => A (p + m) * B (q + d - m))

theorem window_zero (d : Nat) (A B : Nat → Int) (q : Nat) :
    window d A B 0 q = sum d (fun m => A m * B (q + d - m)) :=
  sum_congr (fun m _ => by rw [Nat.zero_add])

theorem window_shift {d : Nat} {A B : Nat → Int}
    (hA : ∀ n, A (n + d) = -A n) (hB : ∀ n, B (n + d) = -B n) (p q : Nat) :
    window d A B p (q + 1) = window d A B (p + 1) q := by
  cases d with
  | zero => rfl
  | succ e =>
    have hfun : (fun m => A (p + (m + 1)) * B (q + 1 + (e + 1) - (m + 1)))
        = (fun m => A (p + 1 + m) * B (q + (e + 1) - m)) := by
      funext m
      rw [show p + (m + 1) = p + 1 + m from by omega,
        show q + 1 + (e + 1) - (m + 1) = q + (e + 1) - m from by omega]
    have hhead : A (p + 0) * B (q + 1 + (e + 1) - 0) = -(A p * B (q + 1)) := by
      rw [Nat.add_zero, Nat.sub_zero, show q + 1 + (e + 1) = (q + 1) + (e + 1) from rfl, hB,
        Int.mul_neg]
    have hlast : A (p + 1 + e) * B (q + (e + 1) - e) = -(A p * B (q + 1)) := by
      rw [show p + 1 + e = p + (e + 1) from by omega,
        show q + (e + 1) - e = q + 1 from by omega, hA, Int.neg_mul]
    show sum (e + 1) _ = sum (e + 1) _
    rw [sum_succ' e, sum_succ e]
    show A (p + 0) * B (q + 1 + (e + 1) - 0)
        + sum e (fun m => A (p + (m + 1)) * B (q + 1 + (e + 1) - (m + 1)))
        = sum e (fun m => A (p + 1 + m) * B (q + (e + 1) - m))
        + A (p + 1 + e) * B (q + (e + 1) - e)
    rw [hfun, hhead, hlast, Int.add_comm]

theorem window_shift_add {d : Nat} {A B : Nat → Int}
    (hA : ∀ n, A (n + d) = -A n) (hB : ∀ n, B (n + d) = -B n) (p q k : Nat) :
    window d A B p (q + k) = window d A B (p + k) q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
    rw [show q + (k + 1) = (q + k) + 1 from by omega, window_shift hA hB, ih,
      show p + 1 + k = p + (k + 1) from by omega]

theorem window_swap_ends {d : Nat} {A B : Nat → Int}
    (hA : ∀ n, A (n + d) = -A n) (hB : ∀ n, B (n + d) = -B n) (q : Nat) :
    window d A B 0 q = window d A B q 0 := by
  have h := window_shift_add hA hB 0 0 q
  rwa [Nat.zero_add] at h

/-- Reversing the order of summation exchanges the two sequences. -/
theorem window_reflect (d : Nat) (A B : Nat → Int) (p q : Nat) :
    window d A B (p + 1) q = window d B A (q + 1) p := by
  rw [window, ← sum_rev d (fun m => A (p + 1 + m) * B (q + d - m))]
  refine sum_congr (fun m hm => ?_)
  show A (p + 1 + (d - 1 - m)) * B (q + d - (d - 1 - m)) = B (q + 1 + m) * A (p + d - m)
  rw [show p + 1 + (d - 1 - m) = p + d - m from by omega,
    show q + d - (d - 1 - m) = q + 1 + m from by omega, Int.mul_comm]

theorem window_comm {d : Nat} {A B : Nat → Int}
    (hA : ∀ n, A (n + d) = -A n) (hB : ∀ n, B (n + d) = -B n) {q : Nat} (hq : 0 < q) :
    window d A B 0 q = window d B A 0 q :=
  calc window d A B 0 q
      = window d A B q 0 := window_swap_ends hA hB q
    _ = window d A B (q - 1 + 1) 0 := by rw [show q - 1 + 1 = q from by omega]
    _ = window d B A (0 + 1) (q - 1) := window_reflect d A B (q - 1) 0
    _ = window d B A 1 (0 + (q - 1)) := by simp only [Nat.zero_add]
    _ = window d B A (1 + (q - 1)) 0 := window_shift_add hB hA 1 0 (q - 1)
    _ = window d B A q 0 := by rw [show 1 + (q - 1) = q from by omega]
    _ = window d B A 0 q := (window_swap_ends hB hA q).symm

/-! ## Multiplication through the window -/

theorem coeff_mul_window (a b : Cyc d) {k : Nat} (hk : k < d) :
    (a * b).coeff k = window d (ecoeff a) (ecoeff b) 0 (k + d) := by
  rw [coeff_mul a b hk, window_zero]
  refine sum_congr (fun i hi => ?_)
  rw [ecoeff_of_lt a hi]
  by_cases h : i ≤ k
  · rw [wrapSign, if_pos h, Int.one_mul, subMod,
      show d + k - i = (k - i) + d from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show k - i < d from by omega),
      show k + d + d - i = (k - i) + 2 * d from by omega, ecoeff_add_two_d,
      ecoeff_of_lt b (show k - i < d from by omega)]
  · rw [wrapSign, if_neg h, subMod, Nat.mod_eq_of_lt (show d + k - i < d from by omega),
      show k + d + d - i = (d + k - i) + d from by omega, ecoeff_add_d,
      ecoeff_of_lt b (show d + k - i < d from by omega)]
    grind

theorem ecoeff_mul (hd : 0 < d) (a b : Cyc d) (n : Nat) :
    ecoeff (a * b) n = window d (ecoeff a) (ecoeff b) 0 (n + d) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < d
    · rw [ecoeff_of_lt _ h, coeff_mul_window a b h]
    · have hrec : n - d + d = n := by omega
      rw [← hrec, ecoeff_add_d, ih (n - d) (by omega), window_zero, window_zero, ← sum_neg]
      refine sum_congr (fun m hm => ?_)
      rw [show n - d + d + d + d - m = (n - d + d + d - m) + d from by omega, ecoeff_add_d,
        Int.mul_neg]

/-! ## Ring laws -/

theorem add_comm (a b : Cyc d) : a + b = b + a :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_add]; omega)

theorem add_assoc (a b c : Cyc d) : a + b + c = a + (b + c) :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_add, coeff_add, coeff_add]; omega)

theorem add_zero (a : Cyc d) : a + zero d = a :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_zero]; omega)

theorem zero_add (a : Cyc d) : zero d + a = a :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_zero]; omega)

theorem neg_add_cancel (a : Cyc d) : -a + a = zero d :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_neg, coeff_zero]; omega)

theorem add_neg_cancel (a : Cyc d) : a + -a = zero d :=
  eq_of_coeff (fun i _ => by rw [coeff_add, coeff_neg, coeff_zero]; omega)

theorem sub_eq_add_neg (a b : Cyc d) : a - b = a + -b := rfl

theorem neg_neg (a : Cyc d) : -(-a) = a :=
  eq_of_coeff (fun i _ => by rw [coeff_neg, coeff_neg]; omega)

theorem mul_comm (a b : Cyc d) : a * b = b * a := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_mul_window a b hk, coeff_mul_window b a hk]
  exact window_comm (ecoeff_add_d a) (ecoeff_add_d b) (by omega)

theorem one_mul (a : Cyc d) : one d * a = a := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_mul _ a hk,
    sum_eq_single (j := 0) (by omega) (fun i hi hi0 => by
      rw [coeff_one hi, if_neg hi0, Int.mul_zero, Int.zero_mul]),
    coeff_one (show 0 < d from by omega), if_pos rfl, wrapSign, if_pos (Nat.zero_le k),
    subMod, Nat.sub_zero, Nat.add_mod_left, Nat.mod_eq_of_lt hk, Int.one_mul, Int.one_mul]

theorem mul_one (a : Cyc d) : a * one d = a := by rw [mul_comm, one_mul]

theorem zero_mul (a : Cyc d) : zero d * a = zero d := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_mul _ a hk, coeff_zero,
    sum_eq_zero (fun i hi => by rw [coeff_zero, Int.mul_zero, Int.zero_mul])]

theorem mul_zero (a : Cyc d) : a * zero d = zero d := by rw [mul_comm, zero_mul]

theorem left_distrib (a b c : Cyc d) : a * (b + c) = a * b + a * c := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_add, coeff_mul a _ hk, coeff_mul a b hk, coeff_mul a c hk, ← sum_add]
  refine sum_congr (fun i hi => ?_)
  rw [coeff_add]
  grind

theorem right_distrib (a b c : Cyc d) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_neg (a b : Cyc d) : a * -b = -(a * b) := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_neg, coeff_mul a _ hk, coeff_mul a b hk, ← sum_neg]
  refine sum_congr (fun i hi => ?_)
  rw [coeff_neg]
  grind

theorem neg_mul (a b : Cyc d) : -a * b = -(a * b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : Cyc d) : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem mul_assoc (a b c : Cyc d) : a * b * c = a * (b * c) := by
  refine eq_of_coeff (fun k hk => ?_)
  have hd : 0 < d := by omega
  have hB := ecoeff_add_d b
  have hC := ecoeff_add_d c
  have hlhs : (a * b * c).coeff k
      = sum d (fun m => sum d (fun i =>
          ecoeff a i * ecoeff b (m + 2 * d - i) * ecoeff c (k + 2 * d - m))) := by
    rw [coeff_mul_window (a * b) c hk, window_zero]
    refine sum_congr (fun m hm => ?_)
    rw [ecoeff_mul hd a b m, window_zero, ← sum_mul_right]
    refine sum_congr (fun i hi => ?_)
    rw [show m + d + d - i = m + 2 * d - i from by omega,
      show k + d + d - m = k + 2 * d - m from by omega]
  have hrhs : (a * (b * c)).coeff k
      = sum d (fun i => sum d (fun m =>
          ecoeff a i * ecoeff b (m + 2 * d - i) * ecoeff c (k + 2 * d - m))) := by
    rw [coeff_mul_window a (b * c) hk, window_zero]
    refine sum_congr (fun i hi => ?_)
    have hw : window d (ecoeff b) (ecoeff c) 0 (k + d + (2 * d - i))
        = window d (ecoeff b) (ecoeff c) (2 * d - i) (k + d) := by
      have h := window_shift_add hB hC 0 (k + d) (2 * d - i)
      rwa [Nat.zero_add] at h
    rw [ecoeff_mul hd b c (k + d + d - i),
      show k + d + d - i + d = k + d + (2 * d - i) from by omega, hw, window, ← sum_mul_left]
    refine sum_congr (fun m hm => ?_)
    rw [show 2 * d - i + m = m + 2 * d - i from by omega,
      show k + d + d - m = k + 2 * d - m from by omega, Int.mul_assoc]
  rw [hlhs, hrhs]
  exact sum_swap d d (fun m i =>
    ecoeff a i * ecoeff b (m + 2 * d - i) * ecoeff c (k + 2 * d - m))

/-- Registering associativity and commutativity lets `ac_rfl` close a goal that
differs only in bracketing or order. -/
instance : Std.Associative (α := Cyc d) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := Cyc d) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := Cyc d) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := Cyc d) (· * ·) := ⟨mul_comm⟩

/-! ## Scalar multiplication -/

theorem smul_eq_ofInt_mul (c : Int) (a : Cyc d) : smul c a = ofInt d c * a := by
  refine eq_of_coeff (fun k hk => ?_)
  rw [coeff_smul, coeff_mul _ a hk,
    sum_eq_single (j := 0) (by omega) (fun i hi hi0 => by
      rw [coeff_ofInt c hi, if_neg hi0, Int.mul_zero, Int.zero_mul]),
    coeff_ofInt c (show 0 < d from by omega), if_pos rfl, wrapSign, if_pos (Nat.zero_le k),
    subMod, Nat.sub_zero, Nat.add_mod_left, Nat.mod_eq_of_lt hk, Int.one_mul]

theorem smul_smul (c e : Int) (a : Cyc d) : smul c (smul e a) = smul (c * e) a :=
  eq_of_coeff (fun i _ => by rw [coeff_smul, coeff_smul, coeff_smul, Int.mul_assoc])

theorem smul_add (c : Int) (a b : Cyc d) : smul c (a + b) = smul c a + smul c b :=
  eq_of_coeff (fun i _ => by
    rw [coeff_smul, coeff_add, coeff_add, coeff_smul, coeff_smul, Int.mul_add])

theorem smul_neg (c : Int) (a : Cyc d) : smul c (-a) = -smul c a :=
  eq_of_coeff (fun i _ => by rw [coeff_smul, coeff_neg, coeff_neg, coeff_smul, Int.mul_neg])

theorem smul_mul (c : Int) (a b : Cyc d) : smul c (a * b) = smul c a * b := by
  rw [smul_eq_ofInt_mul, smul_eq_ofInt_mul, mul_assoc]

theorem smul_mul_right (c : Int) (a b : Cyc d) : smul c (a * b) = a * smul c b := by
  rw [mul_comm a b, smul_mul, mul_comm]

theorem smul_zero (c : Int) : smul c (zero d) = zero d :=
  eq_of_coeff (fun i _ => by rw [coeff_smul, coeff_zero, Int.mul_zero])

theorem one_smul (a : Cyc d) : smul 1 a = a :=
  eq_of_coeff (fun i _ => by rw [coeff_smul, Int.one_mul])

theorem two_smul (a : Cyc d) : smul 2 a = a + a :=
  eq_of_coeff (fun i _ => by rw [coeff_smul, coeff_add]; omega)

theorem smul_one (c : Int) : smul c (one d) = ofInt d c := by
  rw [smul_eq_ofInt_mul, mul_one]

theorem smul_left_cancel {c : Int} (hc : c ≠ 0) {a b : Cyc d} (h : smul c a = smul c b) :
    a = b := by
  refine eq_of_coeff (fun i _ => ?_)
  have := congrArg (fun x => coeff x i) h
  rw [coeff_smul, coeff_smul] at this
  exact Int.eq_of_mul_eq_mul_left hc this

/-! ## Halving

`Dy` is the localisation at two, so a representative `(a, n)` denoting `a / 2 ^ n`
can be brought to lowest terms by halving the numerator while it stays integral.
`allEven` recognizes an integral half, `halve` computes it, and
`smul_two_halve` proves that halving preserves the represented value. -/

/-- Every coefficient is even, so the element is twice another. -/
def allEven (a : Cyc d) : Bool := a.coeffs.all (fun c => c % 2 == 0)

/-- Halve every coefficient.  Under `allEven`, `smul_two_halve` proves that
doubling restores the input.  On an odd coefficient, `Int.ediv` rounds toward
negative infinity. -/
def halve (a : Cyc d) : Cyc d :=
  ⟨a.coeffs.map (fun c => c / 2), by rw [List.length_map, a.length_eq]⟩

theorem coeff_halve (a : Cyc d) {i : Nat} (h : i < d) : (halve a).coeff i = a.coeff i / 2 := by
  have hl : i < a.coeffs.length := by rw [a.length_eq]; exact h
  have hm : i < (a.coeffs.map (fun c => c / 2)).length := by rw [List.length_map]; exact hl
  rw [coeff_eq_getElem _ hm, coeff_eq_getElem _ hl]
  simp [halve]

theorem coeff_even_of_allEven {a : Cyc d} (h : allEven a = true) {i : Nat} (hi : i < d) :
    a.coeff i % 2 = 0 := by
  have hl : i < a.coeffs.length := by rw [a.length_eq]; exact hi
  rw [coeff_eq_getElem _ hl]
  have := List.all_eq_true.mp h a.coeffs[i] (List.getElem_mem hl)
  exact of_decide_eq_true this

/-- Halving and doubling recover the element, proving that reduction to lowest
terms preserves its value. -/
theorem smul_two_halve {a : Cyc d} (h : allEven a = true) : smul 2 (halve a) = a :=
  eq_of_coeff fun i hi => by
    rw [coeff_smul, coeff_halve a hi]
    have := coeff_even_of_allEven h hi
    omega

/-! ## Powers -/

theorem pow_zero (a : Cyc d) : a ^ 0 = one d := rfl

theorem pow_succ (a : Cyc d) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem pow_succ' (a : Cyc d) (n : Nat) : a ^ (n + 1) = a * a ^ n := by
  rw [pow_succ, mul_comm]

theorem pow_eq_mul_pred (a : Cyc d) {n : Nat} (hn : 0 < n) : a ^ n = a * a ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ', Nat.add_sub_cancel]

theorem pow_add (a : Cyc d) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [show m + (n + 1) = (m + n) + 1 from rfl, pow_succ, ih, pow_succ, mul_assoc]

theorem pow_mul (a : Cyc d) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, pow_succ]

/-! ## The root of unity -/

theorem zeta_mul_coeff (a : Cyc d) {k : Nat} (hk : k < d) :
    (zeta d * a).coeff k = if k = 0 then -a.coeff (d - 1) else a.coeff (k - 1) := by
  have hd : 0 < d := by omega
  rw [coeff_mul _ a hk]
  by_cases h1 : 1 < d
  · rw [sum_eq_single (j := 1) h1 (fun i hi hi1 => by
      rw [coeff_zeta hi, if_pos h1, if_neg hi1, Int.mul_zero, Int.zero_mul]),
      coeff_zeta h1, if_pos h1, if_pos rfl, Int.mul_one]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, wrapSign, if_neg (by omega), subMod,
        Nat.mod_eq_of_lt (show d + 0 - 1 < d from by omega),
        show d + 0 - 1 = d - 1 from by omega]
      grind
    · rw [if_neg hk0, wrapSign, if_pos (by omega), subMod,
        show d + k - 1 = (k - 1) + d from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show k - 1 < d from by omega), Int.one_mul]
  · have hd1 : d = 1 := by omega
    subst hd1
    have hk0 : k = 0 := by omega
    subst hk0
    rw [sum_eq_single (j := 0) (by omega) (fun i hi hi0 => absurd (show i = 0 from by omega) hi0),
      coeff_zeta (by omega), if_neg h1, wrapSign, if_pos (Nat.le_refl 0), subMod]
    grind

/-- Powers of `x` below the degree are the basis elements. -/
theorem coeff_zeta_pow {n : Nat} (hn : n < d) {i : Nat} (hi : i < d) :
    ((zeta d) ^ n).coeff i = if i = n then 1 else 0 := by
  induction n generalizing i with
  | zero => exact coeff_one hi
  | succ n ih =>
    have hn' : n < d := by omega
    rw [pow_succ' (zeta d) n, zeta_mul_coeff _ hi]
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl, ih hn' (show d - 1 < d from by omega), if_neg (show d - 1 ≠ n from by omega),
        if_neg (show (0 : Nat) ≠ n + 1 from by omega)]
      rfl
    · rw [if_neg hi0, ih hn' (show i - 1 < d from by omega)]
      by_cases he : i = n + 1
      · rw [if_pos he, if_pos (show i - 1 = n from by omega)]
      · rw [if_neg he, if_neg (show i - 1 ≠ n from by omega)]

theorem zeta_pow_d : (zeta d) ^ d = -one d := by
  refine eq_of_coeff (fun k hk => ?_)
  have hd : 0 < d := by omega
  rw [pow_eq_mul_pred (zeta d) hd, zeta_mul_coeff _ hk, coeff_neg, coeff_one hk]
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl, if_pos rfl,
      coeff_zeta_pow (show d - 1 < d from by omega) (show d - 1 < d from by omega), if_pos rfl]
  · rw [if_neg hk0, if_neg hk0,
      coeff_zeta_pow (show d - 1 < d from by omega) (show k - 1 < d from by omega),
      if_neg (show k - 1 ≠ d - 1 from by omega)]
    rfl

/-! ## Conjugation -/

theorem conj_conj (a : Cyc d) : conj (conj a) = a := by
  refine eq_of_coeff (fun j hj => ?_)
  rw [coeff_conj _ hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl, coeff_conj a hj, if_pos rfl]
  · rw [if_neg hj0, coeff_conj a (show d - j < d from by omega),
      if_neg (show d - j ≠ 0 from by omega), show d - (d - j) = j from by omega, Int.neg_neg]

theorem ecoeff_conj (hd : 0 < d) (a : Cyc d) :
    ∀ n m : Nat, n + m = 2 * d → ecoeff (conj a) n = ecoeff a m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hm
    by_cases hn : n < d
    · rw [ecoeff_of_lt _ hn, coeff_conj a hn]
      by_cases hn0 : n = 0
      · subst hn0
        rw [if_pos rfl, show m = 0 + 2 * d from by omega, ecoeff_add_two_d, ecoeff_of_lt a hd]
      · rw [if_neg hn0, show m = (d - n) + d from by omega, ecoeff_add_d,
          ecoeff_of_lt a (show d - n < d from by omega)]
    · rw [show n = (n - d) + d from by omega, ecoeff_add_d,
        ih (n - d) (by omega) (m + d) (by omega), ecoeff_add_d, Int.neg_neg]

theorem ecoeff_conj' (hd : 0 < d) (a : Cyc d) {n m : Nat} (h : n + m = 4 * d) :
    ecoeff (conj a) n = ecoeff a m := by
  by_cases hn : n < 2 * d
  · rw [show m = (m - 2 * d) + 2 * d from by omega, ecoeff_add_two_d]
    exact ecoeff_conj hd a n (m - 2 * d) (by omega)
  · rw [show n = (n - 2 * d) + 2 * d from by omega, ecoeff_add_two_d]
    exact ecoeff_conj hd a (n - 2 * d) m (by omega)

theorem conj_add (a b : Cyc d) : conj (a + b) = conj a + conj b := by
  refine eq_of_coeff (fun j hj => ?_)
  rw [coeff_add, coeff_conj _ hj, coeff_conj a hj, coeff_conj b hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl, if_pos rfl, if_pos rfl, coeff_add]
  · rw [if_neg hj0, if_neg hj0, if_neg hj0, coeff_add]
    omega

theorem conj_neg (a : Cyc d) : conj (-a) = -conj a := by
  refine eq_of_coeff (fun j hj => ?_)
  rw [coeff_neg, coeff_conj _ hj, coeff_conj a hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl, if_pos rfl, coeff_neg]
  · rw [if_neg hj0, if_neg hj0, coeff_neg, Int.neg_neg]

theorem conj_ofInt (c : Int) : conj (ofInt d c) = ofInt d c := by
  refine eq_of_coeff (fun j hj => ?_)
  rw [coeff_conj _ hj, coeff_ofInt c hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [if_pos rfl, if_pos rfl, coeff_ofInt c hj, if_pos rfl]
  · rw [if_neg hj0, if_neg hj0, coeff_ofInt c (show d - j < d from by omega),
      if_neg (show d - j ≠ 0 from by omega), Int.neg_zero]

theorem conj_one : conj (one d) = one d := conj_ofInt 1

theorem conj_zero : conj (zero d) = zero d := by
  have : zero d = ofInt d 0 := eq_of_coeff (fun i hi => by rw [coeff_zero, coeff_ofInt 0 hi]; grind)
  rw [this]; exact conj_ofInt 0

theorem conj_mul (a b : Cyc d) : conj (a * b) = conj a * conj b := by
  refine eq_of_coeff (fun k hk => ?_)
  have hd : 0 < d := by omega
  have hA := ecoeff_add_d a
  have hB := ecoeff_add_d b
  have hl : (conj (a * b)).coeff k = window d (ecoeff a) (ecoeff b) 0 (5 * d - k) := by
    rw [← ecoeff_of_lt _ hk, ecoeff_conj' hd (a * b) (show k + (4 * d - k) = 4 * d from by omega),
      ecoeff_mul hd a b (4 * d - k), show 4 * d - k + d = 5 * d - k from by omega]
  have hr : (conj a * conj b).coeff k = window d (ecoeff b) (ecoeff a) 0 (5 * d - k) := by
    rw [coeff_mul_window (conj a) (conj b) hk, window_zero]
    have hstep : sum d (fun i => ecoeff (conj a) i * ecoeff (conj b) (k + d + d - i))
        = window d (ecoeff b) (ecoeff a) (2 * d - k) (3 * d) := by
      refine sum_congr (fun i hi => ?_)
      rw [ecoeff_conj' hd a (show i + (4 * d - i) = 4 * d from by omega),
        ecoeff_conj' hd b (show (k + d + d - i) + (2 * d - k + i) = 4 * d from by omega),
        show 4 * d - i = 3 * d + d - i from by omega,
        show 2 * d - k + i = 2 * d - k + i from rfl, Int.mul_comm]
    rw [hstep]
    have h := window_shift_add hB hA (2 * d - k) 0 (3 * d)
    rw [Nat.zero_add, show 2 * d - k + 3 * d = 5 * d - k from by omega] at h
    rw [h]
    exact (window_swap_ends hB hA (5 * d - k)).symm
  rw [hl, hr]
  exact window_comm hA hB (show 0 < 5 * d - k from by omega)

/-! ## The length invariant -/

/-- Every operation returns a `Cyc d`, so the coefficient list has length `d` by
construction.  These restate that for each one. -/
theorem length_add (a b : Cyc d) : (a + b).coeffs.length = d := (a + b).length_eq
theorem length_neg (a : Cyc d) : (-a).coeffs.length = d := (-a).length_eq
theorem length_sub (a b : Cyc d) : (a - b).coeffs.length = d := (a - b).length_eq
theorem length_mul (a b : Cyc d) : (a * b).coeffs.length = d := (a * b).length_eq
theorem length_smul (c : Int) (a : Cyc d) : (smul c a).coeffs.length = d := (smul c a).length_eq
theorem length_pow (a : Cyc d) (n : Nat) : (a ^ n).coeffs.length = d := (a ^ n).length_eq
theorem length_conj (a : Cyc d) : (conj a).coeffs.length = d := (conj a).length_eq
theorem length_zero : (zero d).coeffs.length = d := (zero d).length_eq
theorem length_one : (one d).coeffs.length = d := (one d).length_eq
theorem length_zeta : (zeta d).coeffs.length = d := (zeta d).length_eq

end Cyc
end Algebra
end VQ
