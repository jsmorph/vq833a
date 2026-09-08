/-
Bounded sums of integers over an initial segment of the natural numbers.

Core Lean has no `Finset`, so the convolution proofs in `VQ.Algebra.Cyc` use
this.  `sum n f` adds `f 0` through `f (n - 1)`.  The recursion appends the last
term, which makes `sum_succ` hold by `rfl` and leaves peeling from the front to
`sum_split`.

The lemma the convolution proofs turn on is `sum_swap`.  Associativity of the
negacyclic convolution is an exchange of a double sum over a square, and
`sum_swap` is the only step in it that is not pointwise.
-/

namespace VQ
namespace Algebra

/-- `sum n f = f 0 + f 1 + ⋯ + f (n - 1)`. -/
def sum (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | n + 1 => sum n f + f n

@[simp] theorem sum_zero (f : Nat → Int) : sum 0 f = 0 := rfl

@[simp] theorem sum_succ (n : Nat) (f : Nat → Int) : sum (n + 1) f = sum n f + f n := rfl

/-- Only the values on the range matter. -/
theorem sum_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, sum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h n (Nat.lt_succ_self n)]

theorem sum_eq_zero {n : Nat} {f : Nat → Int} (h : ∀ i, i < n → f i = 0) : sum n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]
    rfl

theorem sum_add (n : Nat) (f g : Nat → Int) :
    sum n (fun i => f i + g i) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ, sum_succ, sum_succ, ih]; omega

theorem sum_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sum n (fun i => c * f i) = c * sum n f := by
  induction n with
  | zero => rw [sum_zero, sum_zero, Int.mul_zero]
  | succ n ih => rw [sum_succ, sum_succ, ih, Int.mul_add]

theorem sum_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    sum n (fun i => f i * c) = sum n f * c := by
  induction n with
  | zero => rw [sum_zero, sum_zero, Int.zero_mul]
  | succ n ih => rw [sum_succ, sum_succ, ih, Int.add_mul]

theorem sum_neg (n : Nat) (f : Nat → Int) : sum n (fun i => -f i) = -sum n f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_succ, sum_succ, ih]; omega

/-- Split a sum at `m`.  The second block is reindexed to start at zero. -/
theorem sum_split (m n : Nat) (f : Nat → Int) :
    sum (m + n) f = sum m f + sum n (fun i => f (m + i)) := by
  induction n with
  | zero => rw [Nat.add_zero, sum_zero, Int.add_zero]
  | succ n ih => rw [Nat.add_succ, sum_succ, sum_succ, ih, Int.add_assoc]

/-- Peel the first term instead of the last. -/
theorem sum_succ' (n : Nat) (f : Nat → Int) :
    sum (n + 1) f = f 0 + sum n (fun i => f (i + 1)) := by
  induction n with
  | zero => rw [sum_succ, sum_zero, sum_zero, Int.zero_add, Int.add_zero]
  | succ n ih => rw [sum_succ, ih, sum_succ, Int.add_assoc]

/-- Reverse the order of summation. -/
theorem sum_rev (n : Nat) (f : Nat → Int) : sum n (fun i => f (n - 1 - i)) = sum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have step : sum n (fun i => f (n + 1 - 1 - i)) = sum n (fun i => f (i + 1)) :=
      (sum_congr (fun i _ => show f (n + 1 - 1 - i) = f (n - 1 - i + 1) by congr 1; omega)).trans
        (ih (fun j => f (j + 1)))
    have h0 : n + 1 - 1 - n = 0 := by omega
    calc sum (n + 1) (fun i => f (n + 1 - 1 - i))
        = sum n (fun i => f (n + 1 - 1 - i)) + f (n + 1 - 1 - n) := rfl
      _ = sum n (fun i => f (i + 1)) + f 0 := by rw [step, h0]
      _ = f 0 + sum n (fun i => f (i + 1)) := Int.add_comm _ _
      _ = sum (n + 1) f := (sum_succ' n f).symm

/-- A sum whose terms vanish off a single index. -/
theorem sum_eq_single {n j : Nat} {f : Nat → Int} (hj : j < n)
    (h : ∀ i, i < n → i ≠ j → f i = 0) : sum n f = f j := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    rw [sum_succ]
    by_cases hjn : j = n
    · subst hjn
      rw [sum_eq_zero (fun i hi => h i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi)), Int.zero_add]
    · have hj' : j < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjn
      rw [ih hj' (fun i hi hij => h i (Nat.lt_succ_of_lt hi) hij),
        h n (Nat.lt_succ_self n) (fun he => hjn he.symm), Int.add_zero]

/-- Exchange a double sum over a rectangle. -/
theorem sum_swap (m n : Nat) (f : Nat → Nat → Int) :
    sum m (fun i => sum n (fun j => f i j)) = sum n (fun j => sum m (fun i => f i j)) := by
  induction m with
  | zero => exact (sum_eq_zero (fun _ _ => rfl)).symm
  | succ m ih =>
    rw [sum_succ, ih, ← sum_add]
    rfl

end Algebra
end VQ
