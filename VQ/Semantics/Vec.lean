/-
States and matrices over the amplitude ring.

A state is a function from a computational basis index to an amplitude, and a
matrix is its two-index form.  Dimensions are values in the propositions rather
than indices in the types, so no definition carries a cast.

Core has no `DecidableEq` on function types.  Equality below a finite bound is
decidable, and well-formedness on both sides extends it to function equality.
SQIR calls the second step `mat_equiv_eq`, and every obligation stated here uses
it.

The amplitude type has no `OfNat` instance, so zero and one are written
`Dy.zero d` and `Dy.one d` throughout.
-/
import VQ.Algebra.Dyadic

namespace VQ
namespace Semantics

open Algebra

/-- A state: the amplitude at each computational basis index.  Wire `q` is bit
`q` of the index, counting from the least significant bit. -/
abbrev Vec (d : Nat) : Type := Nat → Dy d

/-- A matrix: the entry at each row and column. -/
abbrev Mat (d : Nat) : Type := Nat → Nat → Dy d

variable {d : Nat}

/-- The computational basis state `|j⟩`. -/
def basis (j : Nat) : Vec d := fun i => if i = j then Dy.one d else Dy.zero d

theorem basis_self (j : Nat) : (basis j : Vec d) j = Dy.one d := if_pos rfl

theorem basis_of_ne {i j : Nat} (h : i ≠ j) : (basis j : Vec d) i = Dy.zero d := if_neg h

/-! ## Amplitude lemmas

`VQ.Algebra.Dyadic` proves the ring laws.  These are the consequences of them
that the vector proofs use, stated here to keep that file untouched. -/

theorem neg_zero : -(Dy.zero d) = Dy.zero d := by
  have h := Dy.add_zero (-(Dy.zero d))
  rw [Dy.neg_add_cancel] at h
  exact h.symm

theorem sub_zero (x : Dy d) : x - Dy.zero d = x := by
  rw [Dy.sub_eq_add_neg, neg_zero, Dy.add_zero]

theorem neg_eq_neg_one_mul (x : Dy d) : -x = (-Dy.one d) * x := by
  rw [Dy.neg_mul, Dy.one_mul]

theorem neg_add (x y : Dy d) : -(x + y) = -x + -y := by
  rw [neg_eq_neg_one_mul (x + y), neg_eq_neg_one_mul x, neg_eq_neg_one_mul y, Dy.left_distrib]

theorem mul_sub (c x y : Dy d) : c * (x - y) = c * x - c * y := by
  rw [Dy.sub_eq_add_neg, Dy.left_distrib, Dy.mul_neg, Dy.sub_eq_add_neg]

/-- Two sums, regrouped by position.  Additivity of the Hadamard action is this
identity under a scalar. -/
theorem add_add_add (a b c e : Dy d) : (a + b) + (c + e) = (a + c) + (b + e) := by
  rw [Dy.add_assoc, ← Dy.add_assoc b, Dy.add_comm b c, Dy.add_assoc, ← Dy.add_assoc]

theorem add_sub_add (a b c e : Dy d) : (a + b) - (c + e) = (a - c) + (b - e) := by
  rw [Dy.sub_eq_add_neg, Dy.sub_eq_add_neg, Dy.sub_eq_add_neg, neg_add, add_add_add]

/-- Scaling commutes past a fixed factor. -/
theorem mul_left_comm (a c x : Dy d) : a * (c * x) = c * (a * x) := by
  rw [← Dy.mul_assoc, Dy.mul_comm a c, Dy.mul_assoc]

/-! ## Vector operations -/

namespace Vec

/-- The zero state. -/
protected def zero (d : Nat) : Vec d := fun _ => Dy.zero d

protected def add (u v : Vec d) : Vec d := fun i => u i + v i

protected def neg (u : Vec d) : Vec d := fun i => -u i

protected def sub (u v : Vec d) : Vec d := fun i => u i - v i

/-- Scaling by an amplitude. -/
protected def smul (a : Dy d) (u : Vec d) : Vec d := fun i => a * u i

instance : Add (Vec d) := ⟨Vec.add⟩
instance : Neg (Vec d) := ⟨Vec.neg⟩
instance : Sub (Vec d) := ⟨Vec.sub⟩
instance : SMul (Dy d) (Vec d) := ⟨Vec.smul⟩

@[simp] theorem zero_apply (i : Nat) : (Vec.zero d) i = Dy.zero d := rfl
@[simp] theorem add_apply (u v : Vec d) (i : Nat) : (u + v) i = u i + v i := rfl
@[simp] theorem neg_apply (u : Vec d) (i : Nat) : (-u) i = -u i := rfl
@[simp] theorem sub_apply (u v : Vec d) (i : Nat) : (u - v) i = u i - v i := rfl
@[simp] theorem smul_apply (a : Dy d) (u : Vec d) (i : Nat) : (a • u) i = a * u i := rfl

theorem ext {u v : Vec d} (h : ∀ i, u i = v i) : u = v := funext h

theorem zero_add_zero : (Vec.zero d) + Vec.zero d = Vec.zero d :=
  ext (fun _ => Dy.add_zero (Dy.zero d))

theorem smul_zero (a : Dy d) : a • (Vec.zero d) = Vec.zero d := ext (fun _ => Dy.mul_zero a)

theorem one_smul (u : Vec d) : Dy.one d • u = u := ext (fun _ => Dy.one_mul _)

/-- Two scalings collapse into one.  A chain of diagonal gates accumulates a
product of phases through this. -/
theorem smul_smul (a b : Dy d) (u : Vec d) : a • (b • u) = (a * b) • u :=
  ext (fun i => (Dy.mul_assoc a b (u i)).symm)

end Vec

/-! ## Matrix operations -/

namespace Mat

protected def zero (d : Nat) : Mat d := fun _ _ => Dy.zero d

/-- The identity matrix.  Its diagonal runs over every index, not over a block,
so it is not `WFMat n n` for any `n`. -/
protected def id (d : Nat) : Mat d := fun i j => if i = j then Dy.one d else Dy.zero d

protected def add (A B : Mat d) : Mat d := fun i j => A i j + B i j

protected def neg (A : Mat d) : Mat d := fun i j => -A i j

protected def sub (A B : Mat d) : Mat d := fun i j => A i j - B i j

protected def smul (a : Dy d) (A : Mat d) : Mat d := fun i j => a * A i j

instance : Add (Mat d) := ⟨Mat.add⟩
instance : Neg (Mat d) := ⟨Mat.neg⟩
instance : Sub (Mat d) := ⟨Mat.sub⟩
instance : SMul (Dy d) (Mat d) := ⟨Mat.smul⟩

@[simp] theorem zero_apply (i j : Nat) : (Mat.zero d) i j = Dy.zero d := rfl
@[simp] theorem add_apply (A B : Mat d) (i j : Nat) : (A + B) i j = A i j + B i j := rfl
@[simp] theorem neg_apply (A : Mat d) (i j : Nat) : (-A) i j = -A i j := rfl
@[simp] theorem sub_apply (A B : Mat d) (i j : Nat) : (A - B) i j = A i j - B i j := rfl
@[simp] theorem smul_apply (a : Dy d) (A : Mat d) (i j : Nat) : (a • A) i j = a * A i j := rfl

theorem ext {A B : Mat d} (h : ∀ i j, A i j = B i j) : A = B := funext fun i => funext (h i)

theorem id_self (i : Nat) : (Mat.id d) i i = Dy.one d := if_pos rfl

theorem id_of_ne {i j : Nat} (h : i ≠ j) : (Mat.id d) i j = Dy.zero d := if_neg h

end Mat

/-! ## Support -/

/-- A state carrying zero at every index from `n` upwards. -/
def WFVec (n : Nat) (u : Vec d) : Prop := ∀ i, n ≤ i → u i = Dy.zero d

/-- A matrix carrying zero outside its first `n` rows and `m` columns. -/
def WFMat (n m : Nat) (A : Mat d) : Prop := ∀ i j, n ≤ i ∨ m ≤ j → A i j = Dy.zero d

theorem wfVec_zero (n : Nat) : WFVec n (Vec.zero d) := fun _ _ => rfl

theorem wfVec_basis {n j : Nat} (h : j < n) : WFVec n (basis j : Vec d) :=
  fun i hi => basis_of_ne (by omega)

theorem wfVec_add {n : Nat} {u v : Vec d} (hu : WFVec n u) (hv : WFVec n v) :
    WFVec n (u + v) := fun i hi => by
  rw [Vec.add_apply, hu i hi, hv i hi, Dy.add_zero]

theorem wfVec_smul {n : Nat} {u : Vec d} (a : Dy d) (hu : WFVec n u) :
    WFVec n (a • u) := fun i hi => by
  rw [Vec.smul_apply, hu i hi, Dy.mul_zero]

theorem wfMat_zero (n m : Nat) : WFMat n m (Mat.zero d) := fun _ _ _ => rfl

/-! ## Bounded sums

Structural recursion on `Nat`, not `Fin.foldl`, which does not reduce in the
kernel and so would put every concrete obligation out of `decide`'s reach. -/

/-- The sum of `f` over the indices below `n`. -/
def dsum (n : Nat) (f : Nat → Dy d) : Dy d :=
  match n with
  | 0 => Dy.zero d
  | n + 1 => dsum n f + f n

theorem dsum_zero (f : Nat → Dy d) : dsum 0 f = Dy.zero d := rfl

theorem dsum_succ (n : Nat) (f : Nat → Dy d) : dsum (n + 1) f = dsum n f + f n := rfl

theorem dsum_congr {n : Nat} {f g : Nat → Dy d} (h : ∀ i, i < n → f i = g i) :
    dsum n f = dsum n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dsum_succ, dsum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem dsum_eq_zero {n : Nat} {f : Nat → Dy d} (h : ∀ i, i < n → f i = Dy.zero d) :
    dsum n f = Dy.zero d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsum_succ, ih (fun i hi => h i (by omega)), h n (by omega), Dy.add_zero]

/-- A sum with a single term outside the zeros. -/
theorem dsum_eq_single {n j : Nat} {f : Nat → Dy d} (hj : j < n)
    (h : ∀ i, i < n → i ≠ j → f i = Dy.zero d) : dsum n f = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [dsum_succ]
    by_cases hjn : j = n
    · subst hjn
      rw [dsum_eq_zero (fun i hi => h i (by omega) (by omega)), Dy.zero_add]
    · rw [ih (by omega) (fun i hi hij => h i (by omega) hij),
        h n (by omega) (fun he => hjn he.symm), Dy.add_zero]

theorem dsum_add (n : Nat) (f g : Nat → Dy d) :
    dsum n (fun i => f i + g i) = dsum n f + dsum n g := by
  induction n with
  | zero => exact (Dy.add_zero (Dy.zero d)).symm
  | succ n ih => rw [dsum_succ, dsum_succ, dsum_succ, ih, add_add_add]

theorem dsum_mul_right (n : Nat) (f : Nat → Dy d) (x : Dy d) :
    dsum n f * x = dsum n (fun i => f i * x) := by
  induction n with
  | zero => exact Dy.zero_mul x
  | succ n ih => rw [dsum_succ, dsum_succ, Dy.right_distrib, ih]

theorem dsum_mul_left (n : Nat) (x : Dy d) (f : Nat → Dy d) :
    x * dsum n f = dsum n (fun i => x * f i) := by
  induction n with
  | zero => exact Dy.mul_zero x
  | succ n ih => rw [dsum_succ, dsum_succ, Dy.left_distrib, ih]

/-- Two finite nested sums commute, yielding associativity of matrix
multiplication. -/
theorem dsum_comm (n m : Nat) (f : Nat → Nat → Dy d) :
    dsum n (fun i => dsum m (fun j => f i j)) = dsum m (fun j => dsum n (fun i => f i j)) := by
  induction n with
  | zero => exact (dsum_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    calc dsum (n + 1) (fun i => dsum m (fun j => f i j))
        = dsum n (fun i => dsum m (fun j => f i j)) + dsum m (fun j => f n j) :=
          dsum_succ n _
      _ = dsum m (fun j => dsum n (fun i => f i j)) + dsum m (fun j => f n j) := by rw [ih]
      _ = dsum m (fun j => dsum n (fun i => f i j) + f n j) := (dsum_add m _ _).symm
      _ = dsum m (fun j => dsum (n + 1) (fun i => f i j)) := dsum_congr (fun _ _ => rfl)

/-- The sum of the first `n` states. -/
def vsum (n : Nat) (f : Nat → Vec d) : Vec d := fun i => dsum n (fun k => f k i)

theorem vsum_zero (f : Nat → Vec d) : vsum 0 f = Vec.zero d := rfl

theorem vsum_succ (n : Nat) (f : Nat → Vec d) : vsum (n + 1) f = vsum n f + f n := rfl

theorem vsum_apply (n : Nat) (f : Nat → Vec d) (i : Nat) :
    vsum n f i = dsum n (fun k => f k i) := rfl

theorem vsum_congr {n : Nat} {f g : Nat → Vec d} (h : ∀ k, k < n → f k = g k) :
    vsum n f = vsum n g :=
  Vec.ext (fun i => dsum_congr (fun k hk => by rw [h k hk]))

/-- A state supported below `n` is the linear combination of the first `n`
basis states with its entries as coefficients.  This identity converts column
semantics into matrix multiplication. -/
theorem eq_vsum_basis {n : Nat} {u : Vec d} (hu : WFVec n u) :
    u = vsum n (fun k => u k • (basis k : Vec d)) := by
  refine Vec.ext (fun i => ?_)
  show u i = dsum n (fun k => u k * (basis k : Vec d) i)
  by_cases hi : i < n
  · rw [dsum_eq_single hi (fun k _ hki => by rw [basis_of_ne (Ne.symm hki), Dy.mul_zero]),
      basis_self, Dy.mul_one]
  · rw [hu i (Nat.le_of_not_lt hi),
      dsum_eq_zero (fun k hk => by
        rw [basis_of_ne (show i ≠ k from by omega), Dy.mul_zero])]

/-- The matrix product with inner dimension `n`. -/
def Mat.mul (n : Nat) (A B : Mat d) : Mat d := fun i j => dsum n (fun k => A i k * B k j)

theorem Mat.mul_apply (n : Nat) (A B : Mat d) (i j : Nat) :
    Mat.mul n A B i j = dsum n (fun k => A i k * B k j) := rfl

/-- Associativity holds at every index by rearranging the two finite sums,
independently of matrix support. -/
theorem Mat.mul_assoc (k m : Nat) (A B C : Mat d) :
    Mat.mul m (Mat.mul k A B) C = Mat.mul k A (Mat.mul m B C) := by
  refine Mat.ext (fun i j => ?_)
  calc dsum m (fun l => dsum k (fun r => A i r * B r l) * C l j)
      = dsum m (fun l => dsum k (fun r => A i r * B r l * C l j)) :=
        dsum_congr (fun l _ => dsum_mul_right k (fun r => A i r * B r l) (C l j))
    _ = dsum k (fun r => dsum m (fun l => A i r * B r l * C l j)) :=
        dsum_comm m k (fun l r => A i r * B r l * C l j)
    _ = dsum k (fun r => dsum m (fun l => A i r * (B r l * C l j))) :=
        dsum_congr (fun _ _ => dsum_congr (fun _ _ => Dy.mul_assoc _ _ _))
    _ = dsum k (fun r => A i r * dsum m (fun l => B r l * C l j)) :=
        dsum_congr (fun r _ => (dsum_mul_left m (A i r) (fun l => B r l * C l j)).symm)

/-! ## Bounded equality

`Nat.decidableBallLT` supplies the decision procedure, so a concrete obligation
closes by `decide`. -/

/-- Two states agree below `n`. -/
def VecEq (n : Nat) (u v : Vec d) : Prop := ∀ i, i < n → u i = v i

/-- Two matrices agree below `n` rows and `m` columns. -/
def MatEq (n m : Nat) (A B : Mat d) : Prop := ∀ i, i < n → ∀ j, j < m → A i j = B i j

instance (n : Nat) (u v : Vec d) : Decidable (VecEq n u v) :=
  inferInstanceAs (Decidable (∀ i, i < n → u i = v i))

instance (n m : Nat) (A B : Mat d) : Decidable (MatEq n m A B) :=
  inferInstanceAs (Decidable (∀ i, i < n → ∀ j, j < m → A i j = B i j))

theorem vecEq_of_eq {n : Nat} {u v : Vec d} (h : u = v) : VecEq n u v := fun _ _ => by rw [h]

theorem matEq_of_eq {n m : Nat} {A B : Mat d} (h : A = B) : MatEq n m A B :=
  fun _ _ _ _ => by rw [h]

/-- Agreement below `n` is equality when both states vanish from `n` upwards. -/
theorem eq_of_vecEq {n : Nat} {u v : Vec d} (hu : WFVec n u) (hv : WFVec n v)
    (h : VecEq n u v) : u = v := by
  refine Vec.ext (fun i => ?_)
  by_cases hi : i < n
  · exact h i hi
  · rw [hu i (Nat.le_of_not_lt hi), hv i (Nat.le_of_not_lt hi)]

/-- The matrix form of `eq_of_vecEq`, which is SQIR's `mat_equiv_eq`. -/
theorem eq_of_matEq {n m : Nat} {A B : Mat d} (hA : WFMat n m A) (hB : WFMat n m B)
    (h : MatEq n m A B) : A = B := by
  refine Mat.ext (fun i j => ?_)
  by_cases hi : i < n
  · by_cases hj : j < m
    · exact h i hi j hj
    · rw [hA i j (Or.inr (Nat.le_of_not_lt hj)), hB i j (Or.inr (Nat.le_of_not_lt hj))]
  · rw [hA i j (Or.inl (Nat.le_of_not_lt hi)), hB i j (Or.inl (Nat.le_of_not_lt hi))]

/-! ## Matrix algebra on a block

A circuit's matrix is not supported on any block, so `eq_of_matEq` does not
apply to it and every statement about a product of circuit matrices has to stay
a `MatEq`.  These are the lemmas that let such statements be chained: `MatEq` is
an equivalence, the product respects it, and the identity is a unit for it. -/

theorem MatEq.refl (n m : Nat) (A : Mat d) : MatEq n m A A := fun _ _ _ _ => rfl

theorem MatEq.symm {n m : Nat} {A B : Mat d} (h : MatEq n m A B) : MatEq n m B A :=
  fun i hi j hj => (h i hi j hj).symm

theorem MatEq.trans {n m : Nat} {A B C : Mat d} (h₁ : MatEq n m A B) (h₂ : MatEq n m B C) :
    MatEq n m A C := fun i hi j hj => (h₁ i hi j hj).trans (h₂ i hi j hj)

/-- The product respects agreement on a block.  The inner dimension is the
column bound on the left factor and the row bound on the right one, so the two
hypotheses are exactly the entries the sum reads. -/
theorem Mat.mul_congr {n k m : Nat} {A A' B B' : Mat d} (hA : MatEq n k A A')
    (hB : MatEq k m B B') : MatEq n m (Mat.mul k A B) (Mat.mul k A' B') :=
  fun i hi j hj => dsum_congr (fun l hl => by rw [hA i hi l hl, hB l hl j hj])

theorem Mat.mul_id_left (n m : Nat) (A : Mat d) : MatEq n m (Mat.mul n (Mat.id d) A) A := by
  intro i hi j _
  show dsum n (fun k => (Mat.id d) i k * A k j) = A i j
  rw [dsum_eq_single hi (fun k _ hk => by
      rw [Mat.id_of_ne (fun he => hk he.symm), Dy.zero_mul]),
    Mat.id_self, Dy.one_mul]

theorem Mat.mul_id_right (n m : Nat) (A : Mat d) : MatEq n m (Mat.mul m A (Mat.id d)) A := by
  intro i _ j hj
  show dsum m (fun k => A i k * (Mat.id d) k j) = A i j
  rw [dsum_eq_single hj (fun k _ hk => by rw [Mat.id_of_ne hk, Dy.mul_zero]),
    Mat.id_self, Dy.mul_one]

end Semantics
end VQ
