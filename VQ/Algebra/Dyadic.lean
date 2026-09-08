/-
The dyadic cyclotomic integers ℤ[x]/(x^d + 1)[1/2].

An element is a pair `(a, n)` standing for `a / 2 ^ n`, taken up to the relation
`(a, m) ~ (b, n)` when `a * 2 ^ n = b * 2 ^ m`.  The carrier is a quotient rather
than a structure holding a normalisation invariant, so `=` means ring equality
and no definition has to maintain an invariant.  The kernel reduces
`Quot.lift f h (Quot.mk r a)` to `f a`, so a concrete goal still closes by
`decide`.  `normalize` cancels common factors of two and is proven to return an
equal element.  The quotient relation defines equality, while normalization
selects a smaller representative.

At `d` a multiple of four the ring contains `√2 = ζ^(d/4) - ζ^(3d/4)` and hence
`1/√2`, permitting an exact Hadamard gate.
-/
import VQ.Algebra.Cyc

namespace VQ
namespace Algebra

/-! ## Powers of two -/

theorem two_pow_pos (n : Nat) : 0 < (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by decide)

theorem two_pow_ne_zero (n : Nat) : (2 : Int) ^ n ≠ 0 :=
  fun h => absurd (h ▸ two_pow_pos n) (by decide)

theorem two_pow_add (m n : Nat) : (2 : Int) ^ (m + n) = 2 ^ m * 2 ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from rfl, Int.pow_succ, ih, Int.pow_succ, Int.mul_assoc]

namespace Cyc

variable {d : Nat}

/-- Multiplication by `2 ^ n`. -/
def scale (n : Nat) (a : Cyc d) : Cyc d := smul (2 ^ n) a

theorem scale_def (n : Nat) (a : Cyc d) : scale n a = smul (2 ^ n) a := rfl

theorem scale_zero_exp (a : Cyc d) : scale 0 a = a := by
  rw [scale_def, Int.pow_zero, one_smul]

theorem scale_one_exp (a : Cyc d) : scale 1 a = a + a := by
  rw [scale_def, Int.pow_one, two_smul]

theorem scale_scale (m n : Nat) (a : Cyc d) : scale m (scale n a) = scale (m + n) a := by
  rw [scale_def, scale_def, scale_def, smul_smul, two_pow_add]

theorem scale_add (n : Nat) (a b : Cyc d) : scale n (a + b) = scale n a + scale n b :=
  smul_add _ a b

theorem scale_neg (n : Nat) (a : Cyc d) : scale n (-a) = -scale n a := smul_neg _ a

theorem scale_mul (n : Nat) (a b : Cyc d) : scale n (a * b) = scale n a * b := smul_mul _ a b

theorem scale_mul_right (n : Nat) (a b : Cyc d) : scale n (a * b) = a * scale n b :=
  smul_mul_right _ a b

/-- A scaled product splits its exponent between the two factors. -/
theorem scale_add_mul (m n : Nat) (a b : Cyc d) :
    scale (m + n) (a * b) = scale m a * scale n b := by
  rw [← scale_scale, scale_mul_right, scale_mul]

theorem scale_zero (n : Nat) : scale n (zero d) = zero d := smul_zero _

theorem scale_cancel {n : Nat} {a b : Cyc d} (h : scale n a = scale n b) : a = b :=
  smul_left_cancel (two_pow_ne_zero n) h

theorem conj_scale (n : Nat) (a : Cyc d) : conj (scale n a) = scale n (conj a) := by
  rw [scale_def, scale_def, smul_eq_ofInt_mul, smul_eq_ofInt_mul, conj_mul, conj_ofInt]

end Cyc

/-! ## Dyadic quotient -/

open Cyc

/-- `(a, m)` and `(b, n)` denote the same element when `a * 2 ^ n = b * 2 ^ m`. -/
def DyRel (d : Nat) (p q : Cyc d × Nat) : Prop := scale q.2 p.1 = scale p.2 q.1

theorem DyRel.refl {d : Nat} (p : Cyc d × Nat) : DyRel d p p := rfl

theorem DyRel.symm {d : Nat} {p q : Cyc d × Nat} (h : DyRel d p q) : DyRel d q p := Eq.symm h

theorem DyRel.trans {d : Nat} {p q r : Cyc d × Nat}
    (h₁ : DyRel d p q) (h₂ : DyRel d q r) : DyRel d p r := by
  refine scale_cancel (n := q.2) ?_
  calc scale q.2 (scale r.2 p.1)
      = scale r.2 (scale q.2 p.1) := by rw [scale_scale, scale_scale, Nat.add_comm]
    _ = scale r.2 (scale p.2 q.1) := by rw [h₁]
    _ = scale p.2 (scale r.2 q.1) := by rw [scale_scale, scale_scale, Nat.add_comm]
    _ = scale p.2 (scale q.2 r.1) := by rw [h₂]
    _ = scale q.2 (scale p.2 r.1) := by rw [scale_scale, scale_scale, Nat.add_comm]

/-- The localisation of `Cyc d` at two. -/
def Dy (d : Nat) := Quot (DyRel d)

namespace Dy

variable {d : Nat}

/-- The class of `a / 2 ^ n`. -/
def mk (a : Cyc d) (n : Nat) : Dy d := Quot.mk (DyRel d) (a, n)

theorem sound {a b : Cyc d} {m n : Nat} (h : scale n a = scale m b) : mk a m = mk b n :=
  Quot.sound h

@[elab_as_elim]
theorem ind {motive : Dy d → Prop} (h : ∀ (a : Cyc d) (n : Nat), motive (mk a n)) (x : Dy d) :
    motive x :=
  Quot.inductionOn x (fun p => h p.1 p.2)

/-- Lift a binary operation that respects the relation in each argument. -/
def lift₂ {γ : Sort u} (f : Cyc d × Nat → Cyc d × Nat → γ)
    (h : ∀ p q p' q', DyRel d p p' → DyRel d q q' → f p q = f p' q') :
    Dy d → Dy d → γ := by
  show Quot (DyRel d) → Quot (DyRel d) → γ
  refine Quot.lift (fun p => Quot.lift (f p) (fun q q' hq => h p q p q' (DyRel.refl p) hq)) ?_
  intro p p' hp
  funext x
  refine Quot.inductionOn x (fun q => ?_)
  exact h p q p' q hp (DyRel.refl q)

/-! ## Dyadic operations -/

def ofCyc (a : Cyc d) : Dy d := mk a 0

def ofInt (d : Nat) (c : Int) : Dy d := ofCyc (Cyc.ofInt d c)

def zero (d : Nat) : Dy d := ofCyc (Cyc.zero d)

def one (d : Nat) : Dy d := ofCyc (Cyc.one d)

/-!
## Reduction to lowest terms

A representative `(a, n)` denotes `a / 2 ^ n`, and a quotient class may contain
representatives with nonminimal exponents.  The naive rules
`(a, m) + (b, n) = (a·2ⁿ + b·2ᵐ, m + n)` and `(a, m) · (b, n) = (a·b, m + n)`
double the exponent at every addition.  Repeated Hadamards would therefore
produce exponentially large representatives for small ring values.

Reduction happens on representatives and the quotient never sees it.
`mk_reduceRep` proves that reduction preserves the quotient value.  The
well-definedness proofs use that equality to eliminate the reduction step.
-/

/--
Halve the numerator while it stays integral, lowering the exponent each time.

Recursion is on the exponent, structurally and with the exponent as the first
argument.  Neither is presentation.  A `Nat`-bounded loop over the pair would be
compiled by well-founded recursion, which does not reduce in the kernel, and
every obligation about a concrete circuit is closed by kernel evaluation of
exactly these operations.
-/
def reduceAux : Nat → Cyc d → Cyc d × Nat
  | 0, a => (a, 0)
  | n + 1, a =>
    match Cyc.allEven a with
    | true => reduceAux n (Cyc.halve a)
    | false => (a, n + 1)

/-- Divide out common powers of two from a representative. -/
def reduceRep (p : Cyc d × Nat) : Cyc d × Nat := reduceAux p.2 p.1

theorem mk_reduceAux (n : Nat) (a : Cyc d) :
    mk (reduceAux n a).1 (reduceAux n a).2 = mk a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [reduceAux]
    split
    · rename_i he
      refine (ih (Cyc.halve a)).trans (sound ?_)
      show scale (n + 1) (Cyc.halve a) = scale n a
      rw [← scale_scale, scale_one_exp, ← two_smul, Cyc.smul_two_halve he]
    · rfl

/-- Reduction does not move the element it names. -/
theorem mk_reduceRep (p : Cyc d × Nat) :
    mk (reduceRep p).1 (reduceRep p).2 = mk p.1 p.2 :=
  mk_reduceAux p.2 p.1

/-- The class of a reduced representative. -/
def mkR (p : Cyc d × Nat) : Dy d := mk (reduceRep p).1 (reduceRep p).2

theorem mkR_eq (p : Cyc d × Nat) : mkR p = mk p.1 p.2 := mk_reduceRep p

def add : Dy d → Dy d → Dy d :=
  lift₂ (fun p q => mkR (scale q.2 p.1 + scale p.2 q.1, p.2 + q.2)) (by
    intro p q p' q' hp hq
    rw [mkR_eq, mkR_eq]
    refine sound ?_
    have e1 : scale (p'.2 + q'.2 + q.2) p.1 = scale (p.2 + q.2 + q'.2) p'.1 := by
      rw [show p'.2 + q'.2 + q.2 = (q'.2 + q.2) + p'.2 from by omega, ← scale_scale, hp,
        scale_scale, show q'.2 + q.2 + p.2 = p.2 + q.2 + q'.2 from by omega]
    have e2 : scale (p'.2 + q'.2 + p.2) q.1 = scale (p.2 + q.2 + p'.2) q'.1 := by
      rw [show p'.2 + q'.2 + p.2 = (p'.2 + p.2) + q'.2 from by omega, ← scale_scale, hq,
        scale_scale, show p'.2 + p.2 + q.2 = p.2 + q.2 + p'.2 from by omega]
    show scale (p'.2 + q'.2) (scale q.2 p.1 + scale p.2 q.1)
        = scale (p.2 + q.2) (scale q'.2 p'.1 + scale p'.2 q'.1)
    rw [scale_add, scale_add, scale_scale, scale_scale, scale_scale, scale_scale, e1, e2])

def mul : Dy d → Dy d → Dy d :=
  lift₂ (fun p q => mkR (p.1 * q.1, p.2 + q.2)) (by
    intro p q p' q' hp hq
    rw [mkR_eq, mkR_eq]
    refine sound ?_
    show scale (p'.2 + q'.2) (p.1 * q.1) = scale (p.2 + q.2) (p'.1 * q'.1)
    rw [scale_add_mul, scale_add_mul, hp, hq])

def neg : Dy d → Dy d :=
  Quot.lift (fun p => mk (-p.1) p.2) (by
    intro p q h
    refine sound ?_
    show scale q.2 (-p.1) = scale p.2 (-q.1)
    rw [scale_neg, scale_neg, h])

instance : Add (Dy d) := ⟨add⟩
instance : Mul (Dy d) := ⟨mul⟩
instance : Neg (Dy d) := ⟨neg⟩
instance : Sub (Dy d) := ⟨fun x y => add x (neg y)⟩

/-- Division by two. -/
def half : Dy d → Dy d :=
  Quot.lift (fun p => mkR (p.1, p.2 + 1)) (by
    intro p q h
    rw [mkR_eq, mkR_eq]
    refine sound ?_
    show scale (q.2 + 1) p.1 = scale (p.2 + 1) q.1
    rw [show q.2 + 1 = 1 + q.2 from by omega, show p.2 + 1 = 1 + p.2 from by omega,
      ← scale_scale, ← scale_scale, h])

def pow (x : Dy d) : Nat → Dy d
  | 0 => one d
  | n + 1 => pow x n * x

instance : Pow (Dy d) Nat := ⟨pow⟩

/-- Conjugation acts on the numerator and fixes the denominator. -/
def conj : Dy d → Dy d :=
  Quot.lift (fun p => mk (Cyc.conj p.1) p.2) (by
    intro p q h
    refine sound ?_
    show scale q.2 (Cyc.conj p.1) = scale p.2 (Cyc.conj q.1)
    rw [← conj_scale, ← conj_scale]
    exact congrArg Cyc.conj h)

/-! ## Reduction on representatives -/

theorem mk_add_mk (a b : Cyc d) (m n : Nat) :
    mk a m + mk b n = mk (scale n a + scale m b) (m + n) :=
  mkR_eq (scale n a + scale m b, m + n)

theorem mk_mul_mk (a b : Cyc d) (m n : Nat) : mk a m * mk b n = mk (a * b) (m + n) :=
  mkR_eq (a * b, m + n)

theorem neg_mk (a : Cyc d) (m : Nat) : -mk a m = mk (-a) m := rfl

theorem half_mk (a : Cyc d) (m : Nat) : half (mk a m) = mk a (m + 1) :=
  mkR_eq (a, m + 1)

theorem conj_mk (a : Cyc d) (m : Nat) : conj (mk a m) = mk (Cyc.conj a) m := rfl

theorem sub_eq_add_neg (x y : Dy d) : x - y = x + -y := rfl

theorem zero_eq : (zero d) = mk (Cyc.zero d) 0 := rfl

theorem one_eq : (one d) = mk (Cyc.one d) 0 := rfl

/-! ## The embedding of `Cyc d` -/

theorem ofCyc_add (a b : Cyc d) : ofCyc (a + b) = ofCyc a + ofCyc b := by
  show mk (a + b) 0 = mk (scale 0 a + scale 0 b) (0 + 0)
  rw [scale_zero_exp, scale_zero_exp]

theorem ofCyc_mul (a b : Cyc d) : ofCyc (a * b) = ofCyc a * ofCyc b := rfl

theorem ofCyc_neg (a : Cyc d) : ofCyc (-a) = -ofCyc a := rfl

theorem ofCyc_one : ofCyc (Cyc.one d) = one d := rfl

theorem ofCyc_pow (a : Cyc d) (n : Nat) : ofCyc (a ^ n) = ofCyc a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ofCyc (a ^ n * a) = ofCyc a ^ n * ofCyc a
    rw [ofCyc_mul, ih]

/--
The element `(Σ cᵢ ζⁱ) / 2ⁿ`, from its integer coefficients.

Missing coefficients read as zero, and a coefficient at degree `d` or above is
folded through `x^d = -1` rather than dropped: degree `j` contributes with sign
`(-1)^(j/d)` to degree `j % d`.  Dropping it would admit inconsistent encodings:
`[-1, 0, 0, 0, -2]` at degree four represents `+1`.  Truncation would give `-1`.
See `Cyc.ofListWrapped`.
At level 3 the degree is four, so `1/√2` is
`(ofCoeffs [0, 1, 0, -1] 1 : Dy 4)` and `-1` is `(ofCoeffs [-1] 0 : Dy 4)`.

The implicit degree comes from the expected type.
-/
def ofCoeffs {d : Nat} (cs : List Int) (n : Nat) : Dy d := mk (Cyc.ofListWrapped d cs) n

/-- The class of `x`, carried over from `Cyc d`. -/
def zeta (d : Nat) : Dy d := ofCyc (Cyc.zeta d)

theorem zeta_pow_d : zeta d ^ d = -one d := by
  rw [zeta, ← ofCyc_pow, Cyc.zeta_pow_d, ofCyc_neg, ofCyc_one]

/-! ## Decidable equality -/

/-- Equality of representatives, decided in `Cyc d`. -/
def beq : Dy d → Dy d → Bool :=
  lift₂ (fun p q => scale q.2 p.1 == scale p.2 q.1) (by
    intro p q p' q' hp hq
    have hiff : DyRel d p q ↔ DyRel d p' q' :=
      ⟨fun h => (hp.symm.trans h).trans hq, fun h => (hp.trans h).trans hq.symm⟩
    show decide (scale q.2 p.1 = scale p.2 q.1) = decide (scale q'.2 p'.1 = scale p'.2 q'.1)
    exact decide_eq_decide.mpr hiff)

theorem beq_iff (x y : Dy d) : beq x y = true ↔ x = y := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  constructor
  · intro h
    exact sound (of_decide_eq_true h)
  · intro h
    rw [← h]
    show decide (scale m a = scale m a) = true
    exact decide_eq_true rfl

instance : DecidableEq (Dy d) := fun x y =>
  if h : beq x y = true then isTrue ((beq_iff x y).mp h)
  else isFalse (fun he => h ((beq_iff x y).mpr he))

/-! ## Ring laws -/

theorem add_comm (x y : Dy d) : x + y = y + x := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [mk_add_mk, mk_add_mk, Cyc.add_comm, Nat.add_comm]

theorem add_assoc (x y z : Dy d) : x + y + z = x + (y + z) := by
  refine ind (fun a l => ?_) x
  refine ind (fun b m => ?_) y
  refine ind (fun c n => ?_) z
  rw [mk_add_mk, mk_add_mk, mk_add_mk, mk_add_mk, scale_add, scale_scale, scale_scale,
    scale_add, scale_scale, scale_scale,
    show n + m = m + n from by omega, show n + l = l + n from by omega,
    Cyc.add_assoc, show l + m + n = l + (m + n) from by omega]

theorem add_zero (x : Dy d) : x + zero d = x := by
  refine ind (fun a m => ?_) x
  rw [zero_eq, mk_add_mk, scale_zero_exp, scale_zero, Cyc.add_zero, Nat.add_zero]

theorem zero_add (x : Dy d) : zero d + x = x := by rw [add_comm, add_zero]

theorem neg_add_cancel (x : Dy d) : -x + x = zero d := by
  refine ind (fun a m => ?_) x
  rw [neg_mk, mk_add_mk, scale_neg, Cyc.neg_add_cancel, zero_eq]
  exact sound (by rw [scale_zero, scale_zero])

theorem add_neg_cancel (x : Dy d) : x + -x = zero d := by rw [add_comm, neg_add_cancel]

theorem mul_comm (x y : Dy d) : x * y = y * x := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [mk_mul_mk, mk_mul_mk, Cyc.mul_comm, Nat.add_comm]

theorem mul_assoc (x y z : Dy d) : x * y * z = x * (y * z) := by
  refine ind (fun a l => ?_) x
  refine ind (fun b m => ?_) y
  refine ind (fun c n => ?_) z
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, Cyc.mul_assoc,
    show l + m + n = l + (m + n) from by omega]

theorem one_mul (x : Dy d) : one d * x = x := by
  refine ind (fun a m => ?_) x
  rw [one_eq, mk_mul_mk, Cyc.one_mul, Nat.zero_add]

theorem mul_one (x : Dy d) : x * one d = x := by rw [mul_comm, one_mul]

theorem zero_mul (x : Dy d) : zero d * x = zero d := by
  refine ind (fun a m => ?_) x
  rw [zero_eq, mk_mul_mk, Cyc.zero_mul]
  exact sound (by rw [scale_zero, scale_zero])

theorem mul_zero (x : Dy d) : x * zero d = zero d := by rw [mul_comm, zero_mul]

theorem left_distrib (x y z : Dy d) : x * (y + z) = x * y + x * z := by
  refine ind (fun a l => ?_) x
  refine ind (fun b m => ?_) y
  refine ind (fun c n => ?_) z
  rw [mk_add_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_add_mk]
  refine sound ?_
  rw [Cyc.left_distrib, scale_add, scale_add, ← scale_mul_right, ← scale_mul_right,
    scale_scale, scale_scale, scale_scale, scale_scale,
    show l + m + (l + n) + n = l + (m + n) + (l + n) from by omega,
    show l + m + (l + n) + m = l + (m + n) + (l + m) from by omega]

theorem right_distrib (x y z : Dy d) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm z x, mul_comm z y]

theorem mul_neg (x y : Dy d) : x * -y = -(x * y) := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [neg_mk, mk_mul_mk, mk_mul_mk, neg_mk, Cyc.mul_neg]

theorem neg_mul (x y : Dy d) : -x * y = -(x * y) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_neg (x : Dy d) : -(-x) = x := by
  calc -(-x) = -(-x) + zero d := (add_zero _).symm
    _ = -(-x) + (-x + x) := by rw [neg_add_cancel]
    _ = (-(-x) + -x) + x := (add_assoc _ _ _).symm
    _ = zero d + x := by rw [neg_add_cancel]
    _ = x := zero_add x

/-- `neg_neg` has to come first: with `open Cyc` in scope, `neg_neg` inside this
namespace resolves to the `Cyc` lemma until the `Dy` one is declared. -/
theorem neg_add (x y : Dy d) : -(x + y) = -x + -y := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [mk_add_mk, neg_mk, neg_mk, neg_mk, mk_add_mk, Cyc.scale_neg, Cyc.scale_neg]
  congr 1
  refine Cyc.eq_of_coeff (fun i _ => ?_)
  rw [Cyc.coeff_neg, Cyc.coeff_add, Cyc.coeff_add, Cyc.coeff_neg, Cyc.coeff_neg]
  omega

theorem neg_sub (x y : Dy d) : -(y - x) = x - y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]

/-! ## Powers -/

theorem pow_zero_eq (x : Dy d) : x ^ 0 = one d := rfl

theorem pow_succ (x : Dy d) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

/-- Powers add.  Needed wherever a chain of phase gates is collected into a
single power of the root of unity. -/
theorem pow_add (x : Dy d) (m n : Nat) : x ^ (m + n) = x ^ m * x ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero_eq, mul_one]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from rfl, pow_succ, ih, pow_succ, mul_assoc]

/-! ## Conjugation -/

theorem conj_conj (x : Dy d) : conj (conj x) = x := by
  refine ind (fun a m => ?_) x
  rw [conj_mk, conj_mk, Cyc.conj_conj]

theorem conj_add (x y : Dy d) : conj (x + y) = conj x + conj y := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [mk_add_mk, conj_mk, conj_mk, conj_mk, mk_add_mk, Cyc.conj_add, conj_scale, conj_scale]

theorem conj_mul (x y : Dy d) : conj (x * y) = conj x * conj y := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [mk_mul_mk, conj_mk, conj_mk, conj_mk, mk_mul_mk, Cyc.conj_mul]

theorem conj_one : conj (one d) = one d := by
  rw [one_eq, conj_mk, Cyc.conj_one]

theorem conj_zero : conj (zero d) = zero d := by
  rw [zero_eq, conj_mk, Cyc.conj_zero]

/-! ## Halving -/

theorem half_add_half (x : Dy d) : half x + half x = x := by
  refine ind (fun a m => ?_) x
  rw [half_mk, mk_add_mk]
  refine sound ?_
  have hr : scale (m + 1 + (m + 1)) a = scale (m + (m + 1)) a + scale (m + (m + 1)) a := by
    rw [show m + 1 + (m + 1) = 1 + (m + (m + 1)) from by omega, ← scale_scale, scale_one_exp]
  rw [scale_add, scale_scale, hr]

theorem half_mul (x y : Dy d) : half x * y = half (x * y) := by
  refine ind (fun a m => ?_) x
  refine ind (fun b n => ?_) y
  rw [half_mk, mk_mul_mk, mk_mul_mk, half_mk, show m + 1 + n = m + n + 1 from by omega]

/-! ## The square root of two -/

/-- `√2 = ζ^(d/4) - ζ^(3d/4)`, an element of the ring when `4` divides `d`. -/
def sqrt2 (d : Nat) : Dy d := ofCyc (Cyc.zeta d ^ (d / 4) - Cyc.zeta d ^ (3 * (d / 4)))

/-- `1/√2 = √2 / 2`. -/
def invSqrt2 (d : Nat) : Dy d := half (sqrt2 d)

/-- An element whose fourth power is `-1` gives a square root of two: with
`v = u^3` the cross terms `u * v` and `v * u` are both `u^4 = -1`, and the two
squares `u^2` and `v^2 = -u^2` cancel. -/
theorem sq_of_fourth_neg_one {u : Cyc d} (h4 : u * u * (u * u) = -Cyc.one d) :
    (u - u * u * u) * (u - u * u * u) = Cyc.ofInt d 2 := by
  have e1 : u * (u * u * u) = u * u * (u * u) := by ac_rfl
  have e2 : u * u * u * u = u * u * (u * u) := by ac_rfl
  have e3 : u * u * u * (u * u * u) = u * u * (u * u * (u * u)) := by ac_rfl
  rw [Cyc.sub_eq_add_neg, Cyc.right_distrib, Cyc.left_distrib, Cyc.left_distrib,
    Cyc.mul_neg, Cyc.neg_mul, Cyc.neg_mul_neg, e1, e2, e3, h4, Cyc.mul_neg, Cyc.mul_one]
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  rw [Cyc.coeff_add, Cyc.coeff_add, Cyc.coeff_add, Cyc.coeff_neg, Cyc.coeff_neg, Cyc.coeff_neg,
    Cyc.coeff_one hi, Cyc.coeff_ofInt 2 hi]
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]; omega
  · rw [if_neg h0, if_neg h0]; omega

theorem sqrt2_sq_cyc {e : Nat} (he : 4 * e = d) :
    (Cyc.zeta d ^ e - Cyc.zeta d ^ (3 * e)) * (Cyc.zeta d ^ e - Cyc.zeta d ^ (3 * e))
      = Cyc.ofInt d 2 := by
  have h3 : Cyc.zeta d ^ (3 * e) = Cyc.zeta d ^ e * Cyc.zeta d ^ e * Cyc.zeta d ^ e := by
    rw [← Cyc.pow_add, ← Cyc.pow_add, show e + e + e = 3 * e from by omega]
  have h4 : Cyc.zeta d ^ e * Cyc.zeta d ^ e * (Cyc.zeta d ^ e * Cyc.zeta d ^ e)
      = -Cyc.one d := by
    rw [← Cyc.pow_add, ← Cyc.pow_add, show e + e + (e + e) = d from by omega, Cyc.zeta_pow_d]
  rw [h3]
  exact sq_of_fourth_neg_one h4

theorem sqrt2_mul_sqrt2 {e : Nat} (he : 4 * e = d) : sqrt2 d * sqrt2 d = ofInt d 2 := by
  have hq : d / 4 = e := by omega
  rw [sqrt2, ofCyc, mk_mul_mk, hq, sqrt2_sq_cyc he, ofInt, ofCyc, Nat.add_zero]

theorem invSqrt2_mul_sqrt2 {e : Nat} (he : 4 * e = d) : invSqrt2 d * sqrt2 d = one d := by
  rw [invSqrt2, half_mul, sqrt2_mul_sqrt2 he, ofInt, ofCyc, half_mk, one_eq]
  refine sound ?_
  rw [scale_zero_exp, Nat.zero_add, scale_one_exp]
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  rw [Cyc.coeff_add, Cyc.coeff_one hi, Cyc.coeff_ofInt 2 hi]
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]; omega
  · rw [if_neg h0, if_neg h0]; omega

/-! ## Normalisation -/

/-- Divide every coefficient by two. -/
def halveCyc (a : Cyc d) : Cyc d := Cyc.ofFn d (fun i => a.coeff i / 2)

/-- Every coefficient is even. -/
def allEven (a : Cyc d) : Bool := a.coeffs.all (fun c => c % 2 == 0)

theorem coeff_even (a : Cyc d) (h : allEven a = true) {i : Nat} (hi : i < d) :
    a.coeff i % 2 = 0 := by
  have hlen : i < a.coeffs.length := by rw [a.length_eq]; exact hi
  have hmem := (List.all_eq_true.mp h) _ (List.getElem_mem hlen)
  rw [Cyc.coeff_eq_getElem a hlen]
  exact of_decide_eq_true hmem

theorem smul_two_halveCyc (a : Cyc d) (h : allEven a = true) :
    Cyc.smul 2 (halveCyc a) = a := by
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  rw [Cyc.coeff_smul, halveCyc, Cyc.coeff_ofFn hi]
  have := coeff_even a h hi
  omega

/-- Cancel factors of two from the numerator while the denominator allows it. -/
def normAux : Nat → Cyc d → Cyc d × Nat
  | 0, a => (a, 0)
  | n + 1, a => if allEven a then normAux n (halveCyc a) else (a, n + 1)

theorem normAux_succ (n : Nat) (a : Cyc d) :
    normAux (n + 1) a = if allEven a then normAux n (halveCyc a) else (a, n + 1) := rfl

theorem normAux_rel (n : Nat) (a : Cyc d) : DyRel d (normAux n a) (a, n) := by
  induction n generalizing a with
  | zero => exact DyRel.refl (a, 0)
  | succ n ih =>
    rw [normAux_succ]
    by_cases h : allEven a = true
    · rw [if_pos h]
      have hrel : scale n (normAux n (halveCyc a)).1
          = scale (normAux n (halveCyc a)).2 (halveCyc a) := ih (halveCyc a)
      have hfin : halveCyc a + halveCyc a = a := by
        rw [← Cyc.two_smul]; exact smul_two_halveCyc a h
      show scale (n + 1) (normAux n (halveCyc a)).1 = scale (normAux n (halveCyc a)).2 a
      rw [show n + 1 = 1 + n from by omega, ← scale_scale, hrel, scale_scale,
        Nat.add_comm 1 (normAux n (halveCyc a)).2, ← scale_scale, scale_one_exp, hfin]
    · rw [if_neg h]
      exact DyRel.refl (a, n + 1)

def normPre (p : Cyc d × Nat) : Cyc d × Nat := normAux p.2 p.1

theorem normPre_rel (p : Cyc d × Nat) : DyRel d (normPre p) p := by
  obtain ⟨a, n⟩ := p
  exact normAux_rel n a

/-- Cancel common factors of two.  The result is the same element, so this is an
optimisation and no definition depends on it. -/
def normalize : Dy d → Dy d :=
  Quot.lift (fun p => Quot.mk (DyRel d) (normPre p)) (by
    intro p q h
    have hp : Quot.mk (DyRel d) (normPre p) = Quot.mk (DyRel d) p := Quot.sound (normPre_rel p)
    have hq : Quot.mk (DyRel d) (normPre q) = Quot.mk (DyRel d) q := Quot.sound (normPre_rel q)
    rw [hp, hq]
    exact Quot.sound h)

theorem normalize_eq (x : Dy d) : normalize x = x :=
  Quot.inductionOn x (fun p => Quot.sound (normPre_rel p))

end Dy
end Algebra
end VQ
