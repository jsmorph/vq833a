/-
`Lean.Grind.CommRing` instances for the amplitude rings.

`grind` normalises a ring expression by reading its operations off this class,
so registering it lets `grind` prove a symbolic identity over `Cyc d` or `Dy d`
rather than only a concrete one.  `hex-matrix` requires the same class of a
coefficient type.

The ring laws are the theorems already proven in `VQ.Algebra.Cyc` and
`VQ.Algebra.Dyadic`.  Beyond them the class asks for numerals, casts from `Nat`
and `Int`, and scalar multiplication by `Nat` and `Int`, which neither ring
carried.  All five go through `ofInt`: a numeral is the image of an integer, and
a scalar multiple is multiplication by that image.  With that choice
`OfNat.ofNat 1` is `one` and `x ^ n` is the existing `pow`, both definitionally,
so the laws transfer without a translation step.
-/
import VQ.Algebra.Dyadic

namespace VQ
namespace Algebra

namespace Cyc

variable {d : Nat}

/-! ## The image of the integers -/

theorem ofInt_zero : ofInt d 0 = zero d :=
  eq_of_coeff (fun i hi => by rw [coeff_ofInt 0 hi, coeff_zero]; split <;> rfl)

theorem ofInt_add (a b : Int) : ofInt d (a + b) = ofInt d a + ofInt d b :=
  eq_of_coeff (fun i hi => by
    rw [coeff_add, coeff_ofInt _ hi, coeff_ofInt a hi, coeff_ofInt b hi]
    split <;> rfl)

theorem ofInt_neg (a : Int) : ofInt d (-a) = -ofInt d a :=
  eq_of_coeff (fun i hi => by
    rw [coeff_neg, coeff_ofInt _ hi, coeff_ofInt a hi]
    split <;> rfl)

/-! ## Numerals, casts, and scalars -/

instance : NatCast (Cyc d) := ⟨fun n => ofInt d n⟩
instance : IntCast (Cyc d) := ⟨ofInt d⟩
instance (n : Nat) : OfNat (Cyc d) n := ⟨ofInt d n⟩
instance : SMul Nat (Cyc d) := ⟨fun n a => ofInt d n * a⟩
instance : SMul Int (Cyc d) := ⟨fun c a => ofInt d c * a⟩

theorem zero_def : (0 : Cyc d) = zero d := ofInt_zero

theorem one_def : (1 : Cyc d) = one d := rfl

instance : Lean.Grind.CommRing (Cyc d) where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero a := by rw [zero_def]; exact add_zero a
  neg_add_cancel a := by rw [zero_def]; exact neg_add_cancel a
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul a := by rw [zero_def]; exact zero_mul a
  mul_zero a := by rw [zero_def]; exact mul_zero a
  pow_zero := pow_zero
  pow_succ := pow_succ
  sub_eq_add_neg := sub_eq_add_neg
  ofNat_succ n := by
    show ofInt d (Int.ofNat (n + 1)) = ofInt d (Int.ofNat n) + ofInt d 1
    rw [show Int.ofNat (n + 1) = Int.ofNat n + 1 from rfl, ofInt_add]
  neg_zsmul c a := by
    show ofInt d (-c) * a = -(ofInt d c * a)
    rw [ofInt_neg, neg_mul]
  intCast_neg := ofInt_neg

end Cyc

namespace Dy

variable {d : Nat}

/-! ## The image of the integers -/

theorem ofInt_zero : ofInt d 0 = zero d := congrArg ofCyc Cyc.ofInt_zero

theorem ofInt_add (a b : Int) : ofInt d (a + b) = ofInt d a + ofInt d b := by
  show ofCyc (Cyc.ofInt d (a + b)) = ofCyc (Cyc.ofInt d a) + ofCyc (Cyc.ofInt d b)
  rw [Cyc.ofInt_add, ofCyc_add]

theorem ofInt_neg (a : Int) : ofInt d (-a) = -ofInt d a := by
  show ofCyc (Cyc.ofInt d (-a)) = -ofCyc (Cyc.ofInt d a)
  rw [Cyc.ofInt_neg, ofCyc_neg]

/-! ## Numerals, casts, and scalars -/

instance : NatCast (Dy d) := ⟨fun n => ofInt d n⟩
instance : IntCast (Dy d) := ⟨ofInt d⟩
instance (n : Nat) : OfNat (Dy d) n := ⟨ofInt d n⟩
instance : SMul Nat (Dy d) := ⟨fun n x => ofInt d n * x⟩
instance : SMul Int (Dy d) := ⟨fun c x => ofInt d c * x⟩

theorem zero_def : (0 : Dy d) = zero d := ofInt_zero

theorem one_def : (1 : Dy d) = one d := rfl

instance : Lean.Grind.CommRing (Dy d) where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero x := by rw [zero_def]; exact add_zero x
  neg_add_cancel x := by rw [zero_def]; exact neg_add_cancel x
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul x := by rw [zero_def]; exact zero_mul x
  mul_zero x := by rw [zero_def]; exact mul_zero x
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  sub_eq_add_neg := sub_eq_add_neg
  ofNat_succ n := by
    show ofInt d (Int.ofNat (n + 1)) = ofInt d (Int.ofNat n) + ofInt d 1
    rw [show Int.ofNat (n + 1) = Int.ofNat n + 1 from rfl, ofInt_add]
  neg_zsmul c x := by
    show ofInt d (-c) * x = -(ofInt d c * x)
    rw [ofInt_neg, neg_mul]
  intCast_neg := ofInt_neg

end Dy
end Algebra
end VQ
