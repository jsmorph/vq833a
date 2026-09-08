import VQBridge.Palomar833.Language
import VQMathlib.Curve.Secp256k1Order.Order

namespace Palomar833

noncomputable section

attribute [local instance] Classical.propDecidable

def N : Nat := 2 ^ 256
def p : Nat := 2 ^ 256 - 2 ^ 32 - 977
def q : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337
def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240
def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

theorem p_prime : Nat.Prime p := VQBridge.Prime.prime_p
theorem q_prime : Nat.Prime q := VQ.Tests.Secp256k1Order.q_prime

instance primeField : Fact (Nat.Prime p) := ⟨p_prime⟩
instance primeOrder : Fact (Nat.Prime q) := ⟨q_prime⟩
instance fieldNonzero : NeZero p := ⟨p_prime.ne_zero⟩
instance orderNonzero : NeZero q := ⟨q_prime.ne_zero⟩

def curve : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, 0, 7⟩

theorem discriminant_nonzero : curve.Δ ≠ 0 := by
  change VQBridge.Curve.W.Δ ≠ 0
  exact isUnit_iff_ne_zero.mp
    (inferInstance : VQBridge.Curve.W.IsElliptic).isUnit

instance elliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr discriminant_nonzero⟩

abbrev Point := curve.toAffine.Point

def decodeCoordinates (x y : Nat) : Point :=
  if h : curve.toAffine.Equation (x : ZMod p) (y : ZMod p) then
    WeierstrassCurve.Affine.Point.mk h
  else 0

def publicX (code : Nat) : Nat := code % N
def publicY (code : Nat) : Nat := (code / N) % N
def decodePoint (code : Nat) : Point :=
  decodeCoordinates (publicX code) (publicY code)
def generator : Point := decodeCoordinates generatorX generatorY

def validPoint (code : Nat) : Prop :=
  code < N ^ 2 ∧
    ((publicX code = 0 ∧ publicY code = 0) ∨
      (publicX code < p ∧ publicY code < p ∧
        curve.toAffine.Equation (publicX code : ZMod p) (publicY code : ZMod p)))

theorem generator_valid :
    generatorX < p ∧ generatorY < p ∧
      curve.toAffine.Equation (generatorX : ZMod p) (generatorY : ZMod p) := by
  exact ⟨VQ.Tests.Secp256k1Order.generatorX_lt_p,
    VQ.Tests.Secp256k1Order.generatorY_lt_p,
    (VQBridge.Curve.onCurve_iff _ _).mp
      VQ.Tests.Secp256k1Order.generator_onCurve⟩

theorem decodeCoordinates_eq (x y : Nat) :
    decodeCoordinates x y = VQBridge.Curve.groupPoint x y := by
  by_cases h : VQ.Curve.OnCurve x y = true
  · have he := (VQBridge.Curve.onCurve_iff x y).mp h
    change curve.toAffine.Equation (x : ZMod p) (y : ZMod p) at he
    simp only [decodeCoordinates, dite_eq_left he, VQBridge.Curve.groupPoint,
      dite_eq_left h, VQBridge.Curve.pointOf]
    rfl
  · have he : ¬ curve.toAffine.Equation (x : ZMod p) (y : ZMod p) :=
      fun he => h ((VQBridge.Curve.onCurve_iff x y).mpr he)
    simp only [decodeCoordinates, dite_eq_right he, VQBridge.Curve.groupPoint,
      dite_eq_right h]
    rfl

theorem generator_eq : generator = VQ.Tests.Secp256k1Order.decodedGenerator :=
  decodeCoordinates_eq generatorX generatorY

theorem generator_order : addOrderOf generator = q := by
  rw [generator_eq]
  exact VQ.Tests.Secp256k1Order.decodedGenerator_addOrderOf

/-- The zero point has code zero.  Affine coordinates occupy bits 0–255 and 259–514. -/
def encodePoint : Point → Nat
  | .zero => 0
  | .some x y _ => x.val + 2 ^ 259 * y.val

theorem publicX_eq (code : Nat) :
    publicX code = VQ.Curve.PointAddition.Runtime.pointX code := by
  simp [publicX, N, VQ.Curve.PointAddition.Runtime.pointX,
    VQ.Reversible.readField, VQ.Curve.PointAddition.Runtime.n]

theorem publicY_eq (code : Nat) :
    publicY code = VQ.Curve.PointAddition.Runtime.pointY code := by
  simp [publicY, N, VQ.Curve.PointAddition.Runtime.pointY,
    VQ.Reversible.readField, VQ.Curve.PointAddition.Runtime.n, Nat.shiftRight_eq_div_pow]

theorem validPoint_eq (code : Nat) :
    validPoint code ↔ VQ.Tests.FixedBaseScalarMultiplication.PointValid code := by
  have hwidth : N ^ 2 = 2 ^ VQ.Tests.GroupTotalPointAddition.pointWidth :=
    (pow_mul (2 : Nat) 256 2).symm
  simp only [validPoint, VQ.Tests.FixedBaseScalarMultiplication.PointValid,
    VQ.Curve.GroupRepresentable, VQ.Curve.IsInfinity, VQ.Curve.Representable,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    VQBridge.Curve.onCurve_iff, ← publicX_eq, ← publicY_eq, hwidth, and_assoc]
  rfl

theorem decodePoint_eq (code : Nat) :
    decodePoint code = VQBridge.Curve.groupPoint
      (VQ.Curve.PointAddition.Runtime.pointX code)
      (VQ.Curve.PointAddition.Runtime.pointY code) := by
  rw [decodePoint, decodeCoordinates_eq, publicX_eq, publicY_eq]

end

end Palomar833
