import VQBridge.Palomar833.Algorithm
import VQ.Semantics.RegisterState

namespace Palomar833.Connection

open VQ.Reversible VQ.Semantics
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

theorem writeField_below {i offset width value : Nat}
    (hi : i < 2 ^ offset) (hv : value < 2 ^ width) :
    writeField i offset width value = i + 2 ^ offset * value := by
  have htail : i < 2 ^ (offset + width) :=
    hi.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [writeField, Nat.mod_eq_of_lt hi, Nat.shiftRight_eq_zero i _ htail,
    Nat.zero_shiftLeft, Nat.or_zero, Nat.mod_eq_of_lt hv, Nat.shiftLeft_eq,
    Nat.mul_comm value, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hi value,
    Nat.add_comm]

theorem pointState_coordinates (code : Nat) :
    pointState code false = publicX code + 2 ^ 259 * publicY code := by
  have hx : publicX code < 2 ^ 256 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hy : publicY code < 2 ^ 256 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hx259 : publicX code < 2 ^ 259 :=
    hx.trans_le (Nat.pow_le_pow_right (by decide) (by decide))
  have hpair : publicX code + 2 ^ 259 * publicY code < 2 ^ (259 + 256) :=
    VQ.Tests.RegisterState.joinIndex_lt hx259 hy
  have haux : publicX code + 2 ^ 259 * publicY code <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryOffset :=
    hpair.trans_le (Nat.pow_le_pow_right (by decide) (by decide))
  simp only [pointState, VQMathlib.Curve.PackedAffineTranslation.state,
    VQMathlib.Curve.PackedAffineRawTranslation.state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState,
    Bool.false_eq_true, ite_false, ← publicX_eq, ← publicY_eq,
    VQ.Euclid.PackedStepLayout.workTwoOffset]
  rw [writeField_below hx259 hy, writeField_below haux (Nat.two_pow_pos _)]
  simp

theorem encode_decodePoint {code : Nat} (h : validPoint code) :
    encodePoint (decodePoint code) = publicX code + 2 ^ 259 * publicY code := by
  rcases h.2 with ⟨hx, hy⟩ | ⟨hx, hy, he⟩
  · rw [decodePoint, hx, hy, decodeCoordinates_eq, VQBridge.Curve.groupPoint_infinity]
    simp only [encodePoint, mul_zero, zero_add]
  · rw [decodePoint, decodeCoordinates, dite_eq_left he]
    simp only [WeierstrassCurve.Affine.Point.mk, encodePoint,
      ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]

theorem pointState_encoding {code : Nat} (h : validPoint code) :
    pointState code false = encodePoint (decodePoint code) :=
  (pointState_coordinates code).trans (encode_decodePoint h).symm

end Palomar833.Connection
