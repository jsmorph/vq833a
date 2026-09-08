import VQMathlib.Curve.FixedBaseScalarMultiplication.Math

namespace VQ.Tests.Secp256k1Order

open VQ
open VQ.Curve.PointAddition.Runtime
open FixedBaseScalarMultiplication

def q : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240

def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

def generator : Nat := packPoint generatorX generatorY

noncomputable def decodedGenerator : VQBridge.Curve.W.toAffine.Point :=
  VQBridge.Curve.groupPoint generatorX generatorY

theorem q_lt_two_pow_256 : q < 2 ^ 256 := by
  decide

theorem generatorX_lt_p : generatorX < Curve.p := by
  decide

theorem generatorY_lt_p : generatorY < Curve.p := by
  decide

theorem p_lt_two_pow_256 : Curve.p < 2 ^ 256 := by
  decide

theorem generator_onCurve : Curve.OnCurve generatorX generatorY = true := by
  decide

theorem generator_groupRepresentable :
    Curve.GroupRepresentable generatorX generatorY = true := by
  simp [Curve.GroupRepresentable, Curve.IsInfinity, generatorX_lt_p,
    generatorY_lt_p, generator_onCurve, Curve.Representable]

theorem pointX_generator : pointX generator = generatorX := by
  exact pointX_packPoint (generatorX_lt_p.trans p_lt_two_pow_256)

theorem pointY_generator : pointY generator = generatorY := by
  exact pointY_packPoint (generatorX_lt_p.trans p_lt_two_pow_256)
    (generatorY_lt_p.trans p_lt_two_pow_256)

theorem generator_valid : PointValid generator := by
  constructor
  · exact packPoint_lt (generatorX_lt_p.trans p_lt_two_pow_256)
      (generatorY_lt_p.trans p_lt_two_pow_256)
  · rw [pointX_generator, pointY_generator]
    exact generator_groupRepresentable

theorem decodedGenerator_ne_zero : decodedGenerator ≠ 0 := by
  rw [decodedGenerator, VQBridge.Curve.groupPoint_of_onCurve generator_onCurve]
  exact VQBridge.Curve.pointOf_ne_zero generator_onCurve

end VQ.Tests.Secp256k1Order
