import VQMathlib.Curve.Secp256k1Order.Prime

namespace VQ.Tests.Secp256k1Order

open VQ
open VQ.Curve.PointAddition.Runtime
open FixedBaseScalarMultiplication

set_option maxRecDepth 1000000

theorem generator_q_multiple_encoding :
    scalarTableValue q (powerTable 256 generator) = 0 := by
  decide

theorem q_nsmul_decodedGenerator : q • decodedGenerator = 0 := by
  have h := groupPoint_scalarTableValue_powerTable q_lt_two_pow_256 generator_valid
  have hx : pointX 0 = 0 := by
    norm_num [pointX, VQ.Reversible.readField]
  have hy : pointY 0 = 0 := by
    norm_num [pointY, VQ.Reversible.readField]
  rw [generator_q_multiple_encoding, hx, hy,
    VQBridge.Curve.groupPoint_infinity, pointX_generator, pointY_generator] at h
  simpa [decodedGenerator] using h.symm

theorem decodedGenerator_addOrderOf : addOrderOf decodedGenerator = q := by
  exact addOrderOf_eq_prime q_nsmul_decodedGenerator decodedGenerator_ne_zero

end VQ.Tests.Secp256k1Order
