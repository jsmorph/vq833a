import VQ.Euclid.PackedInputPreparation
import VQ.Curve.Field
import VQMathlib.Euclid.PackedInputCounts

namespace VQMathlib.Euclid

open VQ
open VQ.Reversible

theorem packedInputPreparationGates_ccx :
    (VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p).countP RGate.isCcx =
      35204 := by
  exact PackedInputCounts.gates_ccx VQ.Curve.p

end VQMathlib.Euclid
