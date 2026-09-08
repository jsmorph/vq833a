import VQMathlib.ECDLP.FourierRecovery.MarginalWeightData
import VQMathlib.ECDLP.FourierRecovery.SelectedSum

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem normalizedComponentSum_eq_uniformComponentSum
    (d : Nat) (o : ScalarIndex × ScalarIndex) :
    (1 / (q : ℝ)) *
        ∑ k : Fin q,
          ‖fourierPeakAmplitude scalarCard q o.1.val k.val‖ ^ 2 *
            ‖fourierPeakAmplitude scalarCard q o.2.val
              (productLabel q d q_prime.pos k).val‖ ^ 2 =
      ∑ k : Fin q,
        uniformComponentWeight scalarCard q d q_prime.pos k o := by
  rw [Finset.mul_sum]
  rfl

end VQ.Tests.ECDLPFourierRecovery
