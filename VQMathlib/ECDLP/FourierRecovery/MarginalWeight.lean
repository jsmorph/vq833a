import VQMathlib.ECDLP.FourierRecovery.EmittedLatent
import VQMathlib.ECDLP.FourierRecovery.MarginalWeightScalar
import VQMathlib.ECDLP.FourierRecovery.MarginalWeightState

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem scalarPairMarginal_eq_norm_eventState_sq
    (state : FullComplexState) (o : ScalarIndex × ScalarIndex) :
    scalarPairMarginal state o =
      ‖scalarPairEventState o state‖ ^ 2 := by
  exact ApproximationProbability.acceptanceWeight_eq_norm_eventState_sq
    (scalarPairEvent o) state

theorem pairLatentState_weight_eq_uniformComponentSum
    (d : Nat) (o : ScalarIndex × ScalarIndex) :
    ‖pairLatentState d o‖ ^ 2 =
      ∑ k : Fin q, uniformComponentWeight scalarCard q d q_prime.pos k o := by
  calc
    ‖pairLatentState d o‖ ^ 2 =
        (1 / (q : ℝ)) *
        ∑ k : Fin q,
          ‖fourierPeakAmplitude scalarCard q o.1.val k.val‖ ^ 2 *
            ‖fourierPeakAmplitude scalarCard q o.2.val
              (productLabel q d q_prime.pos k).val‖ ^ 2 :=
      pairLatentState_weight_eq_normalizedComponentSum d o
    _ = ∑ k : Fin q,
        uniformComponentWeight scalarCard q d q_prime.pos k o :=
      normalizedComponentSum_eq_uniformComponentSum d o

end VQ.Tests.ECDLPFourierRecovery
