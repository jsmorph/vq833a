import VQMathlib.ECDLP.FourierRecovery.MarginalWeightData

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem pairLatentState_weight_eq_normalizedComponentSum
    (d : Nat) (o : ScalarIndex × ScalarIndex) :
    ‖pairLatentState d o‖ ^ 2 =
      (1 / (q : ℝ)) *
        ∑ k : Fin q,
          ‖fourierPeakAmplitude scalarCard q o.1.val k.val‖ ^ 2 *
            ‖fourierPeakAmplitude scalarCard q o.2.val
              (productLabel q d q_prime.pos k).val‖ ^ 2 := by
  change ‖(pairLatentMixtureData d o).state‖ ^ 2 = _
  calc
    ‖(pairLatentMixtureData d o).state‖ ^ 2 =
        mixtureWeight (invSqrtCard q)
          (fun k output =>
            fourierPeakAmplitude scalarCard q output.val k.val)
          (fun k output =>
            fourierPeakAmplitude scalarCard q output.val
              (productLabel q d q_prime.pos k).val)
          (embeddedShiftEigenFin o.1 o.2) o.1 o.2 :=
      pairLatentState_weight_data d o
    _ = (1 / (q : ℝ)) *
        ∑ k : Fin q,
          ‖fourierPeakAmplitude scalarCard q o.1.val k.val‖ ^ 2 *
            ‖fourierPeakAmplitude scalarCard q o.2.val
              (productLabel q d q_prime.pos k).val‖ ^ 2 :=
      pairLatentMixture_weight_data d o

end VQ.Tests.ECDLPFourierRecovery
