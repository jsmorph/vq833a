import VQMathlib.ECDLP.FourierRecovery.EmittedLatent
import VQMathlib.ECDLP.FourierRecovery.MixtureEmbedding
import VQMathlib.ECDLP.FourierRecovery.SelectedSum

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open ECDLPSubgroupEmbedding
open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

set_option linter.defProp false in
noncomputable def secp256k1CyclicMixtureData :=
  cyclicMixtureSpec q q_prime.pos

attribute [irreducible] secp256k1CyclicMixtureData

set_option linter.defProp false in
noncomputable def subgroupCyclicMixtureData (a b : ScalarIndex) :=
  embeddedCyclicMixtureSpec secp256k1CyclicMixtureData
    (subgroupFullIndex a b) (subgroupEmbeddingData a b)
    (embeddedShiftEigenFin a b) (fun _ => rfl)

attribute [irreducible] subgroupCyclicMixtureData

set_option linter.defProp false in
noncomputable def pairLatentMixture_weight_data
    (d : Nat) (o : ScalarIndex × ScalarIndex) :=
  (subgroupCyclicMixtureData o.1 o.2).weightResultAs
    (fun k output =>
      fourierPeakAmplitude scalarCard q output.val k.val)
    (fun k output =>
      fourierPeakAmplitude scalarCard q output.val
        (productLabel q d q_prime.pos k).val)
    o.1 o.2
    ((1 / (q : ℝ)) *
      ∑ k : Fin q,
        ‖fourierPeakAmplitude scalarCard q o.1.val k.val‖ ^ 2 *
          ‖fourierPeakAmplitude scalarCard q o.2.val
            (productLabel q d q_prime.pos k).val‖ ^ 2) rfl

attribute [irreducible] pairLatentMixture_weight_data

end VQ.Tests.ECDLPFourierRecovery
