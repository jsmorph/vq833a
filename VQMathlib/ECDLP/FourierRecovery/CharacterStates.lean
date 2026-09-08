import VQMathlib.ECDLP.FourierRecovery.CharacterBasis
import VQMathlib.ECDLP.FourierRecovery.CharacterAlgebra

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open ECDLPSpectral
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

noncomputable def pairCharacterState (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  latentMixture (invSqrtCard q)
    (firstCharacterAmplitude level)
    (secondCharacterAmplitude level d)
    (embeddedShiftEigenFin o.1 o.2) o.1 o.2

noncomputable def pairLatentMixtureData (d : Nat)
    (o : ScalarIndex × ScalarIndex) :=
  latentMixtureData (invSqrtCard q)
    (fun k output =>
      fourierPeakAmplitude scalarCard q output.val k.val)
    (fun k output =>
      fourierPeakAmplitude scalarCard q output.val
        (productLabel q d q_prime.pos k).val)
    (embeddedShiftEigenFin o.1 o.2) o.1 o.2

attribute [irreducible] pairLatentMixtureData

noncomputable def pairLatentState (d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  (pairLatentMixtureData d o).state

set_option linter.defProp false in
noncomputable def pairLatentState_eq_latentMixture_data
    (d : Nat) (o : ScalarIndex × ScalarIndex) :=
  (pairLatentMixtureData d o).state_eq

set_option linter.defProp false in
noncomputable def pairLatentState_weight_data
    (d : Nat) (o : ScalarIndex × ScalarIndex) :=
  (pairLatentMixtureData d o).weight_eq

attribute [irreducible]
  pairLatentState_eq_latentMixture_data
  pairLatentState_weight_data

end VQ.Tests.ECDLPFourierRecovery
