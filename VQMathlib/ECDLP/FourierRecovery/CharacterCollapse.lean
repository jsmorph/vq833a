import VQMathlib.ECDLP.FourierRecovery.CharacterCoordinates

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

theorem pairBasisState_eq_pairCharacterState
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    pairBasisState level d o = pairCharacterState level d o := by
  apply euclideanState_eq_of_projection_eq
  intro coordinate
  rw [pairBasisState_projection_apply,
    pairCharacterState_projection_apply]
  exact pairBasisCoordinate_eq_pairCharacterCoordinate
    level d o coordinate

theorem pairCharacterState_eq_pairLatentState
    {level d : Nat} (hlevel : 257 ≤ level)
    (o : ScalarIndex × ScalarIndex) :
    pairCharacterState level d o = pairLatentState d o := by
  change pairCharacterState level d o =
    (pairLatentMixtureData d o).state
  rw [pairLatentState_eq_latentMixture_data d o]
  unfold pairCharacterState latentMixture
  apply Finset.sum_congr rfl
  intro k _
  rw [inputCharacterSum_eq_fourierPeakAmplitude hlevel,
    secondCharacterSum_eq_fourierPeakAmplitude hlevel]

theorem pairBasisState_eq_pairLatentState
    {level d : Nat} (hlevel : 257 ≤ level)
    (o : ScalarIndex × ScalarIndex) :
    pairBasisState level d o = pairLatentState d o :=
  (pairBasisState_eq_pairCharacterState level d o).trans
    (pairCharacterState_eq_pairLatentState hlevel o)

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.pairBasisState_eq_pairLatentState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.pairBasisState_eq_pairLatentState
