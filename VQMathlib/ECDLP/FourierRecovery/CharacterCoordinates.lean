import VQMathlib.ECDLP.FourierRecovery.CharacterStates
import VQMathlib.ECDLP.FourierRecovery.GenericProjection

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

noncomputable def pairBasisCoordinate (level d : Nat)
    (o : ScalarIndex × ScalarIndex) (coordinate : FullIndex) : ℂ :=
  ∑ inputA : ScalarIndex, ∑ inputB : ScalarIndex,
    (inputFourierCoefficient level inputA o.1 *
      inputFourierCoefficient level inputB o.2) •
        subgroupBasis o.1 o.2
          (oracleLabel d inputA inputB) coordinate

noncomputable def pairCharacterCoordinate (level d : Nat)
    (o : ScalarIndex × ScalarIndex) (coordinate : FullIndex) : ℂ :=
  ∑ k : Fin q,
    (invSqrtCard q * firstCharacterAmplitude level k o.1 *
      secondCharacterAmplitude level d k o.2) •
        embeddedShiftEigenFin o.1 o.2 k coordinate

theorem pairBasisState_projection_apply (level d : Nat)
    (o : ScalarIndex × ScalarIndex) (coordinate : FullIndex) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate)
        (pairBasisState level d o) =
      pairBasisCoordinate level d o coordinate := by
  rw [pairBasisState, euclideanProjection_doubleWeightedSum_apply]
  rfl

theorem pairCharacterState_projection_apply (level d : Nat)
    (o : ScalarIndex × ScalarIndex) (coordinate : FullIndex) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate)
        (pairCharacterState level d o) =
      pairCharacterCoordinate level d o coordinate := by
  rw [pairCharacterState, latentMixture,
    euclideanProjection_weightedSum_apply]
  rfl

theorem subgroupBasis_oracleLabel_coordinate_expansion (d : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA inputB : ScalarIndex)
    (coordinate : FullIndex) :
    subgroupBasis o.1 o.2
        (oracleLabel d inputA inputB) coordinate =
      ∑ k : Fin q,
        (invSqrtCard q *
          (ZMod.stdAddChar
              (-(ZMod.finEquiv q k * (inputA.val : ZMod q))) *
            ZMod.stdAddChar
              (-(ZMod.finEquiv q
                  (productLabel q d q_prime.pos k) *
                (inputB.val : ZMod q))))) •
          embeddedShiftEigenFin o.1 o.2 k coordinate := by
  have hprojection := euclideanProjection_congr
    (subgroupBasis_oracleLabel_expansion d o inputA inputB) coordinate
  rw [euclideanProjection_apply,
    euclideanProjection_weightedSum_apply] at hprojection
  exact hprojection

theorem pairBasisCoordinate_eq_pairCharacterCoordinate
    (level d : Nat) (o : ScalarIndex × ScalarIndex)
    (coordinate : FullIndex) :
    pairBasisCoordinate level d o coordinate =
      pairCharacterCoordinate level d o coordinate := by
  unfold pairBasisCoordinate pairCharacterCoordinate
  apply doubleCharacterExpansion
  intro inputA inputB
  exact subgroupBasis_oracleLabel_coordinate_expansion
    d o inputA inputB coordinate

end VQ.Tests.ECDLPFourierRecovery
