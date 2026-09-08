import VQMathlib.ECDLP.FourierRecovery.CharacterAmplitudes
import VQMathlib.ECDLP.FourierRecovery.CharacterAlgebra
import VQMathlib.ECDLP.SubgroupEmbedding.BasisExpansion

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

private theorem oracleLabel_character_factor (d : Nat)
    (inputA inputB : ScalarIndex) (k : Fin q) :
    ZMod.stdAddChar
        (-(ZMod.finEquiv q k * oracleLabel d inputA inputB)) =
      ZMod.stdAddChar
          (-(ZMod.finEquiv q k * (inputA.val : ZMod q))) *
        ZMod.stdAddChar
          (-(ZMod.finEquiv q (productLabel q d q_prime.pos k) *
            (inputB.val : ZMod q))) := by
  rw [← AddChar.map_add_eq_mul, finEquiv_productLabel]
  congr 1
  simp only [oracleLabel]
  ring

set_option linter.defProp false in
def subgroupBasis_oracleLabel_expansion (d : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA inputB : ScalarIndex) :=
  finiteEmbeddingFactoredCyclicBasisFinAs (subgroupFullIndex o.1 o.2)
    (subgroupEmbeddingData o.1 o.2) secp256k1CyclicExpansionData
    (subgroupBasis o.1 o.2) (embeddedShiftEigenFin o.1 o.2)
    (fun _ => rfl) (fun _ => rfl) (oracleLabel d inputA inputB)
    (fun k =>
      ZMod.stdAddChar
        (-(ZMod.finEquiv q k * (inputA.val : ZMod q))))
    (fun k =>
      ZMod.stdAddChar
        (-(ZMod.finEquiv q (productLabel q d q_prime.pos k) *
          (inputB.val : ZMod q))))
    (oracleLabel_character_factor d inputA inputB)

attribute [irreducible] subgroupBasis_oracleLabel_expansion

end VQ.Tests.ECDLPFourierRecovery
