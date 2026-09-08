import VQMathlib.ECDLP.SubgroupEmbedding.BasisExpansionZMod

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

attribute [local irreducible] q
local instance : NeZero q := ⟨q_prime.ne_zero⟩

noncomputable def embeddedShiftEigenFin (a b : ScalarIndex)
    (k : Fin q) : FullComplexState :=
  embeddedShiftEigen a b (ZMod.finEquiv q k)

theorem embedSubgroup_shiftEigenFin_eq_embeddedShiftEigenFin
    (a b : ScalarIndex) (k : Fin q) :
    embedSubgroup a b (shiftEigen q (ZMod.finEquiv q k)) =
      embeddedShiftEigenFin a b k :=
  rfl

set_option linter.defProp false in
def subgroupBasis_character_expansion_fin (a b : ScalarIndex)
    (t : ZMod q) :=
  finiteEmbeddingCyclicBasisFinAs (subgroupFullIndex a b)
    (subgroupEmbeddingData a b) secp256k1CyclicExpansionData
    (subgroupBasis a b) (embeddedShiftEigenFin a b) (fun _ => rfl)
    (fun _ => rfl) t

attribute [irreducible] subgroupBasis_character_expansion_fin

end VQ.Tests.ECDLPSubgroupEmbedding
