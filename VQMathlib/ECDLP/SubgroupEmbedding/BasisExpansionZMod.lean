import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericExpansion
import VQMathlib.ECDLP.SubgroupEmbedding.Spectral
import VQMathlib.ECDLP.SubgroupEmbedding.CyclicExpansion

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

attribute [local irreducible] q
local instance : NeZero q := ⟨q_prime.ne_zero⟩

set_option linter.defProp false in
def subgroupBasis_character_expansion (a b : ScalarIndex)
    (t : ZMod q) :=
  finiteEmbeddingCyclicBasisZModAs (subgroupFullIndex a b)
    (subgroupEmbeddingData a b) secp256k1CyclicExpansionData
    (subgroupBasis a b) (embeddedShiftEigen a b) (fun _ => rfl)
    (fun _ => rfl) t

attribute [irreducible] subgroupBasis_character_expansion

end VQ.Tests.ECDLPSubgroupEmbedding
