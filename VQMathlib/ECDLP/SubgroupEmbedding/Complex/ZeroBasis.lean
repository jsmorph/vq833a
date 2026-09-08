import VQMathlib.ECDLP.SubgroupEmbedding.Complex.Isometry

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem embedSubgroup_zeroBasis (a b : ScalarIndex) :
    embedSubgroup a b (zeroBasis q) = subgroupBasis a b 0 := by
  simpa only [embedSubgroup, subgroupEmbeddingLinear, zeroBasis,
    subgroupBasis, finiteEmbeddingBasis] using
    (subgroupEmbeddingData a b).basis (0 : ZMod q)

end VQ.Tests.ECDLPSubgroupEmbedding
