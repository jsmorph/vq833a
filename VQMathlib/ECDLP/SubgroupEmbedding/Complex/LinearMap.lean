import VQMathlib.ECDLP.SubgroupEmbedding.Complex.GenericIsometry
import VQMathlib.ECDLP.SubgroupEmbedding.Complex.Space
import VQMathlib.ECDLP.SubgroupEmbedding.Injection
import VQMathlib.ECDLP.Spectral.Basic

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

noncomputable section

opaque subgroupEmbeddingData (a b : ScalarIndex) :
    FiniteEmbeddingSpec (ZMod q) FullIndex (subgroupFullIndex a b) :=
  finiteEmbeddingSpec (subgroupFullIndex a b)
    (subgroupFullIndex_injective a b)

def subgroupEmbeddingLinear (a b : ScalarIndex) :
    CyclicState q →ₗ[ℂ] FullComplexState :=
  (subgroupEmbeddingData a b).linear

def embedSubgroup (a b : ScalarIndex)
    (v : CyclicState q) : FullComplexState :=
  subgroupEmbeddingLinear a b v

end

end VQ.Tests.ECDLPSubgroupEmbedding
