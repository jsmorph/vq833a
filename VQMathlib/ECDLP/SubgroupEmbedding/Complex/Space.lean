import Mathlib.Analysis.InnerProductSpace.PiL2
import VQMathlib.ECDLP.SubgroupEmbedding.Basic

open WithLp

namespace VQ.Tests.ECDLPSubgroupEmbedding

open Secp256k1Order

abbrev FullComplexState := EuclideanSpace ℂ FullIndex

noncomputable def subgroupBasis (a b : ScalarIndex) (t : ZMod q) :
    FullComplexState :=
  PiLp.single 2 (subgroupFullIndex a b t) 1

end VQ.Tests.ECDLPSubgroupEmbedding
