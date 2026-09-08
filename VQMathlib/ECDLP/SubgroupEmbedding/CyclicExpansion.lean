import VQMathlib.ECDLP.Spectral.ExpansionSpec
import VQMathlib.Curve.Secp256k1Order.Prime

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

attribute [local irreducible] q
local instance : NeZero q := ⟨q_prime.ne_zero⟩

noncomputable section

opaque secp256k1CyclicExpansionData : CyclicExpansionSpec q :=
  cyclicExpansionSpec q q_prime.pos

set_option linter.defProp false in
def secp256k1_basis_eq_sum_shiftEigen (t : ZMod q) :=
  cyclicExpansionBasisZMod secp256k1CyclicExpansionData t

set_option linter.defProp false in
def secp256k1_basis_eq_sum_shiftEigen_fin (t : ZMod q) :=
  cyclicExpansionBasisFin secp256k1CyclicExpansionData t

attribute [irreducible] secp256k1_basis_eq_sum_shiftEigen
  secp256k1_basis_eq_sum_shiftEigen_fin

end

end VQ.Tests.ECDLPSubgroupEmbedding
