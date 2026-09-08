import VQMathlib.ECDLP.FourierRecovery.ProjectionAlgebra

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem scalarPairEventState_terminalState_eq_pairBasisState
    {level d : Nat} (o : ScalarIndex × ScalarIndex) :
    scalarPairEventState o
        (Approximation.cvec level circuitWidth (terminalState level d)) =
      pairBasisState level d o := by
  have h : terminalProjectionSource level d o = pairBasisState level d o :=
    terminalProjectionAlgebra o
  unfold terminalProjectionSource at h
  exact h

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.scalarPairEventState_terminalState_eq_pairBasisState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.scalarPairEventState_terminalState_eq_pairBasisState
