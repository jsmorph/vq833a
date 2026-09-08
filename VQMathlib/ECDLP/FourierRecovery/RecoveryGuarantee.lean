import VQMathlib.ECDLP.FourierRecovery.ExactMarginal
import VQMathlib.ECDLP.Recovery.Verification

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

attribute [local irreducible] q

theorem selectedObservable_checkedRecovery
    {d pointQ : Nat} (hd : d < q)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator)
    {o : ScalarIndex × ScalarIndex}
    (ho : o ∈ selectedObservables scalarCard q d q_prime.pos
      q_lt_two_pow_256.le) :
    let k := decode q scalarCard o.1.val
    let v := decode q scalarCard o.2.val
    ECDLPRecovery.checkedNatural q k v = some d ∧
      ECDLPRecovery.publicAccepts q decodedGenerator
        (VQBridge.Curve.groupPoint
          (VQ.Curve.PointAddition.Runtime.pointX pointQ)
          (VQ.Curve.PointAddition.Runtime.pointY pointQ)) d := by
  dsimp only
  obtain ⟨hkq, hk, hv⟩ := decode_mem_selectedObservables
    (N := scalarCard) q_prime.pos q_lt_two_pow_256.le ho
  have hvz :
      (decode q scalarCard o.2.val : ZMod q) =
        (d : ZMod q) * (decode q scalarCard o.1.val : ZMod q) := by
    rw [hv, ZMod.natCast_mod]
    push_cast
    rfl
  constructor
  · exact ECDLPRecovery.checkedNatural_recovers
      q_prime hd hkq hk hvz
  · exact (ECDLPRecovery.publicAccepts_iff
      decodedGenerator_addOrderOf hd hQ).2 rfl

theorem emittedSelectedRecoveryGuarantee
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hd : d < q)
    (hQ : VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
      d • decodedGenerator) :
    ((((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedContribution scalarCard q d q_prime.pos
        q_lt_two_pow_256.le
        (scalarPairMarginal (emittedState level pointQ))) ∧
      ∀ o ∈ selectedObservables scalarCard q d q_prime.pos
          q_lt_two_pow_256.le,
        let k := decode q scalarCard o.1.val
        let v := decode q scalarCard o.2.val
        ECDLPRecovery.checkedNatural q k v = some d ∧
          ECDLPRecovery.publicAccepts q decodedGenerator
            (VQBridge.Curve.groupPoint
              (VQ.Curve.PointAddition.Runtime.pointX pointQ)
              (VQ.Curve.PointAddition.Runtime.pointY pointQ)) d := by
  constructor
  · exact emittedSelectedContribution_lower_bound hlevel hpointQ hQ
  · intro o ho
    exact selectedObservable_checkedRecovery hd hQ ho

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.selectedObservable_checkedRecovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.selectedObservable_checkedRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.emittedSelectedRecoveryGuarantee' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.emittedSelectedRecoveryGuarantee
