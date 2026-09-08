import VQMathlib.ECDLP.SubgroupEmbedding.Basic

namespace VQ.Tests.ECDLPSubgroupEmbedding

open Secp256k1Order

theorem nsmul_decodedGenerator_injective :
    Function.Injective
      (fun t : ZMod q => t.val • decodedGenerator) := by
  letI : NeZero q := ⟨q_prime.ne_zero⟩
  intro t u h
  apply ZMod.val_injective q
  have ht : t.val < q := t.val_lt
  have hu : u.val < q := u.val_lt
  rcases le_total t.val u.val with htu | hut
  · have hzero : (u.val - t.val) • decodedGenerator = 0 := by
      have hsum :
          t.val • decodedGenerator + (u.val - t.val) • decodedGenerator =
            t.val • decodedGenerator + 0 := by
        rw [add_zero, ← add_nsmul, Nat.add_sub_of_le htu]
        exact h.symm
      exact add_left_cancel hsum
    have hdiv : q ∣ u.val - t.val := by
      have horderDiv : addOrderOf decodedGenerator ∣ u.val - t.val :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
      simpa only [decodedGenerator_addOrderOf] using horderDiv
    have hdiff : u.val - t.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdiv (by omega)
    omega
  · have hzero : (t.val - u.val) • decodedGenerator = 0 := by
      have hsum :
          u.val • decodedGenerator + (t.val - u.val) • decodedGenerator =
            u.val • decodedGenerator + 0 := by
        rw [add_zero, ← add_nsmul, Nat.add_sub_of_le hut]
        exact h
      exact add_left_cancel hsum
    have hdiv : q ∣ t.val - u.val := by
      have horderDiv : addOrderOf decodedGenerator ∣ t.val - u.val :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
      simpa only [decodedGenerator_addOrderOf] using horderDiv
    have hdiff : t.val - u.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdiv (by omega)
    omega

theorem subgroupPointCode_injective :
    Function.Injective subgroupPointCode := by
  intro t u h
  apply nsmul_decodedGenerator_injective
  change t.val • decodedGenerator = u.val • decodedGenerator
  rw [← subgroupPointCode_decode t, ← subgroupPointCode_decode u, h]

theorem subgroupFullIndex_injective (a b : ScalarIndex) :
    Function.Injective (subgroupFullIndex a b) := by
  intro t u h
  apply subgroupPointCode_injective
  have hval := congrArg Fin.val h
  have hmod := congrArg (fun i => i % 2 ^ ECDLPAlgorithm.firstScalarOffset) hval
  simpa only [subgroupFullIndex_mod_prefix] using hmod

theorem subgroupFullIndex_joint_injective :
    Function.Injective
      (fun p : ScalarIndex × ScalarIndex × ZMod q =>
        subgroupFullIndex p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, t⟩ ⟨a', b', t'⟩ h
  have hval := congrArg Fin.val h
  have hpoint := congrArg
    (fun i => i % 2 ^ ECDLPAlgorithm.firstScalarOffset) hval
  have ht : t = t' := subgroupPointCode_injective (by
    simpa only [subgroupFullIndex_mod_prefix] using hpoint)
  have hpair := congrArg
    (fun i => i / 2 ^ ECDLPAlgorithm.firstScalarOffset) hval
  have haVal : a.val = a'.val := by
    have hmod := congrArg
      (fun i => i % 2 ^ ECDLPAlgorithm.scalarWidth) hpair
    simpa only [subgroupFullIndex_firstScalar] using hmod
  have hbVal : b.val = b'.val := by
    have hdiv := congrArg
      (fun i => i / 2 ^ ECDLPAlgorithm.scalarWidth) hpair
    simpa only [subgroupFullIndex_secondScalar] using hdiv
  have ha : a = a' := Fin.ext haVal
  have hb : b = b' := Fin.ext hbVal
  simp only [ha, hb, ht]

end VQ.Tests.ECDLPSubgroupEmbedding
