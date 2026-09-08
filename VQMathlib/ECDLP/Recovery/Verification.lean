import VQMathlib.ECDLP.Recovery.Algebra

namespace VQ.Tests.ECDLPRecovery

def publicAccepts {G : Type*} [AddMonoid G]
    (q : Nat) (P Q : G) (e : Nat) : Prop :=
  e < q ∧ e • P = Q

theorem publicAccepts_iff {G : Type*} [AddMonoid G]
    {q d e : Nat} {P Q : G} (hP : addOrderOf P = q)
    (hd : d < q) (hQ : Q = d • P) :
    publicAccepts q P Q e ↔ e = d := by
  constructor
  · rintro ⟨he, heq⟩
    apply nsmul_injOn_Iio_addOrderOf (x := P)
    · simpa [hP] using he
    · simpa [hP] using hd
    · simpa [hQ] using heq
  · rintro rfl
    exact ⟨hd, hQ.symm⟩

theorem publicRejects_of_not_lt {G : Type*} [AddMonoid G]
    {q e : Nat} {P Q : G} (he : q ≤ e) :
    ¬ publicAccepts q P Q e := by
  intro h
  exact (Nat.not_lt_of_ge he) h.1

theorem candidate_publicAccepts {G : Type*} [AddMonoid G]
    {q d : Nat} {P Q : G} (hq : q.Prime) (hP : addOrderOf P = q)
    (hd : d < q) (hQ : Q = d • P) {k v : ZMod q} (hk : k ≠ 0)
    (hv : v = (d : ZMod q) * k) :
    publicAccepts q P Q (candidate k v) := by
  rw [publicAccepts_iff hP hd hQ]
  exact candidate_eq_secret hq hd hk hv

theorem checkedCandidate_sound {G : Type*} [AddMonoid G]
    {q d e : Nat} {P Q : G} (hq : q.Prime) (hP : addOrderOf P = q)
    (hd : d < q) (hQ : Q = d • P) {k v : ZMod q} (hk : k ≠ 0)
    (hv : v = (d : ZMod q) * k)
    (hrecover : checkedCandidate k v = some e) :
    e = d ∧ publicAccepts q P Q e := by
  have hsecret := checkedCandidate_recovers hq hd hk hv
  have he : e = d := by
    exact Option.some.inj (hrecover.symm.trans hsecret)
  subst e
  exact ⟨rfl, (publicAccepts_iff hP hd hQ).2 rfl⟩

theorem checkedNatural_sound {G : Type*} [AddMonoid G]
    {q d e k v : Nat} {P Q : G} (hq : q.Prime) (hP : addOrderOf P = q)
    (hd : d < q) (hQ : Q = d • P) (hkq : k < q) (hk : k ≠ 0)
    (hv : (v : ZMod q) = (d : ZMod q) * (k : ZMod q))
    (hrecover : checkedNatural q k v = some e) :
    e = d ∧ publicAccepts q P Q e := by
  have hsecret := checkedNatural_recovers hq hd hkq hk hv
  have he : e = d := by
    exact Option.some.inj (hrecover.symm.trans hsecret)
  subst e
  exact ⟨rfl, (publicAccepts_iff hP hd hQ).2 rfl⟩

end VQ.Tests.ECDLPRecovery
