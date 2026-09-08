import Mathlib.Algebra.Field.ZMod

namespace VQ.Tests.ECDLPRecovery

def quotient {q : Nat} (k v : ZMod q) : ZMod q :=
  v * k⁻¹

def candidate {q : Nat} (k v : ZMod q) : Nat :=
  (quotient k v).val

def checkedCandidate {q : Nat} (k v : ZMod q) : Option Nat :=
  if k = 0 then none else some (candidate k v)

def checkedNatural (q k v : Nat) : Option Nat :=
  checkedCandidate (q := q) (k : ZMod q) (v : ZMod q)

theorem quotient_mul {q d : Nat} (hq : q.Prime) {k : ZMod q}
    (hk : k ≠ 0) :
    quotient k ((d : ZMod q) * k) = (d : ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  simp [quotient, hk]

theorem quotient_eq_secret {q d : Nat} (hq : q.Prime) {k v : ZMod q}
    (hk : k ≠ 0) (hv : v = (d : ZMod q) * k) :
    quotient k v = (d : ZMod q) := by
  rw [hv]
  exact quotient_mul hq hk

theorem candidate_cast {q : Nat} (hq : q.Prime) (k v : ZMod q) :
    (candidate k v : ZMod q) = quotient k v := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact ZMod.natCast_zmod_val (quotient k v)

theorem candidate_lt {q : Nat} (hq : q.Prime) (k v : ZMod q) :
    candidate k v < q := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact ZMod.val_lt (quotient k v)

theorem candidate_eq_secret {q d : Nat} (hq : q.Prime) (hd : d < q)
    {k v : ZMod q} (hk : k ≠ 0) (hv : v = (d : ZMod q) * k) :
    candidate k v = d := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  rw [candidate, quotient_eq_secret hq hk hv, ZMod.val_natCast_of_lt hd]

@[simp]
theorem checkedCandidate_eq_none_iff {q : Nat} {k v : ZMod q} :
    checkedCandidate k v = none ↔ k = 0 := by
  simp [checkedCandidate]

theorem checkedCandidate_eq_some_of_ne {q : Nat} {k v : ZMod q}
    (hk : k ≠ 0) :
    checkedCandidate k v = some (candidate k v) := by
  simp [checkedCandidate, hk]

theorem checkedCandidate_recovers {q d : Nat} (hq : q.Prime) (hd : d < q)
    {k v : ZMod q} (hk : k ≠ 0) (hv : v = (d : ZMod q) * k) :
    checkedCandidate k v = some d := by
  rw [checkedCandidate_eq_some_of_ne hk, candidate_eq_secret hq hd hk hv]

theorem natCast_eq_zero_iff_of_lt {q k : Nat} (hk : k < q) :
    (k : ZMod q) = 0 ↔ k = 0 := by
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    simpa [ZMod.val_natCast_of_lt hk] using hval
  · rintro rfl
    simp

theorem natCast_ne_zero_iff_of_lt {q k : Nat} (hk : k < q) :
    (k : ZMod q) ≠ 0 ↔ k ≠ 0 := by
  exact not_congr (natCast_eq_zero_iff_of_lt hk)

theorem checkedNatural_eq_none_iff_of_lt {q k v : Nat} (hk : k < q) :
    checkedNatural q k v = none ↔ k = 0 := by
  rw [checkedNatural, checkedCandidate_eq_none_iff,
    natCast_eq_zero_iff_of_lt hk]

theorem checkedNatural_recovers {q d k v : Nat} (hq : q.Prime)
    (hd : d < q) (hkq : k < q) (hk : k ≠ 0)
    (hv : (v : ZMod q) = (d : ZMod q) * (k : ZMod q)) :
    checkedNatural q k v = some d := by
  change checkedCandidate (q := q) (k : ZMod q) (v : ZMod q) = some d
  exact checkedCandidate_recovers hq hd
    ((natCast_ne_zero_iff_of_lt hkq).2 hk) hv

end VQ.Tests.ECDLPRecovery
