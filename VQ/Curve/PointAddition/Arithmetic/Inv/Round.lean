/-!
# Kaliski binary extended Euclidean arithmetic

The state and round function of Algorithm 2 of Roetteler, Naehrig, Svore, and
Lauter carry the invariants for almost-inverse correctness and termination
within `2 * n` rounds.  Later modules construct a circuit realizing these
arithmetic transitions.

The round function is the four-case `match` printed in their section 3.4, with
one change: a round whose `v` is already zero leaves the state alone.  Their
circuit does the same thing with a flag qubit that switches the round into
counter mode, and the counter exists to keep the *gate sequence* independent of
the data.  The arithmetic does not need the counter, so this file leaves it out
and the circuit layer carries it.

The invariants are stated as congruences rather than equations because two of
them hold only modulo `p`.  The local `Cong` definition keeps this arithmetic
module independent of Mathlib.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

/-! ## Congruence

Four lemmas, which is everything the invariant proofs use. -/

/-- `a` and `b` agree modulo `p`. -/
def Cong (p a b : Nat) : Prop := a % p = b % p

theorem cong_refl {p a : Nat} : Cong p a a := rfl

theorem cong_trans {p a b c : Nat} (h₁ : Cong p a b) (h₂ : Cong p b c) : Cong p a c :=
  Eq.trans h₁ h₂

/-- Multiplying both sides by the same factor. -/
theorem cong_mul_left {p a b : Nat} (c : Nat) (h : Cong p a b) : Cong p (c * a) (c * b) := by
  show (c * a) % p = (c * b) % p
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- Adding congruent values. -/
theorem cong_add {p a b c d : Nat} (h₁ : Cong p a b) (h₂ : Cong p c d) :
    Cong p (a + c) (b + d) := by
  show (a + c) % p = (b + d) % p
  rw [Nat.add_mod, h₁, h₂, ← Nat.add_mod]

/-! ## State representation and round semantics -/

/-- The four Euclidean registers and the step counter.  `u` starts at the
modulus, `v` at the value being inverted, `r` at zero, and `s` at one. -/
structure St where
  u : Nat
  v : Nat
  r : Nat
  s : Nat
  k : Nat
  deriving Repr, DecidableEq

/-- One round of Kaliski's algorithm, following the four cases of the published
`match`.  Each case halves one of `u` and `v`, doubles one of `r` and `s`,
and increments the halving counter `k`. -/
def step (st : St) : St :=
  if st.u % 2 = 0 then
    { st with u := st.u / 2, s := 2 * st.s, k := st.k + 1 }
  else if st.v % 2 = 0 then
    { st with v := st.v / 2, r := 2 * st.r, k := st.k + 1 }
  else if st.v < st.u then
    { st with u := (st.u - st.v) / 2, r := st.r + st.s, s := 2 * st.s, k := st.k + 1 }
  else
    { st with v := (st.v - st.u) / 2, r := 2 * st.r, s := st.r + st.s, k := st.k + 1 }

/-- The padded round: once `v` is zero the state stops moving.  The circuit
advances its counter during the remaining rounds. -/
def round (st : St) : St := if st.v = 0 then st else step st

/-- `t` rounds. -/
def iter : Nat → St → St
  | 0, st => st
  | t + 1, st => iter t (round st)

theorem iter_succ (t : Nat) (st : St) : iter (t + 1) st = iter t (round st) := rfl

/-- The same, with the round applied last rather than first. -/
theorem iter_succ' : ∀ (t : Nat) (st : St), iter (t + 1) st = round (iter t st)
  | 0, _ => rfl
  | t + 1, st => by
    rw [iter_succ (t + 1) st, iter_succ' t (round st), ← iter_succ t st]

/-- The starting state for modulus `p` and input `x`. -/
def start (p x : Nat) : St := { u := p, v := x, r := 0, s := 1, k := 0 }

/-! ## Arithmetic invariants

Four facts carried through every round.  The first keeps `u` positive, which is
what stops the halving argument from dividing by zero.  The second is the
Euclidean invariant the paper states, `p = r v + s u`, and it is an equation over
the integers rather than a congruence.  The third and fourth are the ones that
make the algorithm compute an inverse: they say `s` tracks `v` and `r` tracks
`-u`, both scaled by the `2 ^ k` the halvings have accumulated.

The third and fourth do not use the second, and the second does not use them. -/

/-- The invariant bundle. -/
def Inv (p x : Nat) (st : St) : Prop :=
  0 < st.u ∧ st.r * st.v + st.s * st.u = p ∧
    Cong p (x * st.s) (st.v * 2 ^ st.k) ∧
    Cong p (x * st.r + st.u * 2 ^ st.k) 0

theorem start_inv {p x : Nat} (hp : 0 < p) : Inv p x (start p x) := by
  refine ⟨hp, by simp [start], ?_, ?_⟩
  · show Cong p (x * 1) (x * 2 ^ 0)
    simp [Cong]
  · show Cong p (x * 0 + p * 2 ^ 0) 0
    simp [Cong]

theorem pow_succ_two (k : Nat) : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-! ### Branch equations

`step` is a chain of `if`s, so its projections do not reduce until the branch is
known.  These four lemmas name the branches. -/

theorem step_ueven {st : St} (he : st.u % 2 = 0) :
    step st = { st with u := st.u / 2, s := 2 * st.s, k := st.k + 1 } := by
  simp [step, he]

theorem step_veven {st : St} (he : st.u % 2 ≠ 0) (hv : st.v % 2 = 0) :
    step st = { st with v := st.v / 2, r := 2 * st.r, k := st.k + 1 } := by
  simp [step, he, hv]

theorem step_ubig {st : St} (he : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : st.v < st.u) :
    step st = { st with u := (st.u - st.v) / 2, r := st.r + st.s, s := 2 * st.s, k := st.k + 1 } := by
  simp [step, he, hv, hlt]

theorem step_vbig {st : St} (he : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : ¬ st.v < st.u) :
    step st = { st with v := (st.v - st.u) / 2, r := 2 * st.r, s := st.r + st.s, k := st.k + 1 } := by
  simp [step, he, hv, hlt]

/-- Rewriting both sides of a congruence. -/
theorem cong_congr {p a b a' b' : Nat} (ha : a = a') (hb : b = b') (h : Cong p a' b') :
    Cong p a b := by rw [Cong, ha, hb]; exact h

/-- The bundle at an explicit state, which is the shape every branch produces. -/
theorem inv_mk {p x u v r s k : Nat} (h0 : 0 < u) (h1 : r * v + s * u = p)
    (h2 : Cong p (x * s) (v * 2 ^ k)) (h3 : Cong p (x * r + u * 2 ^ k) 0) :
    Inv p x { u := u, v := v, r := r, s := s, k := k } := ⟨h0, h1, h2, h3⟩

/-- One round preserves the bundle. -/
theorem step_inv {p x : Nat} {st : St} (_hv0 : st.v ≠ 0) (h : Inv p x st) :
    Inv p x (step st) := by
  obtain ⟨hu, h1, h2, h3⟩ := h
  by_cases he : st.u % 2 = 0
  · -- `u` is even, so it halves and `s` doubles.
    obtain ⟨w, hwd⟩ : ∃ w, st.u / 2 = w := ⟨_, rfl⟩
    have hw : st.u = 2 * w := by omega
    rw [step_ueven he, hwd]
    refine inv_mk (by omega) ?_ ?_ ?_
    · have e : 2 * st.s * w = st.s * st.u := by
        rw [hw]; simp [Nat.mul_comm, Nat.mul_left_comm]
      rw [e]; exact h1
    · refine cong_congr ?_ ?_ (cong_mul_left 2 h2)
      · simp [Nat.mul_comm, Nat.mul_assoc]
      · rw [pow_succ_two]; simp [Nat.mul_left_comm]
    · have e : w * 2 ^ (st.k + 1) = st.u * 2 ^ st.k := by
        rw [pow_succ_two, hw]; simp [Nat.mul_comm, Nat.mul_assoc]
      rw [e]; exact h3
  · by_cases hev : st.v % 2 = 0
    · -- `u` is odd and `v` is even, so `v` halves and `r` doubles.
      obtain ⟨w, hwd⟩ : ∃ w, st.v / 2 = w := ⟨_, rfl⟩
      have hw : st.v = 2 * w := by omega
      rw [step_veven he hev, hwd]
      refine inv_mk hu ?_ ?_ ?_
      · have e : 2 * st.r * w = st.r * st.v := by
          rw [hw]; simp [Nat.mul_comm, Nat.mul_left_comm]
        rw [e]; exact h1
      · have e : w * 2 ^ (st.k + 1) = st.v * 2 ^ st.k := by
          rw [pow_succ_two, hw]; simp [Nat.mul_comm, Nat.mul_assoc]
        rw [e]; exact h2
      · refine cong_congr ?_ (by simp) (cong_mul_left 2 h3)
        rw [pow_succ_two]
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · by_cases hlt : st.v < st.u
      · -- Both odd, `u` the larger: `u` takes the halved difference.
        obtain ⟨w, hwd⟩ : ∃ w, (st.u - st.v) / 2 = w := ⟨_, rfl⟩
        have hw : st.u = st.v + 2 * w := by omega
        rw [step_ubig he hev hlt, hwd]
        refine inv_mk (by omega) ?_ ?_ ?_
        · have e : (st.r + st.s) * st.v + 2 * st.s * w = st.r * st.v + st.s * st.u := by
            rw [hw]
            simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc]
          rw [e]; exact h1
        · refine cong_congr ?_ ?_ (cong_mul_left 2 h2)
          · simp [Nat.mul_comm, Nat.mul_assoc]
          · rw [pow_succ_two]; simp [Nat.mul_left_comm]
        · -- `x (r + s) + w 2^(k+1)` is `x r + x s + 2 w 2^k`, and `x s` tracks `v 2^k`.
          have e : x * (st.r + st.s) + w * 2 ^ (st.k + 1)
              = x * st.r + (x * st.s + 2 * w * 2 ^ st.k) := by
            rw [pow_succ_two]
            simp [Nat.mul_add, Nat.mul_comm,
              Nat.mul_assoc, Nat.add_assoc]
          rw [e]
          refine cong_trans (cong_add (cong_refl (a := x * st.r))
            (cong_add h2 (cong_refl (a := 2 * w * 2 ^ st.k)))) ?_
          have e2 : x * st.r + (st.v * 2 ^ st.k + 2 * w * 2 ^ st.k)
              = x * st.r + st.u * 2 ^ st.k := by
            rw [hw]
            simp [Nat.add_mul, Nat.mul_comm,
              Nat.mul_assoc]
          rw [e2]; exact h3
      · -- Both odd, `v` at least as large: `v` takes the halved difference.
        obtain ⟨w, hwd⟩ : ∃ w, (st.v - st.u) / 2 = w := ⟨_, rfl⟩
        have hw : st.v = st.u + 2 * w := by omega
        rw [step_vbig he hev hlt, hwd]
        refine inv_mk hu ?_ ?_ ?_
        · have e : 2 * st.r * w + (st.r + st.s) * st.u = st.r * st.v + st.s * st.u := by
            rw [hw]
            simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          rw [e]; exact h1
        · -- `x (r + s)` is `x r + x s`.  The first cancels `u 2^k` and the second
          -- supplies `v 2^k`, leaving `w 2^(k+1)`.
          have e0 : x * (st.r + st.s) = x * st.r + x * st.s := by rw [Nat.mul_add]
          rw [e0]
          refine cong_trans (cong_add (cong_refl (a := x * st.r)) h2) ?_
          have e : x * st.r + st.v * 2 ^ st.k
              = (x * st.r + st.u * 2 ^ st.k) + w * 2 ^ (st.k + 1) := by
            rw [hw, pow_succ_two]
            simp [Nat.add_mul, Nat.mul_comm,
              Nat.mul_assoc, Nat.add_assoc]
          rw [e]
          simpa using cong_add h3 (cong_refl (a := w * 2 ^ (st.k + 1)))
        · refine cong_congr ?_ (by simp) (cong_mul_left 2 h3)
          rw [pow_succ_two]
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Every round preserves the bundle, including the rounds that do nothing. -/
theorem round_inv {p x : Nat} {st : St} (h : Inv p x st) : Inv p x (round st) := by
  unfold round
  split
  · exact h
  · exact step_inv (by assumption) h

theorem iter_inv {p x : Nat} : ∀ (t : Nat) {st : St}, Inv p x st → Inv p x (iter t st)
  | 0, _, h => h
  | t + 1, _, h => iter_inv t (round_inv h)

/-! ## Termination

The product `u v` at least halves every round, so it cannot remain positive for
`2 n` rounds when it starts below `2 ^ (2 n)`.  This worst-case bound gives
the published circuit's fixed schedule of `2 n` rounds with counter padding. -/

theorem step_halves {st : St} : 2 * ((step st).u * (step st).v) ≤ st.u * st.v := by
  by_cases he : st.u % 2 = 0
  · obtain ⟨w, hwd⟩ : ∃ w, st.u / 2 = w := ⟨_, rfl⟩
    have hw : st.u = 2 * w := by omega
    rw [step_ueven he, hwd]
    show 2 * (w * st.v) ≤ st.u * st.v
    rw [hw, Nat.mul_assoc]
    exact Nat.le_refl _
  · by_cases hev : st.v % 2 = 0
    · obtain ⟨w, hwd⟩ : ∃ w, st.v / 2 = w := ⟨_, rfl⟩
      have hw : st.v = 2 * w := by omega
      rw [step_veven he hev, hwd]
      show 2 * (st.u * w) ≤ st.u * st.v
      rw [hw, Nat.mul_left_comm]
      exact Nat.le_refl _
    · by_cases hlt : st.v < st.u
      · obtain ⟨w, hwd⟩ : ∃ w, (st.u - st.v) / 2 = w := ⟨_, rfl⟩
        have hw : st.u = st.v + 2 * w := by omega
        rw [step_ubig he hev hlt, hwd]
        show 2 * (w * st.v) ≤ st.u * st.v
        calc 2 * (w * st.v) = 2 * w * st.v := by rw [Nat.mul_assoc]
          _ ≤ (st.v + 2 * w) * st.v := Nat.mul_le_mul_right _ (by omega)
          _ = st.u * st.v := by rw [← hw]
      · obtain ⟨w, hwd⟩ : ∃ w, (st.v - st.u) / 2 = w := ⟨_, rfl⟩
        have hw : st.v = st.u + 2 * w := by omega
        rw [step_vbig he hev hlt, hwd]
        show 2 * (st.u * w) ≤ st.u * st.v
        calc 2 * (st.u * w) = st.u * (2 * w) := by rw [Nat.mul_left_comm]
          _ ≤ st.u * (st.u + 2 * w) := Nat.mul_le_mul_left _ (by omega)
          _ = st.u * st.v := by rw [← hw]

theorem round_halves (st : St) : 2 * ((round st).u * (round st).v) ≤ st.u * st.v := by
  unfold round
  split
  · next h => rw [h]; simp
  · exact step_halves

theorem iter_halves : ∀ (t : Nat) (st : St),
    2 ^ t * ((iter t st).u * (iter t st).v) ≤ st.u * st.v
  | 0, st => by simp [iter]
  | t + 1, st => by
    rw [iter_succ, Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, Nat.mul_assoc]
    calc 2 * (2 ^ t * ((iter t (round st)).u * (iter t (round st)).v))
        ≤ 2 * ((round st).u * (round st).v) :=
          Nat.mul_le_mul_left _ (iter_halves t (round st))
      _ ≤ st.u * st.v := round_halves st

/-- After `2 n` rounds the algorithm has finished, when both the modulus and the
input fit in `n` bits.  `u` stays positive, so a nonzero `v` would keep the
product at least one and the halving bound would force `2 ^ (2 n) ≤ p x`. -/
theorem iter_v_zero {p x n : Nat} (hp : 0 < p) (hpn : p ≤ 2 ^ n) (hx : x < 2 ^ n) :
    (iter (2 * n) (start p x)).v = 0 := by
  cases Nat.eq_zero_or_pos (iter (2 * n) (start p x)).v with
  | inl h => exact h
  | inr hpos =>
  exfalso
  have hne : (iter (2 * n) (start p x)).v ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  have hinv := iter_inv (p := p) (x := x) (2 * n) (start_inv hp)
  have hu : 0 < (iter (2 * n) (start p x)).u := hinv.1
  have hprod : 1 ≤ (iter (2 * n) (start p x)).u * (iter (2 * n) (start p x)).v :=
    Nat.mul_pos hu (Nat.pos_of_ne_zero hne)
  have hle := iter_halves (2 * n) (start p x)
  have h1 : 2 ^ (2 * n) ≤ (start p x).u * (start p x).v :=
    Nat.le_trans (by simpa using Nat.mul_le_mul_left (2 ^ (2 * n)) hprod) hle
  have h2 : (start p x).u * (start p x).v = p * x := rfl
  have h3 : p * x < 2 ^ (2 * n) := by
    have hxle : x ≤ 2 ^ n := Nat.le_of_lt hx
    have : p * x ≤ 2 ^ n * x := Nat.mul_le_mul_right _ hpn
    have h2n : (2 : Nat) ^ (2 * n) = 2 ^ n * 2 ^ n := by
      rw [Nat.two_mul, Nat.pow_add]
    have hpos : 0 < (2 : Nat) ^ n := Nat.two_pow_pos n
    calc p * x ≤ 2 ^ n * x := Nat.mul_le_mul_right _ hpn
      _ < 2 ^ n * 2 ^ n := (Nat.mul_lt_mul_left hpos).mpr hx
      _ = 2 ^ (2 * n) := h2n.symm
  omega

/-! ## Counter and register bounds

`k` counts the active rounds, so it never exceeds the number of rounds run.
The bounds `r ≤ 2 ^ k` and `s ≤ 2 ^ k`, together with the terminal value
`s = p`, give a lower bound on `k`. -/

theorem step_k (st : St) : (step st).k = st.k + 1 := by
  unfold step; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem iter_k_le : ∀ (t : Nat) (st : St), (iter t st).k ≤ st.k + t
  | 0, st => by simp [iter]
  | t + 1, st => by
    have h := iter_k_le t (round st)
    have hr : (round st).k ≤ st.k + 1 := by
      unfold round; split
      · omega
      · rw [step_k]; exact Nat.le_refl _
    rw [iter_succ]; omega

/-- `r` and `s` never exceed `2 ^ k`. -/
def Bnd (st : St) : Prop := st.r ≤ 2 ^ st.k ∧ st.s ≤ 2 ^ st.k

theorem start_bnd (p x : Nat) : Bnd (start p x) := by
  constructor <;> simp [start]

theorem step_bnd {st : St} (h : Bnd st) : Bnd (step st) := by
  obtain ⟨hr, hs⟩ := h
  have hpow : (2 : Nat) ^ (st.k + 1) = 2 ^ st.k + 2 ^ st.k := by
    rw [pow_succ_two, Nat.two_mul]
  by_cases he : st.u % 2 = 0
  · rw [step_ueven he]
    exact ⟨show st.r ≤ 2 ^ (st.k + 1) by omega, show 2 * st.s ≤ 2 ^ (st.k + 1) by omega⟩
  · by_cases hev : st.v % 2 = 0
    · rw [step_veven he hev]
      exact ⟨show 2 * st.r ≤ 2 ^ (st.k + 1) by omega, show st.s ≤ 2 ^ (st.k + 1) by omega⟩
    · by_cases hlt : st.v < st.u
      · rw [step_ubig he hev hlt]
        exact ⟨show st.r + st.s ≤ 2 ^ (st.k + 1) by omega,
               show 2 * st.s ≤ 2 ^ (st.k + 1) by omega⟩
      · rw [step_vbig he hev hlt]
        exact ⟨show 2 * st.r ≤ 2 ^ (st.k + 1) by omega,
               show st.r + st.s ≤ 2 ^ (st.k + 1) by omega⟩

theorem iter_bnd : ∀ (t : Nat) {st : St}, Bnd st → Bnd (iter t st)
  | 0, _, h => h
  | t + 1, _, h => by
    rw [iter_succ]
    refine iter_bnd t ?_
    unfold round; split
    · exact h
    · exact step_bnd h

/-! ## Terminal register state

Kaliski's algorithm stops with `v = 0`, and the invariant then reads `s u = p`.
Ruling out `u = p` needs one fact about the modulus, which this file takes as a
hypothesis: a factorisation of `p` has a factor one.  This states the required
part of primality without a library dependency.

With `u = 1` the third invariant becomes `x r + 2 ^ k ≡ 0`, which is the almost
inverse: `r` is `-x⁻¹ 2 ^ k`.  The correction that follows is a sign flip and
`k - n` modular halvings, and `k ≥ n` because `s` ends at the modulus and never
exceeds `2 ^ k`. -/

/-- Primality of `p`, stated without Mathlib. -/
def PrimeFactor (p : Nat) : Prop := ∀ a b : Nat, a * b = p → a = 1 ∨ b = 1

/-- At termination, `u` is one whenever the input is nonzero. -/
theorem u_eq_one {p x : Nat} {st : St} (hpf : PrimeFactor p)
    (hx0 : x ≠ 0) (hxp : x < p) (hv : st.v = 0) (h : Inv p x st) : st.u = 1 := by
  obtain ⟨hu, h1, h2, _⟩ := h
  have hsu : st.s * st.u = p := by rw [hv] at h1; simpa using h1
  cases hpf st.s st.u hsu with
  | inr h => exact h
  | inl hs1 =>
    exfalso
    have hup : st.u = p := by rw [hs1] at hsu; simpa using hsu
    have : Cong p (x * 1) (0 * 2 ^ st.k) := by rw [← hs1, ← hv]; exact h2
    have hx : x % p = 0 := by
      have h' : (x * 1) % p = (0 * 2 ^ st.k) % p := this
      rw [Nat.mul_one, Nat.zero_mul, Nat.zero_mod] at h'
      exact h'
    rw [Nat.mod_eq_of_lt hxp] at hx
    exact hx0 hx

/-- The almost inverse.  `r` holds `-x⁻¹ 2 ^ k` modulo `p`, in the form the
circuit can act on: `x r + 2 ^ k` is zero modulo `p`. -/
theorem almost_inverse {p x : Nat} {st : St} (hpf : PrimeFactor p) (hx0 : x ≠ 0) (hxp : x < p) (hv : st.v = 0) (h : Inv p x st) :
    (x * st.r + 2 ^ st.k) % p = 0 := by
  have hu := u_eq_one hpf hx0 hxp hv h
  have h3 := h.2.2.2
  rw [hu, Nat.one_mul] at h3
  have h' : (x * st.r + 2 ^ st.k) % p = 0 % p := h3
  rw [Nat.zero_mod] at h'
  exact h'

/-- `k` is at least the bit length of the modulus, because `s` ends at the
modulus and never exceeds `2 ^ k`. -/
theorem k_ge {p x n : Nat} {st : St} (hpf : PrimeFactor p) (hx0 : x ≠ 0) (hxp : x < p) (hv : st.v = 0) (h : Inv p x st) (hb : Bnd st)
    (hpow : 2 ^ (n - 1) < p) : n ≤ st.k := by
  have hu := u_eq_one hpf hx0 hxp hv h
  have h1 := h.2.1
  have hs : st.s = p := by rw [hv, hu] at h1; simpa using h1
  have hsk : p ≤ 2 ^ st.k := by rw [← hs]; exact hb.2
  cases Nat.lt_or_ge st.k n with
  | inr hge => exact hge
  | inl hlt =>
    exfalso
    have hkle : st.k ≤ n - 1 := by omega
    have : (2 : Nat) ^ st.k ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) hkle
    omega

/-! ## Register-width bounds

`r` and `s` fit in `n + 1` bits, which is the width the published circuit gives
them.  While `v` is positive the Euclidean invariant bounds both by the modulus,
since each of `r v` and `s u` is at most `p` and each of `v` and `u` is at least
one.  The step that drives `v` to zero can double one of them, so the bound over
the whole run is `2 p`. -/

/-- Below the modulus while the algorithm is still running. -/
theorem rs_le_p {p x : Nat} {st : St} (hv : 0 < st.v) (h : Inv p x st) :
    st.r ≤ p ∧ st.s ≤ p := by
  obtain ⟨hu, h1, _, _⟩ := h
  constructor
  · have hrv : st.r * st.v ≤ p := by omega
    have hpv : p ≤ p * st.v := by
      have := Nat.mul_le_mul_left p hv
      rwa [Nat.mul_one] at this
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hrv hpv) hv
  · have hsu : st.s * st.u ≤ p := by omega
    have hpu : p ≤ p * st.u := by
      have := Nat.mul_le_mul_left p hu
      rwa [Nat.mul_one] at this
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hsu hpu) hu

/-- At most twice the modulus at every state of the run. -/
def Wide (p : Nat) (st : St) : Prop := st.r ≤ 2 * p ∧ st.s ≤ 2 * p

theorem start_wide {p x : Nat} (hp : 0 < p) : Wide p (start p x) := by
  constructor <;> simp [start] <;> omega

theorem round_wide {p x : Nat} {st : St} (h : Inv p x st) (hw : Wide p st) :
    Wide p (round st) := by
  unfold round
  split
  · exact hw
  · next hv0 =>
    have hv : 0 < st.v := Nat.pos_of_ne_zero hv0
    obtain ⟨hr, hs⟩ := rs_le_p hv h
    by_cases he : st.u % 2 = 0
    · rw [step_ueven he]
      exact ⟨show st.r ≤ 2 * p by omega, show 2 * st.s ≤ 2 * p by omega⟩
    · by_cases hev : st.v % 2 = 0
      · rw [step_veven he hev]
        exact ⟨show 2 * st.r ≤ 2 * p by omega, show st.s ≤ 2 * p by omega⟩
      · by_cases hlt : st.v < st.u
        · rw [step_ubig he hev hlt]
          exact ⟨show st.r + st.s ≤ 2 * p by omega, show 2 * st.s ≤ 2 * p by omega⟩
        · rw [step_vbig he hev hlt]
          exact ⟨show 2 * st.r ≤ 2 * p by omega, show st.r + st.s ≤ 2 * p by omega⟩

theorem iter_wide {p x : Nat} : ∀ (t : Nat) {st : St}, Inv p x st → Wide p st →
    Wide p (iter t st)
  | 0, _, _, hw => hw
  | t + 1, _, h, hw => by
    rw [iter_succ]
    exact iter_wide t (round_inv h) (round_wide h hw)

/-! ## Operand bounds

`u` starts at the modulus and `v` below it, and every branch replaces one of
them by something no larger.  The Euclidean invariant does not give this: `r`
starts at zero, so `r v ≤ p` says nothing about `v`. -/

/-- Both operands stay at or below the modulus. -/
def Small (p : Nat) (st : St) : Prop := st.u ≤ p ∧ st.v ≤ p

theorem start_small {p x : Nat} (hx : x ≤ p) : Small p (start p x) := ⟨Nat.le_refl p, hx⟩

theorem step_small {p : Nat} {st : St} (h : Small p st) : Small p (step st) := by
  obtain ⟨hu, hv⟩ := h
  by_cases he : st.u % 2 = 0
  · rw [step_ueven he]
    exact ⟨show st.u / 2 ≤ p by omega, hv⟩
  · by_cases hev : st.v % 2 = 0
    · rw [step_veven he hev]
      exact ⟨hu, show st.v / 2 ≤ p by omega⟩
    · by_cases hlt : st.v < st.u
      · rw [step_ubig he hev hlt]
        exact ⟨show (st.u - st.v) / 2 ≤ p by omega, hv⟩
      · rw [step_vbig he hev hlt]
        exact ⟨hu, show (st.v - st.u) / 2 ≤ p by omega⟩

theorem round_small {p : Nat} {st : St} (h : Small p st) : Small p (round st) := by
  unfold round; split
  · exact h
  · exact step_small h

/-- A round advances the counter exactly when it does work. -/
theorem round_k (st : St) : (round st).k = st.k + (if st.v = 0 then 0 else 1) := by
  unfold round
  by_cases h : st.v = 0
  · rw [if_pos h, if_pos h]; omega
  · rw [if_neg h, if_neg h, step_k]

theorem iter_small {p : Nat} : ∀ (t : Nat) {st : St}, Small p st → Small p (iter t st)
  | 0, _, h => h
  | t + 1, _, h => by rw [iter_succ]; exact iter_small t (round_small h)

end VQ.Curve.PointAddition.Arithmetic.Inv
