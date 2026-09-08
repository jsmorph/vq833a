import VQ.Curve.PointAddition.Arithmetic.Inv.Wires
import VQ.Curve.PointAddition.Arithmetic.Inv.RoundOK

/-!
# Round chain

`2 n` rounds, one after another.  The state carried through is the four
registers holding the arithmetic's state, the working scratch clear, and the
kept bits of the rounds not yet run still clear.

Each round needs its own two kept wires clear, and `roundGates_touches` is what
says the earlier rounds left them so.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The first `T` rounds. -/
def chainT (n : Nat) : Nat → List RGate
  | 0 => []
  | T + 1 => chainT n T ++ roundGates n T

/-- The registers hold `st` and the working scratch is clear. -/
def Rd (n : Nat) (st : St) (I : Nat) : Prop :=
  readField I (aU n) (bw n) = st.u ∧ readField I (aV n) (bw n) = st.v ∧
    readField I (aR n) (bw n) = st.r ∧ readField I (aS n) (bw n) = st.s ∧
    readField I (aTU n) (bw n) = 0 ∧ readField I (aTR n) (bw n) = 0 ∧
    readField I (aA n) 1 = 0 ∧ readField I (aT n) 1 = 0 ∧
    readField I (aGt n) 1 = 0 ∧ readField I (aC n) 1 = 0

/-- The kept wires of the rounds already run hold what those rounds decided. -/
def Kept (n : Nat) (st0 : St) (T : Nat) (I : Nat) : Prop :=
  ∀ j, j < T → readField I (aM n + j) 1 = mBit (iter j st0) ∧
    readField I (aZ n + j) 1 = zBit (iter j st0)

/-- The kept wires of rounds `T` and above are still clear. -/
def Fresh (n : Nat) (T : Nat) (I : Nat) : Prop :=
  ∀ j, T ≤ j → j < 2 * n → readField I (aM n + j) 1 = 0 ∧ readField I (aZ n + j) 1 = 0

/-- A round leaves every other round's kept wires alone. -/
theorem round_fresh {n t j : Nat} (ht : t < 2 * n) (hj : j < 2 * n) (hne : j ≠ t) (I : Nat) :
    readField (actGates (roundGates n t) I) (aM n + j) 1 = readField I (aM n + j) 1 ∧
      readField (actGates (roundGates n t) I) (aZ n + j) 1 = readField I (aZ n + j) 1 := by
  have hM : ∀ g ∈ roundGates n t, ∀ q ∈ g.wires, q < aM n + j ∨ aM n + j + 1 ≤ q := by
    intro g hg q hq
    have := roundGates_touches ht g hg q hq
    unfold Touches at this
    simp only [aM, aZ, aC, aGt, aT, aA, aTR, aTU, aS, aR, aV, aU, bw] at *
    omega
  have hZ : ∀ g ∈ roundGates n t, ∀ q ∈ g.wires, q < aZ n + j ∨ aZ n + j + 1 ≤ q := by
    intro g hg q hq
    have := roundGates_touches ht g hg q hq
    unfold Touches at this
    simp only [aM, aZ, aC, aGt, aT, aA, aTR, aTU, aS, aR, aV, aU, bw] at *
    omega
  exact ⟨readField_actGates_outside hM, readField_actGates_outside hZ⟩

/-- The register values fit their registers. -/
theorem fits {n p : Nat} {st : St} (hsm : Small p st) (hwd : Wide p st) (hpn : p < 2 ^ n) :
    st.u % 2 ^ (bw n) = st.u ∧ st.v % 2 ^ (bw n) = st.v ∧
      st.r % 2 ^ (bw n) = st.r ∧ st.s % 2 ^ (bw n) = st.s := by
  obtain ⟨hu, hv⟩ := hsm
  obtain ⟨hr, hs⟩ := hwd
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

/-- One round advances the carried state. -/
theorem chain_step {n T p x : Nat} {st : St} (hn : 0 < n) (hp : p % 2 = 1) (hpn : p < 2 ^ n)
    (hT : T < 2 * n) (I : Nat)
    (hinv : Inv p x st) (hsm : Small p st) (hwd : Wide p st)
    (hrd : Rd n st I) (hfr : Fresh n T I) :
    Rd n (round st) (actGates (roundGates n T) I) ∧
      Fresh n (T + 1) (actGates (roundGates n T) I) ∧
      readField (actGates (roundGates n T) I) (aM n + T) 1 = mBit st ∧
      readField (actGates (roundGates n T) I) (aZ n + T) 1 = zBit st := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrd
  obtain ⟨hm0, hz0⟩ := hfr T (Nat.le_refl T) hT
  -- The input is the abstraction at this round.
  have hI : start1 n T I st.u st.v st.r st.s = I := by
    unfold start1
    exact ks_of_reads h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hm0 hz0
  have hact : actGates (roundGates n T) I
      = ks n T I (round st).u (round st).v (round st).r (round st).s 0 0 0 0 0 0
          (mBit st) (zBit st) := by
    have h := roundGates_inv (I := I) hn hT hp hpn hinv hsm hwd
    rw [hI] at h
    exact h
  obtain ⟨fu, fv, fr, fs⟩ :=
    fits (n := n) (p := p) (round_small hsm) (round_wide (x := x) hinv hwd) hpn
  have hmlt : mBit st < 2 := by
    unfold mBit
    by_cases h1 : st.u % 2 = 0
    · rw [if_pos h1]; omega
    · rw [if_neg h1]
      by_cases h2 : st.v % 2 = 0
      · rw [if_pos h2]; omega
      · rw [if_neg h2]
        by_cases h3 : st.v < st.u
        · rw [if_pos h3]; omega
        · rw [if_neg h3]; omega
  have hzlt : zBit st < 2 := by
    unfold zBit
    by_cases h : st.v = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hact]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ks_read_U hT]; exact fu
    · rw [ks_read_V hT]; exact fv
    · rw [ks_read_R hT]; exact fr
    · rw [ks_read_S hT]; exact fs
    · rw [ks_read_TU hT, Nat.zero_mod]
    · rw [ks_read_TR hT, Nat.zero_mod]
    · rw [ks_read_A hT]
    · rw [ks_read_T hT]
    · rw [ks_read_Gt hT]
    · rw [ks_read_C hT]
  · intro j hj hjn
    obtain ⟨em, ez⟩ := round_fresh hT hjn (by omega) I
    obtain ⟨gm, gz⟩ := hfr j (by omega) hjn
    exact ⟨by rw [em, gm], by rw [ez, gz]⟩
  · rw [hact, ks_read_M hT, Nat.pow_one]; omega
  · rw [hact, ks_read_Z hT, Nat.pow_one]; omega

/-- The chain runs the arithmetic.  After `T` rounds the registers hold
`iter T`, the working scratch is clear, and the rounds not yet run still have
their kept wires clear. -/
theorem chainT_act {n p x : Nat} (hn : 0 < n) (hp : p % 2 = 1) (hpn : p < 2 ^ n)
    (hx : x ≤ p) (hp0 : 0 < p) :
    ∀ (T : Nat), T ≤ 2 * n → ∀ I, Rd n (start p x) I → Fresh n 0 I →
      Rd n (iter T (start p x)) (actGates (chainT n T) I) ∧
        Fresh n T (actGates (chainT n T) I) ∧
        Kept n (start p x) T (actGates (chainT n T) I) := by
  intro T
  induction T with
  | zero => intro _ I hrd hfr; exact ⟨hrd, hfr, fun j hj => absurd hj (by omega)⟩
  | succ T ih =>
    intro hT I hrd hfr
    obtain ⟨hrd', hfr', hkp'⟩ := ih (by omega) I hrd hfr
    have hinv := iter_inv (p := p) (x := x) T (start_inv hp0)
    have hsm := iter_small (p := p) T (start_small hx)
    have hwd := iter_wide (p := p) (x := x) T (start_inv hp0) (start_wide (x := x) hp0)
    have hstep := chain_step (T := T) (st := iter T (start p x)) hn hp hpn (by omega)
      (actGates (chainT n T) I) hinv hsm hwd hrd' hfr'
    rw [show chainT n (T + 1) = chainT n T ++ roundGates n T from rfl, actGates_append]
    rw [iter_succ' T (start p x)]
    obtain ⟨hA, hB, hC, hD⟩ := hstep
    refine ⟨hA, hB, ?_⟩
    intro j hj
    by_cases hjT : j = T
    · subst hjT; exact ⟨hC, hD⟩
    · obtain ⟨em, ez⟩ := round_fresh (n := n) (t := T) (j := j) (by omega) (by omega)
        hjT (actGates (chainT n T) I)
      obtain ⟨gm, gz⟩ := hkp' j (by omega)
      exact ⟨by rw [em, gm], by rw [ez, gz]⟩

/-! ## Chain and correction controls

A round touches nothing at or above `aH`, so the halving controls come out of
the chain as they went in. -/

theorem chainT_wires {n : Nat} : ∀ (T : Nat), T ≤ 2 * n →
    ∀ g ∈ chainT n T, ∀ q ∈ g.wires, aU n ≤ q ∧ q < aH n := by
  intro T
  induction T with
  | zero => intro _ g hg; simp [chainT] at hg
  | succ T ih =>
    intro hT g hg q hq
    have hg2 : g ∈ chainT n T ++ roundGates n T := hg
    rw [List.mem_append] at hg2
    cases hg2 with
    | inl h => exact ih (by omega) g h q hq
    | inr h =>
      have := roundGates_touches (n := n) (t := T) (by omega) g h q hq
      unfold Touches at this
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
      omega

/-- The halving controls survive the chain. -/
theorem chainT_keeps_H {n T j I : Nat} (hT : T ≤ 2 * n) :
    readField (actGates (chainT n T) I) (aH n + j) 1 = readField I (aH n + j) 1 :=
  readField_actGates_outside (fun g hg q hq => Or.inl (by
    have := chainT_wires T hT g hg q hq
    omega))

/-- No round touches the nonzero wire. -/
theorem chainT_wires_nz {n : Nat} : ∀ (T : Nat), T ≤ 2 * n →
    ∀ g ∈ chainT n T, ∀ q ∈ g.wires, q ≠ aNZ n := by
  intro T
  induction T with
  | zero => intro _ g hg; simp [chainT] at hg
  | succ T ih =>
    intro hT g hg q hq
    have hg2 : g ∈ chainT n T ++ roundGates n T := hg
    rw [List.mem_append] at hg2
    cases hg2 with
    | inl h => exact ih (by omega) g h q hq
    | inr h =>
      have := roundGates_touches (n := n) (t := T) (by omega) g h q hq
      unfold Touches at this
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
      omega

/-- The nonzero wire survives the chain. -/
theorem chainT_keeps_NZ {n T I : Nat} (hT : T ≤ 2 * n) :
    readField (actGates (chainT n T) I) (aNZ n) 1 = readField I (aNZ n) 1 :=
  readField_actGates_outside (fun g hg q hq => by
    have := chainT_wires_nz T hT g hg q hq
    omega)

/-- The chain is well formed. -/
theorem chainT_wf {n : Nat} (hn : 0 < n) : ∀ (T : Nat), T ≤ 2 * n →
    (chainT n T).all (RGate.wellFormed (totalWidth n)) = true := by
  intro T
  induction T with
  | zero => intro _; simp [chainT]
  | succ T ih =>
    intro hT
    show (chainT n T ++ roundGates n T).all _ = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨ih (by omega), roundGates_wf hn (by omega)⟩

end VQ.Curve.PointAddition.Arithmetic.Inv
