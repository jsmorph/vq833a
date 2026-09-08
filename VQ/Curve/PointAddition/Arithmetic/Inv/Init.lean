import VQ.Curve.PointAddition.Arithmetic.Inv.Fix
import VQ.Curve.Spec

/-!
# Register initialization

The claim's layout is `[n, n, ws]`: the input, the output, and the workspace.
The chain starts from `u = p`, `v = x`, `r = 0`, and `s = 1`, so the forward pass
begins by copying the input into `v` and loading two classical constants.

The copy preserves the input field as required by the claim.  The reverse pass
clears `v`.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- Copy the input into `v`, load the modulus into `u` and one into `s`, and
record whether the input is nonzero.

The record is the comparison against a loaded one, the same device the rounds
use: `v < 1` is `v = 0`, and one negation turns it into `v ≠ 0`. -/
def initGates (n : Nat) : List RGate :=
  copyField 0 (aV n) n
    ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
    ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1

/-- The whole forward pass. -/
def fwdGates (n : Nat) : List RGate :=
  initGates n ++ chainT n (2 * n) ++ fixGates n

/-- The circuit's gates: the forward pass, a copy of the answer into the
output field under the nonzero bit, and the forward pass reversed.

The copy is controlled because the specification sends zero to zero, and at
input zero the chain never runs, so the correction has nothing right to say. -/
def gen (n : Nat) : RCircuit :=
  { width := totalWidth n
    gates := fwdGates n ++ copyC (aNZ n) (aTU n) n n ++ (fwdGates n).reverse }

/-! ## Claim input state

Every workspace register reads zero when the workspace field does, and the
initialisation turns that into the chain's starting state. -/

/-- Each register of a clear workspace is clear. -/
theorem ws_zero {n I : Nat} (hz : readField I (2 * n) (wsWidth n) = 0) :
    readField I (aU n) (bw n) = 0 ∧ readField I (aV n) (bw n) = 0 ∧
      readField I (aR n) (bw n) = 0 ∧ readField I (aS n) (bw n) = 0 ∧
      readField I (aTU n) (bw n) = 0 ∧ readField I (aTR n) (bw n) = 0 ∧
      readField I (aA n) 1 = 0 ∧ readField I (aT n) 1 = 0 ∧
      readField I (aGt n) 1 = 0 ∧ readField I (aC n) 1 = 0 ∧
      readField I (aNZ n) 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine readField_sub_zero (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, wsWidth, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, wsWidth, totalWidth]; omega) hz

/-- Each kept wire of a clear workspace is clear. -/
theorem ws_zero_kept {n I j : Nat} (hj : j < 2 * n)
    (hz : readField I (2 * n) (wsWidth n) = 0) :
    readField I (aM n + j) 1 = 0 ∧ readField I (aZ n + j) 1 = 0 ∧
      readField I (aH n) 1 = 0 ∧ readField I (aG n) 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    refine readField_sub_zero (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw,
        wsWidth, totalWidth] at *
      omega) (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw,
        wsWidth, totalWidth] at *
      omega) hz

set_option maxHeartbeats 2000000 in
/-- The initialisation.  The input goes into `v`, the modulus into `u`, one
into `s`, and the nonzero bit into its own wire. -/
theorem initGates_act {n a I : Nat} (hn : 0 < n) (ha : a < 2 ^ n)
    (h0 : readField I 0 n = a) (h2 : readField I (2 * n) (wsWidth n) = 0) :
    actGates (initGates n) I
      = cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 1 0 0 0 0 0 0 := by
  obtain ⟨zu, zv, zr, zs, ztu, ztr, za, zbo, zgt, zcy, znz⟩ := ws_zero h2
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  have hone : (1 : Nat) < 2 ^ (bw n) := by
    have := Nat.two_pow_pos n; omega
  have hared : a % 2 ^ (bw n) = a := Nat.mod_eq_of_lt (by omega)
  -- The state is the abstraction with every register clear.
  have hI : cs n I 0 0 0 0 0 0 0 0 0 0 = I :=
    cs_of_reads zu zv zr zs ztu ztr za zbo zgt zcy
  -- Copy the input into `v`.
  have e1 : actGates (copyField 0 (aV n) n) I = cs n I 0 a 0 0 0 0 0 0 0 0 := by
    have hzn : readField I (aV n) n = 0 := readField_sub_zero (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) zv
    have hw : writeField I (aV n) n a = writeField I (aV n) (bw n) a :=
      write_widen (by simp only [bw]; omega) (by omega) (by rw [zv]; exact Nat.two_pow_pos _)
    have hgoal : writeField (cs n I 0 0 0 0 0 0 0 0 0 0) (aV n) (bw n) a
        = cs n I 0 a 0 0 0 0 0 0 0 0 := cs_write_V
    rw [hI] at hgoal
    rw [actGates_copyField (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), h0, hzn, Nat.zero_xor, hw, hgoal]
  -- The zero test: the or of `v`'s bits, straight into the nonzero wire.
  have e5 : actGates (nzTest (aV n) (aTR n) (aNZ n) (bw n)) (cs n I 0 a 0 0 0 0 0 0 0 0)
      = cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) 0 a 0 0 0 0 0 0 0 0 := by
    have hsc : readField (cs n I 0 a 0 0 0 0 0 0 0 0) (aTR n) (bw n) = 0 := by
      rw [cs_read_TR, Nat.zero_mod]
    have hsrc : readField (cs n I 0 a 0 0 0 0 0 0 0 0) (aV n) (bw n) = a := by
      rw [cs_read_V]; exact hared
    have hout : readField (cs n I 0 a 0 0 0 0 0 0 0 0) (aNZ n) 1 = 0 := by
      rw [cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
      exact znz
    rw [nzTest_act (Wd := totalWidth n) (by simp only [bw]; omega)
        (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) _ hsc, hsrc, ← readField_one, hout,
      cs_write_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
    refine congrArg (fun q => cs n (writeField I (aNZ n) 1 q) 0 a 0 0 0 0 0 0 0 0) ?_
    by_cases hz0 : a = 0
    · rw [if_pos hz0]
    · rw [if_neg hz0]
  -- Load the two constants.
  have e6 : actGates (loadX (aU n) (bw n) modulus)
      (cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) 0 a 0 0 0 0 0 0 0 0)
      = cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 0 0 0 0 0 0 0 := by
    rw [loadX_act, cs_read_U, Nat.zero_mod, Nat.zero_xor, cs_write_U]
  have e7 : actGates (loadX (aS n) (bw n) 1)
      (cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 0 0 0 0 0 0 0)
      = cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 1 0 0 0 0 0 0 := by
    rw [loadX_act, cs_read_S, Nat.zero_mod, Nat.zero_xor, cs_write_S]
  show actGates (copyField 0 (aV n) n ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
      ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1) _ = _
  rw [actGates_append, actGates_append, actGates_append, e1, e5, e6, e7]

/-! ## Forward pass

Initialization, chain, and correction compose through field-read equations
across their different state abstractions. -/

/-- The modulus is odd and fits. -/
theorem modulus_odd : modulus % 2 = 1 := by decide

theorem modulus_lt {n : Nat} (hp : VQ.Curve.p ≤ 2 ^ n) : modulus < 2 ^ n := by
  have hle : modulus ≤ 2 ^ n := hp
  have hbig : 4 < modulus := by decide
  have hn : 2 ≤ n := by
    cases Nat.lt_or_ge n 2 with
    | inr h => exact h
    | inl h =>
      exfalso
      have h4 : (2 : Nat) ^ n ≤ 4 := by
        have : (2 : Nat) ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have heven : (2 : Nat) ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
  have hodd := modulus_odd
  omega

/-- The chain's starting state, read out of the initialisation's output. -/
theorem init_to_chain {n a I : Nat} (hn : 0 < n) (hp : VQ.Curve.p ≤ 2 ^ n)
    (ha : a < 2 ^ n) (h2 : readField I (2 * n) (wsWidth n) = 0) :
    Rd n (start modulus a)
        (cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 1 0 0 0 0 0 0)
      ∧ Fresh n 0
        (cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 1 0 0 0 0 0 0) := by
  have hml := modulus_lt hp
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  have hone : (1 : Nat) % 2 ^ (bw n) = 1 := Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [cs_read_U]; exact Nat.mod_eq_of_lt (by omega)
  · rw [cs_read_V]; exact Nat.mod_eq_of_lt (by omega)
  · rw [cs_read_R]; exact Nat.zero_mod _
  · rw [cs_read_S]; exact hone
  · rw [cs_read_TU]; exact Nat.zero_mod _
  · rw [cs_read_TR]; exact Nat.zero_mod _
  · rw [cs_read_A]
  · rw [cs_read_T]
  · rw [cs_read_Gt]
  · rw [cs_read_C]
  · intro j _ hj
    obtain ⟨km, kz, _⟩ := ws_zero_kept hj h2
    refine ⟨?_, ?_⟩
    · rw [cs_read_out (by
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
        omega), readField_writeField_of_disjoint (by
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
        omega)]
      exact km
    · rw [cs_read_out (by
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
        omega), readField_writeField_of_disjoint (by
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
        omega)]
      exact kz

/-! ## Terminal chain state

Everything the correction needs about the state after `2 n` rounds. -/

theorem chain_final {n p x : Nat} (hn : 0 < n) (hp : p % 2 = 1) (hpn : p < 2 ^ n)
    (hp0 : 0 < p) (hx0 : x ≠ 0) (hxp : x < p) (hpf : PrimeFactor p) :
    (iter (2 * n) (start p x)).v = 0 ∧ (iter (2 * n) (start p x)).u = 1 ∧
      (iter (2 * n) (start p x)).s = p ∧
      (x * (iter (2 * n) (start p x)).r + 2 ^ (iter (2 * n) (start p x)).k) % p = 0 ∧
      (iter (2 * n) (start p x)).r ≤ 2 * p := by
  have hinv := iter_inv (p := p) (x := x) (2 * n) (start_inv hp0)
  have hwd := iter_wide (p := p) (x := x) (2 * n) (start_inv hp0) (start_wide (x := x) hp0)
  have hv : (iter (2 * n) (start p x)).v = 0 :=
    iter_v_zero hp0 (Nat.le_of_lt hpn) (by omega)
  have hu : (iter (2 * n) (start p x)).u = 1 := u_eq_one hpf hx0 hxp hv hinv
  have hs : (iter (2 * n) (start p x)).s = p := by
    have h1 := hinv.2.1
    rw [hv, hu] at h1
    simpa using h1
  exact ⟨hv, hu, hs, almost_inverse hpf hx0 hxp hv hinv, hwd.1⟩

/-! ## Correction value

The reduction, the negation, and the halvings composed at the arithmetic level:
what the scratch register ends holding, as a function of the chain's output. -/

/-- The almost inverse is not a multiple of the modulus: if it were, the
congruence would make the modulus divide a power of two. -/
theorem r_mod_ne {p x r k : Nat} (hp : p % 2 = 1) (hp1 : 1 < p)
    (halm : (x * r + 2 ^ k) % p = 0) : r % p ≠ 0 := by
  intro hr0
  have hxr : (x * r) % p = 0 := by
    rw [Nat.mul_mod, hr0, Nat.mul_zero, Nat.zero_mod]
  have hpow : (2 ^ k) % p = 0 := by
    have := halm
    rw [Nat.add_mod, hxr, Nat.zero_add, Nat.mod_mod_of_dvd _ (Nat.dvd_refl p)] at this
    exact this
  -- An odd modulus above one divides no power of two.
  have hdvd : ∀ j : Nat, (2 ^ j) % p ≠ 0 := by
    intro j
    induction j with
    | zero => rw [Nat.pow_zero, Nat.mod_eq_of_lt hp1]; omega
    | succ j ih =>
      intro h
      have hd : p ∣ 2 ^ (j + 1) := Nat.dvd_of_mod_eq_zero h
      have hd2 : p ∣ 2 * 2 ^ j := by
        have he : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
        rwa [he] at hd
      obtain ⟨c, hc⟩ := dvd_of_two_mul hp hd2
      exact ih (by rw [hc]; exact Nat.mul_mod_right p c)
  exact hdvd k hpow

/-- The reduction's result is the almost inverse taken modulo the modulus. -/
theorem reduce_val {n p r : Nat} (hp0 : 0 < p) (hr : r ≤ 2 * p) (hw : 2 * p < 2 ^ (bw n))
    (hne : r % p ≠ 0) :
    (r + (2 ^ (bw n) - (if r < p then 0 else p))) % 2 ^ (bw n) = r % p := by
  have hpow := Nat.two_pow_pos (bw n)
  by_cases hlt : r < p
  · rw [if_pos hlt, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt]
    have h2p : r ≠ 2 * p := by
      intro h
      apply hne
      rw [h, Nat.mul_comm]
      exact Nat.mul_mod_right p 2
    have he : r + (2 ^ (bw n) - p) = 2 ^ (bw n) + (r - p) := by omega
    have hrm : r % p = r - p := by
      have hd : r - p < p := by omega
      have : r = p + (r - p) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
      omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hrm]

/-! ## Inversion correctness

`fix_inverts` gives a value whose product with the input is one.  The
specification names `VQ.Curve.inv`, and an inverse below the modulus is
unique. -/

/-- The value the correction leaves is `VQ.Curve.inv`. -/
theorem fix_is_inv {x r k : Nat} (hlaw : VQ.Curve.InverseLaw)
    (hp : modulus % 2 = 1) (hp1 : 1 < modulus)
    (halm : (x * r + 2 ^ k) % modulus = 0) (hr : r < modulus) (hr0 : 0 < r)
    (hx : x < modulus) (hx0 : x ≠ 0) :
    mhalves modulus k (modulus - r) = VQ.Curve.inv x := by
  have hone : (x * mhalves modulus k (modulus - r)) % modulus = 1 % modulus :=
    fix_inverts hp (by omega) halm hr hr0
  have hlt : mhalves modulus k (modulus - r) < modulus :=
    mhalves_lt hp _ _ (by omega)
  have hinvlt : VQ.Curve.inv x < modulus := VQ.Curve.inv_lt x
  have hlawx : VQ.Curve.mul (VQ.Curve.inv x) x = 1 := hlaw x hx hx0
  have hmul : (x * VQ.Curve.inv x) % modulus = 1 % modulus := by
    have : (VQ.Curve.inv x * x) % VQ.Curve.p = 1 := hlawx
    rw [Nat.mul_comm] at this
    show (x * VQ.Curve.inv x) % VQ.Curve.p = 1 % VQ.Curve.p
    rw [this, Nat.mod_eq_of_lt (by decide)]
  exact inv_unique hlt hinvlt hone hmul

/-! ## Forward-pass circuit

The forward pass initializes the registers, runs the chain, reduces, negates,
and halves.  Field-read equations connect the state abstractions used by
adjacent phases. -/

set_option maxHeartbeats 2000000 in
/-- The chain's output, in the correction's abstraction. -/
theorem chain_out {n a I : Nat} (hn : 0 < n) (hp : VQ.Curve.p ≤ 2 ^ n)
    (hpf : PrimeFactor modulus) (ha : a < modulus) (ha0 : a ≠ 0)
    (h0 : readField I 0 n = a) (h2 : readField I (2 * n) (wsWidth n) = 0) :
    ∃ J, actGates (initGates n ++ chainT n (2 * n)) I
          = cs n J 1 0 (iter (2 * n) (start modulus a)).r modulus 0 0 0 0 0 0
        ∧ (∀ j, j < 2 * n → readField J (aZ n + j) 1 = zBit (iter j (start modulus a)))
        ∧ readField J (aH n) 1 = 0 ∧ readField J (aG n) 1 = 0 := by
  have hml := modulus_lt hp
  have hpo := modulus_odd
  have hp0 : 0 < modulus := by decide
  have hain : a < 2 ^ n := by omega
  have hinit := initGates_act hn hain h0 h2
  obtain ⟨hrd0, hfr0⟩ := init_to_chain hn hp hain h2
  have hchain := chainT_act hn hpo hml (Nat.le_of_lt ha) hp0 (2 * n) (Nat.le_refl _) _ hrd0 hfr0
  obtain ⟨hrd, hfr, hkp⟩ := hchain
  obtain ⟨hv, hu, hs, halm, hr2p⟩ := chain_final hn hpo hml hp0 ha0 ha hpf
  refine ⟨actGates (chainT n (2 * n))
      (cs n (writeField I (aNZ n) 1 (if a = 0 then 0 else 1)) modulus a 0 1 0 0 0 0 0 0),
    ?_, ?_, ?_⟩
  · rw [actGates_append, hinit]
    have hcs := cs_of_reads hrd.1 hrd.2.1 hrd.2.2.1 hrd.2.2.2.1 hrd.2.2.2.2.1
      hrd.2.2.2.2.2.1 hrd.2.2.2.2.2.2.1 hrd.2.2.2.2.2.2.2.1
      hrd.2.2.2.2.2.2.2.2.1 hrd.2.2.2.2.2.2.2.2.2
    rw [hu, hv, hs] at hcs
    exact hcs.symm
  · intro j hj
    exact (hkp j hj).2
  refine ⟨?_, ?_⟩
  · show readField (actGates (chainT n (2 * n)) _) (aH n + 0) 1 = 0
    rw [chainT_keeps_H (Nat.le_refl _) (j := 0)]
    have := ws_zero_kept (j := 0) (by omega) h2
    rw [cs_read_out (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega), readField_writeField_of_disjoint (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega)]
    exact this.2.2.1
  · show readField (actGates (chainT n (2 * n)) _) (aH n + 1) 1 = 0
    rw [chainT_keeps_H (Nat.le_refl _) (j := 1)]
    have := ws_zero_kept (j := 0) (by omega) h2
    rw [cs_read_out (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega), readField_writeField_of_disjoint (by
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega)]
    exact this.2.2.2

set_option maxHeartbeats 2000000 in
/-- The forward pass leaves the inverse in the scratch register. -/
theorem fwd_value {n a I : Nat} (hn : 0 < n) (hp : VQ.Curve.p ≤ 2 ^ n)
    (hlaw : VQ.Curve.InverseLaw) (hpf : PrimeFactor modulus)
    (ha : a < modulus) (ha0 : a ≠ 0)
    (h0 : readField I 0 n = a) (h2 : readField I (2 * n) (wsWidth n) = 0) :
    readField (actGates (fwdGates n) I) (aTU n) (bw n) = VQ.Curve.inv a := by
  have hml := modulus_lt hp
  have hpo := modulus_odd
  have hp0 : 0 < modulus := by decide
  have hp1 : 1 < modulus := by decide
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  obtain ⟨hv, hu, hs, halm, hr2p⟩ := chain_final hn hpo hml hp0 ha0 ha hpf
  obtain ⟨J, hJ, hJz, hJh, hJg⟩ := chain_out hn hp hpf ha ha0 h0 h2
  -- The reduction.
  have hrne : (iter (2 * n) (start modulus a)).r % modulus ≠ 0 := r_mod_ne hpo hp1 halm
  have hred := fixReduce_act (n := n) (I := J) (u := 1) (v := 0)
    (r := (iter (2 * n) (start modulus a)).r) (s := modulus) (a := 0) (bo := 0) (m := 0)
    hn rfl (by omega) (by omega) hml (Or.inr (by omega)) (by omega) (by omega)
  rw [reduce_val (n := n) hp0 hr2p (by omega) hrne] at hred
  -- The negation.
  have hrlt : (iter (2 * n) (start modulus a)).r % modulus < modulus := Nat.mod_lt _ hp0
  have hneg := fixNegate_act (n := n) (I := J) (v := 0)
    (r := (iter (2 * n) (start modulus a)).r % modulus) (s := modulus) (a := 0) (bo := 0)
    (gt := if (iter (2 * n) (start modulus a)).r < modulus then 0 else 1)
    rfl (by omega) (by omega) (Nat.mod_eq_of_lt (by omega))
  have hsub : (modulus + (2 ^ (bw n) - (iter (2 * n) (start modulus a)).r % modulus)) % 2 ^ (bw n)
      = modulus - (iter (2 * n) (start modulus a)).r % modulus :=
    sub_exact (by omega) (by omega)
  rw [hsub] at hneg
  -- The halvings.
  have htu0 : modulus - (iter (2 * n) (start modulus a)).r % modulus < modulus := by omega
  have hK := fixHalves_act (n := n) (p := modulus) (x := a) hn rfl hpo hml
    (2 * n) (Nat.le_refl _) _ 1 0 ((iter (2 * n) (start modulus a)).r % modulus) 0 0
    (if (iter (2 * n) (start modulus a)).r < modulus then 0 else 1)
    (modulus - (iter (2 * n) (start modulus a)).r % modulus)
    (by omega) (by omega) (by omega) htu0 hJz hJh hJg
  -- Thread the five phases.
  have hall : actGates (fwdGates n) I
      = cs n J 1 0 ((iter (2 * n) (start modulus a)).r % modulus) modulus
          (mhalves modulus (iter (2 * n) (start modulus a)).k
            (modulus - (iter (2 * n) (start modulus a)).r % modulus)) 0 0 0
          (if (iter (2 * n) (start modulus a)).r < modulus then 0 else 1) 0 := by
    show actGates (initGates n ++ chainT n (2 * n) ++ fixGates n) I = _
    rw [actGates_append]
    show actGates (fixReduce n ++ fixNegate n ++ fixHalves n (2 * n))
      (actGates (initGates n ++ chainT n (2 * n)) I) = _
    rw [hJ, actGates_append, actGates_append, hred, hneg, hK]
  rw [hall, cs_read_TU]
  -- The value is the inverse.
  have hval := fix_is_inv (x := a) (r := (iter (2 * n) (start modulus a)).r % modulus)
    (k := (iter (2 * n) (start modulus a)).k) hlaw hpo hp1
    (by
      have := halm
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_refl modulus),
        ← Nat.mul_mod, ← Nat.add_mod]
      exact this)
    hrlt (by omega) ha ha0
  rw [hval]
  exact Nat.mod_eq_of_lt (by have := VQ.Curve.inv_lt a; omega)

/-! ## Forward-pass wire bounds

Everything the forward pass touches is the input field or lies at or above the
workspace.  The output field, between the two, is what the copy-out writes and
what the uncomputation must not disturb. -/

theorem initGates_wires {n : Nat} : ∀ g ∈ initGates n, ∀ q ∈ g.wires,
    q < n ∨ 2 * n ≤ q := by
  have hw : 0 < bw n := by simp only [bw]; omega
  intro g hg q hq
  have hg2 : g ∈ copyField 0 (aV n) n ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
      ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1 := hg
  rw [List.mem_append, List.mem_append, List.mem_append] at hg2
  rcases hg2 with ((h2 | h2) | h2) | h2
  · have := copyField_mem h2
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    rcases this with ⟨k, hk, rfl⟩
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    omega
  · have := nzTest_wires (aV n) (aTR n) (aNZ n) (bw n) (by simp only [bw]; omega) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega
  · have := loadX_wires (bw n) (aU n) modulus g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega
  · have := loadX_wires (bw n) (aS n) 1 g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega

theorem fwdGates_wires {n : Nat} : ∀ g ∈ fwdGates n, ∀ q ∈ g.wires,
    q < n ∨ 2 * n ≤ q := by
  intro g hg q hq
  have hg2 : g ∈ initGates n ++ chainT n (2 * n) ++ fixGates n := hg
  rw [List.mem_append, List.mem_append] at hg2
  cases hg2 with
  | inr h =>
    have hw := fixGates_wires g h q hq
    rcases hw with h' | h' | h' | h'
    · right
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega
    · right
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega
    · right
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega
    · obtain ⟨j, hj, hq'⟩ := h'
      right
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
      omega
  | inl h1 =>
    cases h1 with
    | inl h => exact initGates_wires g h q hq
    | inr h =>
      right
      have := chainT_wires (2 * n) (Nat.le_refl _) g h q hq
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
      omega

/-! ## Forward-pass well-formedness -/

theorem initGates_wf {n : Nat} (hn : 0 < n) :
    (initGates n).all (RGate.wellFormed (totalWidth n)) = true := by
  have hw : 0 < bw n := by simp only [bw]; omega
  show (copyField 0 (aV n) n ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
    ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1).all _ = true
  rw [List.all_append, List.all_append, List.all_append, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨copyField_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega),
    nzTest_wf (aV n) (aTR n) (aNZ n) (bw n) (totalWidth n) (by simp only [bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    loadX_wf (bw n) (aU n) modulus _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    loadX_wf (bw n) (aS n) 1 _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩

theorem fwdGates_wf {n : Nat} (hn : 0 < n) :
    (fwdGates n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (initGates n ++ chainT n (2 * n) ++ fixGates n).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨initGates_wf hn, chainT_wf hn (2 * n) (Nat.le_refl _)⟩, fixGates_wf hn⟩

/-! ## Circuit composition

The forward pass, a copy of the answer into the output field under the nonzero
bit, and the forward pass reversed.  `actGates_compute_use_uncompute` is what
makes the reverse undo the first while the copy survives, and it needs the
forward pass to leave the output field alone, which `fwdGates_wires` gives. -/

/-- The forward pass avoids the output field. -/
theorem fwdGates_out {n : Nat} : ∀ g ∈ fwdGates n, ∀ q ∈ g.wires, q < n ∨ n + n ≤ q := by
  intro g hg q hq
  have := fwdGates_wires g hg q hq
  omega

/-- The circuit writes the inverse into the output field and restores
everything else. -/
theorem gen_act {n a I : Nat} (hn : 0 < n) (hp : VQ.Curve.p ≤ 2 ^ n)
    (hlaw : VQ.Curve.InverseLaw) (hpf : PrimeFactor modulus)
    (ha : a < modulus)
    (h0 : readField I 0 n = a) (h1 : readField I n n = 0)
    (h2 : readField I (2 * n) (wsWidth n) = 0) :
    act (gen n) I = writeField I n n (VQ.Curve.inv a) := by
  have hcp : ∀ j, actGates (copyC (aNZ n) (aTU n) n n) j
      = writeField j n n ((readField j n n) ^^^ (bv j (aNZ n) * readField j (aTU n) n)) :=
    fun j => copyC_act n (aTU n) n j
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
  have hmain := actGates_compute_use_uncompute (gs := fwdGates n)
    (cp := copyC (aNZ n) (aTU n) n n) (w := totalWidth n) (off := n) (len := n)
    (fwdGates_wf hn) fwdGates_out hcp I
  show actGates (fwdGates n ++ copyC (aNZ n) (aTU n) n n ++ (fwdGates n).reverse) I = _
  rw [hmain]
  -- The output field was clear, so the copy writes what the control admits.
  have hout : readField (actGates (fwdGates n) I) n n = 0 := by
    rw [readField_actGates_outside (fun g hg q hq => fwdGates_out g hg q hq)]
    exact h1
  rw [hout, Nat.zero_xor]
  -- The control holds the input's nonzero bit, which the chain and the
  -- correction both leave alone.
  have hnzval : bv (actGates (fwdGates n) I) (aNZ n) = (if a = 0 then 0 else 1) := by
    rw [← readField_one]
    show readField (actGates (initGates n ++ chainT n (2 * n) ++ fixGates n) I) (aNZ n) 1 = _
    rw [actGates_append, actGates_append, fixGates_keeps_NZ,
      chainT_keeps_NZ (Nat.le_refl _)]
    have hain : a < 2 ^ n := by
      have := modulus_lt hp; omega
    rw [initGates_act hn hain h0 h2, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
      readField_writeField_narrow (by omega), Nat.pow_one]
    by_cases hz : a = 0
    · rw [if_pos hz]
    · rw [if_neg hz]
  rw [hnzval]
  by_cases hz : a = 0
  · -- The specification sends zero to zero, and the copy is switched off.
    rw [if_pos hz, Nat.zero_mul, hz]
    refine congrArg (fun q => writeField I n n q) ?_
    show 0 = VQ.Curve.inv 0
    -- `inv 0` is `0 ^ (p - 2)` modulo the prime, and the exponent is positive.
    have hz0 : VQ.Curve.inv 0 = 0 := by
      show VQ.Curve.powMod 0 (VQ.Curve.p - 2) = 0
      rw [VQ.Curve.powMod_eq, Nat.zero_pow (by decide), Nat.zero_mod]
    exact hz0.symm
  · -- The copy runs, and the register holds the inverse.
    rw [if_neg hz, Nat.one_mul]
    refine congrArg (fun q => writeField I n n q) ?_
    have hfv := fwd_value hn hp hlaw hpf ha hz h0 h2
    have hinvlt : VQ.Curve.inv a < 2 ^ n := by
      have := VQ.Curve.inv_lt a
      have := modulus_lt hp
      omega
    have hnarrow : readField (actGates (fwdGates n) I) (aTU n) n
        = readField (actGates (fwdGates n) I) (aTU n) (bw n) % 2 ^ n := by
      show (_ >>> aTU n) % 2 ^ n = ((_ >>> aTU n) % 2 ^ (bw n)) % 2 ^ n
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by simp only [bw]; omega))]
    rw [hnarrow, hfv, Nat.mod_eq_of_lt hinvlt]

end VQ.Curve.PointAddition.Arithmetic.Inv
