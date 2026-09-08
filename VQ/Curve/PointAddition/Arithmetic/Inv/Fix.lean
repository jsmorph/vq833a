import VQ.Curve.PointAddition.Arithmetic.Inv.Chain
import VQ.Curve.PointAddition.Arithmetic.Inv.CState
import VQ.Curve.PointAddition.Arithmetic.Inv.Halve

/-!
# Correction circuit

After `2 n` rounds the registers hold `u = 1`, `v = 0`, `s = p`, and `r` the
almost inverse, which satisfies `x r + 2 ^ k = 0` modulo `p` and is below `2 p`
rather than below `p`.  Three steps turn that into the inverse.

Reduce, by subtracting the modulus when `r` is at least it.  Negate, into the
scratch register, which needs the modulus and finds it in `s`.  Then halve `k`
times, one halving per round under that round's kept bit, since the number of
active rounds is exactly `k`.

The correction runs inside compute-copy-uncompute, so the reverse pass clears
its workspace.  The forward reduction therefore retains its comparison bit.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- Reduce `r` below the modulus, which sits in `s`. -/
def fixReduce (n : Nat) : List RGate :=
  cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
    ++ loadCX (aGt n) (aTU n) (bw n) modulus
    ++ subAt (bw n) (aTU n) (aR n) (aC n)
    ++ loadCX (aGt n) (aTU n) (bw n) modulus

/-- Put the modulus in the scratch register and subtract `r` from it, leaving
the negation there.  The control of the copy is bit zero of `u`, which is one. -/
def fixNegate (n : Nat) : List RGate :=
  loadX (aTU n) (bw n) modulus ++ subAt (bw n) (aR n) (aTU n) (aC n)

/-- One halving of the scratch register, under round `t`'s kept bit.  The
modulus is added first when the operand is odd, which makes it even.

The control is then recovered and cleared.  Halving sends an even operand below
`(p + 1) / 2` and an odd one to at least `(p + 1) / 2`, so the halved value
decides what the parity was, and comparing it against `halfMod` puts that back
on the wire the control came from.  One wire serves all `2 n` halvings. -/
def hCmp (n : Nat) : List RGate :=
  majPre (bw n) (aTU n) (aTR n) (aC n)
    ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)]

def fixHalve (n t : Nat) : List RGate :=
  [RGate.ccx (aZ n + t) (aTU n) (aH n)]
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ addAt (bw n) (aTR n) (aTU n) (aC n)
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ shiftR (aZ n + t) (aTU n) (bw n)
    ++ loadX (aTR n) (bw n) halfMod
    ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
    ++ loadX (aTR n) (bw n) halfMod

/-- The halvings, one per round. -/
def fixHalves (n : Nat) : Nat → List RGate
  | 0 => []
  | T + 1 => fixHalves n T ++ fixHalve n T

/-- The whole correction. -/
def fixGates (n : Nat) : List RGate :=
  fixReduce n ++ fixNegate n ++ fixHalves n (2 * n)

/-! ## Modular reduction

Compare `r` against the modulus in `s`, negate the answer so it reads "at
least", and subtract under it. -/

theorem fixReduce_act {n I u v r s a bo m : Nat} (hn : 0 < n) (hsm : s = modulus)
    (hrw : r < 2 ^ (bw n)) (hsw : s < 2 ^ (bw n)) (hs : s < 2 ^ n)
    (hdiff : r < s ∨ r - s < 2 ^ n)
    (huw : u < 2 ^ (bw n)) (hvw : v < 2 ^ (bw n)) :
    actGates (fixReduce n) (cs n I u v r s 0 0 a bo 0 0)
      = cs n I u v ((r + (2 ^ (bw n) - (if r < s then 0 else s))) % 2 ^ (bw n)) s 0 0 a bo
          (if r < s then 0 else 1) 0 := by
  have hms : modulus = s := hsm.symm
  have hred : ∀ x : Nat, x < 2 ^ (bw n) → x % 2 ^ (bw n) = x := fun x hx => Nat.mod_eq_of_lt hx
  -- The comparison.
  have e1 : actGates (cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n))
      (cs n I u v r s 0 0 a bo 0 0)
      = cs n I u v r s 0 0 a bo (if r < s then 1 else 0) 0 := by
    have hr0 : readField (cs n I u v r s 0 0 a bo 0 0) (aS n) (bw n) = s := by
      rw [cs_read_S]; exact hred s hsw
    have hr1 : readField (cs n I u v r s 0 0 a bo 0 0) (aR n) (bw n) = r := by
      rw [cs_read_R]; exact hred r hrw
    have hr2 : readField (cs n I u v r s 0 0 a bo 0 0) (aC n) 1 = 0 := by
      rw [cs_read_C]
    have hr3 : readField (cs n I u v r s 0 0 a bo 0 0) (aGt n) 1 = 0 := by
      rw [cs_read_Gt]
    have := cmpAt_act (k := n) (ou := aS n) (ov := aR n) (oc := aC n) (og := aGt n)
      (I := cs n I u v r s 0 0 a bo 0 0) (u := s) (v := r) (g := 0) (Wd := totalWidth n)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) hr0 hr1 hr2 hr3 hs hrw hdiff
    rw [show bw n = n + 1 from rfl] at *
    rw [this, cs_write_Gt]
    refine congrArg (fun q => cs n I u v r s 0 0 a bo q 0) ?_
    by_cases hlt : r < s
    · rw [if_pos hlt]
    · rw [if_neg hlt]
  -- Negate it, so the bit reads "at least".
  have e2 : actGates [RGate.x (aGt n)] (cs n I u v r s 0 0 a bo (if r < s then 1 else 0) 0)
      = cs n I u v r s 0 0 a bo (if r < s then 0 else 1) 0 := by
    show RGate.act (RGate.x (aGt n)) _ = _
    rw [act_x, ← readField_one, cs_read_Gt, Nat.pow_one, cs_write_Gt]
    refine congrArg (fun q => cs n I u v r s 0 0 a bo q 0) ?_
    by_cases hlt : r < s
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt]
  -- Copy the modulus under it.
  have hgb : ∀ r' tu', bv (cs n I u v r' s tu' 0 a bo (if r < s then 0 else 1) 0) (aGt n)
      = (if r < s then 0 else 1) := by
    intro r' tu'
    rw [← readField_one, cs_read_Gt, Nat.pow_one]
    by_cases hlt : r < s
    · rw [if_pos hlt]
    · rw [if_neg hlt]
  have e3 : actGates (loadCX (aGt n) (aTU n) (bw n) modulus)
      (cs n I u v r s 0 0 a bo (if r < s then 0 else 1) 0)
      = cs n I u v r s ((if r < s then 0 else 1) * s) 0 a bo (if r < s then 0 else 1) 0 := by
    rw [loadCX_act (c := aGt n) (bw n) (aTU n) modulus _ (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)), hms,
      cs_read_TU,hgb r 0, Nat.zero_mod, Nat.zero_xor, cs_write_TU]
  -- Subtract it.
  have hsub : (if r < s then 0 else 1) * s < 2 ^ (bw n) := by
    by_cases hlt : r < s
    · rw [if_pos hlt]; simpa using Nat.two_pow_pos (bw n)
    · rw [if_neg hlt]; simpa using hsw
  have e4 : actGates (subAt (bw n) (aTU n) (aR n) (aC n))
      (cs n I u v r s ((if r < s then 0 else 1) * s) 0 a bo (if r < s then 0 else 1) 0)
      = cs n I u v ((r + (2 ^ (bw n) - (if r < s then 0 else 1) * s)) % 2 ^ (bw n)) s
          ((if r < s then 0 else 1) * s) 0 a bo (if r < s then 0 else 1) 0 := by
    have hr0 : readField (cs n I u v r s ((if r < s then 0 else 1) * s) 0 a bo
        (if r < s then 0 else 1) 0) (aTU n) (bw n) = (if r < s then 0 else 1) * s := by
      rw [cs_read_TU]; exact hred _ hsub
    have hr1 : readField (cs n I u v r s ((if r < s then 0 else 1) * s) 0 a bo
        (if r < s then 0 else 1) 0) (aR n) (bw n) = r := by
      rw [cs_read_R]; exact hred r hrw
    have hr2 : readField (cs n I u v r s ((if r < s then 0 else 1) * s) 0 a bo
        (if r < s then 0 else 1) 0) (aC n) 1 = 0 := by
      rw [cs_read_C]
    rw [subAt_act (Wd := totalWidth n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) hr0 hr1 hr2,
      cs_write_R]
  -- Clear the scratch.
  have e5 : actGates (loadCX (aGt n) (aTU n) (bw n) modulus)
      (cs n I u v ((r + (2 ^ (bw n) - (if r < s then 0 else 1) * s)) % 2 ^ (bw n)) s
        ((if r < s then 0 else 1) * s) 0 a bo (if r < s then 0 else 1) 0)
      = cs n I u v ((r + (2 ^ (bw n) - (if r < s then 0 else 1) * s)) % 2 ^ (bw n)) s 0 0 a bo
          (if r < s then 0 else 1) 0 := by
    rw [loadCX_act (c := aGt n) (bw n) (aTU n) modulus _ (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)), hms,
      cs_read_TU,hgb _ _, hred _ hsub, Nat.xor_self, cs_write_TU]
  show actGates (cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
      ++ loadCX (aGt n) (aTU n) (bw n) modulus ++ subAt (bw n) (aTU n) (aR n) (aC n)
      ++ loadCX (aGt n) (aTU n) (bw n) modulus) _ = _
  rw [actGates_append, actGates_append, actGates_append, actGates_append, e1, e2, e3, e4, e5]
  refine congrArg (fun q => cs n I u v ((r + (2 ^ (bw n) - q)) % 2 ^ (bw n)) s 0 0 a bo
    (if r < s then 0 else 1) 0) ?_
  by_cases hlt : r < s
  · rw [if_pos hlt, if_pos hlt, Nat.zero_mul]
  · rw [if_neg hlt, if_neg hlt, Nat.one_mul]

/-! ## Modular negation

Copy the modulus into the scratch register and subtract `r` from it.  The copy's
control is bit zero of `u`, which the chain leaves at one. -/

theorem fixNegate_act {n I v r s a bo gt : Nat} (hsm : s = modulus)
    (hrw : r < 2 ^ (bw n)) (hsw : s < 2 ^ (bw n)) (hu : (1 : Nat) % 2 ^ (bw n) = 1) :
    actGates (fixNegate n) (cs n I 1 v r s 0 0 a bo gt 0)
      = cs n I 1 v r s ((s + (2 ^ (bw n) - r)) % 2 ^ (bw n)) 0 a bo gt 0 := by
  have hms : modulus = s := hsm.symm
  have hred : ∀ x : Nat, x < 2 ^ (bw n) → x % 2 ^ (bw n) = x := fun x hx => Nat.mod_eq_of_lt hx
  have hub : ∀ tu', bv (cs n I 1 v r s tu' 0 a bo gt 0) (aU n) = 1 := by
    intro tu'
    rw [cs_bit_U]
  have e1 : actGates (loadX (aTU n) (bw n) modulus) (cs n I 1 v r s 0 0 a bo gt 0)
      = cs n I 1 v r s s 0 a bo gt 0 := by
    rw [loadX_act (bw n) (aTU n) modulus, hms,
      cs_read_TU,Nat.zero_mod, Nat.zero_xor, cs_write_TU]
  have e2 : actGates (subAt (bw n) (aR n) (aTU n) (aC n)) (cs n I 1 v r s s 0 a bo gt 0)
      = cs n I 1 v r s ((s + (2 ^ (bw n) - r)) % 2 ^ (bw n)) 0 a bo gt 0 := by
    have hr0 : readField (cs n I 1 v r s s 0 a bo gt 0) (aR n) (bw n) = r := by
      rw [cs_read_R]; exact hred r hrw
    have hr1 : readField (cs n I 1 v r s s 0 a bo gt 0) (aTU n) (bw n) = s := by
      rw [cs_read_TU]; exact hred s hsw
    have hr2 : readField (cs n I 1 v r s s 0 a bo gt 0) (aC n) 1 = 0 := by
      rw [cs_read_C]
    rw [subAt_act (Wd := totalWidth n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) hr0 hr1 hr2,
      cs_write_TU]
  show actGates (loadX (aTU n) (bw n) modulus
      ++ subAt (bw n) (aR n) (aTU n) (aC n)) _ = _
  rw [actGates_append, e1, e2]

/-! ## Halving step

The control is the round's kept bit and the operand's parity together.  Under it
the modulus is added, which makes the operand even, and then the operand is
shifted.  The shift's own control is the retained bit alone, so an inactive round leaves
the operand where it is. -/

/-! ### Control recovery

The block `hCmp ++ use ++ hCmp.reverse` is compute-use-uncompute over a
comparison, with the use a single Toffoli onto one wire, which is the shape
`actGates_compute_use_uncompute` wants.  `hCmp` is the comparison's preparation
and the copy of its carry, so the wire `aG` carries `halfMod < tu` for the
duration of the use and nothing afterwards. -/

theorem hCmp_wf {n : Nat} (hn : 0 < n) :
    (hCmp n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (majPre (bw n) (aTU n) (aTR n) (aC n)
    ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)]).all _ = true
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨majPre_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega), ?_⟩
  have hlo : aTU n ≤ aTU n + bw n - 1 := by simp only [bw]; omega
  have hhi : aTU n + bw n - 1 < aTU n + bw n := by simp only [bw]; omega
  have hg : aG n + 1 ≤ totalWidth n := by
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]
    omega
  have hb : aTU n + bw n ≤ totalWidth n := by
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]
    omega
  have hne : aTU n + bw n - 1 ≠ aG n := by
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
    omega
  simp [RGate.wellFormed, hne]
  omega

theorem hCmp_avoids {n : Nat} (hn : 0 < n) :
    ∀ g ∈ hCmp n, ∀ q ∈ g.wires, q < aH n ∨ aH n + 1 ≤ q := by
  intro g hg q hq
  have hg' : g ∈ majPre (bw n) (aTU n) (aTR n) (aC n)
    ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)] := hg
  rw [List.mem_append] at hg'
  cases hg' with
  | inl h =>
    have := majPre_avoids (w := bw n) (og := aH n) (by simp only [bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) g h q hq
    exact this
  | inr h =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hb : 0 < bw n := by simp only [bw]; omega
    rcases h with rfl | rfl <;>
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at * <;> omega

theorem fixHalve_act {n t I u v r s a bo gt tu z : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hsm : s = modulus)
    (htu : tu < 2 ^ n) (hsw : s < 2 ^ (bw n)) (hs : s % 2 = 1) (hsp : tu + s < 2 ^ (bw n))
    (hz : readField I (aZ n + t) 1 = z) (hh : readField I (aH n) 1 = 0)
    (hg : readField I (aG n) 1 = 0) (htlt : tu < s)
    (huw : u < 2 ^ (bw n)) (hvw : v < 2 ^ (bw n)) (hrw : r < 2 ^ (bw n)) :
    actGates (fixHalve n t) (cs n I u v r s tu 0 a bo gt 0)
      = cs n I u v r s (if z % 2 = 1 then mhalve s tu else tu) 0 a bo gt 0 := by
  have hms : modulus = s := hsm.symm
  have hred : ∀ x : Nat, x < 2 ^ (bw n) → x % 2 ^ (bw n) = x := fun x hx => Nat.mod_eq_of_lt hx
  have htuw : tu < 2 ^ (bw n) := by
    have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
      show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
      rw [Nat.pow_succ]; omega
    omega
  -- The control: the round was active and the operand is odd.
  have hzb : ∀ tu' tr' J', readField J' (aZ n + t) 1 = z % 2 →
      bv (cs n J' u v r s tu' tr' a bo gt 0) (aZ n + t) = z % 2 := by
    intro tu' tr' J' hJ
    rw [← readField_one, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), hJ]
  -- The Toffoli that computes the control.
  have e1 : actGates [RGate.ccx (aZ n + t) (aTU n) (aH n)] (cs n I u v r s tu 0 a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu 0 a bo gt 0 := by
    show RGate.act (RGate.ccx (aZ n + t) (aTU n) (aH n)) _ = _
    rw [act_ccx, ← readField_one, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), hh, ← readField_one,
      cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), hz, cs_bit_TU, cs_write_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
    refine congrArg (fun q => cs n (writeField I (aH n) 1 q) u v r s tu 0 a bo gt 0) ?_
    have hz2 : z < 2 := by rw [← hz]; exact readField_lt _ _ _
    have h1 : z = 0 ∨ z = 1 := by omega
    have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
    cases h1 with
    | inl h => rw [h]; simp
    | inr h => cases h2 with
      | inl h' => rw [h, h']
      | inr h' => rw [h, h']
  -- Name the control and the base it was written into.
  have hzr : readField (writeField I (aH n) 1 (z % 2 * (tu % 2))) (aZ n + t) 1 = z := by
    rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]; exact hz
  have hz2 : z < 2 := by rw [← hz]; exact readField_lt _ _ _
  have hcb : ∀ tu' tr',
      bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu' tr' a bo gt 0)
        (aH n) = z % 2 * (tu % 2) := by
    intro tu' tr'
    rw [← readField_one, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), readField_writeField_narrow (by omega),
      Nat.pow_one]
    have : z % 2 * (tu % 2) < 2 := by
      have h1 : z % 2 = 0 ∨ z % 2 = 1 := by omega
      have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
      cases h1 with
      | inl h => rw [h]; omega
      | inr h => cases h2 with
        | inl h' => rw [h, h']; omega
        | inr h' => rw [h, h']; omega
    omega
  -- Copy the modulus under the control.
  have e2 : actGates (loadCX (aH n) (aTR n) (bw n) modulus)
      (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu 0 a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu
          (z % 2 * (tu % 2) * s) a bo gt 0 := by
    rw [loadCX_act (c := aH n) (bw n) (aTR n) modulus _ (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)), hms,
      cs_read_TR,hcb tu 0, Nat.zero_mod, Nat.zero_xor, cs_write_TR]
  -- Add it.
  have hprod : z % 2 * (tu % 2) * s < 2 ^ (bw n) := by
    have h1 : z % 2 = 0 ∨ z % 2 = 1 := by omega
    have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
    cases h1 with
    | inl h => rw [h]; simpa using Nat.two_pow_pos (bw n)
    | inr h => cases h2 with
      | inl h' => rw [h, h']; simpa using Nat.two_pow_pos (bw n)
      | inr h' => rw [h, h']; simpa using hsw
  have e3 : actGates (addAt (bw n) (aTR n) (aTU n) (aC n))
      (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu
        (z % 2 * (tu % 2) * s) a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s
          ((z % 2 * (tu % 2) * s + tu) % 2 ^ (bw n)) (z % 2 * (tu % 2) * s) a bo gt 0 := by
    have hr0 : readField (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu
        (z % 2 * (tu % 2) * s) a bo gt 0) (aTR n) (bw n) = z % 2 * (tu % 2) * s := by
      rw [cs_read_TR]; exact hred _ hprod
    have hr1 : readField (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu
        (z % 2 * (tu % 2) * s) a bo gt 0) (aTU n) (bw n) = tu := by
      rw [cs_read_TU]; exact hred tu htuw
    have hr2 : readField (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s tu
        (z % 2 * (tu % 2) * s) a bo gt 0) (aC n) 1 = 0 := by
      rw [cs_read_C]
    rw [addAt_act (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) hr0 hr1 hr2, cs_write_TU]
  -- Clear the scratch.
  have hsum : (z % 2 * (tu % 2) * s + tu) % 2 ^ (bw n) = z % 2 * (tu % 2) * s + tu := by
    have h1 : z % 2 = 0 ∨ z % 2 = 1 := by omega
    have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
    refine Nat.mod_eq_of_lt ?_
    cases h1 with
    | inl h => rw [h]; simpa using htuw
    | inr h => cases h2 with
      | inl h' => rw [h, h']; simpa using htuw
      | inr h' => rw [h, h']; omega
  have e4 : actGates (loadCX (aH n) (aTR n) (bw n) modulus)
      (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s
        (z % 2 * (tu % 2) * s + tu) (z % 2 * (tu % 2) * s) a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s
          (z % 2 * (tu % 2) * s + tu) 0 a bo gt 0 := by
    rw [loadCX_act (c := aH n) (bw n) (aTR n) modulus _ (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)), hms,
      cs_read_TR,hcb _ _, hred _ hprod, Nat.xor_self, cs_write_TR]
  -- The shift uses the retained bit.  An inactive round leaves the
  -- operand unchanged.  An active round finds it even because the modulus was
  -- added exactly when it was odd.
  have hzbit : ∀ tu', bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2)))
      u v r s tu' 0 a bo gt 0) (aZ n + t) = z := by
    intro tu'
    rw [← readField_one, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), hzr]
  have hpre : actGates ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ addAt (bw n) (aTR n) (aTU n) (aC n)
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ shiftR (aZ n + t) (aTU n) (bw n)) (cs n I u v r s tu 0 a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s
          (if z % 2 = 1 then mhalve s tu else tu) 0 a bo gt 0 := by
    show actGates ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
        ++ loadCX (aH n) (aTR n) (bw n) modulus
        ++ addAt (bw n) (aTR n) (aTU n) (aC n)
        ++ loadCX (aH n) (aTR n) (bw n) modulus
        ++ shiftR (aZ n + t) (aTU n) (bw n)) _ = _
    rw [actGates_append, actGates_append, actGates_append, actGates_append, e1, e2, e3, hsum, e4]
    by_cases hzv : z = 1
    · -- An active round.
      subst hzv
      have heven : bv (cs n (writeField I (aH n) 1 (1 % 2 * (tu % 2)))
          u v r s (1 % 2 * (tu % 2) * s + tu) 0 a bo gt 0) (aTU n) = 0 := by
        rw [cs_bit_TU]
        have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
        cases h2 with
        | inl h' => rw [h']; omega
        | inr h' => rw [h']; omega
      have hfit : (1 % 2 * (tu % 2) * s + tu) % 2 ^ (bw n) = 1 % 2 * (tu % 2) * s + tu := by
        have := hsum
        rw [Nat.one_mod] at *
        exact this
      rw [shiftR_on (bw n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (hzbit _) heven, cs_read_TU, hfit, cs_write_TU]
      refine congrArg (fun q => cs n (writeField I (aH n) 1 (1 % 2 * (tu % 2)))
        u v r s q 0 a bo gt 0) ?_
      rw [if_pos (by omega : (1 : Nat) % 2 = 1)]
      unfold mhalve
      have h2 : tu % 2 = 0 ∨ tu % 2 = 1 := by omega
      cases h2 with
      | inl h' => rw [h']; simp
      | inr h' => rw [h']; simp; omega
    · -- An inactive round: the shift is inert.
      have hz0 : z = 0 := by omega
      subst hz0
      rw [shiftR_off (bw n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (hzbit _)]
      refine congrArg (fun q => cs n (writeField I (aH n) 1 (0 % 2 * (tu % 2)))
        u v r s q 0 a bo gt 0) ?_
      rw [if_neg (by omega : ¬ (0 : Nat) % 2 = 1)]
      simp

  -- The recovery.  Compare the halved operand against `halfMod` and toggle the
  -- control off, which the comparison's own uncomputation leaves clear.
  have hbwp : 0 < bw n := by simp only [bw]; omega
  have hhalf : halfMod = (s - 1) / 2 := by rw [hsm]; rfl
  have hhlt : halfMod < 2 ^ (bw n) := by
    rw [hhalf]
    have := hsw
    omega
  -- Name the two values the pre-recovery half produced.
  obtain ⟨hval, hhv⟩ : ∃ x, (if z % 2 = 1 then mhalve s tu else tu) = x := ⟨_, rfl⟩
  have hvlt : hval < s := by
    rw [← hhv]
    by_cases hz1 : z % 2 = 1
    · rw [if_pos hz1]
      unfold mhalve
      by_cases he : tu % 2 = 0
      · rw [if_pos he]; omega
      · rw [if_neg he]; omega
    · rw [if_neg hz1]; exact htlt
  have hvw2 : hval < 2 ^ (bw n) := by omega
  -- The control combines `z` and the comparison.  In an inactive round `z` is zero, so
  -- the comparison is free to say anything there.
  have hcmp : z % 2 * (if halfMod < hval then 1 else 0) = z % 2 * (tu % 2) := by
    by_cases hz1 : z % 2 = 1
    · rw [hz1, Nat.one_mul, Nat.one_mul, ← hhv, if_pos hz1, hhalf]
      by_cases ho : tu % 2 = 1
      · rw [if_pos ((mhalve_gt hs htlt).mpr ho), ho]
      · have ho0 : tu % 2 = 0 := by omega
        rw [if_neg (fun hc => by have := (mhalve_gt hs htlt).mp hc; omega), ho0]
    · have hz0 : z % 2 = 0 := by omega
      rw [hz0, Nat.zero_mul, Nat.zero_mul]
  -- Load the constant, run the block, unload.
  have e5 : actGates (loadX (aTR n) (bw n) halfMod)
      (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval 0 a bo gt 0)
      = cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0 := by
    rw [loadX_act, cs_read_TR, Nat.zero_mod, Nat.zero_xor, cs_write_TR]
  -- The block: compute the comparison, use it, uncompute it.
  have hcp : ∀ j, actGates [RGate.ccx (aZ n + t) (aG n) (aH n)] j
      = writeField j (aH n) 1 ((bv j (aH n) + bv j (aZ n + t) * bv j (aG n)) % 2) := by
    intro j
    show RGate.act (RGate.ccx (aZ n + t) (aG n) (aH n)) j = _
    rw [act_ccx]
  have hblock := actGates_compute_use_uncompute (gs := hCmp n)
    (cp := [RGate.ccx (aZ n + t) (aG n) (aH n)]) (w := totalWidth n) (off := aH n) (len := 1)
    (hCmp_wf hn) (hCmp_avoids hn) hcp
    (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)
  have hz2 : z < 2 := by rw [← hz]; exact readField_lt I (aZ n + t) 1
  -- The three bits the use reads, at the state the comparison leaves.
  have hY : ∀ q : Nat, (q + 1 ≤ aU n ∨ aNZ n ≤ q) → q ≠ aH n →
      bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0) q
        = bv I q := by
    intro q hq hne
    rw [← readField_one, cs_read_out (by omega), readField_writeField_of_disjoint (by omega),
      readField_one]
  have hXH : bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)
      (aH n) = z % 2 * (tu % 2) % 2 := by
    rw [← readField_one, cs_read_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega), readField_writeField, Nat.pow_one]
  have hXZ : bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)
      (aZ n + t) = z := by
    rw [hY (aZ n + t) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega), ← readField_one, hz]
  have hXG : bv (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)
      (aG n) = 0 := by
    rw [hY (aG n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega), ← readField_one, hg]
  -- The comparison bit, from the carry the chain lays down.
  have hAvG : ∀ g ∈ majPre (bw n) (aTU n) (aTR n) (aC n), ∀ q ∈ g.wires,
      q < aG n ∨ aG n + 1 ≤ q := majPre_avoids (by simp only [bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega)
  have hbit : bv (actGates (hCmp n)
      (cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)) (aG n)
      = (if halfMod < hval then 1 else 0) := by
    have hcar := majPre_carry (w := bw n) (ou := aTU n) (ov := aTR n) (oc := aC n)
      (I := cs n (writeField I (aH n) 1 (z % 2 * (tu % 2))) u v r s hval halfMod a bo gt 0)
      (u := hval) (v := halfMod) (by simp only [bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega)
      (by rw [cs_read_TU, hred _ hvw2]) (by rw [cs_read_TR, hred _ hhlt]) (by rw [cs_read_C])
      hvw2
    show bv (actGates (majPre (bw n) (aTU n) (aTR n) (aC n)
      ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)]) _) (aG n) = _
    rw [actGates_append]
    show bv (RGate.act (RGate.x (aG n)) (RGate.act (RGate.cx (aTU n + bw n - 1) (aG n)) _)) _ = _
    rw [act_x, bv_write_self, act_cx, bv_write_self, hcar,
      bv_actGates_outside hAvG, hXG, carry_lt_iff hvw2 hhlt]
    by_cases hlt : halfMod < hval <;> simp [hlt]
  have hAvZ : ∀ g ∈ hCmp n, ∀ q ∈ g.wires, q < aZ n + t ∨ aZ n + t + 1 ≤ q := by
    intro g hg q hq
    have hg' : g ∈ majPre (bw n) (aTU n) (aTR n) (aC n)
      ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)] := hg
    rw [List.mem_append] at hg'
    cases hg' with
    | inl h =>
      exact majPre_avoids (w := bw n) (ou := aTU n) (ov := aTR n) (oc := aC n) (og := aZ n + t)
        (by simp only [bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) g h q hq
    | inr h =>
      have hb : 0 < bw n := by simp only [bw]; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at * <;>
        omega
  -- The use toggles the control off, and the value it toggles by is the one the
  -- pre-recovery half put there.
  have hzero : (z % 2 * (tu % 2) % 2 + z * (if halfMod < hval then 1 else 0)) % 2 = 0 := by
    rcases (by omega : z = 0 ∨ z = 1) with hz0 | hz1
    · subst hz0; simp
    · subst hz1
      have hc := hcmp
      simp only [Nat.one_mod, Nat.one_mul] at hc ⊢
      rw [hc]
      have : tu % 2 < 2 := by omega
      omega
  have hclr : writeField I (aH n) 1 0 = I := by
    rw [← hh]; exact Reversible.writeField_read I (aH n) 1
  have hcomp4 : ∀ (A B C D : List RGate) (i : Nat),
      actGates (A ++ B ++ C ++ D) i
        = actGates D (actGates C (actGates B (actGates A i))) := by
    intro A B C D i
    rw [actGates_append, actGates_append, actGates_append]
  have e7 : actGates (loadX (aTR n) (bw n) halfMod)
      (cs n I u v r s hval halfMod a bo gt 0)
      = cs n I u v r s hval 0 a bo gt 0 := by
    rw [loadX_act, cs_read_TR, hred _ hhlt, Nat.xor_self, cs_write_TR]
  show actGates ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ addAt (bw n) (aTR n) (aTU n) (aC n)
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ shiftR (aZ n + t) (aTU n) (bw n)
      ++ loadX (aTR n) (bw n) halfMod
      ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
      ++ loadX (aTR n) (bw n) halfMod) _ = _
  rw [hcomp4, hpre, hhv, e5, hblock,
    bv_actGates_outside (hCmp_avoids hn), bv_actGates_outside hAvZ, hXH, hXZ, hbit, hzero,
    cs_write_out (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega),
    writeField_writeField, hclr, e7]
/-! ## Repeated-halving semantics

One halving occurs per active round, whose count is
the counter the arithmetic carries. -/

/-- A halving leaves the kept termination bits alone: it writes only its own
control, which sits above them. -/
theorem fixHalve_keeps' {n t j' j I : Nat} (hj : j < 2 * n) :
    readField (writeField I (aH n) 1 j') (aZ n + j) 1 = readField I (aZ n + j) 1 :=
  readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)

set_option maxHeartbeats 2000000 in
/-- All the halvings.  The operand ends divided by two as many times as the
chain had active rounds, as recorded by the arithmetic counter.

Every halving now puts its control back, so the state outside the registers is
the one it started with and the statement needs no existential.  Before the
recovery this lemma produced a fresh index for each halving, carried an
invariant that every one of the `2 n` control wires was still clear ahead of the
halving that would use it, and threaded both through the induction. -/
theorem fixHalves_act {n p x : Nat} (hn : 0 < n) (hpm : p = modulus)
    (hp : p % 2 = 1) (hpn : p < 2 ^ n) :
    ∀ (T : Nat), T ≤ 2 * n → ∀ (I u v r a bo gt tu : Nat),
      u < 2 ^ (bw n) → v < 2 ^ (bw n) → r < 2 ^ (bw n) → tu < p →
      (∀ j, j < 2 * n → readField I (aZ n + j) 1 = zBit (iter j (start p x))) →
      readField I (aH n) 1 = 0 → readField I (aG n) 1 = 0 →
      actGates (fixHalves n T) (cs n I u v r p tu 0 a bo gt 0)
        = cs n I u v r p (mhalves p (iter T (start p x)).k tu) 0 a bo gt 0 := by
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  have hpw : p < 2 ^ (bw n) := by omega
  intro T
  induction T with
  | zero =>
    intro _ I u v r a bo gt tu _ _ _ _ _ _ _
    show actGates [] _ = _
    rw [actGates_nil]
    rfl
  | succ T ih =>
    intro hT I u v r a bo gt tu hu hv hr htu hz hh hg
    have hprev := ih (by omega) I u v r a bo gt tu hu hv hr htu hz hh hg
    have hsm : mhalves p (iter T (start p x)).k tu < p := mhalves_lt hp _ _ htu
    have hzT : readField I (aZ n + T) 1 = zBit (iter T (start p x)) := hz T (by omega)
    have hstep : actGates (fixHalve n T)
        (cs n I u v r p (mhalves p (iter T (start p x)).k tu) 0 a bo gt 0)
        = cs n I u v r p
            (if zBit (iter T (start p x)) % 2 = 1
              then mhalve p (mhalves p (iter T (start p x)).k tu)
              else mhalves p (iter T (start p x)).k tu) 0 a bo gt 0 :=
      fixHalve_act (n := n) (t := T) (I := I) (u := u) (v := v) (r := r)
        (s := p) (a := a) (bo := bo) (gt := gt)
        (tu := mhalves p (iter T (start p x)).k tu) (z := zBit (iter T (start p x)))
        hn (by omega) hpm (by omega) hpw hp (by omega) hzT hh hg hsm hu hv hr
    have hval : (if zBit (iter T (start p x)) % 2 = 1
          then mhalve p (mhalves p (iter T (start p x)).k tu)
          else mhalves p (iter T (start p x)).k tu)
        = mhalves p (iter (T + 1) (start p x)).k tu := by
      rw [iter_succ' T (start p x), round_k]
      unfold zBit
      by_cases hv0 : (iter T (start p x)).v = 0
      · rw [if_pos hv0]
        simp [mhalves]
      · rw [if_neg hv0, if_pos (by omega : (1 : Nat) % 2 = 1), mhalves_add_one]
    show actGates (fixHalves n T ++ fixHalve n T) _ = _
    rw [actGates_append, hprev, hstep, hval]

/-! ## Retained-wire preservation

Both work inside the ten registers, so the halving controls and the termination
bits come out of them as they went in. -/

theorem fixReduce_wires {n : Nat} : ∀ g ∈ fixReduce n, ∀ q ∈ g.wires,
    aU n ≤ q ∧ q < aNZ n := by
  have hw : 0 < bw n := by simp only [bw]; omega
  intro g hg q hq
  have hg2 : g ∈ cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
      ++ loadCX (aGt n) (aTU n) (bw n) modulus ++ subAt (bw n) (aTU n) (aR n) (aC n)
      ++ loadCX (aGt n) (aTU n) (bw n) modulus := hg
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hg2
  cases hg2 with
  | inr h2 =>
    have := loadCX_wires (bw n) (aTU n) modulus g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega
  | inl h1 =>
    cases h1 with
    | inr h2 =>
      have := addAt_wires (w := bw n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) g (List.mem_reverse.mp h2) q hq
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
      omega
    | inl h1 =>
      cases h1 with
      | inr h2 =>
        have := loadCX_wires (bw n) (aTU n) modulus g h2 q hq
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
        omega
      | inl h1 =>
        cases h1 with
        | inr h2 =>
          simp only [List.mem_singleton] at h2
          subst h2
          simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
          omega
        | inl h2 =>
          have := cmpAt_wires hw (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) g h2 q hq
          simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
          omega

theorem fixNegate_wires {n : Nat} : ∀ g ∈ fixNegate n, ∀ q ∈ g.wires,
    aU n ≤ q ∧ q < aNZ n := by
  intro g hg q hq
  have hg2 : g ∈ loadX (aTU n) (bw n) modulus
      ++ subAt (bw n) (aR n) (aTU n) (aC n) := hg
  rw [List.mem_append] at hg2
  cases hg2 with
  | inl h2 =>
    have := loadX_wires (bw n) (aTU n) modulus g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega
  | inr h2 =>
    have := addAt_wires (w := bw n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega) g (List.mem_reverse.mp h2) q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *
    omega

/-! ## Correction wire bounds

Everything the correction touches is a working register, a halving control, or a
kept termination bit. -/

theorem fixHalve_wires {n t : Nat} : ∀ g ∈ fixHalve n t, ∀ q ∈ g.wires,
    (aU n ≤ q ∧ q < aNZ n) ∨ q = aH n ∨ q = aG n ∨ q = aZ n + t := by
  have hbp : 0 < bw n := by simp only [bw]; omega
  intro g hg q hq
  have hg2 : g ∈ [RGate.ccx (aZ n + t) (aTU n) (aH n)]
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ addAt (bw n) (aTR n) (aTU n) (aC n)
      ++ loadCX (aH n) (aTR n) (bw n) modulus
      ++ shiftR (aZ n + t) (aTU n) (bw n)
      ++ loadX (aTR n) (bw n) halfMod
      ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
      ++ loadX (aTR n) (bw n) halfMod := hg
  have hCw : ∀ g' ∈ hCmp n, ∀ q' ∈ g'.wires,
      (aU n ≤ q' ∧ q' < aNZ n) ∨ q' = aG n := by
    intro g' hg' q' hq'
    have hx : g' ∈ majPre (bw n) (aTU n) (aTR n) (aC n)
      ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)] := hg'
    rw [List.mem_append] at hx
    cases hx with
    | inl h =>
      have hy : g' ∈ loadX (aTU n) (bw n) (2 ^ bw n - 1) ++ loadX (aC n) 1 1
        ++ majAt (aTU n) (aTR n) (aC n) 0 (bw n) := h
      rw [List.mem_append, List.mem_append] at hy
      rcases hy with (h1 | h1) | h1
      · have := loadX_wires (bw n) (aTU n) (2 ^ bw n - 1) g' h1 q' hq'
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
      · have := loadX_wires 1 (aC n) 1 g' h1 q' hq'
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
      · have := majAt_wires (aTU n) (aTR n) (bw n) (aC n) 0 g' h1 q' hq'
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
    | inr h =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      cases h with
      | inl he =>
        subst he
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl
        · exact Or.inl (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw]; omega)
        · exact Or.inr rfl
      | inr he =>
        subst he
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq'
        subst hq'
        exact Or.inr rfl
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append,
    List.mem_append, List.mem_append, List.mem_append] at hg2
  rcases hg2 with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw]; omega)
    · exact Or.inr (Or.inl rfl)
  · have := loadCX_wires (bw n) (aTR n) modulus g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
  · have := addAt_wires (w := bw n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw]; omega) g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
  · have := loadCX_wires (bw n) (aTR n) modulus g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
  · have := shiftR_wires (c := aZ n + t) (bw n) (aTU n) g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
  · have := loadX_wires (bw n) (aTR n) halfMod g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega
  · rw [List.mem_append, List.mem_append] at h
    rcases h with (h1 | h1) | h1
    · have hw := hCw g h1 q hq
      cases hw with
      | inl hl => exact Or.inl hl
      | inr hr => exact Or.inr (Or.inr (Or.inl hr))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      subst h1
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
    · have hw := hCw g (List.mem_reverse.mp h1) q hq
      cases hw with
      | inl hl => exact Or.inl hl
      | inr hr => exact Or.inr (Or.inr (Or.inl hr))
  · have := loadX_wires (bw n) (aTR n) halfMod g h q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, bw] at *; omega

theorem fixHalves_wires {n : Nat} : ∀ (T : Nat), T ≤ 2 * n →
    ∀ g ∈ fixHalves n T, ∀ q ∈ g.wires,
      (aU n ≤ q ∧ q < aNZ n) ∨ q = aH n ∨ q = aG n
        ∨ (∃ j, j < 2 * n ∧ q = aZ n + j) := by
  intro T
  induction T with
  | zero => intro _ g hg; simp [fixHalves] at hg
  | succ T ih =>
    intro hT g hg q hq
    have hg2 : g ∈ fixHalves n T ++ fixHalve n T := hg
    rw [List.mem_append] at hg2
    cases hg2 with
    | inl h => exact ih (by omega) g h q hq
    | inr h =>
      have hw := fixHalve_wires g h q hq
      rcases hw with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr ⟨T, by omega, h'⟩))

theorem fixGates_wires {n : Nat} : ∀ g ∈ fixGates n, ∀ q ∈ g.wires,
    (aU n ≤ q ∧ q < aNZ n) ∨ q = aH n ∨ q = aG n
      ∨ (∃ j, j < 2 * n ∧ q = aZ n + j) := by
  intro g hg q hq
  have hg2 : g ∈ fixReduce n ++ fixNegate n ++ fixHalves n (2 * n) := hg
  rw [List.mem_append, List.mem_append] at hg2
  cases hg2 with
  | inr h => exact fixHalves_wires (2 * n) (Nat.le_refl _) g h q hq
  | inl h1 =>
    cases h1 with
    | inl h => exact Or.inl (fixReduce_wires g h q hq)
    | inr h => exact Or.inl (fixNegate_wires g h q hq)

/-! ## Correction well-formedness -/

theorem fixReduce_wf {n : Nat} (hn : 0 < n) :
    (fixReduce n).all (RGate.wellFormed (totalWidth n)) = true := by
  have hw : 0 < bw n := by simp only [bw]; omega
  show (cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
    ++ loadCX (aGt n) (aTU n) (bw n) modulus ++ subAt (bw n) (aTU n) (aR n) (aC n)
    ++ loadCX (aGt n) (aTU n) (bw n) modulus).all _ = true
  rw [List.all_append, List.all_append, List.all_append, List.all_append,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨cmpAt_wf hw (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega), ?_⟩,
    loadCX_wf (aGt n) (bw n) (aTU n) modulus (totalWidth n) (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    subAt_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    loadCX_wf (aGt n) (bw n) (aTU n) modulus (totalWidth n) (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩
  simp [RGate.wellFormed]
  simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]
  omega

theorem fixNegate_wf {n : Nat} (hn : 0 < n) :
    (fixNegate n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (loadX (aTU n) (bw n) modulus
    ++ subAt (bw n) (aR n) (aTU n) (aC n)).all _ = true
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨loadX_wf (bw n) (aTU n) modulus (totalWidth n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega),
    subAt_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩

theorem fixHalve_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (fixHalve n t).all (RGate.wellFormed (totalWidth n)) = true := by
  have hbp : 0 < bw n := by simp only [bw]; omega
  have hgate : ∀ c x y : Nat, c ≠ x → c ≠ y → x ≠ y → c < totalWidth n → x < totalWidth n →
      y < totalWidth n → ([RGate.ccx c x y]).all (RGate.wellFormed (totalWidth n)) = true := by
    intro c x y h1 h2 h3 h4 h5 h6
    simp [RGate.wellFormed, h1, h2, h3, h4, h5, h6]
  show ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ addAt (bw n) (aTR n) (aTU n) (aC n)
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ shiftR (aZ n + t) (aTU n) (bw n)
    ++ loadX (aTR n) (bw n) halfMod
    ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
    ++ loadX (aTR n) (bw n) halfMod).all _ = true
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
  · exact hgate _ _ _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact loadCX_wf (aH n) (bw n) (aTR n) modulus (totalWidth n) (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact addAt_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact loadCX_wf (aH n) (bw n) (aTR n) modulus (totalWidth n) (Or.inr (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact shiftR_wf (bw n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact loadX_wf (bw n) (aTR n) halfMod _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact hCmp_wf hn
  · exact hgate _ _ _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)
  · exact List.all_eq_true.mpr fun g hg =>
      List.all_eq_true.mp (hCmp_wf hn) g (List.mem_reverse.mp hg)
  · exact loadX_wf (bw n) (aTR n) halfMod _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw, totalWidth]; omega)

theorem fixHalves_wf {n : Nat} (hn : 0 < n) : ∀ (T : Nat), T ≤ 2 * n →
    (fixHalves n T).all (RGate.wellFormed (totalWidth n)) = true := by
  intro T
  induction T with
  | zero => intro _; simp [fixHalves]
  | succ T ih =>
    intro hT
    show (fixHalves n T ++ fixHalve n T).all _ = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨ih (by omega), fixHalve_wf hn (by omega)⟩

theorem fixGates_wf {n : Nat} (hn : 0 < n) :
    (fixGates n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (fixReduce n ++ fixNegate n ++ fixHalves n (2 * n)).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨fixReduce_wf hn, fixNegate_wf hn⟩, fixHalves_wf hn (2 * n) (Nat.le_refl _)⟩

/-- The nonzero wire survives the correction: nothing there touches it. -/
theorem fixGates_keeps_NZ {n I : Nat} :
    readField (actGates (fixGates n) I) (aNZ n) 1 = readField I (aNZ n) 1 := by
  refine readField_actGates_outside (fun g hg q hq => ?_)
  have hw := fixGates_wires g hg q hq
  rcases hw with h | h | h | h
  · exact Or.inl (by omega)
  · right
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
    omega
  · right
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
    omega
  · obtain ⟨j, hj, hq'⟩ := h
    right
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, aG, bw] at *
    omega

end VQ.Curve.PointAddition.Arithmetic.Inv
