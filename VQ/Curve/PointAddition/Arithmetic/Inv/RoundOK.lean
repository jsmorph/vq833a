import VQ.Curve.PointAddition.Arithmetic.Inv.Seg

/-!
# Round circuit semantics

The eight segments composed, in the four branches the two control bits select.

Writing the branches in the numbering `VQ.Curve.PointAddition.Arithmetic.Inv.step` uses -- `u` even, `u` odd with
`v` even, both odd with `v < u`, both odd otherwise -- the bits come out

| branch | `bswap` | kept bit | `both odd` |
|---|---|---|---|
| 1 | 1 | 0 | 0 |
| 2 | 0 | 1 | 0 |
| 3 | 1 | 1 | 1 |
| 4 | 0 | 0 | 1 |

so the swap runs in branches one and three and the arithmetic in three and four,
which is Algorithm 7b.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-! ## Parity from the Euclidean invariant

`r v + s u = p` with odd `p` forces exactly one of `r` and `s` to be odd.
The circuit uses this invariant to clear `bswap` against the parity of the new
`r`.  The branch lemmas derive the required parity equations. -/

/-- A product is odd only when both factors are. -/
theorem odd_of_mul_odd {a b : Nat} (h : a * b % 2 = 1) : a % 2 = 1 ∧ b % 2 = 1 := by
  have hm := Nat.mul_mod a b 2
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  cases ha with
  | inl h0 => rw [h0, Nat.zero_mul] at hm; omega
  | inr h1 => cases hb with
    | inl h0 => rw [h1, h0, Nat.mul_zero] at hm; omega
    | inr h1' => exact ⟨h1, h1'⟩

/-- With `u` even, `r` and `v` are both odd. -/
theorem r_odd_of_u_even {r v s u p : Nat} (hp : p % 2 = 1) (hinv : r * v + s * u = p)
    (hu2 : u % 2 = 0) : r % 2 = 1 ∧ v % 2 = 1 := by
  have h1 : (r * v + s * u) % 2 = 1 := by rw [hinv]; exact hp
  have h2 : s * u % 2 = 0 := by rw [Nat.mul_mod, hu2, Nat.mul_zero]
  exact odd_of_mul_odd (by omega)

/-- With `u` and `v` both odd, exactly one of `r` and `s` is odd. -/
theorem rs_odd_of_both_odd {r v s u p : Nat} (hp : p % 2 = 1) (hinv : r * v + s * u = p)
    (hu2 : u % 2 = 1) (hv2 : v % 2 = 1) : (r + s) % 2 = 1 := by
  have h1 : (r * v + s * u) % 2 = 1 := by rw [hinv]; exact hp
  have h2 : r * v % 2 = r % 2 := by
    rw [Nat.mul_mod, hv2, Nat.mul_one]; omega
  have h3 : s * u % 2 = s % 2 := by
    rw [Nat.mul_mod, hu2, Nat.mul_one]; omega
  omega

/-- The state a round starts from: the four registers, everything else clear. -/
def start1 (n t I u v r s : Nat) : Nat := ks n t I u v r s 0 0 0 0 0 0 0 0

/-- Branch two: `u` odd and `v` even.  Nothing swaps and nothing is added.  `v`
halves and `r` doubles, unless `v` was already zero. -/
theorem round_branch2 {n t I u v r s : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hu2 : u % 2 = 1) (hv2 : v % 2 = 0)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hrw : r < 2 ^ (bw n)) (hsw : s < 2 ^ (bw n))
    (hr : v ≠ 0 → r < 2 ^ n) :
    actGates (roundGates n t) (start1 n t I u v r s)
      = if v = 0 then ks n t I u v r s 0 0 0 0 0 0 1 0
        else ks n t I u (v / 2) (2 * r) s 0 0 0 0 0 0 1 1 := by
  have hured := red_of_lt hu
  have hvred := red_of_lt hv
  have hrred : r % 2 ^ (bw n) = r := Nat.mod_eq_of_lt hrw
  have hsred : s % 2 ^ (bw n) = s := Nat.mod_eq_of_lt hsw
  unfold roundGates start1
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append]
  rw [seg_zero hn ht hv, seg_dispatch ht, hu2, hv2]
  show actGates (segClear n t) (actGates (segSwap n) (actGates (segShift n t)
    (actGates (segArith n) (actGates (segSwap n) (actGates (segCompare n t)
      (ks n t I u v r s 0 0 0 0 0 0 1 (if v = 0 then 0 else 1))))))) = _
  rw [seg_compare hn ht hu hv]
  have hz0 : ((0 : Nat) % 2 + 0 % 2 * (if v < u then 1 else 0)) % 2 = 0 := by simp
  have hm1 : ((1 : Nat) % 2 + 0 % 2 * (if v < u then 1 else 0)) % 2 = 1 := by simp
  rw [hz0, hm1]
  rw [seg_swap ht hured hvred hrred hsred, if_neg (by decide : ¬ (0 : Nat) % 2 = 1)]
  rw [seg_arith_off ht hured hvred hrred hsred (by decide)]
  by_cases hv0 : v = 0
  · -- The round found `v` already zero: the shifts are inert.
    rw [if_pos hv0, seg_shift_off ht (by decide) hv0,
      seg_swap ht hured hvred hrred hsred, if_neg (by decide : ¬ (0 : Nat) % 2 = 1),
      seg_clear ht (by decide) (by simp), if_pos hv0]
  · -- An active round: `v` halves and `r` doubles.
    rw [if_neg hv0, seg_shift ht (by decide) hv2 (hr hv0) hrred hvred]
    have hvd : v / 2 % 2 ^ (bw n) = v / 2 := red_of_lt (by omega)
    have hrd : 2 * r % 2 ^ (bw n) = 2 * r := two_mul_red (hr hv0)
    rw [seg_swap ht hured hvd hrd hsred, if_neg (by decide : ¬ (0 : Nat) % 2 = 1),
      seg_clear ht (by decide) (by omega), if_neg hv0]

/-- Branch one: `u` even.  The registers swap, nothing is added, and the halving
and doubling land on `u` and `s`. -/
theorem round_branch1 {n t I p u v r s : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hp : p % 2 = 1) (hinv : r * v + s * u = p)
    (hu2 : u % 2 = 0) (hv0 : v ≠ 0)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hr : r < 2 ^ n) (hs : s < 2 ^ n) :
    actGates (roundGates n t) (start1 n t I u v r s)
      = ks n t I (u / 2) v r (2 * s) 0 0 0 0 0 0 0 1 := by
  have hured := red_of_lt hu
  have hvred := red_of_lt hv
  have hrred := red_of_lt hr
  have hsred := red_of_lt hs
  have hrodd := (r_odd_of_u_even hp hinv hu2).1
  unfold roundGates start1
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append]
  rw [seg_zero hn ht hv, seg_dispatch ht, hu2, if_neg hv0, Nat.zero_mul]
  show actGates (segClear n t) (actGates (segSwap n) (actGates (segShift n t)
    (actGates (segArith n) (actGates (segSwap n) (actGates (segCompare n t)
      (ks n t I u v r s 0 0 1 0 0 0 0 1)))))) = _
  rw [seg_compare hn ht hu hv]
  have ha1 : ((1 : Nat) % 2 + 0 % 2 * (if v < u then 1 else 0)) % 2 = 1 := by simp
  have hm0 : ((0 : Nat) % 2 + 0 % 2 * (if v < u then 1 else 0)) % 2 = 0 := by simp
  rw [ha1, hm0]
  -- The swap exchanges both pairs.
  rw [seg_swap ht hured hvred hrred hsred, if_pos (by decide : (1 : Nat) % 2 = 1)]
  rw [seg_arith_off ht hvred hured hsred hrred (by decide)]
  -- `u` is even, so the register now holding it halves.  `s` doubles.
  rw [seg_shift ht (by decide) hu2 hs hsred hured]
  have hud : u / 2 % 2 ^ (bw n) = u / 2 := red_of_lt (by omega)
  have hsd : 2 * s % 2 ^ (bw n) = 2 * s := two_mul_red hs
  rw [seg_swap ht hvred hud hsd hrred, if_pos (by decide : (1 : Nat) % 2 = 1)]
  rw [seg_clear ht (by decide) (by omega)]

/-- Branch four: `u` and `v` both odd with `u` at most `v`.  Nothing swaps.
`v` takes the halved difference and `s` picks up `r`. -/
theorem round_branch4 {n t I u v r s : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hu2 : u % 2 = 1) (hv2 : v % 2 = 1) (hle : u ≤ v) (hv0 : v ≠ 0)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hr : r < 2 ^ n) (hs : s < 2 ^ n)
    (hrs : r + s < 2 ^ (bw n)) :
    actGates (roundGates n t) (start1 n t I u v r s)
      = ks n t I u ((v - u) / 2) (2 * r) (r + s) 0 0 0 0 0 0 0 1 := by
  have hured := red_of_lt hu
  have hvred := red_of_lt hv
  have hrred := red_of_lt hr
  have hsred := red_of_lt hs
  unfold roundGates start1
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append]
  rw [seg_zero hn ht hv, seg_dispatch ht, hu2, hv2, if_neg hv0]
  show actGates (segClear n t) (actGates (segSwap n) (actGates (segShift n t)
    (actGates (segArith n) (actGates (segSwap n) (actGates (segCompare n t)
      (ks n t I u v r s 0 0 0 1 0 0 0 1)))))) = _
  rw [seg_compare hn ht hu hv, if_neg (by omega : ¬ v < u)]
  have ha0 : ((0 : Nat) % 2 + 1 % 2 * 0) % 2 = 0 := by decide
  have hm0 : ((0 : Nat) % 2 + 1 % 2 * 0) % 2 = 0 := by decide
  rw [ha0]
  rw [seg_swap ht hured hvred hrred hsred, if_neg (by decide : ¬ (0 : Nat) % 2 = 1)]
  rw [seg_arith ht hured hvred hrred hsred (by decide)]
  -- The difference does not borrow, and the sum stays in range.
  have hsub : (v + (2 ^ (bw n) - u)) % 2 ^ (bw n) = v - u := by
    refine sub_exact hle ?_
    have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
      show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
      rw [Nat.pow_succ]; omega
    omega
  have hadd : (r + s) % 2 ^ (bw n) = r + s := Nat.mod_eq_of_lt hrs
  rw [hsub, hadd]
  have hdiff : (v - u) % 2 = 0 := by omega
  have hvu : v - u < 2 ^ n := by omega
  rw [seg_shift ht (by decide) hdiff hr hrred (red_of_lt hvu)]
  have hvd : (v - u) / 2 % 2 ^ (bw n) = (v - u) / 2 := red_of_lt (by omega)
  have hrd : 2 * r % 2 ^ (bw n) = 2 * r := two_mul_red hr
  rw [seg_swap ht hured hvd hrd hadd, if_neg (by decide : ¬ (0 : Nat) % 2 = 1)]
  rw [seg_clear ht (by decide) (by omega)]

/-- Branch three: `u` and `v` both odd with `v` below `u`.  The registers swap,
`u` takes the halved difference, `r` picks up `s`, and `s` doubles. -/
theorem round_branch3 {n t I p u v r s : Nat} (hn : 0 < n) (ht : t < 2 * n)
    (hp : p % 2 = 1) (hinv : r * v + s * u = p)
    (hu2 : u % 2 = 1) (hv2 : v % 2 = 1) (hlt : v < u) (hv0 : v ≠ 0)
    (hu : u < 2 ^ n) (hv : v < 2 ^ n) (hr : r < 2 ^ n) (hs : s < 2 ^ n)
    (hrs : s + r < 2 ^ (bw n)) :
    actGates (roundGates n t) (start1 n t I u v r s)
      = ks n t I ((u - v) / 2) v (s + r) (2 * s) 0 0 0 0 0 0 1 1 := by
  have hured := red_of_lt hu
  have hvred := red_of_lt hv
  have hrred := red_of_lt hr
  have hsred := red_of_lt hs
  have hodd := rs_odd_of_both_odd hp hinv hu2 hv2
  unfold roundGates start1
  rw [actGates_append, actGates_append, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append]
  rw [seg_zero hn ht hv, seg_dispatch ht, hu2, hv2, if_neg hv0]
  show actGates (segClear n t) (actGates (segSwap n) (actGates (segShift n t)
    (actGates (segArith n) (actGates (segSwap n) (actGates (segCompare n t)
      (ks n t I u v r s 0 0 0 1 0 0 0 1)))))) = _
  rw [seg_compare hn ht hu hv, if_pos hlt]
  have ha1 : ((0 : Nat) % 2 + 1 % 2 * 1) % 2 = 1 := by decide
  rw [ha1]
  rw [seg_swap ht hured hvred hrred hsred, if_pos (by decide : (1 : Nat) % 2 = 1)]
  rw [seg_arith ht hvred hured hsred hrred (by decide)]
  -- After the swap the difference is `u - v`, and the sum is `s + r`.
  have hsub : (u + (2 ^ (bw n) - v)) % 2 ^ (bw n) = u - v := by
    refine sub_exact (by omega) ?_
    have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
      show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
      rw [Nat.pow_succ]; omega
    omega
  have hadd : (s + r) % 2 ^ (bw n) = s + r := Nat.mod_eq_of_lt hrs
  rw [hsub, hadd]
  have hdiff : (u - v) % 2 = 0 := by omega
  have huv : u - v < 2 ^ n := by omega
  rw [seg_shift ht (by decide) hdiff hs hsred (red_of_lt huv)]
  have hvd : (u - v) / 2 % 2 ^ (bw n) = (u - v) / 2 := red_of_lt (by omega)
  have hsd : 2 * s % 2 ^ (bw n) = 2 * s := two_mul_red hs
  rw [seg_swap ht hvred hvd hsd hadd, if_pos (by decide : (1 : Nat) % 2 = 1)]
  rw [seg_clear ht (by decide) (by omega)]

/-! ## Round-step equivalence

The four branches assembled.  `mBit` is the branch bit the round keeps and
`zBit` records that `v` was nonzero, and both are what the chain reads back. -/

/-- The kept branch bit: set in the two branches that do not swap `u` past an
even partner, which are `u` odd with `v` even and both odd with `v` below `u`. -/
def mBit (st : St) : Nat :=
  if st.u % 2 = 0 then 0 else if st.v % 2 = 0 then 1 else if st.v < st.u then 1 else 0

/-- The kept termination bit. -/
def zBit (st : St) : Nat := if st.v = 0 then 0 else 1

/-- One round of gates is one round of the arithmetic. -/
theorem roundGates_round {n t I p : Nat} {st : St} (hn : 0 < n) (ht : t < 2 * n)
    (hp : p % 2 = 1) (hinv : st.r * st.v + st.s * st.u = p)
    (hu : st.u < 2 ^ n) (hv : st.v < 2 ^ n) (hr : st.r < 2 ^ n) (hs : st.s < 2 ^ n)
    (hrs : st.r + st.s < 2 ^ (bw n)) :
    actGates (roundGates n t) (start1 n t I st.u st.v st.r st.s)
      = ks n t I (round st).u (round st).v (round st).r (round st).s 0 0 0 0 0 0
          (mBit st) (zBit st) := by
  by_cases he : st.u % 2 = 0
  · -- `u` even.  The invariant rules out a zero `v` here.
    have hv0 : st.v ≠ 0 := by
      intro h0
      rw [h0, Nat.mul_zero, Nat.zero_add] at hinv
      have : st.s * st.u % 2 = 0 := by rw [Nat.mul_mod, he, Nat.mul_zero]
      omega
    have hstep : round st = step st := by unfold round; rw [if_neg hv0]
    rw [round_branch1 hn ht hp hinv he hv0 hu hv hr hs, hstep, step_ueven he]
    unfold mBit zBit
    rw [if_pos he, if_neg hv0]
  · by_cases hev : st.v % 2 = 0
    · -- `u` odd and `v` even.
      have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
        show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
        rw [Nat.pow_succ]; omega
      rw [round_branch2 hn ht (by omega) hev hu hv (by omega) (by omega) (fun _ => hr)]
      unfold mBit zBit round
      rw [if_neg he, if_pos hev]
      by_cases hv0 : st.v = 0
      · rw [if_pos hv0, if_pos hv0, if_pos hv0]
      · rw [if_neg hv0, if_neg hv0, if_neg hv0, step_veven he hev]
    · by_cases hlt : st.v < st.u
      · -- Both odd, `v` below `u`.
        have hv0 : st.v ≠ 0 := by omega
        have hstep : round st = step st := by unfold round; rw [if_neg hv0]
        rw [round_branch3 hn ht hp hinv (by omega) (by omega) hlt hv0 hu hv hr hs (by omega),
          hstep, step_ubig he hev hlt]
        unfold mBit zBit
        rw [if_neg he, if_neg hev, if_pos hlt, if_neg hv0]
        exact congrArg (fun q => ks n t I ((st.u - st.v) / 2) st.v q (2 * st.s)
          0 0 0 0 0 0 1 1) (Nat.add_comm st.s st.r)
      · -- Both odd, `u` at most `v`.
        have hv0 : st.v ≠ 0 := by omega
        have hstep : round st = step st := by unfold round; rw [if_neg hv0]
        rw [round_branch4 hn ht (by omega) (by omega) (by omega) hv0 hu hv hr hs hrs,
          hstep, step_vbig he hev hlt]
        unfold mBit zBit
        rw [if_neg he, if_neg hev, if_neg hlt, if_neg hv0]

/-! ## Round semantics from the invariant

Every range bound the branches need follows from the Euclidean invariant and
`p < 2 ^ n`: while `v` is positive each of `r` and `s` is at most `p`, so their
sum is below `2 ^ (n + 1)`, and `u` and `v` are at most `p` throughout. -/

theorem round_bounds {n p x : Nat} {st : St} (hinv : Inv p x st) (hsm : Small p st)
    (hpn : p < 2 ^ n) (hv0 : 0 < st.v) :
    st.u < 2 ^ n ∧ st.v < 2 ^ n ∧ st.r < 2 ^ n ∧ st.s < 2 ^ n ∧ st.r + st.s < 2 ^ (bw n) := by
  obtain ⟨hr, hs⟩ := rs_le_p hv0 hinv
  obtain ⟨hup, hvp⟩ := hsm
  have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
    show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
    rw [Nat.pow_succ]; omega
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The round, with the range bounds derived rather than assumed. -/
theorem roundGates_inv {n t I p x : Nat} {st : St} (hn : 0 < n) (ht : t < 2 * n)
    (hp : p % 2 = 1) (hpn : p < 2 ^ n) (hinv : Inv p x st) (hsm : Small p st)
    (hwd : Wide p st) :
    actGates (roundGates n t) (start1 n t I st.u st.v st.r st.s)
      = ks n t I (round st).u (round st).v (round st).r (round st).s 0 0 0 0 0 0
          (mBit st) (zBit st) := by
  by_cases hv0 : st.v = 0
  · -- Nothing moves, and the invariant forces `u` odd, so this is branch two.
    have hsu : st.s * st.u = p := by
      have h1 := hinv.2.1
      rw [hv0, Nat.mul_zero, Nat.zero_add] at h1
      exact h1
    have hu2 : st.u % 2 = 1 := by
      have : st.s * st.u % 2 = 1 := by rw [hsu]; exact hp
      exact (odd_of_mul_odd this).2
    have hpow : (2 : Nat) ^ (bw n) = 2 * 2 ^ n := by
      show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n
      rw [Nat.pow_succ]; omega
    have hup := hsm.1
    have h2' : 1 * st.s ≤ st.s * st.u := by
      have := Nat.mul_le_mul_left st.s (show 1 ≤ st.u by omega)
      omega
    obtain ⟨hrw, hsw⟩ := hwd
    rw [round_branch2 hn ht hu2 (by rw [hv0]) (by omega)
      (by rw [hv0]; exact Nat.two_pow_pos n) (by omega) (by omega)
      (fun hne => absurd hv0 hne), if_pos hv0]
    unfold round mBit zBit
    rw [if_pos hv0, if_pos hv0]
    have : ¬ st.u % 2 = 0 := by omega
    rw [if_neg this, if_pos (show st.v % 2 = 0 by rw [hv0])]
  · have hvpos : 0 < st.v := Nat.pos_of_ne_zero hv0
    obtain ⟨hu, hv, hr, hs, hrs⟩ := round_bounds (n := n) hinv hsm hpn hvpos
    exact roundGates_round hn ht hp hinv.2.1 hu hv hr hs hrs

end VQ.Curve.PointAddition.Arithmetic.Inv
