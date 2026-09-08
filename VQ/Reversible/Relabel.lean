/-
Relabelling a reversible circuit induces a basis-index permutation.

`RCircuit.relabel f w r` rewrites every wire index through `f`.  Wire `q` is bit
`q` of a basis index, so relabelling the wires permutes the bits of the index,
and the action of the relabelled circuit is the action of the original read
through that permutation.  `permuteBits f w i` is the index whose bit `f q` is
bit `q` of `i` for every `q < w`, with every other bit zero, and the theorem
this file exists for is `act_relabel`:

  `act (relabel f w' r) (permuteBits f r.width i) = permuteBits f r.width (act r i)`.

The hypotheses require well-formedness and injectivity of `f` on the wires below
`r.width`.  Injectivity makes `permuteBits` place one bit per wire.  The proof
runs one bit at a time, and `permuteBits` drops the bits of `i` at or above
`r.width` on both sides.

Conjugation in the strict sense, `act (relabel f w' r) = permuteBits f w ∘ act r
∘ permuteBits g w`, is `act_relabel_conj`, and it does need `f` to be a
bijection of the wires below the width: it is stated with an explicit inverse
`g` and holds on the indices below `2 ^ w`.  Two mutually inverse maps are
asked for rather than a `Function.Bijective`, since the inverse is what the
statement mentions and a placement map supplies it directly.
-/
import VQ.Reversible.Act

namespace VQ
namespace Reversible

/-! ## Bit permutations

`permuteBits` recurses on the wire count so that the kernel reduces it, and it
is built from `|||` rather than from addition so that every proof about it is a
statement about one bit at a time. -/

/-- The index whose bit `f q` is bit `q` of `i`, for each `q < w`, and whose
other bits are zero. -/
def permuteBits (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, i => (if i.testBit w then 1 <<< f w else 0) ||| permuteBits f w i

/-- With no wires there are no bits to place. -/
theorem permuteBits_zero (f : Nat → Nat) (i : Nat) : permuteBits f 0 i = 0 := rfl

/-- The top wire contributes its own bit and the rest recurse. -/

theorem permuteBits_succ (f : Nat → Nat) (w i : Nat) :
    permuteBits f (w + 1) i = (if i.testBit w then 1 <<< f w else 0) ||| permuteBits f w i := rfl

/-- A target bit receiving no source wire below `w` is zero.  This conclusion
requires no hypothesis on `f`. -/
theorem testBit_permuteBits_of_ne {f : Nat → Nat} {w r : Nat} (h : ∀ q, q < w → f q ≠ r)
    (i : Nat) : (permuteBits f w i).testBit r = false := by
  induction w with
  | zero => exact Nat.zero_testBit r
  | succ w ih =>
    rw [permuteBits_succ, Nat.testBit_or, ih (fun q hq => h q (Nat.lt_succ_of_lt hq)),
      Bool.or_false]
    have hne : f w ≠ r := h w (Nat.lt_succ_self w)
    by_cases hb : i.testBit w
    · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne hne]
    · rw [if_neg hb]
      exact Nat.zero_testBit r

/-- Bit `f q` of the permuted index equals bit `q` of the original for every
wire below `w`.  Injectivity below `w` prevents two source wires from being
combined by `|||`. -/
theorem testBit_permuteBits {f : Nat → Nat} {w : Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y) {q : Nat} (hq : q < w) (i : Nat) :
    (permuteBits f w i).testBit (f q) = i.testBit q := by
  induction w with
  | zero => exact absurd hq (Nat.not_lt_zero q)
  | succ w ih =>
    rw [permuteBits_succ, Nat.testBit_or]
    rcases Nat.lt_or_ge q w with hlt | hge
    · have hne : f w ≠ f q := fun e => Nat.ne_of_gt hlt (hinj w q (Nat.lt_succ_self w)
        (Nat.lt_succ_of_lt hlt) e)
      have hfirst : (if i.testBit w then 1 <<< f w else 0).testBit (f q) = false := by
        by_cases hb : i.testBit w
        · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne hne]
        · rw [if_neg hb]; exact Nat.zero_testBit (f q)
      rw [hfirst, Bool.false_or,
        ih (fun x y hx hy => hinj x y (Nat.lt_succ_of_lt hx) (Nat.lt_succ_of_lt hy)) hlt]
    · have hqw : q = w := Nat.le_antisymm (Nat.lt_succ_iff.mp hq) hge
      subst hqw
      have hrest : (permuteBits f q i).testBit (f q) = false := by
        refine testBit_permuteBits_of_ne (fun s hs e => ?_) i
        exact absurd (hinj s q (Nat.lt_succ_of_lt hs) (Nat.lt_succ_self q) e) (Nat.ne_of_lt hs)
      rw [hrest, Bool.or_false]
      by_cases hb : i.testBit q
      · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow_self, hb]
      · rw [if_neg hb, Nat.zero_testBit, Bool.eq_false_iff.mpr hb]

/-- The permuted index lives in the block the image wires address. -/
theorem permuteBits_lt {f : Nat → Nat} {w w' : Nat} (hf : ∀ q, q < w → f q < w') (i : Nat) :
    permuteBits f w i < 2 ^ w' := by
  induction w with
  | zero => exact Nat.two_pow_pos w'
  | succ w ih =>
    rw [permuteBits_succ]
    refine Nat.or_lt_two_pow ?_ (ih (fun q hq => hf q (Nat.lt_succ_of_lt hq)))
    by_cases hb : i.testBit w
    · rw [if_pos hb, Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_of_lt (by omega) (hf w (Nat.lt_succ_self w))
    · rw [if_neg hb]
      exact Nat.two_pow_pos w'

/-- Flipping wire `q` of the index flips bit `f q` of the permuted index.  The
gate cases below use this arithmetic identity. -/
theorem permuteBits_xor {f : Nat → Nat} {w q : Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y) (hq : q < w) (i : Nat) :
    permuteBits f w (i ^^^ (1 <<< q)) = permuteBits f w i ^^^ (1 <<< f q) := by
  refine Nat.eq_of_testBit_eq (fun r => ?_)
  simp only [Nat.testBit_xor, Nat.one_shiftLeft]
  by_cases h : ∃ s, s < w ∧ f s = r
  · obtain ⟨s, hs, rfl⟩ := h
    rw [testBit_permuteBits hinj hs, testBit_permuteBits hinj hs, Nat.testBit_xor,
      Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases he : q = s
    · subst he; simp
    · have : f q ≠ f s := fun e => he (hinj q s hq hs e)
      simp [he, this]
  · have hne : ∀ s, s < w → f s ≠ r := fun s hs e => h ⟨s, hs, e⟩
    rw [testBit_permuteBits_of_ne hne, testBit_permuteBits_of_ne hne,
      Nat.testBit_two_pow_of_ne (hne q hq)]
    rfl

/-! ## The action of a relabelled circuit -/

namespace RGate

/-- One gate, relabelled, acting on the permuted index. -/
theorem act_map {g : RGate} {w : Nat} {f : Nat → Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y) (hg : g.wellFormed w = true) (i : Nat) :
    (g.map f).act (permuteBits f w i) = permuteBits f w (g.act i) := by
  cases g with
  | x q =>
    have hq : q < w := by simpa [RGate.wellFormed] using hg
    exact (permuteBits_xor hinj hq i).symm
  | cx a b =>
    have hab : a < w ∧ b < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1, hg.1.2⟩
    show (if (permuteBits f w i).testBit (f a) then _ else _) = permuteBits f w (if _ then _ else _)
    rw [testBit_permuteBits hinj hab.1]
    by_cases hb : i.testBit a
    · rw [if_pos hb, if_pos hb, permuteBits_xor hinj hab.2]
    · rw [if_neg hb, if_neg hb]
  | ccx a b c =>
    have habc : a < w ∧ b < w ∧ c < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1.1.1.1, hg.1.1.1.1.2, hg.1.1.1.2⟩
    show (if (permuteBits f w i).testBit (f a) && (permuteBits f w i).testBit (f b) then _ else _)
      = permuteBits f w (if _ then _ else _)
    rw [testBit_permuteBits hinj habc.1, testBit_permuteBits hinj habc.2.1]
    by_cases hb : i.testBit a && i.testBit b
    · rw [if_pos hb, if_pos hb, permuteBits_xor hinj habc.2.2]
    · rw [if_neg hb, if_neg hb]

end RGate

/-- A gate list, relabelled, acting on the permuted index. -/
theorem actGates_map {gs : List RGate} {w : Nat} {f : Nat → Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) (i : Nat) :
    actGates (gs.map (RGate.map f)) (permuteBits f w i) = permuteBits f w (actGates gs i) := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, actGates_cons, actGates_cons,
      RGate.act_map hinj (hgs g List.mem_cons_self) i]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (g.act i)

/-- Relabelling permutes the bits of the index.  The relabelled circuit run
on the permuted index is the permutation of the original circuit run on the
original index.  The declared width of the relabelled circuit does not appear,
because `act` does not read it.  What the width is for is well-formedness, which
`RCircuit.wellFormed_relabel` carries. -/
theorem act_relabel {r : RCircuit} {f : Nat → Nat} {w' : Nat}
    (hinj : ∀ x y, x < r.width → y < r.width → f x = f y → x = y)
    (hr : r.wellFormed = true) (i : Nat) :
    act (r.relabel f w') (permuteBits f r.width i) = permuteBits f r.width (act r i) :=
  actGates_map hinj (fun _ hg => RCircuit.wellFormed_mem hr hg) i

/-! ## Conjugation

The equivariance above becomes a conjugation once `f` has an inverse on the
wires below the width.  `permuteBits g w` is then the inverse of
`permuteBits f w` on the indices below `2 ^ w`, and the action of the relabelled
circuit is the action of the original with the two applied on either side. -/

/-- Two mutually inverse wire maps give mutually inverse bit permutations on the
block.  The range hypotheses are what confine the result to the block.  Without
them the two permutations compose to the identity on the wires and to zero
elsewhere. -/
theorem permuteBits_permuteBits {f g : Nat → Nat} {w : Nat}
    (hfw : ∀ q, q < w → f q < w) (hgw : ∀ q, q < w → g q < w)
    (hgf : ∀ q, q < w → g (f q) = q) (hfg : ∀ q, q < w → f (g q) = q)
    {i : Nat} (hi : i < 2 ^ w) : permuteBits g w (permuteBits f w i) = i := by
  have hfinj : ∀ x y, x < w → y < w → f x = f y → x = y := by
    intro x y hx hy e
    rw [← hgf x hx, ← hgf y hy, e]
  have hginj : ∀ x y, x < w → y < w → g x = g y → x = y := by
    intro x y hx hy e
    rw [← hfg x hx, ← hfg y hy, e]
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rcases Nat.lt_or_ge b w with hb | hb
  · have hfb : f b < w := hfw b hb
    have : (permuteBits g w (permuteBits f w i)).testBit (g (f b))
        = (permuteBits f w i).testBit (f b) := testBit_permuteBits hginj hfb _
    rw [hgf b hb] at this
    rw [this, testBit_permuteBits hfinj hb]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (permuteBits_lt hgw _)
      (Nat.pow_le_pow_right (by omega) hb)),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hb))]

/-- The action of a relabelled circuit is the conjugate of its action.
Stated on the block, since `permuteBits g` inverts `permuteBits f` there and
nowhere else. -/
theorem act_relabel_conj {r : RCircuit} {f g : Nat → Nat} {w' : Nat}
    (hfw : ∀ q, q < r.width → f q < r.width) (hgw : ∀ q, q < r.width → g q < r.width)
    (hgf : ∀ q, q < r.width → g (f q) = q) (hfg : ∀ q, q < r.width → f (g q) = q)
    (hr : r.wellFormed = true) {j : Nat} (hj : j < 2 ^ r.width) :
    act (r.relabel f w') j = permuteBits f r.width (act r (permuteBits g r.width j)) := by
  have hfinj : ∀ x y, x < r.width → y < r.width → f x = f y → x = y := by
    intro x y hx hy e
    rw [← hgf x hx, ← hgf y hy, e]
  have hround : permuteBits f r.width (permuteBits g r.width j) = j :=
    permuteBits_permuteBits hgw hfw hfg hgf hj
  calc act (r.relabel f w') j
      = act (r.relabel f w') (permuteBits f r.width (permuteBits g r.width j)) := by rw [hround]
    _ = permuteBits f r.width (act r (permuteBits g r.width j)) :=
        act_relabel hfinj hr (permuteBits g r.width j)

end Reversible
end VQ
