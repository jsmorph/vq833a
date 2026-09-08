/-
Semantic placement of a program under an injective wire relabelling.
-/
import VQ.Program.Relabel
import VQ.Program.Realise

namespace VQ
namespace Semantics

open Algebra

/-- Replace the wires selected by `f` with the low `width` bits of `source`.
All other bits retain their value from `ambient`. -/
def replaceBits (f : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, ambient => ambient
  | width + 1, source, ambient =>
      writeBit (replaceBits f width source ambient) (f width)
        (source.testBit width)

theorem testBit_replaceBits {f : Nat → Nat} {width source ambient q : Nat}
    (hq : q < width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    (replaceBits f width source ambient).testBit (f q) = source.testBit q := by
  induction width with
  | zero => omega
  | succ width ih =>
    rw [replaceBits]
    by_cases hqw : q = width
    · subst q
      exact testBit_writeBit _ _ _
    · rw [testBit_writeBit_of_ne]
      · exact ih (by omega) (fun x y hx hy hxy => hinj x y (by omega) (by omega) hxy)
      · exact fun h => hqw (hinj q width (by omega) (by omega) h)

theorem testBit_replaceBits_outside {f : Nat → Nat} {width source ambient r : Nat}
    (hout : ∀ q, q < width → r ≠ f q) :
    (replaceBits f width source ambient).testBit r = ambient.testBit r := by
  induction width with
  | zero => rfl
  | succ width ih =>
    rw [replaceBits, testBit_writeBit_of_ne (hout width (by omega))]
    exact ih (fun q hq => hout q (by omega))

/-- Read the selected wires into a packed low-bit index. -/
def sourceIndex (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, i =>
      writeBit (sourceIndex f width i) width (i.testBit (f width))

theorem testBit_sourceIndex {f : Nat → Nat} {width i q : Nat}
    (hq : q < width) :
    (sourceIndex f width i).testBit q = i.testBit (f q) := by
  induction width with
  | zero => omega
  | succ width ih =>
    rw [sourceIndex]
    by_cases hqw : q = width
    · subst q
      exact testBit_writeBit _ _ _
    · rw [testBit_writeBit_of_ne hqw]
      exact ih (by omega)

theorem testBit_sourceIndex_of_le {f : Nat → Nat} {width i q : Nat}
    (hq : width ≤ q) : (sourceIndex f width i).testBit q = false := by
  induction width with
  | zero => simp [sourceIndex]
  | succ width ih =>
    rw [sourceIndex, testBit_writeBit_of_ne (by omega)]
    exact ih (by omega)

theorem sourceIndex_lt (f : Nat → Nat) (width i : Nat) :
    sourceIndex f width i < 2 ^ width := by
  apply Reversible.lt_two_pow_of_testBit
  intro q hq
  exact testBit_sourceIndex_of_le hq

theorem sourceIndex_id_eq_readField (width i : Nat) :
    sourceIndex id width i = Reversible.readField i 0 width := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < width
  · rw [testBit_sourceIndex hq, Reversible.testBit_readField]
    simp [hq]
  · rw [testBit_sourceIndex_of_le (Nat.le_of_not_gt hq),
      Reversible.testBit_readField]
    simp [hq]

/-- Reading a contiguous source field after extraction reads the corresponding
contiguous field of the ambient register. -/
theorem readField_sourceIndex {f : Nat → Nat}
    {sourceWidth sourceOffset ambientOffset len i : Nat}
    (hfit : sourceOffset + len ≤ sourceWidth)
    (hmap : ∀ b, b < len →
      f (sourceOffset + b) = ambientOffset + b) :
    Reversible.readField (sourceIndex f sourceWidth i) sourceOffset len =
      Reversible.readField i ambientOffset len := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Reversible.testBit_readField, Reversible.testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    rw [testBit_sourceIndex (by omega), hmap b hb]
  · simp [hb]

theorem sourceIndex_replaceBits {f : Nat → Nat} {width source ambient : Nat}
    (hsource : source < 2 ^ width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    sourceIndex f width (replaceBits f width source ambient) = source := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < width
  · rw [testBit_sourceIndex hq, testBit_replaceBits hq hinj]
  · rw [testBit_sourceIndex_of_le (by omega)]
    have hpow : 2 ^ width ≤ 2 ^ q :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hq)
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hsource hpow)).symm

theorem replaceBits_sourceIndex_self {f : Nat → Nat} {width i : Nat}
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    replaceBits f width (sourceIndex f width i) i = i := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases himage : ∃ q, q < width ∧ r = f q
  · obtain ⟨q, hq, rfl⟩ := himage
    rw [testBit_replaceBits hq hinj, testBit_sourceIndex hq]
  · apply testBit_replaceBits_outside
    intro q hq h
    exact himage ⟨q, hq, h⟩

theorem replaceBits_replaceBits {f : Nat → Nat} {width outer inner ambient : Nat}
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    replaceBits f width outer (replaceBits f width inner ambient) =
      replaceBits f width outer ambient := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases himage : ∃ q, q < width ∧ r = f q
  · obtain ⟨q, hq, rfl⟩ := himage
    rw [testBit_replaceBits hq hinj, testBit_replaceBits hq hinj]
  · have hout : ∀ q, q < width → r ≠ f q := by
      intro q hq h
      exact himage ⟨q, hq, h⟩
    rw [testBit_replaceBits_outside hout,
      testBit_replaceBits_outside hout, testBit_replaceBits_outside hout]

private theorem writeBit_lt' {i q totalWidth : Nat} {value : Bool}
    (hq : q < totalWidth) (hi : i < 2 ^ totalWidth) :
    writeBit i q value < 2 ^ totalWidth := by
  apply Reversible.lt_two_pow_of_testBit
  intro r hr
  rw [testBit_writeBit_of_ne (by omega)]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hr))

theorem replaceBits_lt {f : Nat → Nat} {width totalWidth source ambient : Nat}
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hambient : ambient < 2 ^ totalWidth) :
    replaceBits f width source ambient < 2 ^ totalWidth := by
  induction width with
  | zero => exact hambient
  | succ width ih =>
    rw [replaceBits]
    apply writeBit_lt' (hlt width (by omega))
    exact ih (fun q hq => hlt q (by omega))

theorem replaceBits_id_eq_writeField
    (width source ambient : Nat) :
    replaceBits id width source ambient =
      Reversible.writeField ambient 0 width source := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < width
  · change (replaceBits id width source ambient).testBit (id q) = _
    rw [testBit_replaceBits hq (by
        intro x y _ _ hxy
        exact hxy),
      Reversible.testBit_writeField_inside (Nat.zero_le q) (by omega)]
    simp
  · rw [testBit_replaceBits_outside (by
        intro x hx hxy
        simp only [id_eq] at hxy
        omega),
      Reversible.testBit_writeField_outside (Or.inr (by omega))]

theorem replaceBits_xor {f : Nat → Nat} {width source ambient q : Nat}
    (hq : q < width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    replaceBits f width (source ^^^ (1 <<< q)) ambient =
      replaceBits f width source ambient ^^^ (1 <<< f q) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases himage : ∃ k, k < width ∧ r = f k
  · obtain ⟨k, hk, rfl⟩ := himage
    by_cases hkq : k = q
    · subst k
      rw [testBit_replaceBits hq hinj, testBit_xor_self,
        testBit_xor_self, testBit_replaceBits hq hinj]
    · have hfk : f k ≠ f q := fun h => hkq (hinj k q hk hq h)
      rw [testBit_replaceBits hk hinj, testBit_xor_of_ne hkq,
        testBit_xor_of_ne hfk, testBit_replaceBits hk hinj]
  · have hout : ∀ k, k < width → r ≠ f k := by
      intro k hk h
      exact himage ⟨k, hk, h⟩
    rw [testBit_replaceBits_outside hout,
      testBit_xor_of_ne (hout q hq), testBit_replaceBits_outside hout]

theorem replaceBits_cx {f : Nat → Nat} {width source ambient a b : Nat}
    (ha : a < width) (hb : b < width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    replaceBits f width (cxIndex a b source) ambient =
      cxIndex (f a) (f b) (replaceBits f width source ambient) := by
  rw [cxIndex, cxIndex, testBit_replaceBits ha hinj]
  by_cases hbit : source.testBit a = true
  · rw [if_pos hbit, if_pos hbit, replaceBits_xor hb hinj]
  · rw [if_neg hbit, if_neg hbit]

/-- Embed the first `2^width` amplitudes into the basis slice obtained by
replacing the selected wires of `ambient`. -/
def placeVec (f : Nat → Nat) (width ambient : Nat) (u : Vec d) : Vec d :=
  vsum (2 ^ width) fun i => u i • basis (replaceBits f width i ambient)

theorem placeVec_zero (f : Nat → Nat) (width ambient : Nat) :
    placeVec f width ambient (Vec.zero d) = Vec.zero d := by
  apply Vec.ext
  intro i
  simp only [placeVec, vsum_apply, Vec.zero_apply, Vec.smul_apply, Dy.zero_mul]
  exact dsum_eq_zero (fun _ _ => rfl)

theorem placeVec_add (f : Nat → Nat) (width ambient : Nat) (u v : Vec d) :
    placeVec f width ambient (u + v) =
      placeVec f width ambient u + placeVec f width ambient v := by
  apply Vec.ext
  intro i
  show dsum (2 ^ width)
      (fun k => (u k + v k) * basis (replaceBits f width k ambient) i) = _
  rw [show (fun k => (u k + v k) * basis (replaceBits f width k ambient) i) =
      fun k => u k * basis (replaceBits f width k ambient) i +
        v k * basis (replaceBits f width k ambient) i by
      funext k; exact Dy.right_distrib _ _ _, dsum_add]
  rfl

theorem placeVec_smul (f : Nat → Nat) (width ambient : Nat)
    (a : Dy d) (u : Vec d) :
    placeVec f width ambient (a • u) = a • placeVec f width ambient u := by
  apply Vec.ext
  intro i
  show dsum (2 ^ width)
      (fun k => (a * u k) * basis (replaceBits f width k ambient) i) =
    a * dsum (2 ^ width)
      (fun k => u k * basis (replaceBits f width k ambient) i)
  rw [dsum_mul_left]
  exact dsum_congr (fun k _ => Dy.mul_assoc _ _ _)

theorem placeVec_neg (f : Nat → Nat) (width ambient : Nat) (u : Vec d) :
    placeVec f width ambient (-u) = -placeVec f width ambient u := by
  have hsource : -u = (-Dy.one d) • u := by
    apply Vec.ext
    intro i
    exact neg_eq_neg_one_mul (u i)
  have htarget : -placeVec f width ambient u =
      (-Dy.one d) • placeVec f width ambient u := by
    apply Vec.ext
    intro i
    exact neg_eq_neg_one_mul (placeVec f width ambient u i)
  rw [hsource, placeVec_smul, ← htarget]

theorem placeVec_sub (f : Nat → Nat) (width ambient : Nat) (u v : Vec d) :
    placeVec f width ambient (u - v) =
      placeVec f width ambient u - placeVec f width ambient v := by
  change placeVec f width ambient (u + -v) =
    placeVec f width ambient u + -placeVec f width ambient v
  rw [placeVec_add, placeVec_neg]

theorem placeVec_basis {f : Nat → Nat} {width ambient j : Nat}
    (hj : j < 2 ^ width) :
    placeVec f width ambient (basis j : Vec d) =
      basis (replaceBits f width j ambient) := by
  apply Vec.ext
  intro i
  show dsum (2 ^ width)
      (fun k => basis j k * basis (replaceBits f width k ambient) i) =
    basis (replaceBits f width j ambient) i
  rw [dsum_eq_single hj]
  · rw [basis_self, Dy.one_mul]
  · intro k _ hkj
    rw [basis_of_ne hkj, Dy.zero_mul]

theorem placeVec_vsum (f : Nat → Nat) (width ambient n : Nat)
    (u : Nat → Vec d) :
    placeVec f width ambient (vsum n u) =
      vsum n (fun k => placeVec f width ambient (u k)) := by
  induction n with
  | zero => exact placeVec_zero f width ambient
  | succ n ih =>
    rw [vsum_succ, placeVec_add, ih, vsum_succ]

theorem placeVec_id_zero {width : Nat} {u : Vec d}
    (hu : WFVec (2 ^ width) u) :
    placeVec id width 0 u = u := by
  rw [eq_vsum_basis hu, placeVec_vsum]
  apply vsum_congr
  intro j hj
  rw [placeVec_smul, placeVec_basis hj,
    replaceBits_id_eq_writeField,
    Reversible.writeField_zero_eq (Nat.two_pow_pos width) hj]

theorem gateVec_vsum (level totalWidth n : Nat) (g : Gate)
    (u : Nat → Vec (deg level)) :
    gateVec level totalWidth g (vsum n u) =
      vsum n (fun k => gateVec level totalWidth g (u k)) := by
  induction n with
  | zero =>
    rw [vsum_zero, gateVec_zero, vsum_zero]
  | succ n ih =>
    rw [vsum_succ, gateVec_add, ih, vsum_succ]

theorem xor_lt_two_pow {width i q : Nat} (hi : i < 2 ^ width)
    (hq : q < width) : i ^^^ (1 <<< q) < 2 ^ width := by
  apply Nat.xor_lt_two_pow hi
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_of_lt (by omega) hq

theorem gateVec_placeVec_basis {level width totalWidth : Nat}
    {f : Nat → Nat} {ambient j : Nat} {g : Gate}
    (hg : g.wellFormedAt level width = true)
    (hj : j < 2 ^ width)
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    gateVec level totalWidth (g.map f)
        (placeVec f width ambient (basis j)) =
      placeVec f width ambient (gateVec level width g (basis j)) := by
  cases g with
  | x q =>
    simp only [Gate.wellFormedAt, decide_eq_true_eq] at hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_x (hlt q hg), apply_x hg,
      placeVec_basis (xor_lt_two_pow hj hg), replaceBits_xor hg hinj]
  | h q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_h (hlt q hq) hl, apply_h hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_sub,
        placeVec_basis (xor_lt_two_pow hj hq), placeVec_basis hj,
        replaceBits_xor hq hinj]
    · rw [if_neg hbit, if_neg hbit, placeVec_smul, placeVec_add,
        placeVec_basis (xor_lt_two_pow hj hq), placeVec_basis hj,
        replaceBits_xor hq hinj]
  | y q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_y (hlt q hq) hl, apply_y hq hl,
      testBit_replaceBits hq hinj, placeVec_smul,
      placeVec_basis (xor_lt_two_pow hj hq), replaceBits_xor hq hinj]
  | z q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_z (hlt q hq) hl, apply_z hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | s q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_s (hlt q hq) hl, apply_s hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | sdg q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_sdg (hlt q hq) hl, apply_sdg hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | t q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_t (hlt q hq) hl, apply_t hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | tdg q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hq, hl⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_tdg (hlt q hq) hl, apply_tdg hq hl,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | p k q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hq, h4⟩, hk⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_p (hlt q hq) h4 hk, apply_p hq h4 hk,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | pdg k q =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hq, h4⟩, hk⟩ := hg
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_pdg (hlt q hq) h4 hk, apply_pdg hq h4 hk,
      testBit_replaceBits hq hinj]
    by_cases hbit : j.testBit q = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | cx a b =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hg
    obtain ⟨⟨ha, hb⟩, hab⟩ := hg
    have hfab : f a ≠ f b := fun h => hab (hinj a b ha hb h)
    simp only [Gate.map]
    rw [placeVec_basis hj, apply_cx (hlt a ha) (hlt b hb) hfab,
      apply_cx ha hb hab, testBit_replaceBits ha hinj]
    by_cases hbit : j.testBit a = true
    · rw [if_pos hbit, if_pos hbit,
        placeVec_basis (xor_lt_two_pow hj hb), replaceBits_xor hb hinj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]
  | ccz a b c =>
    simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hg
    obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩, hl⟩ := hg
    have hfab : f a ≠ f b := fun h => hab (hinj a b ha hb h)
    have hfbc : f b ≠ f c := fun h => hbc (hinj b c hb hc h)
    have hfac : f a ≠ f c := fun h => hac (hinj a c ha hc h)
    simp only [Gate.map]
    rw [placeVec_basis hj,
      apply_ccz (hlt a ha) (hlt b hb) (hlt c hc) hfab hfbc hfac hl,
      apply_ccz ha hb hc hab hbc hac hl,
      testBit_replaceBits ha hinj, testBit_replaceBits hb hinj,
      testBit_replaceBits hc hinj]
    by_cases hbit : (j.testBit a && j.testBit b && j.testBit c) = true
    · rw [if_pos hbit, if_pos hbit, placeVec_smul, placeVec_basis hj]
    · rw [if_neg hbit, if_neg hbit, placeVec_basis hj]

theorem gateVec_placeVec {level width totalWidth : Nat}
    {f : Nat → Nat} {ambient : Nat} {g : Gate} {u : Vec (deg level)}
    (hg : g.wellFormedAt level width = true)
    (hu : WFVec (2 ^ width) u)
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    gateVec level totalWidth (g.map f) (placeVec f width ambient u) =
      placeVec f width ambient (gateVec level width g u) := by
  rw [eq_vsum_basis hu, placeVec_vsum, gateVec_vsum,
    gateVec_vsum, placeVec_vsum]
  apply vsum_congr
  intro j hj
  rw [placeVec_smul, gateVec_smul, gateVec_smul, placeVec_smul,
    gateVec_placeVec_basis hg hj hlt hinj]

theorem projVec_zero (q : Nat) (value : Bool) :
    projVec q value (Vec.zero d) = Vec.zero d := by
  apply Vec.ext
  intro i
  by_cases hbit : i.testBit q = value <;> simp [projVec, hbit]

theorem projVec_basis (q : Nat) (value : Bool) (j : Nat) :
    projVec q value (basis j : Vec d) =
      if j.testBit q = value then basis j else Vec.zero d := by
  apply Vec.ext
  intro i
  by_cases hij : i = j
  · subst i
    by_cases hbit : j.testBit q = value <;>
      simp [projVec, hbit, basis_self]
  · by_cases hbit : j.testBit q = value
    · rw [if_pos hbit]
      simp [projVec, basis, hij]
    · rw [if_neg hbit]
      simp [projVec, basis, hij]

theorem projVec_vsum (q : Nat) (value : Bool) (n : Nat) (u : Nat → Vec d) :
    projVec q value (vsum n u) =
      vsum n (fun k => projVec q value (u k)) := by
  induction n with
  | zero => rw [vsum_zero, projVec_zero, vsum_zero]
  | succ n ih => rw [vsum_succ, projVec_add, ih, vsum_succ]

theorem projVec_placeVec_basis {d : Nat} {f : Nat → Nat}
    {width ambient q j : Nat}
    {value : Bool} (hq : q < width) (hj : j < 2 ^ width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    projVec (f q) value (placeVec f width ambient (basis j : Vec d)) =
      placeVec f width ambient (projVec q value (basis j : Vec d)) := by
  rw [placeVec_basis hj, projVec_basis, projVec_basis,
    testBit_replaceBits hq hinj]
  by_cases hbit : j.testBit q = value
  · rw [if_pos hbit, if_pos hbit, placeVec_basis hj]
  · rw [if_neg hbit, if_neg hbit, placeVec_zero]

theorem projVec_placeVec {f : Nat → Nat} {width ambient q : Nat}
    {value : Bool} {u : Vec d} (hq : q < width)
    (hu : WFVec (2 ^ width) u)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    projVec (f q) value (placeVec f width ambient u) =
      placeVec f width ambient (projVec q value u) := by
  rw [eq_vsum_basis hu, placeVec_vsum, projVec_vsum,
    projVec_vsum, placeVec_vsum]
  apply vsum_congr
  intro j hj
  rw [placeVec_smul, projVec_smul, projVec_smul, placeVec_smul,
    projVec_placeVec_basis hq hj hinj]

theorem flipVec_placeVec {f : Nat → Nat} {width totalWidth ambient q : Nat}
    {u : Vec (deg level)} (hq : q < width) (hu : WFVec (2 ^ width) u)
    (hlt : ∀ r, r < width → f r < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    flipVec (f q) (placeVec f width ambient u) =
      placeVec f width ambient (flipVec q u) := by
  have h := gateVec_placeVec (level := level) (g := Gate.x q)
    (ambient := ambient) (by simp [Gate.wellFormedAt, hq]) hu hlt hinj
  simpa [gateVec, Gate.wellFormedAt, Gate.map, hq, hlt q hq, gateAction] using h

theorem resetVec_placeVec {f : Nat → Nat} {width totalWidth ambient q : Nat}
    {u : Vec (deg level)} (hq : q < width) (hu : WFVec (2 ^ width) u)
    (hlt : ∀ r, r < width → f r < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    flipVec (f q) (projVec (f q) true (placeVec f width ambient u)) =
      placeVec f width ambient (flipVec q (projVec q true u)) := by
  rw [projVec_placeVec hq hu hinj,
    flipVec_placeVec hq (wfVec_projVec true hu) hlt hinj]

/-- Place the quantum state of a branch while retaining its complete classical
execution record. -/
def placeBranch (f : Nat → Nat) (width ambient : Nat) (b : Branch d) : Branch d :=
  { outcomes := b.outcomes
    creg := b.creg
    state := placeVec f width ambient b.state
    input := b.input }

@[simp] theorem placeBranch_state (f : Nat → Nat) (width ambient : Nat)
    (b : Branch d) :
    (placeBranch f width ambient b).state =
      placeVec f width ambient b.state := rfl

@[simp] theorem placeBranch_outcomes (f : Nat → Nat) (width ambient : Nat)
    (b : Branch d) : (placeBranch f width ambient b).outcomes = b.outcomes := rfl

@[simp] theorem placeBranch_creg (f : Nat → Nat) (width ambient : Nat)
    (b : Branch d) : (placeBranch f width ambient b).creg = b.creg := rfl

@[simp] theorem placeBranch_input (f : Nat → Nat) (width ambient : Nat)
    (b : Branch d) : (placeBranch f width ambient b).input = b.input := rfl

theorem placeVec_sourceIndex_basis {f : Nat → Nat} {width i : Nat}
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    placeVec f width i (basis (sourceIndex f width i) : Vec d) = basis i := by
  rw [placeVec_basis (sourceIndex_lt f width i), replaceBits_sourceIndex_self hinj]

theorem placeBranch_sourceIndex_basis {f : Nat → Nat} {width i : Nat}
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y)
    (rec : List Bool) (cr input : Nat) :
    placeBranch f width i
        (Branch.mk rec cr (basis (sourceIndex f width i) : Vec d) input) =
      Branch.mk rec cr (basis i) input := by
  simp only [placeBranch]
  rw [placeVec_sourceIndex_basis hinj]

private theorem flatMap_congr' {α β : Type} {xs : List α}
    {f g : α → List β} (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      ih (fun y hy => h y (by simp [hy]))]

private theorem runOp_relabel_runOps {level width totalWidth inputBits cbits : Nat}
    {f : Nat → Nat} (ambient : Nat)
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    (∀ o : Op, ∀ b : Branch (deg level),
      Program.opWellFormed level width inputBits cbits o = true →
      WFVec (2 ^ width) b.state →
      runOp level totalWidth (o.relabel f) (placeBranch f width ambient b) =
        (runOp level width o b).map (placeBranch f width ambient)) ∧
    (∀ ops : List Op, ∀ b : Branch (deg level),
      Program.opsWellFormed level width inputBits cbits ops = true →
      WFVec (2 ^ width) b.state →
      runOps level totalWidth (Op.relabelAll f ops)
          (placeBranch f width ambient b) =
        (runOps level width ops b).map (placeBranch f width ambient)) := by
  refine opInduction (fun g b hw hb => ?_) (fun q c b hw hb => ?_)
    (fun q b hw hb => ?_) (fun c value b hw hb => ?_)
    (fun c b hw hb => ?_) (fun c t e ht he b hw hb => ?_)
    (fun b _ _ => rfl) (fun o ops ho hos b hw hb => ?_)
  · simp only [Op.relabel, runOp_gate, List.map_cons, List.map_nil, placeBranch]
    rw [gateVec_placeVec hw hb hlt hinj]
  · simp only [Program.opWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [Op.relabel, runOp_measure, List.map_cons, List.map_nil, placeBranch]
    rw [projVec_placeVec hw.1 hb hinj, projVec_placeVec hw.1 hb hinj]
  · simp only [Program.opWellFormed, decide_eq_true_eq] at hw
    simp only [Op.relabel, runOp_reset, List.map_cons, List.map_nil, placeBranch]
    rw [projVec_placeVec hw hb hinj, resetVec_placeVec hw hb hlt hinj]
  · rfl
  · rfl
  · simp only [Program.opWellFormed, Bool.and_eq_true] at hw
    obtain ⟨⟨_, htrue⟩, hfalse⟩ := hw
    simp only [Op.relabel, runOp_branch]
    dsimp +instances only [placeBranch]
    by_cases hc : c.read b.input b.creg = true
    · rw [if_pos hc, if_pos hc]
      exact ht b htrue hb
    · rw [if_neg hc, if_neg hc]
      exact he b hfalse hb
  · simp only [Program.opsWellFormed, Bool.and_eq_true] at hw
    obtain ⟨hfirst, hrest⟩ := hw
    rw [Op.relabelAll, runOps_cons, runOps_cons, ho b hfirst hb,
      List.flatMap_map, List.map_flatMap]
    apply flatMap_congr'
    intro x hx
    apply hos x hrest
    exact (wfVec_runOp_runOps level width).1 o b hb x hx

theorem runOp_relabel {level width totalWidth inputBits cbits : Nat}
    {f : Nat → Nat} {ambient : Nat} {o : Op} {b : Branch (deg level)}
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y)
    (ho : Program.opWellFormed level width inputBits cbits o = true)
    (hb : WFVec (2 ^ width) b.state) :
    runOp level totalWidth (o.relabel f) (placeBranch f width ambient b) =
      (runOp level width o b).map (placeBranch f width ambient) :=
  (runOp_relabel_runOps ambient hlt hinj).1 o b ho hb

theorem runOps_relabel {level width totalWidth inputBits cbits : Nat}
    {f : Nat → Nat} {ambient : Nat} {ops : List Op}
    {b : Branch (deg level)}
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y)
    (hops : Program.opsWellFormed level width inputBits cbits ops = true)
    (hb : WFVec (2 ^ width) b.state) :
    runOps level totalWidth (Op.relabelAll f ops)
        (placeBranch f width ambient b) =
      (runOps level width ops b).map (placeBranch f width ambient) :=
  (runOp_relabel_runOps ambient hlt hinj).2 ops b hops hb

theorem runProgram_relabel {level totalWidth : Nat} {f : Nat → Nat}
    {ambient : Nat} {p : Program} {b : Branch (deg level)}
    (hlt : ∀ q, q < p.width → f q < totalWidth)
    (hinj : ∀ x y, x < p.width → y < p.width → f x = f y → x = y)
    (hp : p.wellFormed level = true)
    (hb : WFVec (2 ^ p.width) b.state) :
    runOps level totalWidth (Program.relabel f totalWidth p).ops
        (placeBranch f p.width ambient b) =
      (runOps level p.width p.ops b).map (placeBranch f p.width ambient) := by
  apply runOps_relabel hlt hinj
  · exact hp
  · exact hb

theorem runProgram_relabel_basis {level totalWidth : Nat} {f : Nat → Nat}
    {p : Program} (input i : Nat)
    (hlt : ∀ q, q < p.width → f q < totalWidth)
    (hinj : ∀ x y, x < p.width → y < p.width → f x = f y → x = y)
    (hp : p.wellFormed level = true) :
    runProgram level (Program.relabel f totalWidth p) input (basis i) =
      (runProgram level p input (basis (sourceIndex f p.width i))).map
        (placeBranch f p.width i) := by
  have hrun := runOps_relabel (level := level) (width := p.width)
    (totalWidth := totalWidth) (inputBits := p.inputBits) (cbits := p.cbits)
    (f := f) (ambient := i) (ops := p.ops)
    (b := Branch.mk [] 0 (basis (sourceIndex f p.width i)) input)
    hlt hinj hp (wfVec_basis (sourceIndex_lt f p.width i))
  rw [placeBranch_sourceIndex_basis (d := deg level) hinj [] 0 input] at hrun
  simpa [runProgram, Program.relabel] using hrun

/-- An output map transported to the selected wires of a larger basis index. -/
def placedOut (f : Nat → Nat) (width : Nat) (out : Nat → Nat) (i : Nat) : Nat :=
  replaceBits f width (out (sourceIndex f width i)) i

/-- Agreement between input and output on every wire outside the selected
source register. -/
def OutsideBitsPreserved (f : Nat → Nat) (width input output : Nat) : Prop :=
  ∀ r, (∀ q, q < width → r ≠ f q) → output.testBit r = input.testBit r

theorem replaceBits_outsideBitsPreserved (f : Nat → Nat) (width source input : Nat) :
    OutsideBitsPreserved f width input (replaceBits f width source input) := by
  intro r hout
  exact testBit_replaceBits_outside hout

theorem placedOut_outsideBitsPreserved (f : Nat → Nat) (width : Nat)
    (out : Nat → Nat) (i : Nat) :
    OutsideBitsPreserved f width i (placedOut f width out i) :=
  replaceBits_outsideBitsPreserved f width _ i

theorem sourceIndex_placedOut {f : Nat → Nat} {width : Nat}
    {out : Nat → Nat} {i : Nat}
    (hout : out (sourceIndex f width i) < 2 ^ width)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y) :
    sourceIndex f width (placedOut f width out i) =
      out (sourceIndex f width i) :=
  sourceIndex_replaceBits hout hinj

theorem placedOut_lt {f : Nat → Nat} {width totalWidth : Nat}
    {out : Nat → Nat} {i : Nat}
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hi : i < 2 ^ totalWidth) :
    placedOut f width out i < 2 ^ totalWidth :=
  replaceBits_lt hlt hi

namespace RegSpec

/-- Transport a register relation to selected wires of a larger register. -/
def place (f : Nat → Nat) (totalWidth : Nat) (S : RegSpec) : RegSpec where
  width := totalWidth
  Pre i := S.Pre (sourceIndex f S.width i)
  Post i j :=
    S.Post (sourceIndex f S.width i) (sourceIndex f S.width j) ∧
      OutsideBitsPreserved f S.width i j

@[simp] theorem place_width (f : Nat → Nat) (totalWidth : Nat) (S : RegSpec) :
    (place f totalWidth S).width = totalWidth := rfl

@[simp] theorem place_pre (f : Nat → Nat) (totalWidth : Nat) (S : RegSpec)
    (i : Nat) :
    (place f totalWidth S).Pre i = S.Pre (sourceIndex f S.width i) := rfl

@[simp] theorem place_post (f : Nat → Nat) (totalWidth : Nat) (S : RegSpec)
    (i j : Nat) :
    (place f totalWidth S).Post i j =
      (S.Post (sourceIndex f S.width i) (sourceIndex f S.width j) ∧
        OutsideBitsPreserved f S.width i j) := rfl

end RegSpec

theorem ImplementsU.relabel {level width totalWidth input inputBits cbits : Nat}
    {f : Nat → Nat} {dom : Nat → Prop} {out : Nat → Nat}
    {c : Dy (deg level)} {ops : List Op}
    (h : ImplementsU level width input dom out c ops)
    (hops : Program.opsWellFormed level width inputBits cbits ops = true)
    (hlt : ∀ q, q < width → f q < totalWidth)
    (hinj : ∀ x y, x < width → y < width → f x = f y → x = y)
    (hout : ∀ i, i < 2 ^ width → dom i → out i < 2 ^ width) :
    ImplementsU level totalWidth input
      (fun i => dom (sourceIndex f width i)) (placedOut f width out) c
      (Op.relabelAll f ops) := by
  intro i hi hdom rec cr b hb
  let source := sourceIndex f width i
  have hsource : source < 2 ^ width := sourceIndex_lt f width i
  have hrun := runOps_relabel (level := level) (width := width)
    (totalWidth := totalWidth) (inputBits := inputBits) (cbits := cbits)
    (f := f) (ambient := i) (ops := ops)
    (b := Branch.mk rec cr (basis source) input)
    hlt hinj hops (wfVec_basis hsource)
  have hstart : placeBranch f width i
      (Branch.mk rec cr (basis source : Vec (deg level)) input) =
      Branch.mk rec cr (basis i) input :=
    placeBranch_sourceIndex_basis hinj rec cr input
  rw [hstart] at hrun
  rw [hrun, List.mem_map] at hb
  obtain ⟨sourceBranch, hsourceBranch, rfl⟩ := hb
  have hstate := h source hsource hdom rec cr sourceBranch hsourceBranch
  simp only [placeBranch]
  rw [hstate, placeVec_smul,
    placeVec_basis (hout source hsource hdom)]
  rfl

theorem RealisesAt.relabel {level input totalWidth : Nat}
    {f : Nat → Nat} {S : RegSpec} {p : Program}
    (h : RealisesAt level input S p)
    (hlt : ∀ q, q < S.width → f q < totalWidth)
    (hinj : ∀ x y, x < S.width → y < S.width → f x = f y → x = y) :
    RealisesAt level input (S.place f totalWidth)
      (Program.relabel f totalWidth p) := by
  obtain ⟨hwidth, hwf, hinput, out, amp, hreal⟩ := h
  have hltp : ∀ q, q < p.width → f q < totalWidth := by
    intro q hq
    exact hlt q (by rwa [← hwidth])
  have hinjp : ∀ x y, x < p.width → y < p.width → f x = f y → x = y := by
    intro x y hx hy hxy
    exact hinj x y (by rwa [← hwidth]) (by rwa [← hwidth]) hxy
  have hwfPlaced : (Program.relabel f totalWidth p).wellFormed level = true :=
    Program.wellFormed_relabel hltp hinjp hwf
  refine ⟨rfl, hwfPlaced, ?_, placedOut f S.width out, amp, ?_⟩
  · simpa [Program.relabel] using hinput
  · intro i hi hpre
    let source := sourceIndex f S.width i
    have hsource : source < 2 ^ S.width := sourceIndex_lt f S.width i
    obtain ⟨hpost, hout, hbranches, _⟩ := hreal source hsource hpre
    have hsourceOut : sourceIndex f S.width (placedOut f S.width out i) =
        out source := sourceIndex_placedOut hout hinj
    refine ⟨?_, placedOut_lt hlt hi, ?_, totalProb_basis level _ hwfPlaced input hi⟩
    · exact ⟨by simpa [source, hsourceOut] using hpost,
        placedOut_outsideBitsPreserved f S.width out i⟩
    · intro b hb
      have hrun := runProgram_relabel_basis (level := level)
        (totalWidth := totalWidth) (f := f) (p := p) input i hltp hinjp hwf
      have hsourceEq : sourceIndex f p.width i = source := by
        simp [source, hwidth]
      rw [hsourceEq] at hrun
      rw [hrun, List.mem_map] at hb
      obtain ⟨sourceBranch, hsourceBranch, rfl⟩ := hb
      have hstate := hbranches sourceBranch hsourceBranch
      have houtp : out source < 2 ^ p.width := by
        rwa [hwidth]
      simp only [placeBranch]
      rw [hstate, placeVec_smul, placeVec_basis houtp]
      simp [placedOut, source, hwidth]

theorem Realises.relabel {level totalWidth : Nat}
    {f : Nat → Nat} {S : RegSpec} {p : Program}
    (h : Realises level S p)
    (hlt : ∀ q, q < S.width → f q < totalWidth)
    (hinj : ∀ x y, x < S.width → y < S.width → f x = f y → x = y) :
    Realises level (S.place f totalWidth) (Program.relabel f totalWidth p) :=
  RealisesAt.relabel h hlt hinj

end Semantics
end VQ
