import VQ.Curve.PointAddition.Arithmetic.Inv.Place
import VQ.Curve.PointAddition.Arithmetic.Inv.Load

/-!
# Comparison circuit

`v < u` as one bit, computed and later uncomputed.

The circuit complements the `u` register, sets the carry wire, and adds into
`v`.  With both values below `2 ^ (w - 1)` in registers of `w` bits, the sum is
`v - u` modulo `2 ^ w`, and its top bit is one exactly when `v < u`: if `v ≥ u`
the difference is below `2 ^ (w - 1)`, and if `v < u` the wrap puts it above.
A CNOT copies that bit out, and the whole preparation runs backwards.

`actGates_compute_use_uncompute` proves that the reversed preparation restores
its input while preserving the copied bit.  Its `hout` hypothesis states that
the preparation leaves the target wire unchanged.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add


/-! ## Carry-chain semantics

Cuccaro's adder is a chain of `maj` steps that lays the carries down the augend
register, then a chain of `uma` steps that turns them back into the operands and
writes the sum.  A comparison needs the carries and not the sum, so it can stop
after the first chain, copy the bit it wants, and run that chain backwards.  Two
chains rather than four, and `maj` and `uma` cost one Toffoli each, so the
comparison halves.

Cuccaro's carry is stored on the augend wire of the preceding position.  The
recursion therefore passes `ou + st` as the next carry wire. -/

/-- The MAJ chain over `m` positions from `st`, with carry-in on wire `c`. -/
def majAt (ou ov : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | c, st, m + 1 => maj c (ov + st) (ou + st) ++ majAt ou ov (ou + st) (st + 1) m

/-- The chain lays the carry out on the top augend wire. -/
theorem majAt_carry {ou ov : Nat} :
    ∀ (m c st i : Nat), 0 < m → ou + st + m ≤ ov + st →
      (c + 1 ≤ ou + st ∨ ov + st + m ≤ c) →
      bv (actGates (majAt ou ov c st m) i) (ou + st + m - 1)
        = (readField i (ou + st) m + readField i (ov + st) m + bv i c) / 2 ^ m := by
  intro m
  induction m with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
    intro c st i _ hdis hc1
    have hab : ou + st ≠ ov + st := by omega
    have hac : ou + st ≠ c := by omega
    have hcb : c ≠ ov + st := by omega
    show bv (actGates (maj c (ov + st) (ou + st)
      ++ majAt ou ov (ou + st) (st + 1) m) i) (ou + st + (m + 1) - 1) = _
    rw [actGates_append, act_maj' hab hac hcb rfl rfl rfl]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [show majAt ou ov (ou + st) (st + 1) 0 = [] from rfl, actGates_nil,
        show ou + st + (0 + 1) - 1 = ou + st from by omega,
        bv_majState_a (bv_lt i (ou + st)) (bv_lt i (ov + st)) (bv_lt i c),
        readField_one, readField_one, Nat.pow_one]
    · have hstep := ih (ou + st) (st + 1) (majState i (ou + st) (ov + st) c
        (bv i (ou + st)) (bv i (ov + st)) (bv i c)) hm (by omega) (by omega)
      rw [show ou + st + (m + 1) - 1 = ou + (st + 1) + m - 1 from by omega, hstep,
        readField_majState (o := ou + (st + 1)) (len := m) (by omega) (by omega) (by omega),
        readField_majState (o := ov + (st + 1)) (len := m) (by omega) (by omega) (by omega),
        bv_majState_a (bv_lt i (ou + st)) (bv_lt i (ov + st)) (bv_lt i c)]
      have hA := readField_succ i (ou + st) m
      have hB := readField_succ i (ov + st) m
      have hp : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      rw [show ou + st + 1 = ou + (st + 1) from by omega] at hA
      rw [show ov + st + 1 = ov + (st + 1) from by omega] at hB
      rw [hA, hB, hp, ← Nat.div_div_eq_div_mul]
      refine congrArg (fun q => q / 2 ^ m) ?_
      have h1 := bv_lt i (ou + st)
      have h2 := bv_lt i (ov + st)
      have h3 := bv_lt i c
      omega

/-- Complement `u`, set the carry, and subtract into `v`. -/
def cmpPre (w ou ov oc : Nat) : List RGate :=
  loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc

/-- Every gate of the chain sits in the two registers or on the carry wire. -/
theorem majAt_wires (ou ov : Nat) : ∀ (m c st : Nat), ∀ g ∈ majAt ou ov c st m, ∀ q ∈ g.wires,
    q = c ∨ (ou + st ≤ q ∧ q < ou + st + m) ∨ (ov + st ≤ q ∧ q < ov + st + m) := by
  intro m
  induction m with
  | zero => intro c st g hg; simp [majAt] at hg
  | succ m ih =>
    intro c st g hg q hq
    rw [show majAt ou ov c st (m + 1)
      = maj c (ov + st) (ou + st) ++ majAt ou ov (ou + st) (st + 1) m from rfl,
      List.mem_append] at hg
    cases hg with
    | inl h =>
      simp only [maj, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;>
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> omega
    | inr h =>
      have := ih (ou + st) (st + 1) g h q hq
      omega

theorem majAt_wf (ou ov : Nat) : ∀ (m c st Wd : Nat), ou + st + m ≤ ov + st →
    (c + 1 ≤ ou + st ∨ ov + st + m ≤ c) → c < Wd → ou + st + m ≤ Wd → ov + st + m ≤ Wd →
    (majAt ou ov c st m).all (RGate.wellFormed Wd) = true := by
  intro m
  induction m with
  | zero => intro c st Wd _ _ _ _ _; simp [majAt]
  | succ m ih =>
    intro c st Wd hdis hc h1 h2 h3
    show (maj c (ov + st) (ou + st) ++ majAt ou ov (ou + st) (st + 1) m).all _ = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨maj_wf (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      ih (ou + st) (st + 1) Wd (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem majAt_ccx (ou ov : Nat) : ∀ (m c st : Nat),
    (majAt ou ov c st m).countP RGate.isCcx = m
  | 0, _, _ => rfl
  | m + 1, c, st => by
    show (maj c (ov + st) (ou + st) ++ majAt ou ov (ou + st) (st + 1) m).countP _ = _
    rw [List.countP_append, majAt_ccx ou ov m (ou + st) (st + 1),
      show List.countP RGate.isCcx (maj c (ov + st) (ou + st)) = 1 from rfl]
    omega

theorem majAt_len (ou ov : Nat) : ∀ (m c st : Nat), (majAt ou ov c st m).length = 3 * m
  | 0, _, _ => rfl
  | m + 1, c, st => by
    show (maj c (ov + st) (ou + st) ++ majAt ou ov (ou + st) (st + 1) m).length = _
    rw [List.length_append, majAt_len ou ov m (ou + st) (st + 1),
      show (maj c (ov + st) (ou + st)).length = 3 from rfl]
    omega

/-- The preparation: complement the augend, set the carry in, lay the carries. -/
def majPre (w ou ov oc : Nat) : List RGate :=
  loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w

/-- The carry out of the comparison's addition says `u ≤ v`. -/
theorem majPre_carry {w ou ov oc I u v : Nat} (hw : 0 < w) (hord : ou + w ≤ ov)
    (hc : oc + 1 ≤ ou ∨ ov + w ≤ oc)
    (h0 : readField I ou w = u) (h1 : readField I ov w = v) (h2 : readField I oc 1 = 0)
    (hu : u < 2 ^ w) :
    bv (actGates (majPre w ou ov oc) I) (ou + w - 1)
      = (2 ^ w - 1 - u + v + 1) / 2 ^ w := by
  have hA : actGates (loadX ou w (2 ^ w - 1)) I = writeField I ou w (2 ^ w - 1 - u) := by
    rw [loadX_ones, h0]
  have hstate : actGates (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1) I
      = writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1 := by
    rw [actGates_append, hA, loadX_act,
      readField_writeField_of_disjoint (by omega), h2, Nat.zero_xor]
  have hr0 : readField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) (ou + 0) w
      = 2 ^ w - 1 - u := by
    rw [Nat.add_zero, readField_writeField_of_disjoint (by omega), readField_writeField,
      Nat.mod_eq_of_lt (by omega)]
  have hr1 : readField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) (ov + 0) w = v := by
    rw [Nat.add_zero, readField_writeField_of_disjoint (by omega),
      readField_writeField_of_disjoint (by omega), h1]
  have hr2 : bv (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) oc = 1 := by
    rw [← readField_one, readField_writeField, Nat.pow_one]
  show bv (actGates (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w) I) _ = _
  rw [actGates_append, hstate,
    show ou + w - 1 = ou + 0 + w - 1 from by omega,
    majAt_carry w oc 0 _ hw (by omega) (by omega), hr0, hr1, hr2]

/-- The halved comparison: the preparation, one CNOT out of the carry wire, a
negation, and the preparation reversed.  The carry out of `v + (2^w - 1 - u) + 1`
is one exactly when `u ≤ v`, so the negation turns it into `v < u`. -/
def cmpMaj (w ou ov oc og : Nat) : List RGate :=
  majPre w ou ov oc ++ [RGate.cx (ou + w - 1) og, RGate.x og] ++ (majPre w ou ov oc).reverse

theorem majPre_avoids {w ou ov oc og : Nat} (hw : 0 < w)
    (hu : ou + w ≤ og ∨ og + 1 ≤ ou) (hv : ov + w ≤ og ∨ og + 1 ≤ ov)
    (hc : oc + 1 ≤ og ∨ og + 1 ≤ oc) :
    ∀ g ∈ majPre w ou ov oc, ∀ q ∈ g.wires, q < og ∨ og + 1 ≤ q := by
  intro g hg q hq
  have hg' : g ∈ loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w := hg
  rw [List.mem_append, List.mem_append] at hg'
  rcases hg' with (h | h) | h
  · have := loadX_wires w ou (2 ^ w - 1) g h q hq; omega
  · have := loadX_wires 1 oc 1 g h q hq; omega
  · have := majAt_wires ou ov w oc 0 g h q hq; omega

theorem majPre_wf {w ou ov oc Wd : Nat} (hord : ou + w ≤ ov)
    (hc : oc + 1 ≤ ou ∨ ov + w ≤ oc)
    (hwu : ou + w ≤ Wd) (hwv : ov + w ≤ Wd) (hwc : oc + 1 ≤ Wd) :
    (majPre w ou ov oc).all (RGate.wellFormed Wd) = true := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨loadX_wf w ou (2 ^ w - 1) Wd (by omega), loadX_wf 1 oc 1 Wd (by omega)⟩,
    majAt_wf ou ov w oc 0 Wd (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- The carry out of `v + (2 ^ w - 1 - u) + 1` is one exactly when `u ≤ v`. -/
theorem carry_lt_iff {w u v : Nat} (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    (2 ^ w - 1 - u + v + 1) / 2 ^ w = if v < u then 0 else 1 := by
  have hpow : (0 : Nat) < 2 ^ w := Nat.two_pow_pos w
  generalize hP : (2 : Nat) ^ w = P at hu hv hpow ⊢
  by_cases h : v < u
  · rw [if_pos h, Nat.div_eq_of_lt (by omega)]
  · rw [if_neg h]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The halved comparison writes the same bit the full one did. -/
theorem cmpMaj_act {w ou ov oc og I u v g Wd : Nat} (hw : 0 < w)
    (hord : ou + w ≤ ov) (hc : oc + 1 ≤ ou ∨ ov + w ≤ oc)
    (hgu : ou + w ≤ og ∨ og + 1 ≤ ou) (hgv : ov + w ≤ og ∨ og + 1 ≤ ov)
    (hgc : oc + 1 ≤ og ∨ og + 1 ≤ oc)
    (hwu : ou + w ≤ Wd) (hwv : ov + w ≤ Wd) (hwc : oc + 1 ≤ Wd)
    (h0 : readField I ou w = u) (h1 : readField I ov w = v)
    (h2 : readField I oc 1 = 0) (h3 : readField I og 1 = g)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    actGates (cmpMaj w ou ov oc og) I
      = writeField I og 1 ((g + if v < u then 1 else 0) % 2) := by
  have hcp : ∀ j, actGates [RGate.cx (ou + w - 1) og, RGate.x og] j
      = writeField j og 1 (((bv j og + bv j (ou + w - 1)) % 2 + 1) % 2) := by
    intro j
    show RGate.act (RGate.x og) (RGate.act (RGate.cx (ou + w - 1) og) j) = _
    rw [act_cx, act_x, bv_write_self, writeField_writeField]
    refine congrArg (fun q => writeField j og 1 q) ?_
    omega
  have hmain := actGates_compute_use_uncompute (gs := majPre w ou ov oc)
    (cp := [RGate.cx (ou + w - 1) og, RGate.x og]) (w := Wd) (off := og) (len := 1)
    (majPre_wf hord hc hwu hwv hwc) (majPre_avoids hw hgu hgv hgc) hcp I
  have hogS : bv (actGates (majPre w ou ov oc) I) og = g := by
    have hav : ∀ q ∈ majPre w ou ov oc, ∀ r ∈ q.wires, r < og ∨ og + 1 ≤ r :=
      majPre_avoids hw hgu hgv hgc
    rw [← readField_one, readField_actGates_outside hav, readField_one, ← h3, readField_one]
  have hcarry := majPre_carry (I := I) (u := u) (v := v) hw hord hc h0 h1 h2 hu
  have hg2 : g < 2 := by rw [← h3]; exact readField_lt I og 1
  show actGates (majPre w ou ov oc ++ [RGate.cx (ou + w - 1) og, RGate.x og]
    ++ (majPre w ou ov oc).reverse) I = _
  rw [hmain, hogS, hcarry, carry_lt_iff hu hv]
  refine congrArg (fun q => writeField I og 1 q) ?_
  by_cases h : v < u <;> simp [h] <;> omega

/-- The comparison: the preparation, one CNOT out of `v`'s top bit, and the
preparation reversed. -/
def cmpAt (w ou ov oc og : Nat) : List RGate :=
  cmpPre w ou ov oc ++ [RGate.cx (ov + (w - 1)) og] ++ (cmpPre w ou ov oc).reverse

/-- The top bit of `v - u` modulo `2 ^ (k + 1)` is the comparison.

The subtrahend must fit below `2 ^ k`, but the minuend needs only the full
register, provided the difference itself fits.  The correction's reduction needs
that: it compares the almost inverse, which reaches twice the modulus, against
the modulus. -/
theorem top_bit_lt {k u v : Nat} (hu : u < 2 ^ k) (hv : v < 2 ^ (k + 1))
    (hd : v < u ∨ v - u < 2 ^ k) :
    ((2 ^ (k + 1) - 1 - u + v + 1) % 2 ^ (k + 1)) / 2 ^ k % 2 = if v < u then 1 else 0 := by
  have hp : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  by_cases hlt : v < u
  · rw [if_pos hlt]
    have he : 2 ^ (k + 1) - 1 - u + v + 1 = 2 ^ k + (2 ^ k + v - u) := by omega
    have hr : 2 ^ k + (2 ^ k + v - u) < 2 ^ (k + 1) := by omega
    have hq : (2 ^ k + (2 ^ k + v - u)) / 2 ^ k = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [he, Nat.mod_eq_of_lt hr, hq]
  · rw [if_neg hlt]
    have hvu : v - u < 2 ^ k := by
      cases hd with
      | inl h => omega
      | inr h => exact h
    have he : 2 ^ (k + 1) - 1 - u + v + 1 = 2 ^ (k + 1) + (v - u) := by omega
    have hr : v - u < 2 ^ (k + 1) := by omega
    have hq : (v - u) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hr, hq]

/-! ## Comparison preparation

Three writes: the complement of `u`, the carry set to one, and the difference
into `v`. -/

/-- The state after the preparation. -/
def cmpState (w ou ov oc I u v : Nat) : Nat :=
  writeField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) ov w
    ((2 ^ w - 1 - u + v + 1) % 2 ^ w)

theorem cmpPre_act {w ou ov oc I u v : Nat}
    (hab : ou + w ≤ ov ∨ ov + w ≤ ou)
    (hac : ou + w ≤ oc ∨ oc + 1 ≤ ou)
    (hbc : ov + w ≤ oc ∨ oc + 1 ≤ ov)
    (h0 : readField I ou w = u) (h1 : readField I ov w = v)
    (h2 : readField I oc 1 = 0) :
    actGates (cmpPre w ou ov oc) I = cmpState w ou ov oc I u v := by
  have e1 : actGates (loadX ou w (2 ^ w - 1)) I = writeField I ou w (2 ^ w - 1 - u) := by
    rw [loadX_ones, h0]
  have dUC : ou + w ≤ oc ∨ oc + 1 ≤ ou := hac
  have dCU : oc + 1 ≤ ou ∨ ou + w ≤ oc := hac.symm
  have dCV : oc + 1 ≤ ov ∨ ov + w ≤ oc := hbc.symm
  have dUV : ou + w ≤ ov ∨ ov + w ≤ ou := hab
  have hcarry : readField (writeField I ou w (2 ^ w - 1 - u)) oc 1 = 0 := by
    rw [readField_writeField_of_disjoint dUC]; exact h2
  have e2 : actGates (loadX oc 1 1) (writeField I ou w (2 ^ w - 1 - u))
      = writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1 := by
    rw [loadX_act, hcarry]; rfl
  have hone : (1 : Nat) < 2 ^ 1 := by decide
  have hcpl : 2 ^ w - 1 - u < 2 ^ w := by
    have h := Nat.two_pow_pos w
    omega
  have hu2 : readField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) ou w
      = 2 ^ w - 1 - u := by
    rw [readField_writeField_of_disjoint dCU]
    exact readField_writeField_self hcpl
  have hv2 : readField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) ov w = v := by
    rw [readField_writeField_of_disjoint dCV, readField_writeField_of_disjoint dUV]
    exact h1
  have hc2 : readField (writeField (writeField I ou w (2 ^ w - 1 - u)) oc 1 1) oc 1 = 1 :=
    readField_writeField_self hone
  have e3 := addAt_act_carry (w := w) hab hac hbc hu2 hv2 hc2
  show actGates (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc) I = _
  rw [actGates_append, actGates_append, e1, e2, e3]
  rfl

/-- The preparation touches only the three registers. -/
theorem cmpPre_avoids {w ou ov oc og : Nat}
    (hu : ou + w ≤ og ∨ og + 1 ≤ ou)
    (hv : ov + w ≤ og ∨ og + 1 ≤ ov)
    (hc : oc + 1 ≤ og ∨ og + 1 ≤ oc) :
    ∀ g ∈ cmpPre w ou ov oc, ∀ q ∈ g.wires, q < og ∨ og + 1 ≤ q := by
  intro g hg q hq
  have hg' : g ∈ loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc := hg
  rw [List.mem_append, List.mem_append] at hg'
  replace hg := hg'
  cases hg with
  | inl h =>
    cases h with
    | inl h => have := loadX_wires w ou (2 ^ w - 1) g h q hq; omega
    | inr h => have := loadX_wires 1 oc 1 g h q hq; omega
  | inr h =>
    refine placeGates_avoids (L := addL w) (W := [ou, ov, oc]) (by simp [addL])
      (add_wf w) ?_ g h q hq
    intro j hj
    simp only [addL, List.length_cons, List.length_nil] at hj
    match j with
    | 0 => exact hu
    | 1 => exact hv
    | 2 => exact hc
    | _ + 3 => omega

theorem cmpPre_wf {w ou ov oc Wd : Nat}
    (hab : ou + w ≤ ov ∨ ov + w ≤ ou)
    (hac : ou + w ≤ oc ∨ oc + 1 ≤ ou)
    (hbc : ov + w ≤ oc ∨ oc + 1 ≤ ov)
    (hwu : ou + w ≤ Wd) (hwv : ov + w ≤ Wd) (hwc : oc + 1 ≤ Wd) :
    (cmpPre w ou ov oc).all (RGate.wellFormed Wd) = true := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨loadX_wf w ou (2 ^ w - 1) Wd hwu, loadX_wf 1 oc 1 Wd hwc⟩,
    addAt_wf hab hac hbc hwu hwv hwc⟩

/-! ## Comparison circuit -/

/-- The comparison writes `v < u` into one wire and restores everything
else.  The operands are stated at `k + 1` bits holding values below `2 ^ k`,
which is the width the round gives `u` and `v` for exactly this reason. -/
theorem cmpAt_act {k ou ov oc og I u v g Wd : Nat}
    (hab : ou + (k + 1) ≤ ov ∨ ov + (k + 1) ≤ ou)
    (hac : ou + (k + 1) ≤ oc ∨ oc + 1 ≤ ou)
    (hbc : ov + (k + 1) ≤ oc ∨ oc + 1 ≤ ov)
    (hgu : ou + (k + 1) ≤ og ∨ og + 1 ≤ ou)
    (hgv : ov + (k + 1) ≤ og ∨ og + 1 ≤ ov)
    (hgc : oc + 1 ≤ og ∨ og + 1 ≤ oc)
    (hwu : ou + (k + 1) ≤ Wd) (hwv : ov + (k + 1) ≤ Wd) (hwc : oc + 1 ≤ Wd)
    (h0 : readField I ou (k + 1) = u) (h1 : readField I ov (k + 1) = v)
    (h2 : readField I oc 1 = 0) (h3 : readField I og 1 = g)
    (hu : u < 2 ^ k) (hv : v < 2 ^ (k + 1)) (hd : v < u ∨ v - u < 2 ^ k) :
    actGates (cmpAt (k + 1) ou ov oc og) I
      = writeField I og 1 ((g + if v < u then 1 else 0) % 2) := by
  have hcp : ∀ j, actGates [RGate.cx (ov + (k + 1 - 1)) og] j
      = writeField j og 1 ((bv j og + bv j (ov + (k + 1 - 1))) % 2) := by
    intro j
    show RGate.act (RGate.cx (ov + (k + 1 - 1)) og) j = _
    rw [act_cx]
  have hmain := actGates_compute_use_uncompute
    (gs := cmpPre (k + 1) ou ov oc) (cp := [RGate.cx (ov + (k + 1 - 1)) og])
    (w := Wd) (off := og) (len := 1)
    (cmpPre_wf hab hac hbc hwu hwv hwc)
    (cmpPre_avoids hgu hgv hgc) hcp I
  show actGates (cmpPre (k + 1) ou ov oc ++ [RGate.cx (ov + (k + 1 - 1)) og]
      ++ (cmpPre (k + 1) ou ov oc).reverse) I = _
  rw [hmain, cmpPre_act hab hac hbc h0 h1 h2]
  -- The copied bit is the top bit of the difference, and `og` was clear.
  have hogS : bv (cmpState (k + 1) ou ov oc I u v) og = g := by
    have e : bv (cmpState (k + 1) ou ov oc I u v) og = readField I og 1 := by
      rw [← readField_one]
      unfold cmpState
      rw [readField_writeField_of_disjoint hgv,
        readField_writeField_of_disjoint hgc,
        readField_writeField_of_disjoint hgu]
    rw [e, h3]
  have hbitS : bv (cmpState (k + 1) ou ov oc I u v) (ov + (k + 1 - 1))
      = if v < u then 1 else 0 := by
    have hread : readField (cmpState (k + 1) ou ov oc I u v) ov (k + 1)
        = (2 ^ (k + 1) - 1 - u + v + 1) % 2 ^ (k + 1) := by
      unfold cmpState
      exact readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos _))
    have hb := readField_top (cmpState (k + 1) ou ov oc I u v) ov k
    rw [show k + 1 - 1 = k from rfl, ← hb, hread, top_bit_lt hu hv hd]
  rw [hogS, hbitS]

end VQ.Curve.PointAddition.Arithmetic.Inv
