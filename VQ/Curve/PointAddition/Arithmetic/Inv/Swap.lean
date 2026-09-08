import VQ.Curve.PointAddition.Arithmetic.Inv.Load

/-!
# Controlled swaps and cyclic shifts

Algorithm 7b arranges its four branches with swaps: `u` with `v` and `r` with
`s`, under the branch bit, before and after the arithmetic.  It then halves `v`
and doubles `r`, which the published circuit does as cyclic qubit shifts.

A cyclic shift is a permutation of wires, and this build realises it with swap
gates at a fixed layout rather than by rotating each round's wire placement.
That costs about `6 n` CNOTs per round and no Toffolis, and it keeps every round
identical, so the `2 n`-round induction is one chain lemma rather than a
per-round wire map.  Both shifts also need a control, because a round that finds
`v` already zero must not double `r`.

The Fredkin gate here is the CNOT-Toffoli-CNOT form, one Toffoli and two CNOTs.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- Swap wires `x` and `y` when wire `c` is set. -/
def fred (c x y : Nat) : List RGate :=
  [RGate.cx y x, RGate.ccx c x y, RGate.cx y x]

theorem fred_split (c x y i : Nat) :
    actGates (fred c x y) i
      = RGate.act (RGate.cx y x) (RGate.act (RGate.ccx c x y) (RGate.act (RGate.cx y x) i)) := by
  show actGates [RGate.cx y x, RGate.ccx c x y, RGate.cx y x] i = _
  rw [show [RGate.cx y x, RGate.ccx c x y, RGate.cx y x]
        = [RGate.cx y x] ++ [RGate.ccx c x y] ++ [RGate.cx y x] from rfl,
    actGates_append, actGates_append]
  rfl

/-- With the control clear the gate is the identity. -/
theorem fred_off {c x y i : Nat} (hxy : x ≠ y) (hcx : c ≠ x) (h : bv i c = 0) :
    actGates (fred c x y) i = i := by
  have hbx := bv_lt i x
  have hby := bv_lt i y
  have e1 : RGate.act (RGate.cx y x) i = writeField i x 1 ((bv i x + bv i y) % 2) := act_cx y x i
  have b1c : bv (writeField i x 1 ((bv i x + bv i y) % 2)) c = bv i c := bv_write_ne hcx
  have b1x : bv (writeField i x 1 ((bv i x + bv i y) % 2)) x = (bv i x + bv i y) % 2 % 2 :=
    bv_write_self _ _ _
  have b1y : bv (writeField i x 1 ((bv i x + bv i y) % 2)) y = bv i y := bv_write_ne (Ne.symm hxy)
  rw [fred_split, e1, act_ccx, b1c, b1x, b1y, h, Nat.zero_mul,
    write_of_bv (by omega), act_cx, b1x, b1y, writeField_writeField]
  exact write_of_bv (by omega)

/-- With the control set the gate exchanges the two wires. -/
theorem fred_on {c x y i : Nat} (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y)
    (h : bv i c = 1) :
    actGates (fred c x y) i
      = writeField (writeField i x 1 (bv i y)) y 1 (bv i x) := by
  have hbx := bv_lt i x
  have hby := bv_lt i y
  have e1 : RGate.act (RGate.cx y x) i = writeField i x 1 ((bv i x + bv i y) % 2) := act_cx y x i
  have b1c : bv (writeField i x 1 ((bv i x + bv i y) % 2)) c = bv i c := bv_write_ne hcx
  have b1x : bv (writeField i x 1 ((bv i x + bv i y) % 2)) x = (bv i x + bv i y) % 2 % 2 :=
    bv_write_self _ _ _
  have b1y : bv (writeField i x 1 ((bv i x + bv i y) % 2)) y = bv i y := bv_write_ne (Ne.symm hxy)
  rw [fred_split, e1, act_ccx, b1c, b1x, b1y, h, Nat.one_mul]
  -- `y` now holds the original `x`.
  have hy2 : (bv i y + (bv i x + bv i y) % 2 % 2) % 2 = bv i x := by omega
  rw [hy2]
  have b2x : bv (writeField (writeField i x 1 ((bv i x + bv i y) % 2)) y 1 (bv i x)) x
      = (bv i x + bv i y) % 2 % 2 := by
    rw [bv_write_ne hxy, b1x]
  have b2y : bv (writeField (writeField i x 1 ((bv i x + bv i y) % 2)) y 1 (bv i x)) y
      = bv i x % 2 := bv_write_self _ _ _
  rw [act_cx, b2x, b2y]
  -- `x` now holds the original `y`.
  have hx2 : ((bv i x + bv i y) % 2 % 2 + bv i x % 2) % 2 = bv i y := by omega
  rw [hx2, writeField_comm (by omega), writeField_writeField]

/-! ## Field-swap semantics -/

/-- Exchange fields `A` and `B`, each of `p` wires, when wire `c` is set. -/
def swapC (c : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | A, B, p + 1 => fred c A B ++ swapC c (A + 1) (B + 1) p

theorem swapC_off {c : Nat} : ∀ (p A B i : Nat),
    (A + p ≤ B ∨ B + p ≤ A) → (c < A ∨ A + p ≤ c) →
    bv i c = 0 → actGates (swapC c A B p) i = i := by
  intro p
  induction p with
  | zero => intro A B i _ _ _; rfl
  | succ p ih =>
    intro A B i hAB hcA h
    show actGates (fred c A B ++ swapC c (A + 1) (B + 1) p) i = i
    rw [actGates_append, fred_off (by omega) (by omega) h]
    exact ih (A + 1) (B + 1) i (by omega) (by omega) h

theorem swapC_on {c : Nat} : ∀ (p A B i : Nat),
    (A + p ≤ B ∨ B + p ≤ A) → (c < A ∨ A + p ≤ c) → (c < B ∨ B + p ≤ c) →
    bv i c = 1 →
    actGates (swapC c A B p) i
      = writeField (writeField i A p (readField i B p)) B p (readField i A p) := by
  intro p
  induction p with
  | zero => intro A B i _ _ _ _; rw [writeField_zero, writeField_zero]; rfl
  | succ p ih =>
    intro A B i hAB hcA hcB h
    have hne : A ≠ B := by omega
    have hbA := bv_lt i A
    have hbB := bv_lt i B
    -- One Fredkin exchanges the low bits.
    have e1 := fred_on (c := c) (x := A) (y := B) (i := i) hne (by omega) (by omega) h
    -- The rest of the register, with the low bits already exchanged.
    have hJc : bv (writeField (writeField i A 1 (bv i B)) B 1 (bv i A)) c = 1 := by
      rw [bv_write_ne (by omega), bv_write_ne (by omega)]; exact h
    have hJA : readField (writeField (writeField i A 1 (bv i B)) B 1 (bv i A)) (A + 1) p
        = readField i (A + 1) p := by
      rw [readField_writeField_of_disjoint (by omega),
        readField_writeField_of_disjoint (by omega)]
    have hJB : readField (writeField (writeField i A 1 (bv i B)) B 1 (bv i A)) (B + 1) p
        = readField i (B + 1) p := by
      rw [readField_writeField_of_disjoint (by omega),
        readField_writeField_of_disjoint (by omega)]
    show actGates (fred c A B ++ swapC c (A + 1) (B + 1) p) i = _
    rw [actGates_append, e1,
      ih (A + 1) (B + 1) _ (by omega) (by omega) (by omega) hJc, hJA, hJB]
    -- Both sides are the same four writes.
    rw [writeField_succ i A p (readField i B (p + 1)),
      writeField_succ _ B p (readField i A (p + 1))]
    have hrA : readField i A (p + 1) % 2 = bv i A := by
      have := readField_succ i A p; omega
    have hrB : readField i B (p + 1) % 2 = bv i B := by
      have := readField_succ i B p; omega
    have hdA : readField i A (p + 1) / 2 = readField i (A + 1) p := by
      have := readField_succ i A p; omega
    have hdB : readField i B (p + 1) / 2 = readField i (B + 1) p := by
      have := readField_succ i B p; omega
    rw [hrA, hrB, hdA, hdB]
    exact congrArg (fun z => writeField z (B + 1) p (readField i (A + 1) p))
      (writeField_comm (i := writeField i A 1 (bv i B)) (o₁ := B) (n₁ := 1)
        (v := bv i A) (o₂ := A + 1) (n₂ := p) (u := readField i (B + 1) p) (by omega))

/-- A wider write at the same offset absorbs a narrower one. -/
theorem writeField_absorb {i o a b v u : Nat} (h : a ≤ b) :
    writeField (writeField i o a v) o b u = writeField i o b u := by
  refine Nat.eq_of_testBit_eq (fun t => ?_)
  by_cases ht : o ≤ t ∧ t < o + b
  · rw [testBit_writeField_inside ht.1 ht.2, testBit_writeField_inside ht.1 ht.2]
  · rw [testBit_writeField_outside (by omega), testBit_writeField_outside (by omega),
      testBit_writeField_outside (by omega)]

/-! ## Cyclic shifts

Adjacent swaps in increasing order rotate a field right.  In decreasing order,
left.  Each is stated at the precondition the round supplies: `v` is even when
it is halved, and `r` is below half its register when it is doubled, so in both
cases the bit that wraps is zero and the rotation is an ordinary shift. -/

/-- Halve a field, when wire `c` is set. -/
def shiftR (c : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, p + 2 => fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)

/-! ## Uncontrolled halving

A round with `v = 0` must preserve the state.  Halving zero already has this
property, so an unconditional shift agrees with the controlled shift on every
reachable state.  Each controlled swap uses one Toffoli and two CNOTs, while an
unconditional swap uses three CNOTs. -/

/-- Swap two wires, with no control.  Written in `fred`'s order so the two
differ in one gate. -/
def swapU (x y : Nat) : List RGate := [RGate.cx y x, RGate.cx x y, RGate.cx y x]

/-- Halve a field, unconditionally. -/
def shiftRU : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, p + 2 => swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)

theorem swapU_split (x y i : Nat) :
    actGates (swapU x y) i
      = RGate.act (RGate.cx y x) (RGate.act (RGate.cx x y) (RGate.act (RGate.cx y x) i)) := by
  show actGates [RGate.cx y x, RGate.cx x y, RGate.cx y x] i = _
  rw [actGates_cons, actGates_cons, actGates_cons, actGates_nil]

/-- With its control set, the Fredkin is the plain swap. -/
theorem swapU_eq_fred {c x y i : Nat} (hcx : c ≠ x) (hcy : c ≠ y) (hc : bv i c = 1) :
    actGates (swapU x y) i = actGates (fred c x y) i := by
  rw [swapU_split, fred_split]
  have hkeep : bv (RGate.act (RGate.cx y x) i) c = 1 := by
    rw [act_cx, ← readField_one, readField_writeField_of_disjoint (by omega), readField_one, hc]
  refine congrArg (RGate.act (RGate.cx y x)) ?_
  rw [act_cx, act_ccx, hkeep, Nat.one_mul]

theorem swapU_zero {x y i : Nat} (hx : bv i x = 0) (hy : bv i y = 0) :
    actGates (swapU x y) i = i := by
  have e1 : RGate.act (RGate.cx y x) i = i := by
    rw [act_cx, hx, hy]; exact write_of_bv (by rw [hx])
  have e2 : RGate.act (RGate.cx x y) i = i := by
    rw [act_cx, hx, hy]; exact write_of_bv (by rw [hy])
  rw [swapU_split, e1, e2, e1]

/-- The unconditional halving agrees with the controlled one when the control
is set. -/
theorem shiftRU_eq {c : Nat} : ∀ (w off i : Nat), (c < off ∨ off + w ≤ c) → bv i c = 1 →
    actGates (shiftRU off w) i = actGates (shiftR c off w) i
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | p + 2, off, i, hc, h1 => by
    have hcx : c ≠ off := by omega
    have hcy : c ≠ off + 1 := by omega
    have hswap := swapU_eq_fred (c := c) hcx hcy h1
    have hbw : ∀ (j q v : Nat), c ≠ q → bv (writeField j q 1 v) c = bv j c := by
      intro j q v h
      rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]
    have hkeep : bv (actGates (swapU off (off + 1)) i) c = 1 := by
      rw [swapU_split, act_cx, hbw _ _ _ hcx, act_cx, hbw _ _ _ hcy, act_cx, hbw _ _ _ hcx]
      exact h1
    show actGates (swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)) i
      = actGates (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)) i
    rw [actGates_append, actGates_append, ← hswap,
      shiftRU_eq (p + 1) (off + 1) _ (by omega) hkeep]

/-- Halving a field of zeroes changes nothing. -/
theorem shiftRU_zero : ∀ (w off i : Nat), readField i off w = 0 →
    actGates (shiftRU off w) i = i
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | p + 2, off, i, h => by
    have h' : readField i off (p + 1 + 1) = 0 := h
    have hs := readField_succ i off (p + 1)
    have hx : bv i off = 0 := by omega
    have hy : bv i (off + 1) = 0 := by
      have := readField_succ i (off + 1) p
      omega
    have htail : readField i (off + 1) (p + 1) = 0 := by omega
    show actGates (swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)) i = i
    rw [actGates_append, swapU_zero hx hy, shiftRU_zero (p + 1) (off + 1) i htail]

/-- Double a field, when wire `c` is set. -/
def shiftL (c : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | _, 1 => []
  | off, p + 2 => shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)

theorem shiftR_on {c : Nat} : ∀ (w off i : Nat), (c < off ∨ off + w ≤ c) → bv i c = 1 →
    bv i off = 0 →
    actGates (shiftR c off w) i = writeField i off w (readField i off w / 2)
  | 0 => by intro off i _ _ _; rw [writeField_zero]; rfl
  | 1 => by
      intro off i _ _ hz
      have : readField i off 1 = 0 := by rw [readField_one]; exact hz
      rw [show shiftR c off 1 = [] from rfl, actGates_nil, this]
      exact (write_of_bv (by rw [hz])).symm
  | p + 2 => by
      intro off i hc h hz
      have hbo1 := bv_lt i (off + 1)
      have e1 := fred_on (c := c) (x := off) (y := off + 1) (i := i)
        (by omega) (by omega) (by omega) h
      rw [hz] at e1
      have hJc : bv (writeField (writeField i off 1 (bv i (off + 1))) (off + 1) 1 0) c = 1 := by
        rw [bv_write_ne (by omega), bv_write_ne (by omega)]; exact h
      have hJz : bv (writeField (writeField i off 1 (bv i (off + 1))) (off + 1) 1 0) (off + 1)
          = 0 := by
        rw [bv_write_self]
      show actGates (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)) i = _
      rw [actGates_append, e1,
        shiftR_on (p + 1) (off + 1) _ (by omega) hJc hJz]
      -- Read the upper part back through the two single-bit writes.
      have hR : readField (writeField (writeField i off 1 (bv i (off + 1))) (off + 1) 1 0)
          (off + 1) (p + 1) = 2 * (readField i (off + 1) (p + 1) / 2) := by
        have hsucc := readField_succ
          (writeField (writeField i off 1 (bv i (off + 1))) (off + 1) 1 0) (off + 1) p
        have hup : readField (writeField (writeField i off 1 (bv i (off + 1))) (off + 1) 1 0)
            (off + 2) p = readField i (off + 2) p := by
          rw [readField_writeField_of_disjoint (by omega),
            readField_writeField_of_disjoint (by omega)]
        have hsucc' := readField_succ i (off + 1) p
        rw [show off + 1 + 1 = off + 2 from rfl] at hsucc
        rw [show off + 1 + 1 = off + 2 from rfl] at hsucc'
        omega
      rw [hR, show 2 * (readField i (off + 1) (p + 1) / 2) / 2
            = readField i (off + 1) (p + 1) / 2 from by omega,
        writeField_absorb (by omega)]
      -- Both sides are the same two writes.
      have hsplit := readField_succ i off (p + 1)
      rw [show p + 1 + 1 = p + 2 from rfl] at hsplit
      rw [writeField_succ i off (p + 1) (readField i off (p + 2) / 2)]
      have hlow : readField i off (p + 2) / 2 % 2 = bv i (off + 1) := by
        have h2 := readField_succ i (off + 1) p
        omega
      have hhigh : readField i off (p + 2) / 2 / 2 = readField i (off + 1) (p + 1) / 2 := by
        omega
      rw [hlow, hhigh]

theorem shiftL_on {c : Nat} : ∀ (w off i : Nat), (c < off ∨ off + w ≤ c) → bv i c = 1 →
    bv i (off + w - 1) = 0 →
    actGates (shiftL c off w) i = writeField i off w (2 * readField i off w)
  | 0 => by intro off i _ _ _; rw [writeField_zero]; rfl
  | 1 => by
      intro off i _ _ hz
      have hb : readField i off 1 = 0 := by rw [readField_one]; simpa using hz
      rw [show shiftL c off 1 = [] from rfl, actGates_nil, hb]
      exact (write_of_bv (by rw [← readField_one, hb])).symm
  | p + 2 => by
      intro off i hc h hz
      have hb0 := bv_lt i off
      -- The upper part doubles first.
      have htop : bv i (off + 1 + (p + 1) - 1) = 0 := by
        rw [show off + 1 + (p + 1) - 1 = off + (p + 2) - 1 from by omega]
        exact hz
      have hIH := shiftL_on (p + 1) (off + 1) i (by omega) h htop
      have hR := readField_succ i off (p + 1)
      rw [show p + 1 + 1 = p + 2 from rfl] at hR
      -- After doubling, the low bit of the upper part is clear.
      have hJ0 : bv (writeField i (off + 1) (p + 1) (2 * readField i (off + 1) (p + 1)))
          (off + 1) = 0 := by
        have hlt : 2 * readField i (off + 1) (p + 1) < 2 ^ (p + 1) := by
          have h2 := readField_succ i (off + 1) p
          have hb1 := bv_lt i (off + 1)
          have hup := readField_lt i (off + 1 + 1) p
          have hpow : (2 : Nat) ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
          have hzz : bv i (off + 1 + p) = 0 := by
            rw [show off + 1 + p = off + (p + 2) - 1 from by omega]; exact hz
          have hnar : readField i (off + 1) (p + 1) < 2 ^ p :=
            lt_of_top_bit_zero (readField_lt i (off + 1) (p + 1))
              (by rw [readField_top]; exact hzz)
          omega
        rw [← readField_one, readField_writeField_narrow (by omega), Nat.pow_one]
        omega
      have hJc : bv (writeField i (off + 1) (p + 1) (2 * readField i (off + 1) (p + 1))) c = 1 := by
        rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]
        exact h
      have hJoff : bv (writeField i (off + 1) (p + 1) (2 * readField i (off + 1) (p + 1))) off
          = bv i off := by
        rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]
      have e2 := fred_on (c := c) (x := off) (y := off + 1)
        (i := writeField i (off + 1) (p + 1) (2 * readField i (off + 1) (p + 1)))
        (by omega) (by omega) (by omega) hJc
      show actGates (shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)) i = _
      rw [actGates_append, hIH, e2, hJ0, hJoff]
      -- Both sides are the same two writes.
      rw [writeField_succ i off (p + 1) (2 * readField i off (p + 2))]
      have hlow : 2 * readField i off (p + 2) % 2 = 0 := by omega
      have hhigh : 2 * readField i off (p + 2) / 2 = readField i off (p + 2) := by omega
      rw [hlow, hhigh]
      -- Move the two single-bit writes past each other and fold the low one in.
      rw [writeField_comm (i := writeField i (off + 1) (p + 1)
          (2 * readField i (off + 1) (p + 1)))
        (o₁ := off) (n₁ := 1) (v := 0) (o₂ := off + 1) (n₂ := 1) (u := bv i off) (by omega)]
      rw [writeField_low (i := i) (o := off + 1) (m := p)
        (v := 2 * readField i (off + 1) (p + 1)) (u := bv i off)]
      have hb0' : bv i off % 2 = bv i off := by omega
      have hv2 : 2 * readField i (off + 1) (p + 1) / 2 = readField i (off + 1) (p + 1) := by omega
      rw [hb0', hv2]
      have hval : bv i off + 2 * readField i (off + 1) (p + 1) = readField i off (p + 2) := hR.symm
      rw [hval]
      exact writeField_comm (by omega)

/-- With the control clear, a shift does nothing. -/
theorem shiftR_off {c : Nat} : ∀ (w off i : Nat), (c < off ∨ off + w ≤ c) → bv i c = 0 →
    actGates (shiftR c off w) i = i
  | 0 => by intro off i _ _; rfl
  | 1 => by intro off i _ _; rfl
  | p + 2 => by
      intro off i hc h
      show actGates (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)) i = i
      rw [actGates_append, fred_off (by omega) (by omega) h]
      exact shiftR_off (p + 1) (off + 1) i (by omega) h

theorem shiftL_off {c : Nat} : ∀ (w off i : Nat), (c < off ∨ off + w ≤ c) → bv i c = 0 →
    actGates (shiftL c off w) i = i
  | 0 => by intro off i _ _; rfl
  | 1 => by intro off i _ _; rfl
  | p + 2 => by
      intro off i hc h
      show actGates (shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)) i = i
      rw [actGates_append, shiftL_off (p + 1) (off + 1) i (by omega) h,
        fred_off (by omega) (by omega) h]

end VQ.Curve.PointAddition.Arithmetic.Inv
