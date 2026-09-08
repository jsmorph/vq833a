import VQ.Curve.PointAddition.Arithmetic.Inv.Init

/-!
# Gate counts

The Toffoli count of each gadget, then of the round, the chain, the correction,
and the whole circuit.  `RGate.map` changes wires and not constructors, so a
placed component has the count of the component it places.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible

/-- Relabelling does not change what a gate is. -/
theorem countP_map (f : Nat → Nat) (gs : List RGate) :
    (gs.map (RGate.map f)).countP RGate.isCcx = gs.countP RGate.isCcx := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]
    cases g <;> rfl

theorem addAt_ccx (w oa ob oc : Nat) :
    (addAt w oa ob oc).countP RGate.isCcx = 2 * w := by
  rw [addAt, countP_map]
  exact VQ.Curve.PointAddition.Arithmetic.Inv.Add.ccx_body w w 0

theorem subAt_ccx (w oa ob oc : Nat) :
    (subAt w oa ob oc).countP RGate.isCcx = 2 * w := by
  rw [subAt, List.countP_reverse]
  exact addAt_ccx w oa ob oc

theorem loadX_ccx : ∀ (p W v : Nat), (loadX W p v).countP RGate.isCcx = 0
  | 0, _, _ => rfl
  | p + 1, W, v => by
    rw [loadX, List.countP_append, loadX_ccx p (W + 1) (v / 2)]
    by_cases h : v % 2 = 1
    · rw [if_pos h]; rfl
    · rw [if_neg h]; rfl

theorem copyC_ccx {c : Nat} : ∀ (p src dst : Nat),
    (copyC c src dst p).countP RGate.isCcx = p
  | 0, _, _ => rfl
  | p + 1, src, dst => by
    show ((RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p)).countP _ = _
    rw [List.countP_cons, copyC_ccx p (src + 1) (dst + 1)]
    rfl

theorem fred_ccx (c x y : Nat) : (fred c x y).countP RGate.isCcx = 1 := rfl

theorem swapC_ccx {c : Nat} : ∀ (p A B : Nat), (swapC c A B p).countP RGate.isCcx = p
  | 0, _, _ => rfl
  | p + 1, A, B => by
    show (fred c A B ++ swapC c (A + 1) (B + 1) p).countP _ = _
    rw [List.countP_append, fred_ccx, swapC_ccx p (A + 1) (B + 1)]
    omega

theorem shiftR_ccx {c : Nat} : ∀ (w off : Nat), (shiftR c off w).countP RGate.isCcx = w - 1
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)).countP _ = _
    rw [List.countP_append, fred_ccx, shiftR_ccx (p + 1) (off + 1)]
    omega

theorem swapU_ccx (x y : Nat) : (swapU x y).countP RGate.isCcx = 0 := rfl

theorem shiftRU_ccx : ∀ (w off : Nat), (shiftRU off w).countP RGate.isCcx = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)).countP _ = _
    rw [List.countP_append, swapU_ccx, shiftRU_ccx (p + 1) (off + 1)]

theorem shiftL_ccx {c : Nat} : ∀ (w off : Nat), (shiftL c off w).countP RGate.isCcx = w - 1
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)).countP _ = _
    rw [List.countP_append, fred_ccx, shiftL_ccx (p + 1) (off + 1)]
    omega

theorem copyField_ccx (s d len : Nat) : (copyField s d len).countP RGate.isCcx = 0 :=
  copyField_no_ccx s d len

theorem cmpPre_ccx (w ou ov oc : Nat) :
    (cmpPre w ou ov oc).countP RGate.isCcx = 2 * w := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc).countP _ = _
  rw [List.countP_append, List.countP_append, loadX_ccx, loadX_ccx, addAt_ccx]
  omega

theorem majPre_ccx (w ou ov oc : Nat) :
    (majPre w ou ov oc).countP RGate.isCcx = w := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w).countP _ = _
  rw [List.countP_append, List.countP_append, loadX_ccx, loadX_ccx, majAt_ccx]
  omega

theorem cmpMaj_ccx (w ou ov oc og : Nat) :
    (cmpMaj w ou ov oc og).countP RGate.isCcx = 2 * w := by
  show (majPre w ou ov oc ++ [RGate.cx (ou + w - 1) og, RGate.x og]
    ++ (majPre w ou ov oc).reverse).countP _ = _
  rw [List.countP_append, List.countP_append, List.countP_reverse, majPre_ccx,
    show List.countP RGate.isCcx [RGate.cx (ou + w - 1) og, RGate.x og] = 0 from rfl]
  omega

theorem cmpAt_ccx (w ou ov oc og : Nat) :
    (cmpAt w ou ov oc og).countP RGate.isCcx = 4 * w := by
  have hpre := cmpPre_ccx w ou ov oc
  show (cmpPre w ou ov oc ++ [RGate.cx (ov + (w - 1)) og]
    ++ (cmpPre w ou ov oc).reverse).countP _ = _
  rw [List.countP_append, List.countP_append, hpre, List.countP_reverse, hpre,
    show List.countP RGate.isCcx [RGate.cx (ov + (w - 1)) og] = 0 from rfl]
  omega

/-! ## Round circuit

Twenty-six Toffolis per register bit, plus four for the dispatch and the two
clears.  The shifts are one short of a full register each, which the count
carries rather than rounding away. -/

theorem roundGates_ccx (n t : Nat) :
    (roundGates n t).countP RGate.isCcx = 17 * bw n + 1 := by
  have hz : (segZero n t).countP RGate.isCcx = 2 * (bw n - 1) := by
    show (nzTest (aV n) (aTR n) (aZ n + t) (bw n)).countP _ = _
    rw [nzTest_ccx]
  have hd : (segDispatch n t).countP RGate.isCcx = 1 := rfl
  have hc : (segCompare n t).countP RGate.isCcx = 2 * bw n + 2 := by
    show (majPre (bw n) (aU n) (aV n) (aC n)
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ cmpUse n t
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ (majPre (bw n) (aU n) (aV n) (aC n)).reverse).countP _ = _
    simp only [List.countP_append, List.countP_reverse, majPre_ccx,
      show List.countP RGate.isCcx
        [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)] = 0 from rfl,
      show List.countP RGate.isCcx (cmpUse n t) = 2 from rfl]
    omega
  have hs : (segSwap n).countP RGate.isCcx = 2 * bw n := by
    show (swapC (aA n) (aU n) (aV n) (bw n) ++ swapC (aA n) (aR n) (aS n) (bw n)).countP _ = _
    rw [List.countP_append, swapC_ccx, swapC_ccx]
    omega
  have ha : (segArith n).countP RGate.isCcx = 8 * bw n := by
    show (copyC (aT n) (aU n) (aTU n) (bw n) ++ subAt (bw n) (aTU n) (aV n) (aC n)
      ++ copyC (aT n) (aU n) (aTU n) (bw n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n) ++ addAt (bw n) (aTR n) (aS n) (aC n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n)).countP _ = _
    simp only [List.countP_append, copyC_ccx, subAt_ccx, addAt_ccx]
    omega
  have hh : (segShift n t).countP RGate.isCcx = bw n - 1 := by
    show (shiftRU (aV n) (bw n) ++ shiftL (aZ n + t) (aR n) (bw n)).countP _ = _
    rw [List.countP_append, shiftRU_ccx, shiftL_ccx]
    omega
  have hcl : (segClear n t).countP RGate.isCcx = 1 := rfl
  show (segZero n t ++ segDispatch n t ++ segCompare n t ++ segSwap n ++ segArith n
    ++ segShift n t ++ segSwap n ++ segClear n t).countP _ = _
  rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append,
    List.countP_append, List.countP_append, List.countP_append,
    hz, hd, hc, hs, ha, hh, hcl]
  have : 0 < bw n := by simp only [bw]; omega
  omega

theorem chainT_ccx (n : Nat) : ∀ (T : Nat),
    (chainT n T).countP RGate.isCcx = T * (17 * bw n + 1) := by
  intro T
  induction T with
  | zero => simp [chainT]
  | succ T ih =>
    show (chainT n T ++ roundGates n T).countP _ = _
    rw [List.countP_append, ih, roundGates_ccx]
    rw [Nat.add_mul, Nat.one_mul]

/-! ## Correction circuit

The reduction runs a comparison and a conditional subtraction, the negation one
more subtraction, and each halving a conditional addition and a shift. -/

theorem bw_pos (n : Nat) : 0 < bw n := by simp only [bw]; omega

theorem fixReduce_ccx (n : Nat) : (fixReduce n).countP RGate.isCcx = 6 * bw n := by
  show (cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
    ++ loadCX (aGt n) (aTU n) (bw n) modulus
    ++ subAt (bw n) (aTU n) (aR n) (aC n)
    ++ loadCX (aGt n) (aTU n) (bw n) modulus).countP _ = _
  simp only [List.countP_append, cmpAt_ccx, loadCX_ccx, subAt_ccx,
    show List.countP RGate.isCcx [RGate.x (aGt n)] = 0 from rfl]
  omega

theorem fixNegate_ccx (n : Nat) : (fixNegate n).countP RGate.isCcx = 2 * bw n := by
  show (loadX (aTU n) (bw n) modulus ++ subAt (bw n) (aR n) (aTU n) (aC n)).countP _ = _
  simp only [List.countP_append, loadX_ccx, subAt_ccx]
  omega

theorem hCmp_ccx (n : Nat) : (hCmp n).countP RGate.isCcx = bw n := by
  show (majPre (bw n) (aTU n) (aTR n) (aC n)
    ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)]).countP _ = _
  rw [List.countP_append, majPre_ccx,
    show List.countP RGate.isCcx
      [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)] = 0 from rfl]
  omega

theorem fixHalve_ccx (n t : Nat) : (fixHalve n t).countP RGate.isCcx = 5 * bw n + 1 := by
  show ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ addAt (bw n) (aTR n) (aTU n) (aC n)
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ shiftR (aZ n + t) (aTU n) (bw n)
    ++ loadX (aTR n) (bw n) halfMod
    ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
    ++ loadX (aTR n) (bw n) halfMod).countP _ = _
  simp only [List.countP_append, List.countP_reverse, loadCX_ccx, loadX_ccx, addAt_ccx,
    shiftR_ccx, hCmp_ccx,
    show List.countP RGate.isCcx [RGate.ccx (aZ n + t) (aTU n) (aH n)] = 1 from rfl,
    show List.countP RGate.isCcx [RGate.ccx (aZ n + t) (aG n) (aH n)] = 1 from rfl]
  have := bw_pos n
  omega

theorem fixHalves_ccx (n : Nat) : ∀ (T : Nat),
    (fixHalves n T).countP RGate.isCcx = T * (5 * bw n + 1) := by
  intro T
  induction T with
  | zero => rw [Nat.zero_mul]; rfl
  | succ T ih =>
    show (fixHalves n T ++ fixHalve n T).countP _ = _
    rw [List.countP_append, ih, fixHalve_ccx, Nat.add_mul, Nat.one_mul]

theorem fixGates_ccx (n : Nat) :
    (fixGates n).countP RGate.isCcx = 8 * bw n + 2 * n * (5 * bw n + 1) := by
  show (fixReduce n ++ fixNegate n ++ fixHalves n (2 * n)).countP _ = _
  rw [List.countP_append, List.countP_append, fixReduce_ccx, fixNegate_ccx, fixHalves_ccx]
  omega

/-! ## Circuit composition

The initialisation is one comparison.  The loads are classical.  The forward pass
is the initialisation, `2 n` rounds, and the correction, and the circuit runs it
twice with the controlled copy-out between. -/

theorem initGates_ccx (n : Nat) : (initGates n).countP RGate.isCcx = 2 * (bw n - 1) := by
  show (copyField 0 (aV n) n ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
    ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1).countP _ = _
  simp only [List.countP_append, copyField_ccx, loadX_ccx, nzTest_ccx]
  omega

theorem fwdGates_ccx (n : Nat) :
    (fwdGates n).countP RGate.isCcx
      = 2 * (bw n - 1) + 2 * n * (17 * bw n + 1) + (8 * bw n + 2 * n * (5 * bw n + 1)) := by
  show (initGates n ++ chainT n (2 * n) ++ fixGates n).countP _ = _
  rw [List.countP_append, List.countP_append, initGates_ccx, chainT_ccx, fixGates_ccx]

/-- The circuit's Toffoli count.  At `n = 256` this is `8168222`. -/
theorem gen_ccx (n : Nat) :
    (gen n).gates.countP RGate.isCcx = 88 * n * n + 117 * n + 16 := by
  show (fwdGates n ++ copyC (aNZ n) (aTU n) n n ++ (fwdGates n).reverse).countP _ = _
  rw [List.countP_append, List.countP_append, List.countP_reverse, copyC_ccx,
    fwdGates_ccx]
  simp only [bw]
  have p1 : 2 * n * (17 * (n + 1) + 1) = 34 * (n * n) + 36 * n := by
    rw [show 17 * (n + 1) + 1 = 17 * n + 18 from by omega, Nat.mul_add,
      Nat.mul_comm 17 n, ← Nat.mul_assoc, Nat.mul_assoc 2 n n]
    omega
  have p2 : 2 * n * (5 * (n + 1) + 1) = 10 * (n * n) + 12 * n := by
    rw [show 5 * (n + 1) + 1 = 5 * n + 6 from by omega, Nat.mul_add,
      Nat.mul_comm 5 n, ← Nat.mul_assoc, Nat.mul_assoc 2 n n]
    omega
  have p3 : 88 * n * n = 88 * (n * n) := Nat.mul_assoc 88 n n
  omega

example : (gen 256).gates.countP RGate.isCcx = 5797136 := by
  rw [gen_ccx]

/-! ## Gate-list lengths

The gate count needs the list lengths as well as the Toffoli count, since a
Toffoli compiles to three primitives and everything else to one.  Every gadget
has an exact length except `loadX`, which emits one gate per set bit of its
constant and so is bounded by its width.  That bound is the only slack in the
whole figure. -/

theorem addAt_len (w oa ob oc : Nat) : (addAt w oa ob oc).length = 6 * w := by
  rw [addAt, List.length_map]
  exact VQ.Curve.PointAddition.Arithmetic.Inv.Add.length_body w w 0

theorem subAt_len (w oa ob oc : Nat) : (subAt w oa ob oc).length = 6 * w := by
  rw [subAt, List.length_reverse]
  exact addAt_len w oa ob oc

theorem loadX_len : ∀ (p W v : Nat), (loadX W p v).length ≤ p
  | 0, _, _ => Nat.le_refl 0
  | p + 1, W, v => by
    rw [loadX, List.length_append]
    have h := loadX_len p (W + 1) (v / 2)
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

theorem copyC_len {c : Nat} : ∀ (p src dst : Nat), (copyC c src dst p).length = p
  | 0, _, _ => rfl
  | p + 1, src, dst => by
    show ((RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p)).length = _
    rw [List.length_cons, copyC_len p (src + 1) (dst + 1)]

theorem fred_len (c x y : Nat) : (fred c x y).length = 3 := rfl

theorem swapC_len {c : Nat} : ∀ (p A B : Nat), (swapC c A B p).length = 3 * p
  | 0, _, _ => rfl
  | p + 1, A, B => by
    show (fred c A B ++ swapC c (A + 1) (B + 1) p).length = _
    rw [List.length_append, fred_len, swapC_len p (A + 1) (B + 1)]
    omega

theorem shiftR_len {c : Nat} : ∀ (w off : Nat), (shiftR c off w).length = 3 * (w - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)).length = _
    rw [List.length_append, fred_len, shiftR_len (p + 1) (off + 1)]
    omega

theorem swapU_len (x y : Nat) : (swapU x y).length = 3 := rfl

theorem shiftRU_len : ∀ (w off : Nat), (shiftRU off w).length = 3 * (w - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)).length = _
    rw [List.length_append, swapU_len, shiftRU_len (p + 1) (off + 1)]
    omega

theorem shiftL_len {c : Nat} : ∀ (w off : Nat), (shiftL c off w).length = 3 * (w - 1)
  | 0, _ => rfl
  | 1, _ => rfl
  | p + 2, off => by
    show (shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)).length = _
    rw [List.length_append, fred_len, shiftL_len (p + 1) (off + 1)]
    omega

theorem copyField_len (s d len : Nat) : (copyField s d len).length = len := by
  rw [copyField, List.length_map, List.length_range]

/-- A zero constant loads nothing. -/
theorem loadX_zero : ∀ (p W : Nat), (loadX W p 0).length = 0
  | 0, _ => rfl
  | p + 1, W => by
    rw [loadX, if_neg (by decide), List.length_append, loadX_zero p (W + 1)]
    rfl

/-- Loading one is a single gate. -/
theorem loadX_one : ∀ (p W : Nat), 0 < p → (loadX W p 1).length = 1
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | p + 1, W, _ => by
    rw [loadX, if_pos (by decide), List.length_append,
      show (1 : Nat) / 2 = 0 from by decide, loadX_zero p (W + 1)]
    rfl

theorem cmpPre_len (w ou ov oc : Nat) : (cmpPre w ou ov oc).length ≤ 7 * w + 1 := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc).length ≤ _
  rw [List.length_append, List.length_append, addAt_len]
  have h1 := loadX_len w ou (2 ^ w - 1)
  have h2 := loadX_len 1 oc 1
  omega

theorem majPre_len (w ou ov oc : Nat) : (majPre w ou ov oc).length ≤ 4 * w + 1 := by
  show (loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w).length ≤ _
  rw [List.length_append, List.length_append, majAt_len]
  have h1 := loadX_len w ou (2 ^ w - 1)
  have h2 := loadX_len 1 oc 1
  omega

theorem cmpAt_len (w ou ov oc og : Nat) : (cmpAt w ou ov oc og).length ≤ 14 * w + 3 := by
  have hpre := cmpPre_len w ou ov oc
  show (cmpPre w ou ov oc ++ [RGate.cx (ov + (w - 1)) og]
    ++ (cmpPre w ou ov oc).reverse).length ≤ _
  rw [List.length_append, List.length_append, List.length_reverse]
  simp only [List.length_cons, List.length_nil]
  omega

/-! ### Round and chain semantics -/

theorem roundGates_len (n t : Nat) : (roundGates n t).length ≤ 48 * bw n + 8 := by
  have hz : (segZero n t).length ≤ 6 * bw n - 3 := by
    show (nzTest (aV n) (aTR n) (aZ n + t) (bw n)).length ≤ _
    rw [nzTest_len _ _ _ _ (bw_pos n)]
    exact Nat.le_refl _
  have hd : (segDispatch n t).length = 5 := rfl
  have hc : (segCompare n t).length ≤ 8 * bw n + 8 := by
    show (majPre (bw n) (aU n) (aV n) (aC n)
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ cmpUse n t
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ (majPre (bw n) (aU n) (aV n) (aC n)).reverse).length ≤ _
    simp only [List.length_append, List.length_reverse,
      show (cmpUse n t).length = 2 from rfl,
      show [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)].length = 2 from rfl]
    have h := majPre_len (bw n) (aU n) (aV n) (aC n)
    omega
  have hs : (segSwap n).length = 6 * bw n := by
    show (swapC (aA n) (aU n) (aV n) (bw n) ++ swapC (aA n) (aR n) (aS n) (bw n)).length = _
    rw [List.length_append, swapC_len, swapC_len]
    omega
  have ha : (segArith n).length = 16 * bw n := by
    show (copyC (aT n) (aU n) (aTU n) (bw n) ++ subAt (bw n) (aTU n) (aV n) (aC n)
      ++ copyC (aT n) (aU n) (aTU n) (bw n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n) ++ addAt (bw n) (aTR n) (aS n) (aC n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n)).length = _
    simp only [List.length_append, copyC_len, subAt_len, addAt_len]
    omega
  have hh : (segShift n t).length = 6 * bw n - 6 := by
    show (shiftRU (aV n) (bw n) ++ shiftL (aZ n + t) (aR n) (bw n)).length = _
    rw [List.length_append, shiftRU_len, shiftL_len]
    have := bw_pos n
    omega
  have hcl : (segClear n t).length = 4 := rfl
  show (segZero n t ++ segDispatch n t ++ segCompare n t ++ segSwap n ++ segArith n
    ++ segShift n t ++ segSwap n ++ segClear n t).length ≤ _
  simp only [List.length_append]
  rw [hd, hs, ha, hh, hcl]
  have := bw_pos n
  omega

theorem chainT_len (n : Nat) : ∀ (T : Nat),
    (chainT n T).length ≤ T * (48 * bw n + 8) := by
  intro T
  induction T with
  | zero => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | succ T ih =>
    show (chainT n T ++ roundGates n T).length ≤ _
    rw [List.length_append, Nat.add_mul, Nat.one_mul]
    have := roundGates_len n T
    omega

/-! ### Circuit resource composition -/

theorem fixReduce_len (n : Nat) : (fixReduce n).length ≤ 22 * bw n + 4 := by
  show (cmpAt (bw n) (aS n) (aR n) (aC n) (aGt n) ++ [RGate.x (aGt n)]
    ++ loadCX (aGt n) (aTU n) (bw n) modulus
    ++ subAt (bw n) (aTU n) (aR n) (aC n)
    ++ loadCX (aGt n) (aTU n) (bw n) modulus).length ≤ _
  simp only [List.length_append, subAt_len, List.length_cons, List.length_nil]
  have h := cmpAt_len (bw n) (aS n) (aR n) (aC n) (aGt n)
  have h1 := loadCX_len (aGt n) (bw n) (aTU n) modulus
  omega

theorem fixNegate_len (n : Nat) : (fixNegate n).length ≤ 7 * bw n := by
  show (loadX (aTU n) (bw n) modulus ++ subAt (bw n) (aR n) (aTU n) (aC n)).length ≤ _
  rw [List.length_append, subAt_len]
  have h := loadX_len (bw n) (aTU n) modulus
  omega

theorem hCmp_len (n : Nat) : (hCmp n).length ≤ 4 * bw n + 3 := by
  show (majPre (bw n) (aTU n) (aTR n) (aC n)
    ++ [RGate.cx (aTU n + bw n - 1) (aG n), RGate.x (aG n)]).length ≤ _
  rw [List.length_append]
  have h := majPre_len (bw n) (aTU n) (aTR n) (aC n)
  simp only [List.length_cons, List.length_nil]
  omega

theorem fixHalve_len (n t : Nat) : (fixHalve n t).length ≤ 21 * bw n + 6 := by
  show ([RGate.ccx (aZ n + t) (aTU n) (aH n)]
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ addAt (bw n) (aTR n) (aTU n) (aC n)
    ++ loadCX (aH n) (aTR n) (bw n) modulus
    ++ shiftR (aZ n + t) (aTU n) (bw n)
    ++ loadX (aTR n) (bw n) halfMod
    ++ (hCmp n ++ [RGate.ccx (aZ n + t) (aG n) (aH n)] ++ (hCmp n).reverse)
    ++ loadX (aTR n) (bw n) halfMod).length ≤ _
  simp only [List.length_append, List.length_reverse, addAt_len, shiftR_len,
    List.length_cons, List.length_nil]
  have := bw_pos n
  have h1 := loadCX_len (aH n) (bw n) (aTR n) modulus
  have h2 := loadX_len (bw n) (aTR n) halfMod
  have h3 := hCmp_len n
  omega

theorem fixHalves_len (n : Nat) : ∀ (T : Nat),
    (fixHalves n T).length ≤ T * (21 * bw n + 6) := by
  intro T
  induction T with
  | zero => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | succ T ih =>
    show (fixHalves n T ++ fixHalve n T).length ≤ _
    rw [List.length_append, Nat.add_mul, Nat.one_mul]
    have h := fixHalve_len n T
    omega

theorem fixGates_len (n : Nat) :
    (fixGates n).length ≤ 29 * bw n + 4 + 2 * n * (21 * bw n + 6) := by
  show (fixReduce n ++ fixNegate n ++ fixHalves n (2 * n)).length ≤ _
  rw [List.length_append, List.length_append]
  have h0 := fixNegate_len n
  have h1 := fixReduce_len n
  have h2 := fixHalves_len n (2 * n)
  omega

theorem initGates_len (n : Nat) : (initGates n).length ≤ n + 7 * bw n - 2 := by
  show (copyField 0 (aV n) n ++ nzTest (aV n) (aTR n) (aNZ n) (bw n)
    ++ loadX (aU n) (bw n) modulus ++ loadX (aS n) (bw n) 1).length ≤ _
  simp only [List.length_append, copyField_len]
  rw [nzTest_len _ _ _ _ (bw_pos n)]
  have h2 := loadX_one (bw n) (aS n) (bw_pos n)
  have h3 := loadX_len (bw n) (aU n) modulus
  have := bw_pos n
  omega

theorem fwdGates_len (n : Nat) :
    (fwdGates n).length
      ≤ n + 7 * bw n - 2 + 2 * n * (48 * bw n + 8)
        + (29 * bw n + 4 + 2 * n * (21 * bw n + 6)) := by
  show (initGates n ++ chainT n (2 * n) ++ fixGates n).length ≤ _
  rw [List.length_append, List.length_append]
  have h1 := initGates_len n
  have h2 := chainT_len n (2 * n)
  have h3 := fixGates_len n
  omega

/-- The circuit's gate count.  At `n = 256` the bound is `39270826`.
The only slack is the modulus load, which emits one gate per set bit and is
counted at the register width. -/
theorem gen_len (n : Nat) :
    (gen n).gates.length ≤ 276 * n * n + 407 * n + 76 := by
  show (fwdGates n ++ copyC (aNZ n) (aTU n) n n ++ (fwdGates n).reverse).length ≤ _
  rw [List.length_append, List.length_append, List.length_reverse, copyC_len]
  have h := fwdGates_len n
  simp only [bw] at h ⊢
  have p1 : 2 * n * (48 * (n + 1) + 8) = 96 * (n * n) + 112 * n := by
    rw [show 48 * (n + 1) + 8 = 48 * n + 56 from by omega, Nat.mul_add,
      Nat.mul_comm 48 n, ← Nat.mul_assoc, Nat.mul_assoc 2 n n]
    omega
  have p2 : 2 * n * (21 * (n + 1) + 6) = 42 * (n * n) + 54 * n := by
    rw [show 21 * (n + 1) + 6 = 21 * n + 27 from by omega, Nat.mul_add,
      Nat.mul_comm 21 n, ← Nat.mul_assoc, Nat.mul_assoc 2 n n]
    omega
  have p3 : 276 * n * n = 276 * (n * n) := Nat.mul_assoc 276 n n
  have hbp : 0 < n + 1 := by omega
  omega

end VQ.Curve.PointAddition.Arithmetic.Inv
