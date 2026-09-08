import VQ.Curve.PointAddition.Arithmetic.Inv.Swap
import VQ.Curve.PointAddition.Arithmetic.Inv.Cmp
import VQ.Curve.PointAddition.Arithmetic.Inv.Geom
import VQ.Curve.PointAddition.Arithmetic.Inv.Round

/-!
# Round circuit

Algorithm 7b of Häner, Jaques, Naehrig, Roetteler, and Soeken, laid out on the
registers `VQ.Curve.PointAddition.Arithmetic.Inv/Geom.lean` fixes.

    bswap := (u even and v odd) or (u odd and v odd and u > v)
    if bswap:  swap u v;  swap r s
    if both odd:  v := v - u;  s := r + s
    v := v / 2
    r := 2 r
    if bswap:  swap u v;  swap r s

Two control bits drive it and both are computed from `u`, `v`, and the
comparison, before anything moves.  Writing the four branches in the numbering
`VQ.Curve.PointAddition.Arithmetic.Inv.step` uses -- `u` even, `u` odd and `v` even, both odd with `v < u`, both
odd otherwise -- the two bits are

    a = bswap = branch 1 or branch 3
    m         = branch 2 or branch 3

so `both odd` is their exclusive-nor, and `a` is the parity of the new `r`,
which is how it is cleared at the end.  `m` stays: it is the one kept qubit per
round the published circuit also carries.

The third control is `z`, meaning `v` was nonzero at the start of the round.
It gates the two shifts, and it stays as well.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The zero test: `v != 0` into the round's second kept bit.

A general comparator against the constant one answers the question at four
adders' worth of Toffolis.  The question is the or of `v`'s bits, and an
or-ladder answers it at one Toffoli per bit with its own uncomputation, using
the scratch register the arithmetic has not reached yet. -/
def segZero (n t : Nat) : List RGate :=
  nzTest (aV n) (aTR n) (aZ n + t) (bw n)

/-- The dispatch: `bswap` as `u` even, `both odd`, and the kept branch bit. -/
def segDispatch (n t : Nat) : List RGate :=
  [RGate.x (aA n), RGate.cx (aU n) (aA n)]
    ++ [RGate.ccx (aU n) (aV n) (aT n)]
    ++ [RGate.cx (aU n) (aM n + t), RGate.cx (aT n) (aM n + t)]

/-- The two dispatch bits the comparison feeds. -/
def cmpUse (n t : Nat) : List RGate :=
  [RGate.ccx (aT n) (aGt n) (aA n), RGate.ccx (aT n) (aGt n) (aM n + t)]

/-- The comparison, feeding both dispatch bits and then cleared.

`cmpAt` consists of an adder, a copy of the difference's top bit, and the
reversed adder.  Invoking it before and after the use requires four adder
passes because the second invocation rebuilds the difference only to clear
`aGt`.  The prepared difference remains after the first copy, so another copy
from the same bit clears `aGt` before one reversed adder.  This construction
uses two adder passes. -/
def segCompare (n t : Nat) : List RGate :=
  majPre (bw n) (aU n) (aV n) (aC n)
    ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
    ++ cmpUse n t
    ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
    ++ (majPre (bw n) (aU n) (aV n) (aC n)).reverse

/-- Reference construction that runs the comparison before and after the use. -/
def segCompareOld (n t : Nat) : List RGate :=
  cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) ++ cmpUse n t
    ++ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)

/-- `u` with `v` and `r` with `s`, under `bswap`. -/
def segSwap (n : Nat) : List RGate :=
  swapC (aA n) (aU n) (aV n) (bw n) ++ swapC (aA n) (aR n) (aS n) (bw n)

/-- `v := v - u` and `s := s + r`, under `both odd`. -/
def segArith (n : Nat) : List RGate :=
  copyC (aT n) (aU n) (aTU n) (bw n) ++ subAt (bw n) (aTU n) (aV n) (aC n)
    ++ copyC (aT n) (aU n) (aTU n) (bw n)
    ++ copyC (aT n) (aR n) (aTR n) (bw n) ++ addAt (bw n) (aTR n) (aS n) (aC n)
    ++ copyC (aT n) (aR n) (aTR n) (bw n)

/-- `v` halves and `r` doubles.

The doubling carries the termination bit, because doubling `r` after the chain
has finished destroys the answer.  The halving carries nothing: a finished round
has `v = 0` and halving zero changes nothing, so an unconditional swap network
does the same work as a Fredkin one at no Toffoli cost. -/
def segShift (n t : Nat) : List RGate :=
  shiftRU (aV n) (bw n) ++ shiftL (aZ n + t) (aR n) (bw n)

/-- `both odd` against the two kept bits, then `bswap` against the new `r`. -/
def segClear (n t : Nat) : List RGate :=
  [RGate.cx (aA n) (aT n), RGate.cx (aM n + t) (aT n), RGate.x (aT n)]
    ++ [RGate.ccx (aZ n + t) (aR n) (aA n)]


/-! ## Comparison equivalence

`cmpUse` touches `aA`, `aT`, `aGt`, and the kept bit.  The adder touches `u`,
`v`, and the carry.  Those sets are disjoint, so the use commutes past the
adder, and the two shapes have the same action on every state, not only on
states where `aGt` starts clear. -/

theorem bv_actGates_outside {gs : List RGate} {q i : Nat}
    (h : ∀ g ∈ gs, ∀ r ∈ g.wires, r < q ∨ q + 1 ≤ r) :
    bv (actGates gs i) q = bv i q := by
  rw [← readField_one, readField_actGates_outside h, readField_one]

/-- The two Toffolis as a pair of one-bit writes. -/
theorem cmpUse_act (n t : Nat) (j : Nat) :
    actGates (cmpUse n t) j
      = writeField (writeField j (aA n) 1 ((bv j (aA n) + bv j (aT n) * bv j (aGt n)) % 2))
          (aM n + t) 1 ((bv j (aM n + t) + bv j (aT n) * bv j (aGt n)) % 2) := by
  have hA : ∀ x : Nat, aA n + 1 ≤ x →
      bv (writeField j (aA n) 1 ((bv j (aA n) + bv j (aT n) * bv j (aGt n)) % 2)) x
        = bv j x := by
    intro x hx
    rw [← readField_one, readField_writeField_of_disjoint (Or.inl hx), readField_one]
  show RGate.act (RGate.ccx (aT n) (aGt n) (aM n + t))
    (RGate.act (RGate.ccx (aT n) (aGt n) (aA n)) j) = _
  rw [act_ccx, act_ccx, hA (aM n + t) (by simp only [aM, aNZ, aC, aGt, aT, aA]; omega),
    hA (aT n) (by simp only [aT, aA]; omega),
    hA (aGt n) (by simp only [aGt, aT, aA]; omega)]

/-- The adder avoids every wire the use writes or reads. -/
theorem cmpPre_avoids_use {n t : Nat} (ht : t < 2 * n) (q : Nat)
    (hq : q = aA n ∨ q = aT n ∨ q = aGt n ∨ q = aM n + t) :
    ∀ g ∈ majPre (bw n) (aU n) (aV n) (aC n), ∀ r ∈ g.wires, r < q ∨ q + 1 ≤ r := by
  have hgeu : aU n + bw n ≤ q ∨ q + 1 ≤ aU n := by
    rcases hq with h | h | h | h <;>
      simp only [h, aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, bw] <;> omega
  have hgev : aV n + bw n ≤ q ∨ q + 1 ≤ aV n := by
    rcases hq with h | h | h | h <;>
      simp only [h, aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, bw] <;> omega
  have hgec : aC n + 1 ≤ q ∨ q + 1 ≤ aC n := by
    rcases hq with h | h | h | h <;>
      simp only [h, aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, bw] <;> omega
  exact majPre_avoids (by simp only [bw]; omega) hgeu hgev hgec

/-- The gates of round `t`, at width `n`.  `t` selects which kept qubits this
round writes into. -/
def roundGates (n t : Nat) : List RGate :=
  segZero n t ++ segDispatch n t ++ segCompare n t ++ segSwap n ++ segArith n
    ++ segShift n t ++ segSwap n ++ segClear n t


/-- The use commutes past any gates avoiding its four wires. -/
theorem cmpUse_comm {n t : Nat} {gs : List RGate}
    (hA : ∀ g ∈ gs, ∀ r ∈ g.wires, r < aA n ∨ aA n + 1 ≤ r)
    (hT : ∀ g ∈ gs, ∀ r ∈ g.wires, r < aT n ∨ aT n + 1 ≤ r)
    (hG : ∀ g ∈ gs, ∀ r ∈ g.wires, r < aGt n ∨ aGt n + 1 ≤ r)
    (hM : ∀ g ∈ gs, ∀ r ∈ g.wires, r < aM n + t ∨ aM n + t + 1 ≤ r) (X : Nat) :
    actGates (cmpUse n t) (actGates gs X) = actGates gs (actGates (cmpUse n t) X) := by
  rw [cmpUse_act, cmpUse_act,
    bv_actGates_outside hA, bv_actGates_outside hT, bv_actGates_outside hG,
    bv_actGates_outside hM,
    actGates_write_of_outside hM, actGates_write_of_outside hA]

/-! ### Gate-list containment

The wire bounds and the well-formedness proof then transfer without being
redone, since both are statements about the gates one at a time. -/

theorem mem_cmpMaj_of_mem_pre {w ou ov oc og : Nat} {g : RGate}
    (h : g ∈ majPre w ou ov oc) : g ∈ cmpMaj w ou ov oc og :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem mem_cmpMaj_of_mem_rev {w ou ov oc og : Nat} {g : RGate}
    (h : g ∈ (majPre w ou ov oc).reverse) : g ∈ cmpMaj w ou ov oc og :=
  List.mem_append_right _ h

theorem cx_mem_cmpMaj (w ou ov oc og : Nat) :
    RGate.cx (ou + w - 1) og ∈ cmpMaj w ou ov oc og :=
  List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem x_mem_cmpMaj (w ou ov oc og : Nat) :
    RGate.x og ∈ cmpMaj w ou ov oc og :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem segCompare_mem_old {n t : Nat} : ∀ g ∈ segCompare n t, g ∈ segCompareOld n t := by
  intro g hg
  have hg' : g ∈ majPre (bw n) (aU n) (aV n) (aC n)
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)] ++ cmpUse n t
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ (majPre (bw n) (aU n) (aV n) (aC n)).reverse := hg
  have goal : ∀ h : g ∈ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) ∨ g ∈ cmpUse n t,
      g ∈ segCompareOld n t := by
    intro h
    show g ∈ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) ++ cmpUse n t
      ++ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)
    cases h with
    | inl h => exact List.mem_append_left _ (List.mem_append_left _ h)
    | inr h => exact List.mem_append_left _ (List.mem_append_right _ h)
  have hpair : ∀ g' : RGate, g' = RGate.cx (aU n + bw n - 1) (aGt n) ∨ g' = RGate.x (aGt n) →
      g' ∈ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) := by
    intro g' h
    cases h with
    | inl h => rw [h]; exact cx_mem_cmpMaj _ _ _ _ _
    | inr h => rw [h]; exact x_mem_cmpMaj _ _ _ _ _
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hg'
  rcases hg' with ((((h | h) | h) | h) | h)
  · exact goal (Or.inl (mem_cmpMaj_of_mem_pre h))
  · refine goal (Or.inl (hpair g ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact h
  · exact goal (Or.inr h)
  · refine goal (Or.inl (hpair g ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact h
  · exact goal (Or.inl (mem_cmpMaj_of_mem_rev h))

/-- The two shapes agree.  Four adders become two. -/
theorem segCompare_act {n t : Nat} (ht : t < 2 * n) (X : Nat) :
    actGates (segCompare n t) X = actGates (segCompareOld n t) X := by
  have hwf : (majPre (bw n) (aU n) (aV n) (aC n)).all
      (RGate.wellFormed (totalWidth n)) = true :=
    majPre_wf (by simp only [aU, aV, bw]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, bw]; omega)
      (by simp only [aU, aV, bw, totalWidth]; omega)
      (by simp only [aU, aV, bw, totalWidth]; omega)
      (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, bw, totalWidth]; omega)
  have hrev : ∀ i, actGates (majPre (bw n) (aU n) (aV n) (aC n))
      (actGates (majPre (bw n) (aU n) (aV n) (aC n)).reverse i) = i := by
    intro i
    have h := actGates_reverse (w := totalWidth n)
      (gs := (majPre (bw n) (aU n) (aV n) (aC n)).reverse)
      (by exact List.all_eq_true.mpr fun g hg =>
        List.all_eq_true.mp hwf g (List.mem_reverse.mp hg)) i
    rwa [List.reverse_reverse] at h
  have hfwd := actGates_reverse (w := totalWidth n) hwf
  show actGates (majPre (bw n) (aU n) (aV n) (aC n)
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)] ++ cmpUse n t
      ++ [RGate.cx (aU n + bw n - 1) (aGt n), RGate.x (aGt n)]
      ++ (majPre (bw n) (aU n) (aV n) (aC n)).reverse) X
    = actGates (cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) ++ cmpUse n t
      ++ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)) X
  have hrevAvoid : ∀ q : Nat, (q = aA n ∨ q = aT n ∨ q = aGt n ∨ q = aM n + t) →
      ∀ g ∈ (majPre (bw n) (aU n) (aV n) (aC n)).reverse, ∀ r ∈ g.wires,
        r < q ∨ q + 1 ≤ r := by
    intro q hq g hg
    exact cmpPre_avoids_use ht q hq g (List.mem_reverse.mp hg)
  have key : ∀ Y, actGates (majPre (bw n) (aU n) (aV n) (aC n))
      (actGates (cmpUse n t)
        (actGates (majPre (bw n) (aU n) (aV n) (aC n)).reverse Y))
      = actGates (cmpUse n t) Y := by
    intro Y
    rw [cmpUse_comm (hrevAvoid (aA n) (Or.inl rfl))
      (hrevAvoid (aT n) (Or.inr (Or.inl rfl)))
      (hrevAvoid (aGt n) (Or.inr (Or.inr (Or.inl rfl))))
      (hrevAvoid (aM n + t) (Or.inr (Or.inr (Or.inr rfl)))), hrev]
  simp only [cmpMaj, actGates_append]
  rw [key]



end VQ.Curve.PointAddition.Arithmetic.Inv
