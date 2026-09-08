import VQ.Curve.PointAddition.Arithmetic.Inv.Seg
import VQ.Reversible.Blocks

/-!
# Round wire bounds

Round `t` leaves the retained bits of every other round unchanged.  Wire
bounds for each gadget establish this property for the round's gate list.

Everything a round touches lies in the block from `aU` up to `aM`, except the
two kept wires `aM + t` and `aZ + t`, which are its own.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The wires of a placed adder lie in its three registers. -/
theorem addAt_wires {w oa ob oc : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob) :
    ∀ g ∈ addAt w oa ob oc, ∀ q ∈ g.wires,
      (oa ≤ q ∧ q < oa + w) ∨ (ob ≤ q ∧ q < ob + w) ∨ q = oc := by
  intro g hg q hq
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  have hlt : q' < Layout.width (addL w) := by
    have := add_wf w g' hg'
    cases g' <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega
  obtain ⟨j, b, hj, hb, rfl⟩ := exists_field (addL w) q' hlt
  rw [place_field (addL w) [oa, ob, oc] j b (by simp only [addL] at hj ⊢; omega) hb]
  simp only [addL, List.length_cons, List.length_nil] at hj
  match j with
  | 0 =>
    refine Or.inl ⟨by simp, ?_⟩
    simp only [addL, Layout.size] at hb
    simp
    omega
  | 1 =>
    refine Or.inr (Or.inl ⟨by simp, ?_⟩)
    simp only [addL, Layout.size] at hb
    simp
    omega
  | 2 =>
    refine Or.inr (Or.inr ?_)
    simp only [addL, Layout.size] at hb
    simp
    omega
  | _ + 3 => omega

/-- Reversing a list does not change which wires it uses. -/
theorem reverse_wires {gs : List RGate} {P : Nat → Prop}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, P q) : ∀ g ∈ gs.reverse, ∀ q ∈ g.wires, P q :=
  fun g hg => h g (List.mem_reverse.mp hg)

/-- The wires of a Fredkin are its three. -/
theorem fred_wires {c x y : Nat} : ∀ g ∈ fred c x y, ∀ q ∈ g.wires,
    q = c ∨ q = x ∨ q = y := by
  intro g hg q hq
  simp only [fred, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp only [RGate.wires, List.mem_cons,
    List.not_mem_nil, or_false] at hq <;> omega

/-- A field swap touches the control and the two fields. -/
theorem swapC_wires {c : Nat} : ∀ (p A B : Nat), ∀ g ∈ swapC c A B p, ∀ q ∈ g.wires,
    q = c ∨ (A ≤ q ∧ q < A + p) ∨ (B ≤ q ∧ q < B + p) := by
  intro p
  induction p with
  | zero => intro A B g hg; simp [swapC] at hg
  | succ p ih =>
    intro A B g hg q hq
    rw [show swapC c A B (p + 1) = fred c A B ++ swapC c (A + 1) (B + 1) p from rfl,
      List.mem_append] at hg
    cases hg with
    | inl h => have := fred_wires g h q hq; omega
    | inr h => have := ih (A + 1) (B + 1) g h q hq; omega

/-- A shift touches the control and the field. -/
theorem swapU_wires {x y : Nat} : ∀ g ∈ swapU x y, ∀ q ∈ g.wires, q = x ∨ q = y := by
  intro g hg q hq
  simp only [swapU, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp only [RGate.wires, List.mem_cons,
    List.not_mem_nil, or_false] at hq <;> omega

theorem shiftRU_wires : ∀ (w off : Nat), ∀ g ∈ shiftRU off w, ∀ q ∈ g.wires,
    off ≤ q ∧ q < off + w
  | 0 => by intro off g hg; simp [shiftRU] at hg
  | 1 => by intro off g hg; simp [shiftRU] at hg
  | p + 2 => by
      intro off g hg q hq
      rw [show shiftRU off (p + 2) = swapU off (off + 1) ++ shiftRU (off + 1) (p + 1) from rfl,
        List.mem_append] at hg
      cases hg with
      | inl h => have := swapU_wires g h q hq; omega
      | inr h => have := shiftRU_wires (p + 1) (off + 1) g h q hq; omega

theorem swapU_wf {x y W : Nat} (hxy : x ≠ y) (hx : x < W) (hy : y < W) :
    (swapU x y).all (RGate.wellFormed W) = true := by
  simp [swapU, RGate.wellFormed]
  omega

theorem shiftRU_wf : ∀ (w off W : Nat), off + w ≤ W →
    (shiftRU off w).all (RGate.wellFormed W) = true
  | 0 => by intro off W _; simp [shiftRU]
  | 1 => by intro off W _; simp [shiftRU]
  | p + 2 => by
      intro off W h
      show (swapU off (off + 1) ++ shiftRU (off + 1) (p + 1)).all _ = true
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨swapU_wf (by omega) (by omega) (by omega),
        shiftRU_wf (p + 1) (off + 1) W (by omega)⟩

theorem shiftR_wires {c : Nat} : ∀ (w off : Nat), ∀ g ∈ shiftR c off w, ∀ q ∈ g.wires,
    q = c ∨ (off ≤ q ∧ q < off + w)
  | 0 => by intro off g hg; simp [shiftR] at hg
  | 1 => by intro off g hg; simp [shiftR] at hg
  | p + 2 => by
      intro off g hg q hq
      rw [show shiftR c off (p + 2) = fred c off (off + 1) ++ shiftR c (off + 1) (p + 1) from rfl,
        List.mem_append] at hg
      cases hg with
      | inl h => have := fred_wires g h q hq; omega
      | inr h => have := shiftR_wires (p + 1) (off + 1) g h q hq; omega

theorem shiftL_wires {c : Nat} : ∀ (w off : Nat), ∀ g ∈ shiftL c off w, ∀ q ∈ g.wires,
    q = c ∨ (off ≤ q ∧ q < off + w)
  | 0 => by intro off g hg; simp [shiftL] at hg
  | 1 => by intro off g hg; simp [shiftL] at hg
  | p + 2 => by
      intro off g hg q hq
      rw [show shiftL c off (p + 2) = shiftL c (off + 1) (p + 1) ++ fred c off (off + 1) from rfl,
        List.mem_append] at hg
      cases hg with
      | inl h => have := shiftL_wires (p + 1) (off + 1) g h q hq; omega
      | inr h => have := fred_wires g h q hq; omega

/-- A controlled copy touches the control and the two fields. -/
theorem copyC_wires {c : Nat} : ∀ (p src dst : Nat), ∀ g ∈ copyC c src dst p, ∀ q ∈ g.wires,
    q = c ∨ (src ≤ q ∧ q < src + p) ∨ (dst ≤ q ∧ q < dst + p) := by
  intro p
  induction p with
  | zero => intro src dst g hg; simp [copyC] at hg
  | succ p ih =>
    intro src dst g hg q hq
    rw [show copyC c src dst (p + 1) = RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p
      from rfl, List.mem_cons] at hg
    cases hg with
    | inl h =>
      subst h
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    | inr h => have := ih (src + 1) (dst + 1) g h q hq; omega

/-! ## Round circuit

Every wire a round touches is below `aM`, or is one of the round's own two kept
wires. -/

/-- The property the round's wires satisfy.

The bound is `aNZ`, not `aM`: the nonzero wire sits between the working
registers and the kept region, and the copy-out's control is that wire, so the
rounds have to be shown not to touch it. -/
def Touches (n t q : Nat) : Prop :=
  (aU n ≤ q ∧ q < aNZ n) ∨ q = aM n + t ∨ q = aZ n + t

/-- The comparison touches its four registers. -/
theorem cmpMaj_wires {w ou ov oc og : Nat} (hw : 0 < w) :
    ∀ g ∈ cmpMaj w ou ov oc og, ∀ q ∈ g.wires,
      (ou ≤ q ∧ q < ou + w) ∨ (ov ≤ q ∧ q < ov + w) ∨ q = oc ∨ q = og := by
  have hpre : ∀ g ∈ majPre w ou ov oc, ∀ q ∈ g.wires,
      (ou ≤ q ∧ q < ou + w) ∨ (ov ≤ q ∧ q < ov + w) ∨ q = oc ∨ q = og := by
    intro g hg q hq
    have hg' : g ∈ loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ majAt ou ov oc 0 w := hg
    rw [List.mem_append, List.mem_append] at hg'
    rcases hg' with (h | h) | h
    · have := loadX_wires w ou (2 ^ w - 1) g h q hq; omega
    · have := loadX_wires 1 oc 1 g h q hq; omega
    · have := majAt_wires ou ov w oc 0 g h q hq; omega
  intro g hg q hq
  have hg' : g ∈ majPre w ou ov oc ++ [RGate.cx (ou + w - 1) og, RGate.x og]
    ++ (majPre w ou ov oc).reverse := hg
  rw [List.mem_append, List.mem_append] at hg'
  rcases hg' with (h | h) | h
  · exact hpre g h q hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> omega
  · exact hpre g (List.mem_reverse.mp h) q hq

theorem cmpMaj_wf {w ou ov oc og W : Nat} (hw : 0 < w) (hord : ou + w ≤ ov)
    (hc : oc + 1 ≤ ou ∨ ov + w ≤ oc) (hgu : ou + w ≤ og ∨ og + 1 ≤ ou)
    (hwu : ou + w ≤ W) (hwv : ov + w ≤ W) (hwc : oc + 1 ≤ W) (hwg : og + 1 ≤ W) :
    (cmpMaj w ou ov oc og).all (RGate.wellFormed W) = true := by
  have hpre := majPre_wf (Wd := W) hord hc hwu hwv hwc
  show (majPre w ou ov oc ++ [RGate.cx (ou + w - 1) og, RGate.x og]
    ++ (majPre w ou ov oc).reverse).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hpre, ?_⟩, List.all_eq_true.mpr fun g hg =>
    List.all_eq_true.mp hpre g (List.mem_reverse.mp hg)⟩
  have hlo : ou ≤ ou + w - 1 := by omega
  have hhi : ou + w - 1 < ou + w := by omega
  simp [RGate.wellFormed]
  constructor
  · omega
  · omega

theorem cmpAt_wires {w ou ov oc og : Nat} (hw : 0 < w)
    (hab : ou + w ≤ ov ∨ ov + w ≤ ou)
    (hac : ou + w ≤ oc ∨ oc + 1 ≤ ou)
    (hbc : ov + w ≤ oc ∨ oc + 1 ≤ ov) :
    ∀ g ∈ cmpAt w ou ov oc og, ∀ q ∈ g.wires,
      (ou ≤ q ∧ q < ou + w) ∨ (ov ≤ q ∧ q < ov + w) ∨ q = oc ∨ q = og := by
  have hpre : ∀ g ∈ cmpPre w ou ov oc, ∀ q ∈ g.wires,
      (ou ≤ q ∧ q < ou + w) ∨ (ov ≤ q ∧ q < ov + w) ∨ q = oc ∨ q = og := by
    intro g hg q hq
    have hg' : g ∈ loadX ou w (2 ^ w - 1) ++ loadX oc 1 1 ++ addAt w ou ov oc := hg
    rw [List.mem_append, List.mem_append] at hg'
    cases hg' with
    | inl h =>
      cases h with
      | inl h => have := loadX_wires w ou (2 ^ w - 1) g h q hq; omega
      | inr h => have := loadX_wires 1 oc 1 g h q hq; omega
    | inr h => have := addAt_wires hab hac hbc g h q hq; omega
  intro g hg q hq
  have hg' : g ∈ cmpPre w ou ov oc ++ [RGate.cx (ov + (w - 1)) og]
      ++ (cmpPre w ou ov oc).reverse := hg
  rw [List.mem_append, List.mem_append] at hg'
  cases hg' with
  | inl h =>
    cases h with
    | inl h => exact hpre g h q hq
    | inr h =>
      simp only [List.mem_singleton] at h
      subst h
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      cases hq with
      | inl h => refine Or.inr (Or.inl ⟨by omega, by omega⟩)
      | inr h => exact Or.inr (Or.inr (Or.inr (by omega)))
  | inr h => exact hpre g (List.mem_reverse.mp h) q hq

/-! ### Well-formedness

A gate is well formed at a width when its wires lie below it and, for the
multi-wire gates, are distinct.  Each gadget's distinctness is its own. -/

theorem copyField_wf {s d len W : Nat} (hd : s + len ≤ d ∨ d + len ≤ s)
    (hs : s + len ≤ W) (hdw : d + len ≤ W) :
    (copyField s d len).all (RGate.wellFormed W) = true := by
  refine List.all_eq_true.mpr (fun g hg => ?_)
  obtain ⟨t, ht, rfl⟩ := copyField_mem hg
  simp [RGate.wellFormed]
  omega

theorem copyC_wf {c : Nat} : ∀ (p src dst W : Nat),
    (dst + p ≤ src ∨ src + p ≤ dst) → (c < dst ∨ dst + p ≤ c) →
    (c < src ∨ src + p ≤ c) → c < W → src + p ≤ W → dst + p ≤ W →
    (copyC c src dst p).all (RGate.wellFormed W) = true := by
  intro p
  induction p with
  | zero => intro src dst W _ _ _ _ _ _; simp [copyC]
  | succ p ih =>
    intro src dst W h1 h2 h3 h4 h5 h6
    show ((RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p)).all _ = true
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih (src + 1) (dst + 1) W (by omega) (by omega) (by omega) h4
      (by omega) (by omega)⟩
    simp [RGate.wellFormed]
    omega

theorem fred_wf {c x y W : Nat} (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y)
    (h1 : x < W) (h2 : y < W) (h3 : c < W) :
    (fred c x y).all (RGate.wellFormed W) = true := by
  simp [fred, RGate.wellFormed, hxy, hcx, hcy, h1, h2, h3, Ne.symm hxy]

theorem swapC_wf {c : Nat} : ∀ (p A B W : Nat),
    (A + p ≤ B ∨ B + p ≤ A) → (c < A ∨ A + p ≤ c) → (c < B ∨ B + p ≤ c) →
    c < W → A + p ≤ W → B + p ≤ W →
    (swapC c A B p).all (RGate.wellFormed W) = true := by
  intro p
  induction p with
  | zero => intro A B W _ _ _ _ _ _; simp [swapC]
  | succ p ih =>
    intro A B W h1 h2 h3 h4 h5 h6
    show (fred c A B ++ swapC c (A + 1) (B + 1) p).all _ = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨fred_wf (by omega) (by omega) (by omega) (by omega) (by omega) h4,
      ih (A + 1) (B + 1) W (by omega) (by omega) (by omega) h4 (by omega) (by omega)⟩

theorem shiftR_wf {c : Nat} : ∀ (w off W : Nat), (c < off ∨ off + w ≤ c) →
    c < W → off + w ≤ W → (shiftR c off w).all (RGate.wellFormed W) = true
  | 0 => by intro off W _ _ _; simp [shiftR]
  | 1 => by intro off W _ _ _; simp [shiftR]
  | p + 2 => by
      intro off W h1 h2 h3
      show (fred c off (off + 1) ++ shiftR c (off + 1) (p + 1)).all _ = true
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨fred_wf (by omega) (by omega) (by omega) (by omega) (by omega) h2,
        shiftR_wf (p + 1) (off + 1) W (by omega) h2 (by omega)⟩

theorem shiftL_wf {c : Nat} : ∀ (w off W : Nat), (c < off ∨ off + w ≤ c) →
    c < W → off + w ≤ W → (shiftL c off w).all (RGate.wellFormed W) = true
  | 0 => by intro off W _ _ _; simp [shiftL]
  | 1 => by intro off W _ _ _; simp [shiftL]
  | p + 2 => by
      intro off W h1 h2 h3
      show (shiftL c (off + 1) (p + 1) ++ fred c off (off + 1)).all _ = true
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨shiftL_wf (p + 1) (off + 1) W (by omega) h2 (by omega),
        fred_wf (by omega) (by omega) (by omega) (by omega) (by omega) h2⟩

theorem cmpAt_wf {w ou ov oc og W : Nat} (hw : 0 < w)
    (hab : ou + w ≤ ov ∨ ov + w ≤ ou)
    (hac : ou + w ≤ oc ∨ oc + 1 ≤ ou)
    (hbc : ov + w ≤ oc ∨ oc + 1 ≤ ov)
    (hgv : ov + w ≤ og ∨ og + 1 ≤ ov)
    (hwu : ou + w ≤ W) (hwv : ov + w ≤ W) (hwc : oc + 1 ≤ W) (hwg : og + 1 ≤ W) :
    (cmpAt w ou ov oc og).all (RGate.wellFormed W) = true := by
  have hpre := cmpPre_wf (Wd := W) hab hac hbc hwu hwv hwc
  show (cmpPre w ou ov oc ++ [RGate.cx (ov + (w - 1)) og]
    ++ (cmpPre w ou ov oc).reverse).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hpre, ?_⟩, ?_⟩
  · simp [RGate.wellFormed]
    omega
  · rw [List.all_reverse]; exact hpre

theorem subAt_wf {w oa ob oc W : Nat}
    (hab : oa + w ≤ ob ∨ ob + w ≤ oa)
    (hac : oa + w ≤ oc ∨ oc + 1 ≤ oa)
    (hbc : ob + w ≤ oc ∨ oc + 1 ≤ ob)
    (ha : oa + w ≤ W) (hb : ob + w ≤ W) (hc : oc + 1 ≤ W) :
    (subAt w oa ob oc).all (RGate.wellFormed W) = true := by
  show (addAt w oa ob oc).reverse.all _ = true
  rw [List.all_reverse]
  exact addAt_wf hab hac hbc ha hb hc

/-! ### Segment semantics -/

theorem segZero_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segZero n t, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  have := nzTest_wires (aV n) (aTR n) (aZ n + t) (bw n) (by simp only [bw]; omega) g hg q hq
  simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
  omega

theorem segDispatch_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segDispatch n t, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  simp only [segDispatch, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((rfl | rfl) | rfl) | (rfl | rfl) <;>
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at * <;> omega

theorem segCompareOld_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segCompareOld n t, ∀ q ∈ g.wires, Touches n t q := by
  have hw : 0 < bw n := by simp only [bw]; omega
  intro g hg q hq
  unfold Touches
  have hg2 : g ∈ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)
      ++ [RGate.ccx (aT n) (aGt n) (aA n), RGate.ccx (aT n) (aGt n) (aM n + t)]
      ++ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n) := hg
  rw [List.mem_append, List.mem_append] at hg2
  cases hg2 with
  | inr h2 =>
    have := cmpMaj_wires hw g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega
  | inl h1 =>
    cases h1 with
    | inl h2 =>
      have := cmpMaj_wires hw g h2 q hq
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
      omega
    | inr h2 =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl <;>
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at * <;> omega

/-- The new shape's gates all appear in the old one, so the bound transfers. -/
theorem segCompare_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segCompare n t, ∀ q ∈ g.wires, Touches n t q :=
  fun g hg => segCompareOld_touches ht g (segCompare_mem_old g hg)

theorem segSwap_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segSwap n, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  have hg2 : g ∈ swapC (aA n) (aU n) (aV n) (bw n)
      ++ swapC (aA n) (aR n) (aS n) (bw n) := hg
  rw [List.mem_append] at hg2
  cases hg2 with
  | inl h2 =>
    have := swapC_wires (bw n) (aU n) (aV n) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega
  | inr h2 =>
    have := swapC_wires (bw n) (aR n) (aS n) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega

theorem segArith_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segArith n, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  have hg2 : g ∈ copyC (aT n) (aU n) (aTU n) (bw n) ++ subAt (bw n) (aTU n) (aV n) (aC n)
      ++ copyC (aT n) (aU n) (aTU n) (bw n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n) ++ addAt (bw n) (aTR n) (aS n) (aC n)
      ++ copyC (aT n) (aR n) (aTR n) (bw n) := hg
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append,
    List.mem_append] at hg2
  cases hg2 with
  | inr h2 =>
    have := copyC_wires (bw n) (aR n) (aTR n) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega
  | inl h1 =>
    cases h1 with
    | inr h2 =>
      have := addAt_wires (w := bw n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) g h2 q hq
      simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
      omega
    | inl h1 =>
      cases h1 with
      | inr h2 =>
        have := copyC_wires (bw n) (aR n) (aTR n) g h2 q hq
        simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
        omega
      | inl h1 =>
        cases h1 with
        | inr h2 =>
          have := copyC_wires (bw n) (aU n) (aTU n) g h2 q hq
          simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
          omega
        | inl h1 =>
          cases h1 with
          | inl h2 =>
            have := copyC_wires (bw n) (aU n) (aTU n) g h2 q hq
            simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
            omega
          | inr h2 =>
            have := addAt_wires (w := bw n) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega) g (List.mem_reverse.mp h2) q hq
            simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
            omega

theorem segShift_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segShift n t, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  have hg2 : g ∈ shiftRU (aV n) (bw n) ++ shiftL (aZ n + t) (aR n) (bw n) := hg
  rw [List.mem_append] at hg2
  cases hg2 with
  | inl h2 =>
    have := shiftRU_wires (bw n) (aV n) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega
  | inr h2 =>
    have := shiftL_wires (bw n) (aR n) g h2 q hq
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at *
    omega

theorem segClear_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ segClear n t, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  unfold Touches
  simp only [segClear, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl) | rfl <;>
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw] at * <;> omega

/-- A round touches only the working block and its own two kept wires. -/
theorem roundGates_touches {n t : Nat} (ht : t < 2 * n) :
    ∀ g ∈ roundGates n t, ∀ q ∈ g.wires, Touches n t q := by
  intro g hg q hq
  have hg2 : g ∈ segZero n t ++ segDispatch n t ++ segCompare n t ++ segSwap n ++ segArith n
      ++ segShift n t ++ segSwap n ++ segClear n t := hg
  rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
    List.mem_append, List.mem_append] at hg2
  cases hg2 with
  | inr h => exact segClear_touches ht g h q hq
  | inl h1 =>
    cases h1 with
    | inr h => exact segSwap_touches ht g h q hq
    | inl h1 =>
      cases h1 with
      | inr h => exact segShift_touches ht g h q hq
      | inl h1 =>
        cases h1 with
        | inr h => exact segArith_touches ht g h q hq
        | inl h1 =>
          cases h1 with
          | inr h => exact segSwap_touches ht g h q hq
          | inl h1 =>
            cases h1 with
            | inr h => exact segCompare_touches ht g h q hq
            | inl h1 =>
              cases h1 with
              | inl h => exact segZero_touches ht g h q hq
              | inr h => exact segDispatch_touches ht g h q hq

/-! ## Round well-formedness

Each segment from its gadgets, then the eight together. -/

theorem segZero_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segZero n t).all (RGate.wellFormed (totalWidth n)) = true :=
  nzTest_wf (aV n) (aTR n) (aZ n + t) (bw n) (totalWidth n) (by simp only [bw]; omega)
    (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)

theorem segDispatch_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segDispatch n t).all (RGate.wellFormed (totalWidth n)) = true := by
  simp [segDispatch, RGate.wellFormed]
  simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]
  omega

theorem segCompareOld_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segCompareOld n t).all (RGate.wellFormed (totalWidth n)) = true := by
  have hw : 0 < bw n := by simp only [bw]; omega
  show (cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)
    ++ [RGate.ccx (aT n) (aGt n) (aA n), RGate.ccx (aT n) (aGt n) (aM n + t)]
    ++ cmpMaj (bw n) (aU n) (aV n) (aC n) (aGt n)).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨cmpMaj_wf hw (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega), ?_⟩,
    cmpMaj_wf hw (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩
  simp [RGate.wellFormed]
  simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]
  omega

theorem segCompare_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segCompare n t).all (RGate.wellFormed (totalWidth n)) = true :=
  List.all_eq_true.mpr fun g hg =>
    List.all_eq_true.mp (segCompareOld_wf hn ht) g (segCompare_mem_old g hg)

theorem segSwap_wf {n : Nat} (hn : 0 < n) :
    (segSwap n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (swapC (aA n) (aU n) (aV n) (bw n) ++ swapC (aA n) (aR n) (aS n) (bw n)).all _ = true
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨swapC_wf (bw n) (aU n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega),
    swapC_wf (bw n) (aR n) (aS n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩

theorem segArith_wf {n : Nat} (hn : 0 < n) :
    (segArith n).all (RGate.wellFormed (totalWidth n)) = true := by
  show (copyC (aT n) (aU n) (aTU n) (bw n) ++ subAt (bw n) (aTU n) (aV n) (aC n)
    ++ copyC (aT n) (aU n) (aTU n) (bw n)
    ++ copyC (aT n) (aR n) (aTR n) (bw n) ++ addAt (bw n) (aTR n) (aS n) (aC n)
    ++ copyC (aT n) (aR n) (aTR n) (bw n)).all _ = true
  rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨copyC_wf (bw n) (aU n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega),
    subAt_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    copyC_wf (bw n) (aU n) (aTU n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    copyC_wf (bw n) (aR n) (aTR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    addAt_wf (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩,
    copyC_wf (bw n) (aR n) (aTR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩

theorem segShift_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segShift n t).all (RGate.wellFormed (totalWidth n)) = true := by
  show (shiftRU (aV n) (bw n) ++ shiftL (aZ n + t) (aR n) (bw n)).all _ = true
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨shiftRU_wf (bw n) (aV n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega), shiftL_wf (bw n) (aR n) _ (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega) (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]; omega)⟩

theorem segClear_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (segClear n t).all (RGate.wellFormed (totalWidth n)) = true := by
  simp [segClear, RGate.wellFormed]
  simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw, totalWidth]
  omega

theorem roundGates_wf {n t : Nat} (hn : 0 < n) (ht : t < 2 * n) :
    (roundGates n t).all (RGate.wellFormed (totalWidth n)) = true := by
  show (segZero n t ++ segDispatch n t ++ segCompare n t ++ segSwap n ++ segArith n
    ++ segShift n t ++ segSwap n ++ segClear n t).all _ = true
  rw [List.all_append, List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨segZero_wf hn ht, segDispatch_wf hn ht⟩, segCompare_wf hn ht⟩,
    segSwap_wf hn⟩, segArith_wf hn⟩, segShift_wf hn ht⟩, segSwap_wf hn⟩, segClear_wf hn ht⟩

end VQ.Curve.PointAddition.Arithmetic.Inv
