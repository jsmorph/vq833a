/-
Resource metrics under composition.

Concrete-circuit bounds close by kernel evaluation.  Bounds for assembled
families also require theorems that express each composite metric through its
components.  This module supplies those theorems for `Circuit.append` and
`Circuit.relabel`.

Counting metrics are additive over `append` and invariant under `relabel`.
Depth metrics are subadditive when the circuits have equal widths or when both
circuits are well formed.  Without either condition, widening can make an
out-of-range gate consume a layer: `Tests/Compose.lean` records two depth-zero
circuits whose composition has depth one.

Placement gives components a common width.  The theorem
`depthOf_append_le_of_wellFormed` also handles arbitrary widths by using
`depthOf_le_of_wellFormed`: redeclaring a well-formed gate list can only drop
writes or add untouched level-vector entries.  Injectivity of relabelling
preserves `usedWires` and well-formedness, while counting metrics remain
invariant under an arbitrary relabelling.
-/
import VQ.Circuit.Resources

namespace VQ

namespace Gate

/-- Relabelling a gate relabels its wires.  Every statement below about the
wires a relabelled circuit touches goes through this. -/
theorem wires_map (f : Nat → Nat) (g : Gate) : (g.map f).wires = g.wires.map f := by
  cases g <;> rfl

/-- Relabelling preserves gate kind because `Gate.map` changes wire indices
while preserving the constructor.  The counting-metric invariance theorems use
this identity. -/
theorem kind_map (f : Nat → Nat) (g : Gate) : (g.map f).kind = g.kind := by
  cases g <;> rfl

theorem isT_map (f : Nat → Nat) (g : Gate) : (g.map f).isT = g.isT := by
  cases g <;> rfl

theorem isPhase_map (f : Nat → Nat) (g : Gate) : (g.map f).isPhase = g.isPhase := by
  cases g <;> rfl

theorem isCcz_map (f : Nat → Nat) (g : Gate) : (g.map f).isCcz = g.isCcz := by
  cases g <;> rfl

theorem isTwoQubit_map (f : Nat → Nat) (g : Gate) : (g.map f).isTwoQubit = g.isTwoQubit := by
  cases g <;> rfl

theorem isNonClifford_map (f : Nat → Nat) (g : Gate) :
    (g.map f).isNonClifford = g.isNonClifford := by
  cases g <;> rfl

/-- A well-formed gate names no wire at or above the width.  The depth lemmas use
this bound to record every gate write inside the level vector. -/
theorem lt_of_mem_wires {g : Gate} {w q : Nat} (h : g.wellFormed w = true)
    (hq : q ∈ g.wires) : q < w := by
  cases g <;> simp_all [Gate.wellFormed, Gate.wires] <;> omega

/-- A relabelling that lands below `w'` and is injective below `w` preserves
well-formedness of a gate.  Injectivity is needed for the multi-wire gates
alone, whose well-formedness says their wires are distinct. -/
theorem wellFormed_map {g : Gate} {w w' : Nat} {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < w')
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (h : g.wellFormed w = true) : (g.map f).wellFormed w' = true := by
  cases g with
  | h q | x q | y q | z q | s q | sdg q | t q | tdg q =>
    simp only [Gate.map, Gate.wellFormed, decide_eq_true_eq] at h ⊢
    exact hlt q h
  | p k q | pdg k q =>
    simp only [Gate.map, Gate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨hlt q h.1, h.2⟩
  | cx a b =>
    simp only [Gate.map, Gate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    exact ⟨⟨hlt a ha, hlt b hb⟩, fun e => hab (hinj a b ha hb e)⟩
  | ccz a b c =>
    simp only [Gate.map, Gate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := h
    exact ⟨⟨⟨⟨⟨hlt a ha, hlt b hb⟩, hlt c hc⟩,
      fun e => hab (hinj a b ha hb e)⟩,
      fun e => hbc (hinj b c hb hc e)⟩,
      fun e => hac (hinj a c ha hc e)⟩

end Gate

namespace Circuit

/-! ### The counting metrics over `append` -/

/-- The gate list of an `append` is the concatenation for every pair of widths.
`append` records their maximum only in the resulting circuit width. -/
theorem gates_append (a b : Circuit) : (a.append b).gates = a.gates ++ b.gates := rfl

/-- Every counting metric is a `List.countP` over the gate list.  Concatenation
splits that count additively.  The corresponding metrics are therefore additive
under `append`. -/
theorem countP_gates_append (pred : Gate → Bool) (a b : Circuit) :
    (a.append b).gates.countP pred = a.gates.countP pred + b.gates.countP pred := by
  simp [gates_append]

theorem gateCount_append (a b : Circuit) :
    (a.append b).gateCount = a.gateCount + b.gateCount := by
  simp [gateCount, gates_append]

theorem tCount_append (a b : Circuit) : (a.append b).tCount = a.tCount + b.tCount :=
  countP_gates_append _ a b

theorem toffoliCount_append (a b : Circuit) :
    (a.append b).toffoliCount = a.toffoliCount + b.toffoliCount :=
  countP_gates_append _ a b

theorem cnotCount_append (a b : Circuit) :
    (a.append b).cnotCount = a.cnotCount + b.cnotCount :=
  countP_gates_append _ a b

theorem phaseCount_append (a b : Circuit) :
    (a.append b).phaseCount = a.phaseCount + b.phaseCount :=
  countP_gates_append _ a b

theorem nonCliffordCount_append (a b : Circuit) :
    (a.append b).nonCliffordCount = a.nonCliffordCount + b.nonCliffordCount :=
  countP_gates_append _ a b

theorem cliffordCount_append (a b : Circuit) :
    (a.append b).cliffordCount = a.cliffordCount + b.cliffordCount :=
  countP_gates_append _ a b

theorem countKind_append (k : GateKind) (a b : Circuit) :
    (a.append b).countKind k = a.countKind k + b.countKind k :=
  countP_gates_append _ a b

/-! ### Scheduler level vectors

The depth metrics fold a per-wire level vector over the gate list, so
subadditivity needs the fold compared against itself from two different starting
vectors.  The comparison that carries through the fold is "pointwise below, up
to a constant offset `k`", together with "no longer than", the second because
`List.set` past the end of a vector is the identity and a shorter vector would
otherwise be able to ignore a gate the longer one records. -/

namespace Levels

/-- Reading past the end of a level vector gives zero. -/
theorem get_of_length_le {l : Levels} {q : Nat} (h : l.length ≤ q) : l.get q = 0 := by
  simp [Levels.get, List.getElem?_eq_none h]

/-- The starting vector reads as zero at every wire, inside its length and
outside it. -/
theorem get_replicate_zero (w q : Nat) : Levels.get (List.replicate w 0) q = 0 := by
  simp only [Levels.get, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem get_set_self {l : Levels} {i n : Nat} (h : i < l.length) :
    Levels.get (l.set i n) i = n := by
  simp [Levels.get, List.getElem?_set_self h]

theorem get_set_ne {l : Levels} {i n q : Nat} (h : q ≠ i) :
    Levels.get (l.set i n) q = l.get q := by
  simp [Levels.get, List.getElem?_set_ne (Ne.symm h)]

/-- `setAll` writes through `List.set`, which never changes a length. -/
theorem length_setAll (ws : List Nat) (l : Levels) (n : Nat) :
    (l.setAll ws n).length = l.length := by
  induction ws generalizing l with
  | nil => rfl
  | cons i rest ih =>
    show (Levels.setAll (l.set i n) rest n).length = l.length
    rw [ih, List.length_set]

theorem length_step (l : Levels) (ws : List Nat) : (l.step ws).length = l.length :=
  length_setAll ws l _

theorem length_sync (l : Levels) (ws : List Nat) : (l.sync ws).length = l.length :=
  length_setAll ws l _

/-- A starting value below another by `k` keeps that bound through the fold that
computes `base`. -/
theorem foldl_base_le {l m : Levels} {k : Nat} (hget : ∀ q, l.get q ≤ m.get q + k) :
    ∀ (ws : List Nat) {a b : Nat}, a ≤ b + k →
      ws.foldl (fun acc q => max acc (l.get q)) a
        ≤ ws.foldl (fun acc q => max acc (m.get q)) b + k := by
  intro ws
  induction ws with
  | nil => exact fun h => h
  | cons i rest ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (by have := hget i; omega)

/-- The latest level occupied by a set of wires respects the offset bound. -/
theorem base_le {l m : Levels} {k : Nat} (hget : ∀ q, l.get q ≤ m.get q + k) (ws : List Nat) :
    l.base ws ≤ m.base ws + k :=
  foldl_base_le hget ws (Nat.zero_le _)

/-- Writing the same wires with values `k` apart keeps every entry `k` apart.
The length hypothesis is what rules out the shorter vector silently dropping a
write the longer one performs. -/
theorem get_setAll_le {l m : Levels} {n n' k : Nat}
    (hlen : l.length ≤ m.length) (hn : n ≤ n' + k)
    (hget : ∀ q, l.get q ≤ m.get q + k) (ws : List Nat) (q : Nat) :
    (l.setAll ws n).get q ≤ (m.setAll ws n').get q + k := by
  induction ws generalizing l m with
  | nil => exact hget q
  | cons i rest ih =>
    show Levels.get (Levels.setAll (l.set i n) rest n) q
      ≤ Levels.get (Levels.setAll (m.set i n') rest n') q + k
    refine ih (by rw [List.length_set, List.length_set]; exact hlen) ?_
    intro p
    by_cases hp : p = i
    · subst hp
      by_cases hlt : p < l.length
      · rw [get_set_self hlt, get_set_self (Nat.lt_of_lt_of_le hlt hlen)]
        exact hn
      · rw [get_of_length_le (l := l.set p n) (by rw [List.length_set]; omega)]
        exact Nat.zero_le _
    · rw [get_set_ne hp, get_set_ne hp]
      exact hget p

theorem get_step_le {l m : Levels} {k : Nat} (hlen : l.length ≤ m.length)
    (hget : ∀ q, l.get q ≤ m.get q + k) (ws : List Nat) (q : Nat) :
    (l.step ws).get q ≤ (m.step ws).get q + k :=
  get_setAll_le hlen (by have := base_le hget ws; omega) hget ws q

theorem get_sync_le {l m : Levels} {k : Nat} (hlen : l.length ≤ m.length)
    (hget : ∀ q, l.get q ≤ m.get q + k) (ws : List Nat) (q : Nat) :
    (l.sync ws).get q ≤ (m.sync ws).get q + k :=
  get_setAll_le hlen (base_le hget ws) hget ws q

/--
The same bound with the length hypothesis replaced by a hypothesis on the wires
written.

`get_setAll_le` uses `l.length ≤ m.length` to ensure that `m` contains every
wire written through `l`.  An explicit bound on each written wire gives the
same conclusion without relating the vector lengths.  `depthOf_le_of_wellFormed`
uses this form, with well-formedness supplying the wire bound.
-/
theorem get_setAll_le_of_mem {k : Nat} : ∀ (ws : List Nat) {l m : Levels} {n n' : Nat},
    (∀ i ∈ ws, i < m.length) → n ≤ n' + k → (∀ q, l.get q ≤ m.get q + k) →
      ∀ q, (l.setAll ws n).get q ≤ (m.setAll ws n').get q + k := by
  intro ws
  induction ws with
  | nil => exact fun _ _ hget q => hget q
  | cons i rest ih =>
    intro l m n n' hws hn hget q
    show Levels.get (Levels.setAll (l.set i n) rest n) q
      ≤ Levels.get (Levels.setAll (m.set i n') rest n') q + k
    refine ih (fun j hj => ?_) hn (fun p => ?_) q
    · rw [List.length_set]
      exact hws j (List.mem_cons_of_mem i hj)
    · by_cases hp : p = i
      · subst hp
        by_cases hlt : p < l.length
        · rw [get_set_self hlt, get_set_self (hws p List.mem_cons_self)]
          exact hn
        · rw [get_of_length_le (l := l.set p n) (by rw [List.length_set]; omega)]
          exact Nat.zero_le _
      · rw [get_set_ne hp, get_set_ne hp]
        exact hget p

theorem get_step_le_of_mem {l m : Levels} {k : Nat} (hget : ∀ q, l.get q ≤ m.get q + k)
    (ws : List Nat) (hws : ∀ i ∈ ws, i < m.length) (q : Nat) :
    (l.step ws).get q ≤ (m.step ws).get q + k :=
  get_setAll_le_of_mem ws hws (by have := base_le hget ws; omega) hget q

theorem get_sync_le_of_mem {l m : Levels} {k : Nat} (hget : ∀ q, l.get q ≤ m.get q + k)
    (ws : List Nat) (hws : ∀ i ∈ ws, i < m.length) (q : Nat) :
    (l.sync ws).get q ≤ (m.sync ws).get q + k :=
  get_setAll_le_of_mem ws hws (base_le hget ws) hget q

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], a => Nat.le_refl a
  | x :: rest, a => Nat.le_trans (Nat.le_max_left a x) (le_foldl_max rest _)

theorem mem_le_foldl_max : ∀ {l : List Nat} {x a : Nat}, x ∈ l → x ≤ l.foldl max a := by
  intro l
  induction l with
  | nil => intro x a h; simp at h
  | cons y rest ih =>
    intro x a h
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_trans (Nat.le_max_right a x) (le_foldl_max rest _)
    · exact ih h'

theorem foldl_max_le {n : Nat} : ∀ {l : List Nat} {a : Nat},
    a ≤ n → (∀ x ∈ l, x ≤ n) → l.foldl max a ≤ n := by
  intro l
  induction l with
  | nil => intro a ha _; exact ha
  | cons y rest ih =>
    intro a ha h
    exact ih (Nat.max_le.mpr ⟨ha, h y (List.mem_cons_self ..)⟩)
      (fun x hx => h x (List.mem_cons_of_mem y hx))

/-- Every wire level lies at or below the vector's peak, including indices
outside the stored range. -/
theorem get_le_peak (l : Levels) (q : Nat) : l.get q ≤ l.peak := by
  by_cases h : q < l.length
  · have hq : l.get q = l[q] := by simp [Levels.get, List.getElem?_eq_getElem h]
    rw [hq]
    exact mem_le_foldl_max (List.getElem_mem h)
  · rw [get_of_length_le (Nat.le_of_not_lt h)]
    exact Nat.zero_le _

/-- A bound on every wire is a bound on the peak. -/
theorem peak_le {l : Levels} {n : Nat} (h : ∀ q, l.get q ≤ n) : l.peak ≤ n := by
  refine foldl_max_le (Nat.zero_le n) ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hq : l.get i = l[i] := by simp [Levels.get, List.getElem?_eq_getElem hi]
  exact hq ▸ h i

end Levels

/-! ### The depth metrics over `append`

`depth` and `depthOf` are the same fold with different per-gate moves, so both
bounds come from one lemma about a move that preserves lengths and carries the
offset bound. -/

/-- A scheduling fold preserves the length of the level vector. -/
theorem length_foldl_levels {F : Levels → Gate → Levels}
    (hlen : ∀ l g, (F l g).length = l.length) :
    ∀ (gs : List Gate) (l : Levels), (gs.foldl F l).length = l.length := by
  intro gs
  induction gs with
  | nil => exact fun _ => rfl
  | cons g rest ih => exact fun l => (ih (F l g)).trans (hlen l g)

/-- A scheduling fold carries the offset bound from its starting vectors to its
result. -/
theorem foldl_levels_get_le {F : Levels → Gate → Levels}
    (hlen : ∀ l g, (F l g).length = l.length)
    (hmove : ∀ (l m : Levels) (k : Nat), l.length ≤ m.length →
      (∀ q, l.get q ≤ m.get q + k) → ∀ (g : Gate) (q : Nat),
        (F l g).get q ≤ (F m g).get q + k) :
    ∀ (gs : List Gate) (l m : Levels) (k : Nat), l.length ≤ m.length →
      (∀ q, l.get q ≤ m.get q + k) →
      ∀ q, (gs.foldl F l).get q ≤ (gs.foldl F m).get q + k := by
  intro gs
  induction gs with
  | nil => exact fun _ _ _ _ hget q => hget q
  | cons g rest ih =>
    intro l m k hle hget q
    exact ih (F l g) (F m g) k (by rw [hlen, hlen]; exact hle) (hmove l m k hle hget g) q

/-- The same, with the wires of the gates constrained instead of the two
lengths.  The condition is stated on `m`, the vector being compared against, and
survives the fold because a scheduling move preserves lengths. -/
theorem foldl_levels_get_le_of_wires {F : Levels → Gate → Levels}
    (hlen : ∀ l g, (F l g).length = l.length)
    (hmove : ∀ (l m : Levels) (k : Nat) (g : Gate), (∀ q ∈ g.wires, q < m.length) →
      (∀ q, l.get q ≤ m.get q + k) → ∀ q, (F l g).get q ≤ (F m g).get q + k) :
    ∀ (gs : List Gate) (l m : Levels) (k : Nat),
      (∀ g ∈ gs, ∀ q ∈ g.wires, q < m.length) → (∀ q, l.get q ≤ m.get q + k) →
      ∀ q, (gs.foldl F l).get q ≤ (gs.foldl F m).get q + k := by
  intro gs
  induction gs with
  | nil => exact fun _ _ _ _ hget q => hget q
  | cons g rest ih =>
    intro l m k hws hget q
    refine ih (F l g) (F m g) k (fun g' hg' p hp => ?_)
      (hmove l m k g (hws g List.mem_cons_self) hget) q
    rw [hlen]
    exact hws g' (List.mem_cons_of_mem g hg') p hp

/--
Subadditivity of a scheduling fold's peak over a concatenation of gate lists.

Running the second list from the first list's final vector is bounded by running
it from the starting vector and adding the first list's peak, because every
entry of the first list's final vector is at most that peak.  This is the whole
argument for depth subadditivity, and it is stated at a fixed width `w` because
both runs must start from a vector of the same length.
-/
theorem peak_foldl_append_le {F : Levels → Gate → Levels}
    (hlen : ∀ l g, (F l g).length = l.length)
    (hmove : ∀ (l m : Levels) (k : Nat), l.length ≤ m.length →
      (∀ q, l.get q ≤ m.get q + k) → ∀ (g : Gate) (q : Nat),
        (F l g).get q ≤ (F m g).get q + k)
    (w : Nat) (as bs : List Gate) :
    ((as ++ bs).foldl F (List.replicate w 0)).peak
      ≤ (as.foldl F (List.replicate w 0)).peak + (bs.foldl F (List.replicate w 0)).peak := by
  rw [List.foldl_append]
  refine Levels.peak_le ?_
  intro q
  have hstart : ∀ p, (as.foldl F (List.replicate w 0)).get p
      ≤ Levels.get (List.replicate w 0) p + (as.foldl F (List.replicate w 0)).peak := by
    intro p
    rw [Levels.get_replicate_zero]
    simpa using Levels.get_le_peak _ p
  have hle : (as.foldl F (List.replicate w 0)).length ≤ (List.replicate w 0 : Levels).length :=
    Nat.le_of_eq (length_foldl_levels hlen as _)
  have hbound := foldl_levels_get_le hlen hmove bs _ _ _ hle hstart q
  have hpeak := Levels.get_le_peak (bs.foldl F (List.replicate w 0)) q
  omega

/-- Total depth is `depthOf` with every gate in the class. -/
theorem depth_eq_depthOf (c : Circuit) : c.depth = depthOf (fun _ => true) c := rfl

/-- Subadditivity of a class-restricted depth over concatenation at a fixed
width. -/
theorem depthOf_append_gates_le (pred : Gate → Bool) (w : Nat) (as bs : List Gate) :
    depthOf pred ⟨w, as ++ bs⟩ ≤ depthOf pred ⟨w, as⟩ + depthOf pred ⟨w, bs⟩ := by
  refine peak_foldl_append_le (F := fun l g => if pred g then l.step g.wires else l.sync g.wires)
    ?_ ?_ w as bs
  · intro l g
    by_cases hp : pred g = true
    · rw [if_pos hp]; exact Levels.length_step l g.wires
    · rw [if_neg hp]; exact Levels.length_sync l g.wires
  · intro l m k hle hget g q
    by_cases hp : pred g = true
    · rw [if_pos hp, if_pos hp]; exact Levels.get_step_le hle hget g.wires q
    · rw [if_neg hp, if_neg hp]; exact Levels.get_sync_le hle hget g.wires q

/-- Subadditivity of total depth over concatenation at a fixed width. -/
theorem depth_append_gates_le (w : Nat) (as bs : List Gate) :
    depth ⟨w, as ++ bs⟩ ≤ depth ⟨w, as⟩ + depth ⟨w, bs⟩ :=
  depthOf_append_gates_le (fun _ => true) w as bs

/--
A class-restricted depth is subadditive over `append` for circuits of equal
width, and the three depth metrics below are its instances.

The width hypothesis is not removable on its own.  `append` widens to the larger
of the two widths, a level vector has one entry per declared wire, and a write
past the end of it does nothing, so a circuit whose gates name wires beyond its
own declared width has a depth that grows when it is appended to a wider
circuit.  With `a = ⟨0, [h 0]⟩` and `b = ⟨1, []⟩` both depths are zero and the
composite's depth is one.  What replaces the width hypothesis is well-formedness
of both arguments, which is `depthOf_append_le_of_wellFormed`.
-/
theorem depthOf_append_le (pred : Gate → Bool) {a b : Circuit} (hw : a.width = b.width) :
    depthOf pred (a.append b) ≤ depthOf pred a + depthOf pred b := by
  obtain ⟨wa, ga⟩ := a
  obtain ⟨wb, gb⟩ := b
  subst hw
  simpa [append, Nat.max_self] using depthOf_append_gates_le pred wa ga gb

/-- Total depth is subadditive over `append` for circuits of equal width. -/
theorem depth_append_le {a b : Circuit} (hw : a.width = b.width) :
    (a.append b).depth ≤ a.depth + b.depth :=
  depthOf_append_le (fun _ => true) hw

/-- T-depth is subadditive over `append` for circuits of equal width. -/
theorem tDepth_append_le {a b : Circuit} (hw : a.width = b.width) :
    (a.append b).tDepth ≤ a.tDepth + b.tDepth :=
  depthOf_append_le Gate.isT hw

/-- Non-Clifford depth is subadditive over `append` for circuits of equal
width. -/
theorem nonCliffordDepth_append_le {a b : Circuit} (hw : a.width = b.width) :
    (a.append b).nonCliffordDepth ≤ a.nonCliffordDepth + b.nonCliffordDepth :=
  depthOf_append_le Gate.isNonClifford hw

/-! ### The depth metrics over `append` without the width hypothesis

A gate list well formed at its own width names only entries in that width's
level vector.  Redeclaring the width can only drop writes or add entries that
remain zero, so depth is maximal at the well-formed width. -/

/--
The declared width of a well-formed gate list bounds its depth at every other
declared width.

`w'` may have any relation to `w`.  Widening adds untouched entries to the
level vector, and narrowing drops writes, so the peak remains bounded by its
value at `w`.
-/
theorem peak_foldl_le_of_wires {F : Levels → Gate → Levels}
    (hlen : ∀ l g, (F l g).length = l.length)
    (hmove : ∀ (l m : Levels) (k : Nat) (g : Gate), (∀ q ∈ g.wires, q < m.length) →
      (∀ q, l.get q ≤ m.get q + k) → ∀ q, (F l g).get q ≤ (F m g).get q + k)
    (w w' : Nat) (gs : List Gate) (hgs : ∀ g ∈ gs, ∀ q ∈ g.wires, q < w) :
    (gs.foldl F (List.replicate w' 0)).peak ≤ (gs.foldl F (List.replicate w 0)).peak := by
  refine Levels.peak_le (fun q => ?_)
  have hws : ∀ g ∈ gs, ∀ q ∈ g.wires, q < (List.replicate w 0 : Levels).length := by
    intro g hg p hp
    rw [List.length_replicate]
    exact hgs g hg p hp
  have hstart : ∀ p, Levels.get (List.replicate w' 0) p
      ≤ Levels.get (List.replicate w 0) p + 0 := by
    intro p
    rw [Levels.get_replicate_zero, Levels.get_replicate_zero]
    exact Nat.le_refl 0
  have hbound := foldl_levels_get_le_of_wires hlen hmove gs _ _ 0 hws hstart q
  have hpeak := Levels.get_le_peak (gs.foldl F (List.replicate w 0)) q
  omega

theorem depthOf_le_of_wellFormed (pred : Gate → Bool) {w w' : Nat} {gs : List Gate}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) :
    depthOf pred ⟨w', gs⟩ ≤ depthOf pred ⟨w, gs⟩ := by
  refine peak_foldl_le_of_wires (F := fun l g => if pred g then l.step g.wires else l.sync g.wires)
    ?_ ?_ w w' gs (fun g hg q hq => Gate.lt_of_mem_wires (hgs g hg) hq)
  · intro l g
    by_cases hp : pred g = true
    · rw [if_pos hp]; exact Levels.length_step l g.wires
    · rw [if_neg hp]; exact Levels.length_sync l g.wires
  · intro l m k g hws hget q
    by_cases hp : pred g = true
    · rw [if_pos hp, if_pos hp]; exact Levels.get_step_le_of_mem hget g.wires hws q
    · rw [if_neg hp, if_neg hp]; exact Levels.get_sync_le_of_mem hget g.wires hws q

/--
A class-restricted depth is subadditive over `append` for well-formed
circuits, whatever their widths.

Both arguments have to be well formed and neither hypothesis can be dropped.
The counterexample to the unhypothesised statement is `a = ⟨0, [h 0]⟩` with
`b = ⟨1, []⟩`, where `a` is ill formed.  Exchanging them gives `a = ⟨1, []⟩` with
`b = ⟨0, [h 0]⟩`, where `a` is well formed, `b` is not, both depths are still
zero, and the append still has depth one.  So neither one-sided version holds,
and this is the form the placement of a component uses.
-/
theorem depthOf_append_le_of_wellFormed (pred : Gate → Bool) {a b : Circuit}
    (ha : a.wellFormed = true) (hb : b.wellFormed = true) :
    depthOf pred (a.append b) ≤ depthOf pred a + depthOf pred b := by
  obtain ⟨wa, ga⟩ := a
  obtain ⟨wb, gb⟩ := b
  have hga : ∀ g ∈ ga, g.wellFormed wa = true := List.all_eq_true.mp ha
  have hgb : ∀ g ∈ gb, g.wellFormed wb = true := List.all_eq_true.mp hb
  have hsplit : depthOf pred ⟨max wa wb, ga ++ gb⟩
      ≤ depthOf pred ⟨max wa wb, ga⟩ + depthOf pred ⟨max wa wb, gb⟩ :=
    depthOf_append_gates_le pred (max wa wb) ga gb
  have hleft : depthOf pred ⟨max wa wb, ga⟩ ≤ depthOf pred ⟨wa, ga⟩ :=
    depthOf_le_of_wellFormed pred hga
  have hright : depthOf pred ⟨max wa wb, gb⟩ ≤ depthOf pred ⟨wb, gb⟩ :=
    depthOf_le_of_wellFormed pred hgb
  show depthOf pred ⟨max wa wb, ga ++ gb⟩ ≤ depthOf pred ⟨wa, ga⟩ + depthOf pred ⟨wb, gb⟩
  omega

/-- Total depth is subadditive over `append` for well-formed circuits. -/
theorem depth_append_le_of_wellFormed {a b : Circuit} (ha : a.wellFormed = true)
    (hb : b.wellFormed = true) : (a.append b).depth ≤ a.depth + b.depth :=
  depthOf_append_le_of_wellFormed (fun _ => true) ha hb

/-- T-depth is subadditive over `append` for well-formed circuits. -/
theorem tDepth_append_le_of_wellFormed {a b : Circuit} (ha : a.wellFormed = true)
    (hb : b.wellFormed = true) : (a.append b).tDepth ≤ a.tDepth + b.tDepth :=
  depthOf_append_le_of_wellFormed Gate.isT ha hb

/-- Non-Clifford depth is subadditive over `append` for well-formed circuits. -/
theorem nonCliffordDepth_append_le_of_wellFormed {a b : Circuit} (ha : a.wellFormed = true)
    (hb : b.wellFormed = true) :
    (a.append b).nonCliffordDepth ≤ a.nonCliffordDepth + b.nonCliffordDepth :=
  depthOf_append_le_of_wellFormed Gate.isNonClifford ha hb

/-! ### The counting metrics under `relabel` -/

theorem gates_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).gates = c.gates.map (Gate.map f) := rfl

/-- A predicate blind to wire indices counts the same gates before and after a
relabelling.  No hypothesis on `f`: the map is applied gatewise and preserves
constructors, so the multiset of kinds is untouched even when `f` is
constant. -/
theorem countP_map_gate {pred : Gate → Bool} {f : Nat → Nat}
    (hpred : ∀ g : Gate, pred (g.map f) = pred g) (gs : List Gate) :
    (gs.map (Gate.map f)).countP pred = gs.countP pred := by
  induction gs with
  | nil => rfl
  | cons g rest ih => simp [List.countP_cons, ih, hpred g]

/-- The same statement for a circuit, which is where every count below reads
it. -/
theorem countP_gates_relabel {pred : Gate → Bool} {f : Nat → Nat}
    (hpred : ∀ g : Gate, pred (g.map f) = pred g) (w : Nat) (c : Circuit) :
    (relabel f w c).gates.countP pred = c.gates.countP pred :=
  countP_map_gate hpred c.gates

theorem gateCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).gateCount = c.gateCount := by
  simp [gateCount, gates_relabel]

theorem tCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).tCount = c.tCount :=
  countP_gates_relabel (Gate.isT_map f) w c

theorem toffoliCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).toffoliCount = c.toffoliCount :=
  countP_gates_relabel (Gate.isCcz_map f) w c

theorem cnotCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).cnotCount = c.cnotCount :=
  countP_gates_relabel (Gate.isTwoQubit_map f) w c

theorem phaseCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).phaseCount = c.phaseCount :=
  countP_gates_relabel (Gate.isPhase_map f) w c

theorem nonCliffordCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).nonCliffordCount = c.nonCliffordCount :=
  countP_gates_relabel (Gate.isNonClifford_map f) w c

theorem cliffordCount_relabel (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).cliffordCount = c.cliffordCount :=
  countP_gates_relabel (f := f) (fun g => by rw [Gate.isNonClifford_map]) w c

theorem countKind_relabel (k : GateKind) (f : Nat → Nat) (w : Nat) (c : Circuit) :
    (relabel f w c).countKind k = c.countKind k :=
  countP_gates_relabel (f := f) (fun g => by rw [Gate.kind_map]) w c

/-! ### The wires a relabelled circuit touches -/

/-- The wires of a relabelled gate list are the relabelled wires of the original,
in the same order and with the same repetitions. -/
theorem flatMap_wires_map (f : Nat → Nat) (gs : List Gate) :
    (gs.map (Gate.map f)).flatMap Gate.wires = (gs.flatMap Gate.wires).map f := by
  induction gs with
  | nil => rfl
  | cons g rest ih => simp [Gate.wires_map, ih]

/--
Deduplication commutes with a map that is injective on the list's elements.

The hypothesis states injectivity on the elements present.  A subcircuit
placement may be injective on its wires without defining a globally injective
map.
-/
theorem eraseDups_map_of_injOn {f : Nat → Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      (l.map f).eraseDups = l.eraseDups.map f
  | [], _ => rfl
  | a :: as, hinj => by
    have hmem : ∀ x ∈ as, x ∈ a :: as := fun x hx => List.mem_cons_of_mem a hx
    have hbeq : ∀ x ∈ as, ((fun b => !(b == f a)) ∘ f) x = (fun x => !(x == a)) x := by
      intro x hx
      have hb : (f x == f a) = (x == a) := by
        by_cases hxa : x = a
        · subst hxa; simp
        · have hne : f x ≠ f a :=
            fun e => hxa (hinj x (hmem x hx) a (List.mem_cons_self ..) e)
          rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hxa]
      show (!(f x == f a)) = (!(x == a))
      rw [hb]
    have hsub : ∀ x ∈ as.filter (fun x => !(x == a)),
        ∀ y ∈ as.filter (fun x => !(x == a)), f x = f y → x = y := by
      intro x hx y hy
      exact hinj x (hmem x (List.mem_filter.mp hx).1) y (hmem y (List.mem_filter.mp hy).1)
    calc ((a :: as).map f).eraseDups
        = f a :: ((as.map f).filter fun b => !(b == f a)).eraseDups := by
          rw [List.map_cons, List.eraseDups_cons]
      _ = f a :: ((as.filter fun x => !(x == a)).map f).eraseDups := by
          rw [List.filter_map, List.filter_congr hbeq]
      _ = f a :: (as.filter fun x => !(x == a)).eraseDups.map f := by
          rw [eraseDups_map_of_injOn _ hsub]
      _ = ((a :: as).eraseDups).map f := by rw [List.eraseDups_cons, List.map_cons]
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ as)

/-- The wires a relabelled circuit touches are the images of the wires the
original touches, in the same order.  Injectivity is required on the wires used
and nowhere else. -/
theorem wiresUsed_relabel {c : Circuit} {f : Nat → Nat} {w : Nat}
    (hinj : ∀ x ∈ c.wiresUsed, ∀ y ∈ c.wiresUsed, f x = f y → x = y) :
    (relabel f w c).wiresUsed = c.wiresUsed.map f := by
  show ((c.gates.map (Gate.map f)).flatMap Gate.wires).eraseDups = _
  rw [flatMap_wires_map]
  exact eraseDups_map_of_injOn _ fun x hx y hy =>
    hinj x (List.mem_eraseDups.mpr hx) y (List.mem_eraseDups.mpr hy)

/-- An injective relabelling changes which wires a circuit uses and not how
many. -/
theorem usedWires_relabel {c : Circuit} {f : Nat → Nat} {w : Nat}
    (hinj : ∀ x ∈ c.wiresUsed, ∀ y ∈ c.wiresUsed, f x = f y → x = y) :
    (relabel f w c).usedWires = c.usedWires := by
  rw [usedWires, wiresUsed_relabel hinj, List.length_map, usedWires]

/-! ### Well-formedness under `relabel` -/

/-- A relabelling that maps every wire below `c.width` injectively into the
wires below `w'` carries well-formedness to `w'`.  This is the placement lemma:
a subcircuit proved well formed on its own wires stays well formed wherever an
injective assignment puts it.  It is the `relabel` counterpart of
`wellFormed_widen`, which is the same statement for the identity relabelling. -/
theorem wellFormed_relabel {c : Circuit} {f : Nat → Nat} {w' : Nat}
    (hlt : ∀ q, q < c.width → f q < w')
    (hinj : ∀ x y, x < c.width → y < c.width → f x = f y → x = y)
    (h : c.wellFormed = true) : (relabel f w' c).wellFormed = true := by
  simp only [Circuit.wellFormed, gates_relabel, List.all_eq_true, List.mem_map] at h ⊢
  rintro g ⟨g', hg', rfl⟩
  exact Gate.wellFormed_map hlt hinj (h g' hg')

/-! ### Depth against count

Each in-class gate raises the peak by at most one and each gate outside the class
does not raise it at all, so a class-restricted depth never exceeds the number of
gates in that class.  A serial circuit meets this bound with equality.  The
difference between gate count and depth measures available within-class
parallelism.  Sharper scheduling results require circuit-specific dependency
analysis. -/

namespace Levels

theorem get_setAll_le_max : ∀ (ws : List Nat) {l : Levels} {v : Nat} (q : Nat),
    Levels.get (Levels.setAll l ws v) q ≤ max (Levels.get l q) v := by
  intro ws
  induction ws with
  | nil => intro l v q; exact Nat.le_max_left _ _
  | cons i rest ih =>
    intro l v q
    show Levels.get (Levels.setAll (l.set i v) rest v) q ≤ _
    have h := ih (l := l.set i v) (v := v) q
    have h2 : Levels.get (l.set i v) q ≤ max (Levels.get l q) v := by
      by_cases hq : q = i
      · subst hq
        by_cases hlt : q < l.length
        · rw [get_set_self hlt]; exact Nat.le_max_right _ _
        · rw [get_of_length_le (l := l.set q v) (by rw [List.length_set]; omega)]
          exact Nat.zero_le _
      · rw [get_set_ne hq]; exact Nat.le_max_left _ _
    omega

theorem foldl_base_le_peak (l : Levels) : ∀ (ws : List Nat) (a : Nat), a ≤ l.peak →
    ws.foldl (fun acc q => max acc (Levels.get l q)) a ≤ l.peak := by
  intro ws
  induction ws with
  | nil => exact fun a h => h
  | cons i rest ih =>
    intro a h
    simp only [List.foldl_cons]
    exact ih _ (by have := get_le_peak l i; omega)

theorem base_le_peak (l : Levels) (ws : List Nat) : l.base ws ≤ l.peak :=
  foldl_base_le_peak l ws 0 (Nat.zero_le _)

theorem peak_step_le (l : Levels) (ws : List Nat) : (l.step ws).peak ≤ l.peak + 1 := by
  refine peak_le (fun q => ?_)
  show Levels.get (Levels.setAll l ws (l.base ws + 1)) q ≤ _
  have h := get_setAll_le_max ws (l := l) (v := l.base ws + 1) q
  have hb := base_le_peak l ws
  have hq := get_le_peak l q
  omega

theorem peak_sync_le (l : Levels) (ws : List Nat) : (l.sync ws).peak ≤ l.peak := by
  refine peak_le (fun q => ?_)
  show Levels.get (Levels.setAll l ws (l.base ws)) q ≤ _
  have h := get_setAll_le_max ws (l := l) (v := l.base ws) q
  have hb := base_le_peak l ws
  have hq := get_le_peak l q
  omega

theorem peak_replicate_zero (w : Nat) : Levels.peak (List.replicate w 0) = 0 := by
  refine Nat.le_antisymm (peak_le (fun q => ?_)) (Nat.zero_le _)
  rw [get_replicate_zero]
  omega

end Levels

theorem peak_foldl_le_countP (pred : Gate → Bool) :
    ∀ (gs : List Gate) (l : Levels),
      (gs.foldl (fun l g => if pred g then l.step g.wires else l.sync g.wires) l).peak
        ≤ l.peak + gs.countP pred := by
  intro gs
  induction gs with
  | nil => intro l; simp
  | cons g rest ih =>
    intro l
    rw [List.countP_cons]
    simp only [List.foldl_cons]
    by_cases hp : pred g = true
    · rw [if_pos hp]
      have h1 := ih (l.step g.wires)
      have h2 := Levels.peak_step_le l g.wires
      simp only [hp, if_true]
      omega
    · rw [if_neg hp]
      have h1 := ih (l.sync g.wires)
      have h2 := Levels.peak_sync_le l g.wires
      simp only [hp, if_false, Bool.false_eq_true]
      omega

/-- A class-restricted depth is at most the number of gates in that class. -/
theorem depthOf_le_countP (pred : Gate → Bool) (c : Circuit) :
    depthOf pred c ≤ c.gates.countP pred := by
  show (c.gates.foldl
    (fun l g => if pred g then l.step g.wires else l.sync g.wires) c.initialLevels).peak ≤ _
  have h := peak_foldl_le_countP pred c.gates c.initialLevels
  have hz : c.initialLevels.peak = 0 := Levels.peak_replicate_zero c.width
  omega

theorem depth_le_gateCount (c : Circuit) : c.depth ≤ c.gateCount := by
  rw [depth_eq_depthOf]
  simpa [gateCount] using depthOf_le_countP (fun _ => true) c

/-- Toffoli depth is at most the Toffoli count. -/
theorem toffoliDepth_le_toffoliCount (c : Circuit) :
    toffoliDepth c ≤ toffoliCount c :=
  depthOf_le_countP Gate.isCcz c

/-! ### Depth over disjoint supports

For gate lists with disjoint supports, concatenation depth equals the larger
individual depth.  Each list leaves scheduler levels unchanged on the support
of the other.  The final level vector therefore agrees with the first list off
the second support and with the second list on that support.  These coordinate
equalities yield the maximum formula. -/

namespace Levels

theorem get_setAll_of_not_mem : ∀ (ws : List Nat) {l : Levels} {v q : Nat}, q ∉ ws →
    Levels.get (Levels.setAll l ws v) q = Levels.get l q := by
  intro ws
  induction ws with
  | nil => intro l v q _; rfl
  | cons i rest ih =>
    intro l v q h
    have hne : q ≠ i := fun hq => h (hq ▸ List.mem_cons_self)
    have hrest : q ∉ rest := fun hq => h (List.mem_cons_of_mem i hq)
    show Levels.get (Levels.setAll (l.set i v) rest v) q = _
    rw [ih (l := l.set i v) hrest, get_set_ne hne]

theorem get_setAll_of_mem : ∀ (ws : List Nat) {l : Levels} {v q : Nat}, q ∈ ws →
    q < l.length → Levels.get (Levels.setAll l ws v) q = v := by
  intro ws
  induction ws with
  | nil => intro l v q h _; exact absurd h (by simp)
  | cons i rest ih =>
    intro l v q h hlt
    show Levels.get (Levels.setAll (l.set i v) rest v) q = v
    by_cases hr : q ∈ rest
    · exact ih (l := l.set i v) hr (by rw [List.length_set]; exact hlt)
    · have hq : q = i := by
        rcases List.mem_cons.mp h with h' | h'
        · exact h'
        · exact absurd h' hr
      subst hq
      rw [get_setAll_of_not_mem rest hr, get_set_self hlt]

theorem base_congr {l m : Levels} (ws : List Nat)
    (h : ∀ q ∈ ws, Levels.get l q = Levels.get m q) : l.base ws = m.base ws := by
  show ws.foldl (fun acc q => max acc (Levels.get l q)) 0
    = ws.foldl (fun acc q => max acc (Levels.get m q)) 0
  have go : ∀ (vs : List Nat) (a : Nat), (∀ q ∈ vs, Levels.get l q = Levels.get m q) →
      vs.foldl (fun acc q => max acc (Levels.get l q)) a
        = vs.foldl (fun acc q => max acc (Levels.get m q)) a := by
    intro vs
    induction vs with
    | nil => intro a _; rfl
    | cons i rest ih =>
      intro a hh
      simp only [List.foldl_cons, hh i List.mem_cons_self]
      exact ih _ (fun q hq => hh q (List.mem_cons_of_mem i hq))
  exact go ws 0 h

end Levels

/-- The move one gate makes, as the fold performs it. -/
def sched (pred : Gate → Bool) (l : Levels) (g : Gate) : Levels :=
  if pred g then l.step g.wires else l.sync g.wires

theorem sched_length (pred : Gate → Bool) (l : Levels) (g : Gate) :
    (sched pred l g).length = l.length := by
  unfold sched
  by_cases h : pred g = true
  · rw [if_pos h]; exact Levels.length_step l g.wires
  · rw [if_neg h]; exact Levels.length_sync l g.wires

theorem get_sched_of_not_mem (pred : Gate → Bool) (l : Levels) (g : Gate)
    {q : Nat} (h : q ∉ g.wires) : Levels.get (sched pred l g) q = Levels.get l q := by
  unfold sched
  by_cases hp : pred g = true
  · rw [if_pos hp]; exact Levels.get_setAll_of_not_mem g.wires h
  · rw [if_neg hp]; exact Levels.get_setAll_of_not_mem g.wires h

/-- A fold leaves a wire no gate names exactly as it found it. -/
theorem foldl_sched_of_not_mem (pred : Gate → Bool) :
    ∀ (gs : List Gate) (l : Levels) {q : Nat}, (∀ g ∈ gs, q ∉ g.wires) →
      Levels.get (gs.foldl (sched pred) l) q = Levels.get l q := by
  intro gs
  induction gs with
  | nil => intro l q _; rfl
  | cons g rest ih =>
    intro l q h
    rw [List.foldl_cons, ih (sched pred l g) (fun g' hg' => h g' (List.mem_cons_of_mem g hg')),
      get_sched_of_not_mem pred l g (h g List.mem_cons_self)]

/-- Two starting vectors of the same length that agree on every wire the gates
name give results agreeing there. -/
theorem foldl_sched_congr (pred : Gate → Bool) (S : Nat → Prop) :
    ∀ (gs : List Gate) {l m : Levels}, l.length = m.length →
      (∀ g ∈ gs, ∀ q ∈ g.wires, S q) →
      (∀ q, S q → Levels.get l q = Levels.get m q) →
      ∀ q, S q → Levels.get (gs.foldl (sched pred) l) q
        = Levels.get (gs.foldl (sched pred) m) q := by
  intro gs
  induction gs with
  | nil => intro l m _ _ hag q hq; exact hag q hq
  | cons g rest ih =>
    intro l m hlen hsupp hag q hq
    have hbase : l.base g.wires = m.base g.wires :=
      Levels.base_congr g.wires (fun p hp => hag p (hsupp g List.mem_cons_self p hp))
    have hstep : ∀ p, S p → Levels.get (sched pred l g) p = Levels.get (sched pred m g) p := by
      intro p hp
      by_cases hmem : p ∈ g.wires
      · by_cases hlt : p < l.length
        · unfold sched
          by_cases hpr : pred g = true
          · rw [if_pos hpr, if_pos hpr]
            show Levels.get (Levels.setAll l g.wires (l.base g.wires + 1)) p
              = Levels.get (Levels.setAll m g.wires (m.base g.wires + 1)) p
            rw [Levels.get_setAll_of_mem g.wires hmem hlt,
              Levels.get_setAll_of_mem g.wires hmem (by omega), hbase]
          · rw [if_neg hpr, if_neg hpr]
            show Levels.get (Levels.setAll l g.wires (l.base g.wires)) p
              = Levels.get (Levels.setAll m g.wires (m.base g.wires)) p
            rw [Levels.get_setAll_of_mem g.wires hmem hlt,
              Levels.get_setAll_of_mem g.wires hmem (by omega), hbase]
        · have hl : Levels.get (sched pred l g) p = 0 := by
            refine Levels.get_of_length_le ?_
            rw [sched_length]; omega
          have hm : Levels.get (sched pred m g) p = 0 := by
            refine Levels.get_of_length_le ?_
            rw [sched_length]; omega
          rw [hl, hm]
      · rw [get_sched_of_not_mem pred l g hmem, get_sched_of_not_mem pred m g hmem]
        exact hag p hp
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (by rw [sched_length, sched_length]; exact hlen)
      (fun g' hg' => hsupp g' (List.mem_cons_of_mem g hg')) hstep q hq

/-- `depthOf` as a fold of `sched`, which is how the lemmas below read it. -/
theorem depthOf_eq_foldl_sched (pred : Gate → Bool) (c : Circuit) :
    depthOf pred c = (c.gates.foldl (sched pred) c.initialLevels).peak := rfl

/-- Gate lists on disjoint wires do not order each other.  The depth of
their concatenation is the larger of the two, not the sum. -/
theorem depthOf_append_gates_le_max (pred : Gate → Bool) (w : Nat) (as bs : List Gate)
    (hdisj : ∀ g ∈ as, ∀ q ∈ g.wires, ∀ h ∈ bs, q ∉ h.wires) :
    depthOf pred ⟨w, as ++ bs⟩
      ≤ max (depthOf pred ⟨w, as⟩) (depthOf pred ⟨w, bs⟩) := by
  rw [depthOf_eq_foldl_sched, depthOf_eq_foldl_sched, depthOf_eq_foldl_sched]
  show (List.foldl (sched pred) (List.replicate w 0) (as ++ bs)).peak ≤ _
  rw [List.foldl_append]
  refine Levels.peak_le (fun q => ?_)
  have hlen : (as.foldl (sched pred) (List.replicate w 0)).length
      = (List.replicate w 0 : Levels).length :=
    length_foldl_levels (sched_length pred) as (List.replicate w 0)
  by_cases hq : ∃ g ∈ bs, q ∈ g.wires
  · have hagree : ∀ p, (∃ g ∈ bs, p ∈ g.wires) →
        Levels.get (as.foldl (sched pred) (List.replicate w 0)) p
          = Levels.get (List.replicate w 0 : Levels) p := by
      intro p hp
      refine foldl_sched_of_not_mem pred as (List.replicate w 0) (fun g hg hmem => ?_)
      obtain ⟨h, hh, hph⟩ := hp
      exact hdisj g hg p hmem h hh hph
    rw [foldl_sched_congr pred (fun p => ∃ g ∈ bs, p ∈ g.wires) bs hlen
      (fun g hg p hp => ⟨g, hg, hp⟩) hagree q hq]
    exact Nat.le_trans (Levels.get_le_peak _ q) (Nat.le_max_right _ _)
  · rw [foldl_sched_of_not_mem pred bs _ (fun g hg hmem => hq ⟨g, hg, hmem⟩)]
    exact Nat.le_trans (Levels.get_le_peak _ q) (Nat.le_max_left _ _)

/-- Toffoli depth over disjoint supports. -/
theorem toffoliDepth_append_gates_le_max (w : Nat) (as bs : List Gate)
    (hdisj : ∀ g ∈ as, ∀ q ∈ g.wires, ∀ h ∈ bs, q ∉ h.wires) :
    toffoliDepth ⟨w, as ++ bs⟩
      ≤ max (toffoliDepth ⟨w, as⟩) (toffoliDepth ⟨w, bs⟩) :=
  depthOf_append_gates_le_max Gate.isCcz w as bs hdisj

end Circuit

end VQ
