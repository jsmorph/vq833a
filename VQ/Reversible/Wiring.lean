/-
Components on arbitrary wire sets.

`VQ.Reversible.Place` puts a component at an offset, which is enough when each
component's fields are a contiguous block in the order its own layout names.  An
assembly does not have that.  Step 5 of the published point addition multiplies
the slope register by the x register and writes the y register.  Step 11 does the
same three in a different order.  Step 8 subtracts the t register from the x
register.  No single ordering of the assembly's registers makes every component
call contiguous, so a component has to be placeable on any injective set of
wires.

`RGate.map f` already relabels, and `VQ.Reversible.Relabel` proves the
equivariance `actGates (gs.map (RGate.map f)) (permuteBits f w i) = permuteBits f
w (actGates gs i)`.  That is stated on the component's own register embedded in a
wider one with zeros everywhere else, which an assembly never has: the other
components' data is in those wires.  What is needed is the other direction --
read the component's register *out of* an arbitrary index, act, and read again.
`gatherBits` is that read, and `gatherBits_actGates` is the theorem.
-/
import VQ.Reversible.Place

namespace VQ
namespace Reversible

/-! ## Reading a component's register out of an assembly

`gatherBits f w i` collects the `w` wires the component occupies, wire `q` of the
component being wire `f q` of the assembly.  It recurses on the wire count so
the kernel reduces it, and it is built from `|||` so every proof about it is a
statement about one bit. -/

/-- The index whose bit `q` is bit `f q` of `i`, for each `q < w`, and whose
other bits are zero. -/
def gatherBits (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, i => (if i.testBit (f w) then 1 <<< w else 0) ||| gatherBits f w i

@[simp] theorem gatherBits_zero (f : Nat → Nat) (i : Nat) : gatherBits f 0 i = 0 := rfl

theorem gatherBits_succ (f : Nat → Nat) (w i : Nat) :
    gatherBits f (w + 1) i = (if i.testBit (f w) then 1 <<< w else 0) ||| gatherBits f w i :=
  rfl

/-- Every bit of the gathered index, with no hypothesis on `f`.  Each wire of the
component contributes to its own bit position, so injectivity is not needed
here.  It is needed for the action, where two wires of the component must not be
the same wire of the assembly. -/
theorem testBit_gatherBits (f : Nat → Nat) (w i q : Nat) :
    (gatherBits f w i).testBit q = (decide (q < w) && i.testBit (f q)) := by
  induction w with
  | zero => simp [gatherBits]
  | succ w ih =>
    rw [gatherBits_succ, Nat.testBit_or, ih]
    by_cases h : q = w
    · subst h
      have hlt : ¬ q < q := Nat.lt_irrefl q
      simp only [hlt, decide_false, Bool.false_and, Bool.or_false,
        Nat.lt_succ_self, decide_true, Bool.true_and]
      by_cases hb : i.testBit (f q)
      · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow_self, hb]
      · rw [if_neg hb, Nat.zero_testBit, Bool.eq_false_iff.mpr hb]
    · have hne : (if i.testBit (f w) then (1 <<< w : Nat) else 0).testBit q = false := by
        by_cases hb : i.testBit (f w)
        · rw [if_pos hb, Nat.one_shiftLeft]
          exact Nat.testBit_two_pow_of_ne (Ne.symm h)
        · rw [if_neg hb]; exact Nat.zero_testBit q
      rw [hne, Bool.false_or]
      by_cases hq : q < w
      · simp [hq, Nat.lt_succ_of_lt hq]
      · simp [hq, show ¬ q < w + 1 by omega]

/-- The gathered index fits the component's register. -/
theorem gatherBits_lt (f : Nat → Nat) (w i : Nat) : gatherBits f w i < 2 ^ w := by
  induction w with
  | zero => exact Nat.two_pow_pos 0
  | succ w ih =>
    rw [gatherBits_succ]
    refine Nat.or_lt_two_pow ?_ (Nat.lt_trans ih
      (Nat.pow_lt_pow_of_lt (by omega) (Nat.lt_succ_self w)))
    by_cases hb : i.testBit (f w)
    · rw [if_pos hb, Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_of_lt (by omega) (Nat.lt_succ_self w)
    · rw [if_neg hb]; exact Nat.two_pow_pos _

/-! ## Placed component action

When placement is injective, flipping assembly wire `f q` flips component wire
`q`.  The three gate cases combine this identity with control values read at
the corresponding wires. -/

/-- Flipping a wire of the assembly that the component occupies. -/
theorem gatherBits_xor {f : Nat → Nat} {w q : Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y) (hq : q < w) (i : Nat) :
    gatherBits f w (i ^^^ (1 <<< f q)) = gatherBits f w i ^^^ (1 <<< q) := by
  refine Nat.eq_of_testBit_eq (fun r => ?_)
  rw [testBit_gatherBits, Nat.testBit_xor, Nat.testBit_xor, testBit_gatherBits,
    Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases hr : r < w
  · have he : (decide (f q = f r)) = (decide (q = r)) := by
      by_cases h : q = r
      · subst h; simp
      · have hne : f q ≠ f r := fun e => h (hinj q r hq hr e)
        simp [h, hne]
    simp only [hr, decide_true, Bool.true_and, he]
  · have hne : ¬ q = r := by omega
    simp [hr, hne]

namespace RGate

/-- One gate, placed on the component's wires. -/
theorem gatherBits_act_map {g : RGate} {w : Nat} {f : Nat → Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (hg : g.wellFormed w = true) (i : Nat) :
    gatherBits f w ((g.map f).act i) = g.act (gatherBits f w i) := by
  have hread : ∀ q, q < w → i.testBit (f q) = (gatherBits f w i).testBit q := by
    intro q hq; rw [testBit_gatherBits]; simp [hq]
  cases g with
  | x q =>
    have hq : q < w := by simpa [RGate.wellFormed] using hg
    exact gatherBits_xor hinj hq i
  | cx a b =>
    have hab : a < w ∧ b < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1, hg.1.2⟩
    simp only [RGate.map, RGate.act, hread a hab.1]
    by_cases hbit : (gatherBits f w i).testBit a
    · rw [if_pos hbit, if_pos hbit]; exact gatherBits_xor hinj hab.2 i
    · rw [if_neg hbit, if_neg hbit]
  | ccx a b c =>
    have habc : a < w ∧ b < w ∧ c < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1.1.1.1, hg.1.1.1.1.2, hg.1.1.1.2⟩
    simp only [RGate.map, RGate.act, hread a habc.1, hread b habc.2.1]
    by_cases hbit : (gatherBits f w i).testBit a && (gatherBits f w i).testBit b
    · rw [if_pos hbit, if_pos hbit]; exact gatherBits_xor hinj habc.2.2 i
    · rw [if_neg hbit, if_neg hbit]

end RGate

/-- A component placed on an arbitrary wire set acts on its own register.

The assembly's index goes in, the component's register is read out of it by
`gatherBits`, and the placed circuit does to that register exactly what the
component does. -/
theorem gatherBits_actGates {gs : List RGate} {w : Nat} {f : Nat → Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) (i : Nat) :
    gatherBits f w (actGates (gs.map (RGate.map f)) i) = actGates gs (gatherBits f w i) := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, actGates_cons, actGates_cons,
      ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')),
      RGate.gatherBits_act_map hinj (hgs g List.mem_cons_self)]

/-- A placed component changes no wire it does not occupy. -/
theorem testBit_actGates_map_of_outside {gs : List RGate} {w b : Nat} {f : Nat → Nat}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) (hb : ∀ q, q < w → f q ≠ b) (i : Nat) :
    (actGates (gs.map (RGate.map f)) i).testBit b = i.testBit b := by
  refine testBit_actGates_of_outside (fun g hg hmem => ?_) i
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hmem
  obtain ⟨q, hq, he⟩ := hmem
  have : q < w := by
    have := hgs g' hg'
    cases g' <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega
  exact hb q this he

/-- The field form: a field of the assembly no wire of the component reaches
reads the same before and after. -/
theorem readField_actGates_map_of_outside {gs : List RGate} {w off len : Nat} {f : Nat → Nat}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true)
    (hb : ∀ q, q < w → f q < off ∨ off + len ≤ f q) (i : Nat) :
    readField (actGates (gs.map (RGate.map f)) i) off len = readField i off len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hbl : b < len
  · simp only [hbl, decide_true, Bool.true_and]
    refine testBit_actGates_map_of_outside hgs (fun q hq he => ?_) i
    have := hb q hq
    omega
  · simp only [hbl, decide_false, Bool.false_and]

/-! ## Disjoint wiring conditions

A component is placed by saying where each of its fields goes.  `place L W` maps
wire `q` of a component with layout `L` to the assembly wire carrying it, and it
recurses on the layout so the kernel reduces it.

`Disjoint` requires pairwise-disjoint blocks and makes `place` injective.  Block
order and contiguity are unrestricted. -/

/-- Where each field of a component's layout sits in the assembly, one offset per
field. -/
abbrev Wiring := List Nat

/-- The assembly wire carrying wire `q` of the component. -/
def place : Layout → Wiring → Nat → Nat
  | [], _, q => q
  | _ :: _, [], q => q
  | l :: L, o :: W, q => if q < l then o + q else place L W (q - l)

/-- Wire `b` of field `j` maps to offset `b` within field `j`'s assigned block. -/
theorem place_field : ∀ (L : Layout) (W : Wiring) (j b : Nat),
    j < W.length → b < Layout.size L j →
      place L W (Layout.offset L j + b) = W.getD j 0 + b := by
  intro L
  induction L with
  | nil =>
    intro W j b _ hb
    exact absurd hb (Nat.not_lt_zero b)
  | cons l L ih =>
    intro W j b hjW hb
    cases W with
    | nil => exact absurd hjW (Nat.not_lt_zero j)
    | cons o W =>
      cases j with
      | zero =>
        have hbl : b < l := hb
        show (if 0 + b < l then o + (0 + b) else place L W (0 + b - l)) = o + b
        rw [if_pos (by omega)]
        omega
      | succ j =>
        show (if l + Layout.offset L j + b < l then o + (l + Layout.offset L j + b)
              else place L W (l + Layout.offset L j + b - l)) = W.getD j 0 + b
        rw [if_neg (by omega),
          show l + Layout.offset L j + b - l = Layout.offset L j + b by omega]
        exact ih W j b (Nat.lt_of_succ_lt_succ hjW) hb

/-- Every wire of a component belongs to one of its fields. -/
theorem exists_field : ∀ (L : Layout) (q : Nat), q < Layout.width L →
    ∃ j b, j < L.length ∧ b < Layout.size L j ∧ q = Layout.offset L j + b := by
  intro L
  induction L with
  | nil => intro q hq; exact absurd hq (Nat.not_lt_zero q)
  | cons l L ih =>
    intro q hq
    have hw : Layout.width (l :: L) = l + Layout.width L := rfl
    by_cases h : q < l
    · exact ⟨0, q, Nat.succ_pos _, h, (Nat.zero_add q).symm⟩
    · obtain ⟨j, b, hj, hb, he⟩ := ih (q - l) (by omega)
      refine ⟨j + 1, b, Nat.succ_lt_succ hj, hb, ?_⟩
      show q = l + Layout.offset L j + b
      omega

/-- The blocks named by a wiring are pairwise disjoint, which makes placement
injective. -/
def Wiring.Disjoint (L : Layout) (W : Wiring) : Prop :=
  ∀ j k, j < W.length → k < W.length → j ≠ k →
    W.getD j 0 + Layout.size L j ≤ W.getD k 0 ∨
      W.getD k 0 + Layout.size L k ≤ W.getD j 0

/-- A placement onto disjoint blocks is injective on the component's wires.
An assembly discharges this `gatherBits_actGates` hypothesis once per
component. -/
theorem place_inj {L : Layout} {W : Wiring} (hlen : L.length ≤ W.length)
    (hd : Wiring.Disjoint L W) :
    ∀ x y, x < Layout.width L → y < Layout.width L → place L W x = place L W y → x = y := by
  intro x y hx hy he
  obtain ⟨j, b, hj, hb, rfl⟩ := exists_field L x hx
  obtain ⟨k, c, hk, hc, rfl⟩ := exists_field L y hy
  rw [place_field L W j b (by omega) hb, place_field L W k c (by omega) hc] at he
  by_cases hne : j = k
  · subst hne; omega
  · rcases hd j k (by omega) (by omega) hne with hh | hh <;> omega

theorem actGates_placed_congr {gs hs : List RGate} {L : Layout} {W : Wiring}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hgs : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (hhs : ∀ g ∈ hs, g.wellFormed (Layout.width L) = true)
    (I : Nat)
    (hact : actGates gs (gatherBits (place L W) (Layout.width L) I) =
      actGates hs (gatherBits (place L W) (Layout.width L) I)) :
    actGates (gs.map (RGate.map (place L W))) I =
      actGates (hs.map (RGate.map (place L W))) I := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases him : ∃ q, q < Layout.width L ∧ place L W q = b
  · obtain ⟨q, hq, rfl⟩ := him
    have hg := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hgs (i := I))
    have hh := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hhs (i := I))
    simp only [testBit_gatherBits, hq, decide_true, Bool.true_and] at hg hh
    rw [hg, hh, hact]
  · rw [testBit_actGates_map_of_outside hgs
        (fun q hq he => him ⟨q, hq, he⟩) I,
      testBit_actGates_map_of_outside hhs
        (fun q hq he => him ⟨q, hq, he⟩) I]

/-- A field of a placed component reads its assigned block.  Every
component claim is an equation about `Layout.read` of its own layout, and this
is what turns such an equation into one about the assembly's register. -/
theorem readField_gatherBits (L : Layout) (W : Wiring) (j I : Nat)
    (hjW : j < W.length) :
    readField (gatherBits (place L W) (Layout.width L) I)
        (Layout.offset L j) (Layout.size L j)
      = readField I (W.getD j 0) (Layout.size L j) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < Layout.size L j
  · have hlt : Layout.offset L j + b < Layout.width L := by
      have := Layout.offset_add_size_le_width L j
      omega
    simp only [hb, decide_true, Bool.true_and, testBit_gatherBits, hlt,
      place_field L W j b hjW hb]
  · simp only [hb, decide_false, Bool.false_and]

/-- Reading part of a field rather than all of it.  An assembly that consumes a
component's answer where the component left it reads one field of that
component's workspace, which is a sub-field of the block assigned to the workspace
to. -/
theorem readField_gatherBits_sub (L : Layout) (W : Wiring) (j q len I : Nat)
    (hjW : j < W.length) (hq : q + len ≤ Layout.size L j) :
    readField (gatherBits (place L W) (Layout.width L) I)
        (Layout.offset L j + q) len
      = readField I (W.getD j 0 + q) len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < len
  · have hb2 : q + b < Layout.size L j := by omega
    have hlt : Layout.offset L j + (q + b) < Layout.width L := by
      have := Layout.offset_add_size_le_width L j
      omega
    have he : Layout.offset L j + q + b = Layout.offset L j + (q + b) := by omega
    have he2 : W.getD j 0 + q + b = W.getD j 0 + (q + b) := by omega
    simp only [hb, decide_true, Bool.true_and, he, he2, testBit_gatherBits, hlt,
      place_field L W j (q + b) hjW hb2]
  · simp only [hb, decide_false, Bool.false_and]

/-- Reading part of a block acted on by a placed component.

`actGates_placed_write` covers a component whose whole action is one field write.
A component that leaves its answer inside its own workspace, with garbage beside
it, has no such equation.  An assembly that consumes the answer where it lies
reads one field of that workspace instead.  Division can then compose inversion
with multiplication without copying the entire workspace. -/
theorem readField_actGates_placed {gs : List RGate} {L : Layout} {W : Wiring}
    {k q len I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length) (hk : k < L.length)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (hq : q + len ≤ Layout.size L k) :
    readField (actGates (gs.map (RGate.map (place L W))) I) (W.getD k 0 + q) len
      = readField (actGates gs (gatherBits (place L W) (Layout.width L) I))
          (Layout.offset L k + q) len := by
  rw [← gatherBits_actGates (place_inj hlen hd) hwf I,
    readField_gatherBits_sub L W k q len _ (by omega) hq]

/-- The `Layout.read` form. -/
theorem read_gatherBits (L : Layout) (W : Wiring) (j I : Nat) (hjW : j < W.length) :
    L.read (gatherBits (place L W) (Layout.width L) I) j
      = readField I (W.getD j 0) (Layout.size L j) :=
  readField_gatherBits L W j I hjW


/-! ## From a component's equation to the assembly's register

Every component specification ends in an equation `act r i = L.write i k v`.
An assembly needs the same statement about its own register: the placed circuit
writes the block assigned to field `k` and leaves every other wire alone.  This
is the theorem each step of an assembly applies once. -/

/-- A placed component writes one block and preserves every other block. -/
theorem actGates_placed_write {gs : List RGate} {L : Layout} {W : Wiring}
    {k v I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length) (hk : k < L.length)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (h : actGates gs (gatherBits (place L W) (Layout.width L) I)
       = L.write (gatherBits (place L W) (Layout.width L) I) k v) :
    actGates (gs.map (RGate.map (place L W))) I
      = writeField I (W.getD k 0) (Layout.size L k) v := by
  have hkW : k < W.length := by omega
  -- Every bit of the placed circuit's output, read through the placement.
  have hbit : ∀ q, q < Layout.width L →
      (actGates (gs.map (RGate.map (place L W))) I).testBit (place L W q)
        = (L.write (gatherBits (place L W) (Layout.width L) I) k v).testBit q := by
    intro q hq
    have := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hwf (i := I))
    simp only [testBit_gatherBits, hq, decide_true, Bool.true_and] at this
    rw [this, h]
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hin : W.getD k 0 ≤ b ∧ b < W.getD k 0 + Layout.size L k
  · -- Inside the block assigned to field `k`.
    obtain ⟨hlo, hhi⟩ := hin
    have hd' : b - W.getD k 0 < Layout.size L k := by omega
    have hplace : place L W (Layout.offset L k + (b - W.getD k 0)) = b := by
      rw [place_field L W k _ hkW hd']; omega
    have hqlt : Layout.offset L k + (b - W.getD k 0) < Layout.width L := by
      have := Layout.offset_add_size_le_width L k
      omega
    have hRHS : (writeField I (W.getD k 0) (Layout.size L k) v).testBit b
        = v.testBit (b - W.getD k 0) := testBit_writeField_inside hlo hhi
    have hLHS : (actGates (gs.map (RGate.map (place L W))) I).testBit b
        = v.testBit (b - W.getD k 0) := by
      have h1 := hbit (Layout.offset L k + (b - W.getD k 0)) hqlt
      rw [hplace] at h1
      rw [h1]
      show (writeField (gatherBits (place L W) (Layout.width L) I)
             (Layout.offset L k) (Layout.size L k) v).testBit
             (Layout.offset L k + (b - W.getD k 0)) = _
      rw [testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
      congr 1
      omega
    rw [hLHS, hRHS]
  · -- Outside it.  The right-hand side is unchanged, and so is the left.
    rw [testBit_writeField_outside (by omega)]
    by_cases him : ∃ q, q < Layout.width L ∧ place L W q = b
    · obtain ⟨q, hq, rfl⟩ := him
      rw [hbit q hq]
      have hout : Layout.offset L k + Layout.size L k ≤ q ∨ q < Layout.offset L k := by
        obtain ⟨j, e, hj, he, rfl⟩ := exists_field L q hq
        have hjk : j ≠ k := by
          intro hje
          subst hje
          rw [place_field L W j e (by omega) he] at hin
          exact hin ⟨Nat.le_add_right _ _, by omega⟩
        rcases Layout.disjoint (l := L) hjk with hh | hh
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      show (writeField _ (Layout.offset L k) (Layout.size L k) v).testBit q = _
      rw [testBit_writeField_outside (by omega), testBit_gatherBits]
      simp [hq]
    · exact testBit_actGates_map_of_outside hwf
        (fun q hq he => him ⟨q, hq, he⟩) I

/-- A placed component writes two blocks and preserves every other block. -/
theorem actGates_placed_write₂ {gs : List RGate} {L : Layout} {W : Wiring}
    {k₁ k₂ v₁ v₂ I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hk₁ : k₁ < L.length) (hk₂ : k₂ < L.length) (hne : k₁ ≠ k₂)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (h : actGates gs (gatherBits (place L W) (Layout.width L) I) =
      L.write (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
        k₂ v₂) :
    actGates (gs.map (RGate.map (place L W))) I =
      writeField
        (writeField I (W.getD k₁ 0) (Layout.size L k₁) v₁)
        (W.getD k₂ 0) (Layout.size L k₂) v₂ := by
  have hk₁W : k₁ < W.length := by omega
  have hk₂W : k₂ < W.length := by omega
  have hbit : ∀ q, q < Layout.width L →
      (actGates (gs.map (RGate.map (place L W))) I).testBit (place L W q) =
        (L.write
          (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
          k₂ v₂).testBit q := by
    intro q hq
    have haction := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hwf (i := I))
    simp only [testBit_gatherBits, hq, decide_true, Bool.true_and] at haction
    rw [haction, h]
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hin₁ : W.getD k₁ 0 ≤ b ∧
      b < W.getD k₁ 0 + Layout.size L k₁
  · obtain ⟨hlo, hhi⟩ := hin₁
    have hb₁ : b - W.getD k₁ 0 < Layout.size L k₁ := by omega
    have hplace : place L W
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = b := by
      rw [place_field L W k₁ _ hk₁W hb₁]
      omega
    have hqlt : Layout.offset L k₁ + (b - W.getD k₁ 0) <
        Layout.width L := by
      have := Layout.offset_add_size_le_width L k₁
      omega
    have hphys :
        b < W.getD k₂ 0 ∨
          W.getD k₂ 0 + Layout.size L k₂ ≤ b := by
      rcases hd k₁ k₂ hk₁W hk₂W hne with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [testBit_writeField_outside hphys,
      testBit_writeField_inside hlo hhi]
    have hlocal :
        Layout.offset L k₁ + Layout.size L k₁ ≤ Layout.offset L k₂ ∨
          Layout.offset L k₂ + Layout.size L k₂ ≤ Layout.offset L k₁ :=
      Layout.disjoint hne
    have hout :
        Layout.offset L k₁ + (b - W.getD k₁ 0) < Layout.offset L k₂ ∨
          Layout.offset L k₂ + Layout.size L k₂ ≤
            Layout.offset L k₁ + (b - W.getD k₁ 0) := by
      rcases hlocal with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hq := hbit
      (Layout.offset L k₁ + (b - W.getD k₁ 0)) hqlt
    rw [hplace] at hq
    rw [hq]
    change (writeField
      (writeField (gatherBits (place L W) (Layout.width L) I)
        (Layout.offset L k₁) (Layout.size L k₁) v₁)
      (Layout.offset L k₂) (Layout.size L k₂) v₂).testBit
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = _
    rw [testBit_writeField_outside hout,
      testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
    congr 1
    omega
  · by_cases hin₂ : W.getD k₂ 0 ≤ b ∧
        b < W.getD k₂ 0 + Layout.size L k₂
    · obtain ⟨hlo, hhi⟩ := hin₂
      have hb₂ : b - W.getD k₂ 0 < Layout.size L k₂ := by omega
      have hplace : place L W
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = b := by
        rw [place_field L W k₂ _ hk₂W hb₂]
        omega
      have hqlt : Layout.offset L k₂ + (b - W.getD k₂ 0) <
          Layout.width L := by
        have := Layout.offset_add_size_le_width L k₂
        omega
      rw [testBit_writeField_inside hlo hhi]
      have hq := hbit
        (Layout.offset L k₂ + (b - W.getD k₂ 0)) hqlt
      rw [hplace] at hq
      rw [hq]
      change (writeField
        (writeField (gatherBits (place L W) (Layout.width L) I)
          (Layout.offset L k₁) (Layout.size L k₁) v₁)
        (Layout.offset L k₂) (Layout.size L k₂) v₂).testBit
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = _
      rw [testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
      congr 1
      omega
    · rw [testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega)]
      by_cases him : ∃ q, q < Layout.width L ∧ place L W q = b
      · obtain ⟨q, hq, rfl⟩ := him
        rw [hbit q hq]
        obtain ⟨j, e, hj, he, rfl⟩ := exists_field L q hq
        have hj₁ : j ≠ k₁ := by
          intro h
          subst j
          rw [place_field L W k₁ e hk₁W he] at hin₁
          exact hin₁ ⟨Nat.le_add_right _ _, by omega⟩
        have hj₂ : j ≠ k₂ := by
          intro h
          subst j
          rw [place_field L W k₂ e hk₂W he] at hin₂
          exact hin₂ ⟨Nat.le_add_right _ _, by omega⟩
        have hout₁ :
            Layout.offset L k₁ + Layout.size L k₁ ≤
                Layout.offset L j + e ∨
              Layout.offset L j + e < Layout.offset L k₁ := by
          rcases Layout.disjoint (l := L) (Ne.symm hj₁) with hh | hh
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        have hout₂ :
            Layout.offset L k₂ + Layout.size L k₂ ≤
                Layout.offset L j + e ∨
              Layout.offset L j + e < Layout.offset L k₂ := by
          rcases Layout.disjoint (l := L) (Ne.symm hj₂) with hh | hh
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        change (writeField
          (writeField (gatherBits (place L W) (Layout.width L) I)
            (Layout.offset L k₁) (Layout.size L k₁) v₁)
          (Layout.offset L k₂) (Layout.size L k₂) v₂).testBit
            (Layout.offset L j + e) = _
        rw [testBit_writeField_outside (by omega),
          testBit_writeField_outside (by omega), testBit_gatherBits]
        simp [hq]
      · exact testBit_actGates_map_of_outside hwf
          (fun q hq he => him ⟨q, hq, he⟩) I

/-- A placed component writes three blocks and preserves every other block. -/
theorem actGates_placed_write₃ {gs : List RGate} {L : Layout} {W : Wiring}
    {k₁ k₂ k₃ v₁ v₂ v₃ I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hk₁ : k₁ < L.length) (hk₂ : k₂ < L.length) (hk₃ : k₃ < L.length)
    (hne₁₂ : k₁ ≠ k₂) (hne₁₃ : k₁ ≠ k₃) (hne₂₃ : k₂ ≠ k₃)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (h : actGates gs (gatherBits (place L W) (Layout.width L) I) =
      L.write
        (L.write
          (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
          k₂ v₂)
        k₃ v₃) :
    actGates (gs.map (RGate.map (place L W))) I =
      writeField
        (writeField
          (writeField I (W.getD k₁ 0) (Layout.size L k₁) v₁)
          (W.getD k₂ 0) (Layout.size L k₂) v₂)
        (W.getD k₃ 0) (Layout.size L k₃) v₃ := by
  have hk₁W : k₁ < W.length := by omega
  have hk₂W : k₂ < W.length := by omega
  have hk₃W : k₃ < W.length := by omega
  have hbit : ∀ q, q < Layout.width L →
      (actGates (gs.map (RGate.map (place L W))) I).testBit (place L W q) =
        (L.write
          (L.write
            (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
            k₂ v₂)
          k₃ v₃).testBit q := by
    intro q hq
    have haction := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hwf (i := I))
    simp only [testBit_gatherBits, hq, decide_true, Bool.true_and] at haction
    rw [haction, h]
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hin₁ : W.getD k₁ 0 ≤ b ∧
      b < W.getD k₁ 0 + Layout.size L k₁
  · obtain ⟨hlo, hhi⟩ := hin₁
    have hb₁ : b - W.getD k₁ 0 < Layout.size L k₁ := by omega
    have hplace : place L W
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = b := by
      rw [place_field L W k₁ _ hk₁W hb₁]
      omega
    have hqlt : Layout.offset L k₁ + (b - W.getD k₁ 0) <
        Layout.width L := by
      have := Layout.offset_add_size_le_width L k₁
      omega
    have hout₂ : b < W.getD k₂ 0 ∨
        W.getD k₂ 0 + Layout.size L k₂ ≤ b := by
      rcases hd k₁ k₂ hk₁W hk₂W hne₁₂ with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hout₃ : b < W.getD k₃ 0 ∨
        W.getD k₃ 0 + Layout.size L k₃ ≤ b := by
      rcases hd k₁ k₃ hk₁W hk₃W hne₁₃ with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [testBit_writeField_outside hout₃,
      testBit_writeField_outside hout₂,
      testBit_writeField_inside hlo hhi]
    have hlocal₂ := Layout.disjoint (l := L) hne₁₂
    have hlocal₃ := Layout.disjoint (l := L) hne₁₃
    have hq := hbit
      (Layout.offset L k₁ + (b - W.getD k₁ 0)) hqlt
    rw [hplace] at hq
    rw [hq]
    change (writeField
      (writeField
        (writeField (gatherBits (place L W) (Layout.width L) I)
          (Layout.offset L k₁) (Layout.size L k₁) v₁)
        (Layout.offset L k₂) (Layout.size L k₂) v₂)
      (Layout.offset L k₃) (Layout.size L k₃) v₃).testBit
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = _
    rw [testBit_writeField_outside (by rcases hlocal₃ with hh | hh <;> omega),
      testBit_writeField_outside (by rcases hlocal₂ with hh | hh <;> omega),
      testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
    congr 1
    omega
  · by_cases hin₂ : W.getD k₂ 0 ≤ b ∧
        b < W.getD k₂ 0 + Layout.size L k₂
    · obtain ⟨hlo, hhi⟩ := hin₂
      have hb₂ : b - W.getD k₂ 0 < Layout.size L k₂ := by omega
      have hplace : place L W
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = b := by
        rw [place_field L W k₂ _ hk₂W hb₂]
        omega
      have hqlt : Layout.offset L k₂ + (b - W.getD k₂ 0) <
          Layout.width L := by
        have := Layout.offset_add_size_le_width L k₂
        omega
      have hout₃ : b < W.getD k₃ 0 ∨
          W.getD k₃ 0 + Layout.size L k₃ ≤ b := by
        rcases hd k₂ k₃ hk₂W hk₃W hne₂₃ with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [testBit_writeField_outside hout₃,
        testBit_writeField_inside hlo hhi]
      have hq := hbit
        (Layout.offset L k₂ + (b - W.getD k₂ 0)) hqlt
      rw [hplace] at hq
      rw [hq]
      have hlocal₁ := Layout.disjoint (l := L) (Ne.symm hne₁₂)
      have hlocal₃ := Layout.disjoint (l := L) hne₂₃
      change (writeField
        (writeField
          (writeField (gatherBits (place L W) (Layout.width L) I)
            (Layout.offset L k₁) (Layout.size L k₁) v₁)
          (Layout.offset L k₂) (Layout.size L k₂) v₂)
        (Layout.offset L k₃) (Layout.size L k₃) v₃).testBit
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = _
      rw [testBit_writeField_outside (by rcases hlocal₃ with hh | hh <;> omega),
        testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
      congr 1
      omega
    · by_cases hin₃ : W.getD k₃ 0 ≤ b ∧
          b < W.getD k₃ 0 + Layout.size L k₃
      · obtain ⟨hlo, hhi⟩ := hin₃
        have hb₃ : b - W.getD k₃ 0 < Layout.size L k₃ := by omega
        have hplace : place L W
            (Layout.offset L k₃ + (b - W.getD k₃ 0)) = b := by
          rw [place_field L W k₃ _ hk₃W hb₃]
          omega
        have hqlt : Layout.offset L k₃ + (b - W.getD k₃ 0) <
            Layout.width L := by
          have := Layout.offset_add_size_le_width L k₃
          omega
        rw [testBit_writeField_inside hlo hhi]
        have hq := hbit
          (Layout.offset L k₃ + (b - W.getD k₃ 0)) hqlt
        rw [hplace] at hq
        rw [hq]
        change (writeField
          (writeField
            (writeField (gatherBits (place L W) (Layout.width L) I)
              (Layout.offset L k₁) (Layout.size L k₁) v₁)
            (Layout.offset L k₂) (Layout.size L k₂) v₂)
          (Layout.offset L k₃) (Layout.size L k₃) v₃).testBit
            (Layout.offset L k₃ + (b - W.getD k₃ 0)) = _
        rw [testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
        congr 1
        omega
      · rw [testBit_writeField_outside (by omega),
          testBit_writeField_outside (by omega),
          testBit_writeField_outside (by omega)]
        by_cases him : ∃ q, q < Layout.width L ∧ place L W q = b
        · obtain ⟨q, hq, rfl⟩ := him
          rw [hbit q hq]
          obtain ⟨j, e, hj, he, rfl⟩ := exists_field L q hq
          have hj₁ : j ≠ k₁ := by
            intro hjk
            subst j
            rw [place_field L W k₁ e hk₁W he] at hin₁
            exact hin₁ ⟨Nat.le_add_right _ _, by omega⟩
          have hj₂ : j ≠ k₂ := by
            intro hjk
            subst j
            rw [place_field L W k₂ e hk₂W he] at hin₂
            exact hin₂ ⟨Nat.le_add_right _ _, by omega⟩
          have hj₃ : j ≠ k₃ := by
            intro hjk
            subst j
            rw [place_field L W k₃ e hk₃W he] at hin₃
            exact hin₃ ⟨Nat.le_add_right _ _, by omega⟩
          change (writeField
            (writeField
              (writeField (gatherBits (place L W) (Layout.width L) I)
                (Layout.offset L k₁) (Layout.size L k₁) v₁)
              (Layout.offset L k₂) (Layout.size L k₂) v₂)
            (Layout.offset L k₃) (Layout.size L k₃) v₃).testBit
              (Layout.offset L j + e) = _
          rw [testBit_writeField_outside (by
                rcases Layout.disjoint (l := L) (Ne.symm hj₃) with hh | hh <;>
                  omega),
            testBit_writeField_outside (by
                rcases Layout.disjoint (l := L) (Ne.symm hj₂) with hh | hh <;>
                  omega),
            testBit_writeField_outside (by
                rcases Layout.disjoint (l := L) (Ne.symm hj₁) with hh | hh <;>
                  omega),
            testBit_gatherBits]
          simp [hq]
        · exact testBit_actGates_map_of_outside hwf
            (fun q hq he => him ⟨q, hq, he⟩) I

/-- A placed component writes four blocks and preserves every other block. -/
theorem actGates_placed_write₄ {gs : List RGate} {L : Layout} {W : Wiring}
    {k₁ k₂ k₃ k₄ v₁ v₂ v₃ v₄ I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hk₁ : k₁ < L.length) (hk₂ : k₂ < L.length)
    (hk₃ : k₃ < L.length) (hk₄ : k₄ < L.length)
    (hne₁₂ : k₁ ≠ k₂) (hne₁₃ : k₁ ≠ k₃) (hne₁₄ : k₁ ≠ k₄)
    (hne₂₃ : k₂ ≠ k₃) (hne₂₄ : k₂ ≠ k₄) (hne₃₄ : k₃ ≠ k₄)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (h : actGates gs (gatherBits (place L W) (Layout.width L) I) =
      L.write
        (L.write
          (L.write
            (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
            k₂ v₂)
          k₃ v₃)
        k₄ v₄) :
    actGates (gs.map (RGate.map (place L W))) I =
      writeField
        (writeField
          (writeField
            (writeField I (W.getD k₁ 0) (Layout.size L k₁) v₁)
            (W.getD k₂ 0) (Layout.size L k₂) v₂)
          (W.getD k₃ 0) (Layout.size L k₃) v₃)
        (W.getD k₄ 0) (Layout.size L k₄) v₄ := by
  have hk₁W : k₁ < W.length := by omega
  have hk₂W : k₂ < W.length := by omega
  have hk₃W : k₃ < W.length := by omega
  have hk₄W : k₄ < W.length := by omega
  have hbit : ∀ q, q < Layout.width L →
      (actGates (gs.map (RGate.map (place L W))) I).testBit (place L W q) =
        (L.write
          (L.write
            (L.write
              (L.write (gatherBits (place L W) (Layout.width L) I) k₁ v₁)
              k₂ v₂)
            k₃ v₃)
          k₄ v₄).testBit q := by
    intro q hq
    have haction := congrArg (fun j => Nat.testBit j q)
      (gatherBits_actGates (place_inj hlen hd) hwf (i := I))
    simp only [testBit_gatherBits, hq, decide_true, Bool.true_and] at haction
    rw [haction, h]
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hin₁ : W.getD k₁ 0 ≤ b ∧
      b < W.getD k₁ 0 + Layout.size L k₁
  · obtain ⟨hlo, hhi⟩ := hin₁
    have hb₁ : b - W.getD k₁ 0 < Layout.size L k₁ := by omega
    have hplace : place L W
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = b := by
      rw [place_field L W k₁ _ hk₁W hb₁]
      omega
    have hqlt : Layout.offset L k₁ + (b - W.getD k₁ 0) <
        Layout.width L := by
      have := Layout.offset_add_size_le_width L k₁
      omega
    have hout₂ : b < W.getD k₂ 0 ∨
        W.getD k₂ 0 + Layout.size L k₂ ≤ b := by
      rcases hd k₁ k₂ hk₁W hk₂W hne₁₂ with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hout₃ : b < W.getD k₃ 0 ∨
        W.getD k₃ 0 + Layout.size L k₃ ≤ b := by
      rcases hd k₁ k₃ hk₁W hk₃W hne₁₃ with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hout₄ : b < W.getD k₄ 0 ∨
        W.getD k₄ 0 + Layout.size L k₄ ≤ b := by
      rcases hd k₁ k₄ hk₁W hk₄W hne₁₄ with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [testBit_writeField_outside hout₄,
      testBit_writeField_outside hout₃,
      testBit_writeField_outside hout₂,
      testBit_writeField_inside hlo hhi]
    have hlocal₂ := Layout.disjoint (l := L) hne₁₂
    have hlocal₃ := Layout.disjoint (l := L) hne₁₃
    have hlocal₄ := Layout.disjoint (l := L) hne₁₄
    have hq := hbit
      (Layout.offset L k₁ + (b - W.getD k₁ 0)) hqlt
    rw [hplace] at hq
    rw [hq]
    change (writeField
      (writeField
        (writeField
          (writeField (gatherBits (place L W) (Layout.width L) I)
            (Layout.offset L k₁) (Layout.size L k₁) v₁)
          (Layout.offset L k₂) (Layout.size L k₂) v₂)
        (Layout.offset L k₃) (Layout.size L k₃) v₃)
      (Layout.offset L k₄) (Layout.size L k₄) v₄).testBit
        (Layout.offset L k₁ + (b - W.getD k₁ 0)) = _
    rw [testBit_writeField_outside (by rcases hlocal₄ with hh | hh <;> omega),
      testBit_writeField_outside (by rcases hlocal₃ with hh | hh <;> omega),
      testBit_writeField_outside (by rcases hlocal₂ with hh | hh <;> omega),
      testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
    congr 1
    omega
  · by_cases hin₂ : W.getD k₂ 0 ≤ b ∧
        b < W.getD k₂ 0 + Layout.size L k₂
    · obtain ⟨hlo, hhi⟩ := hin₂
      have hb₂ : b - W.getD k₂ 0 < Layout.size L k₂ := by omega
      have hplace : place L W
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = b := by
        rw [place_field L W k₂ _ hk₂W hb₂]
        omega
      have hqlt : Layout.offset L k₂ + (b - W.getD k₂ 0) <
          Layout.width L := by
        have := Layout.offset_add_size_le_width L k₂
        omega
      have hout₃ : b < W.getD k₃ 0 ∨
          W.getD k₃ 0 + Layout.size L k₃ ≤ b := by
        rcases hd k₂ k₃ hk₂W hk₃W hne₂₃ with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hout₄ : b < W.getD k₄ 0 ∨
          W.getD k₄ 0 + Layout.size L k₄ ≤ b := by
        rcases hd k₂ k₄ hk₂W hk₄W hne₂₄ with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [testBit_writeField_outside hout₄,
        testBit_writeField_outside hout₃,
        testBit_writeField_inside hlo hhi]
      have hlocal₁ := Layout.disjoint (l := L) (Ne.symm hne₁₂)
      have hlocal₃ := Layout.disjoint (l := L) hne₂₃
      have hlocal₄ := Layout.disjoint (l := L) hne₂₄
      have hq := hbit
        (Layout.offset L k₂ + (b - W.getD k₂ 0)) hqlt
      rw [hplace] at hq
      rw [hq]
      change (writeField
        (writeField
          (writeField
            (writeField (gatherBits (place L W) (Layout.width L) I)
              (Layout.offset L k₁) (Layout.size L k₁) v₁)
            (Layout.offset L k₂) (Layout.size L k₂) v₂)
          (Layout.offset L k₃) (Layout.size L k₃) v₃)
        (Layout.offset L k₄) (Layout.size L k₄) v₄).testBit
          (Layout.offset L k₂ + (b - W.getD k₂ 0)) = _
      rw [testBit_writeField_outside (by rcases hlocal₄ with hh | hh <;> omega),
        testBit_writeField_outside (by rcases hlocal₃ with hh | hh <;> omega),
        testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
      congr 1
      omega
    · by_cases hin₃ : W.getD k₃ 0 ≤ b ∧
          b < W.getD k₃ 0 + Layout.size L k₃
      · obtain ⟨hlo, hhi⟩ := hin₃
        have hb₃ : b - W.getD k₃ 0 < Layout.size L k₃ := by omega
        have hplace : place L W
            (Layout.offset L k₃ + (b - W.getD k₃ 0)) = b := by
          rw [place_field L W k₃ _ hk₃W hb₃]
          omega
        have hqlt : Layout.offset L k₃ + (b - W.getD k₃ 0) <
            Layout.width L := by
          have := Layout.offset_add_size_le_width L k₃
          omega
        have hout₄ : b < W.getD k₄ 0 ∨
            W.getD k₄ 0 + Layout.size L k₄ ≤ b := by
          rcases hd k₃ k₄ hk₃W hk₄W hne₃₄ with hh | hh
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        rw [testBit_writeField_outside hout₄,
          testBit_writeField_inside hlo hhi]
        have hlocal₁ := Layout.disjoint (l := L) (Ne.symm hne₁₃)
        have hlocal₂ := Layout.disjoint (l := L) (Ne.symm hne₂₃)
        have hlocal₄ := Layout.disjoint (l := L) hne₃₄
        have hq := hbit
          (Layout.offset L k₃ + (b - W.getD k₃ 0)) hqlt
        rw [hplace] at hq
        rw [hq]
        change (writeField
          (writeField
            (writeField
              (writeField (gatherBits (place L W) (Layout.width L) I)
                (Layout.offset L k₁) (Layout.size L k₁) v₁)
              (Layout.offset L k₂) (Layout.size L k₂) v₂)
            (Layout.offset L k₃) (Layout.size L k₃) v₃)
          (Layout.offset L k₄) (Layout.size L k₄) v₄).testBit
            (Layout.offset L k₃ + (b - W.getD k₃ 0)) = _
        rw [testBit_writeField_outside (by
              rcases hlocal₄ with hh | hh <;> omega),
          testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
        congr 1
        omega
      · by_cases hin₄ : W.getD k₄ 0 ≤ b ∧
            b < W.getD k₄ 0 + Layout.size L k₄
        · obtain ⟨hlo, hhi⟩ := hin₄
          have hb₄ : b - W.getD k₄ 0 < Layout.size L k₄ := by omega
          have hplace : place L W
              (Layout.offset L k₄ + (b - W.getD k₄ 0)) = b := by
            rw [place_field L W k₄ _ hk₄W hb₄]
            omega
          have hqlt : Layout.offset L k₄ + (b - W.getD k₄ 0) <
              Layout.width L := by
            have := Layout.offset_add_size_le_width L k₄
            omega
          rw [testBit_writeField_inside hlo hhi]
          have hq := hbit
            (Layout.offset L k₄ + (b - W.getD k₄ 0)) hqlt
          rw [hplace] at hq
          rw [hq]
          change (writeField
            (writeField
              (writeField
                (writeField (gatherBits (place L W) (Layout.width L) I)
                  (Layout.offset L k₁) (Layout.size L k₁) v₁)
                (Layout.offset L k₂) (Layout.size L k₂) v₂)
              (Layout.offset L k₃) (Layout.size L k₃) v₃)
            (Layout.offset L k₄) (Layout.size L k₄) v₄).testBit
              (Layout.offset L k₄ + (b - W.getD k₄ 0)) = _
          rw [testBit_writeField_inside (Nat.le_add_right _ _) (by omega)]
          congr 1
          omega
        · rw [testBit_writeField_outside (by omega),
            testBit_writeField_outside (by omega),
            testBit_writeField_outside (by omega),
            testBit_writeField_outside (by omega)]
          by_cases him : ∃ q, q < Layout.width L ∧ place L W q = b
          · obtain ⟨q, hq, rfl⟩ := him
            rw [hbit q hq]
            obtain ⟨j, e, hj, he, rfl⟩ := exists_field L q hq
            have hj₁ : j ≠ k₁ := by
              intro hjk
              subst j
              rw [place_field L W k₁ e hk₁W he] at hin₁
              exact hin₁ ⟨Nat.le_add_right _ _, by omega⟩
            have hj₂ : j ≠ k₂ := by
              intro hjk
              subst j
              rw [place_field L W k₂ e hk₂W he] at hin₂
              exact hin₂ ⟨Nat.le_add_right _ _, by omega⟩
            have hj₃ : j ≠ k₃ := by
              intro hjk
              subst j
              rw [place_field L W k₃ e hk₃W he] at hin₃
              exact hin₃ ⟨Nat.le_add_right _ _, by omega⟩
            have hj₄ : j ≠ k₄ := by
              intro hjk
              subst j
              rw [place_field L W k₄ e hk₄W he] at hin₄
              exact hin₄ ⟨Nat.le_add_right _ _, by omega⟩
            change (writeField
              (writeField
                (writeField
                  (writeField (gatherBits (place L W) (Layout.width L) I)
                    (Layout.offset L k₁) (Layout.size L k₁) v₁)
                  (Layout.offset L k₂) (Layout.size L k₂) v₂)
                (Layout.offset L k₃) (Layout.size L k₃) v₃)
              (Layout.offset L k₄) (Layout.size L k₄) v₄).testBit
                (Layout.offset L j + e) = _
            rw [testBit_writeField_outside (by
                  rcases Layout.disjoint (l := L) (Ne.symm hj₄) with hh | hh <;>
                    omega),
              testBit_writeField_outside (by
                  rcases Layout.disjoint (l := L) (Ne.symm hj₃) with hh | hh <;>
                    omega),
              testBit_writeField_outside (by
                  rcases Layout.disjoint (l := L) (Ne.symm hj₂) with hh | hh <;>
                    omega),
              testBit_writeField_outside (by
                  rcases Layout.disjoint (l := L) (Ne.symm hj₁) with hh | hh <;>
                    omega),
              testBit_gatherBits]
            simp [hq]
          · exact testBit_actGates_map_of_outside hwf
              (fun q hq he => him ⟨q, hq, he⟩) I


/-! ## Well-formedness of a placed component

A placed component must be well formed at the assembly's width for its
uncomputation to undo it, which `actGates_reverse` needs. -/

/-- Every wire a placement uses lies inside one of the blocks the wiring names. -/
theorem place_lt {L : Layout} {W : Wiring} {Wd : Nat} (hlen : L.length ≤ W.length)
    (hW : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ Wd) :
    ∀ q, q < Layout.width L → place L W q < Wd := by
  intro q hq
  obtain ⟨j, b, hj, hb, rfl⟩ := exists_field L q hq
  rw [place_field L W j b (by omega) hb]
  have := hW j hj
  omega

/-- A placed component is well formed at the assembly's width. -/
theorem wellFormed_placeGates {L : Layout} {W : Wiring} {gs : List RGate} {Wd : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hW : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ Wd)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true) :
    (gs.map (RGate.map (place L W))).all (RGate.wellFormed Wd) = true := by
  refine List.all_eq_true.mpr (fun g hg => ?_)
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact RGate.wellFormed_map (place_lt hlen hW) (place_inj hlen hd) (hwf g' hg')

/-- The uncomputation of a placed component undoes it.  A step of the
assembly that runs a component backwards reads as this. -/
theorem actGates_placed_reverse {L : Layout} {W : Wiring} {gs : List RGate} {Wd : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hW : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ Wd)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true) (i : Nat) :
    actGates (gs.map (RGate.map (place L W))).reverse
        (actGates (gs.map (RGate.map (place L W))) i) = i :=
  actGates_reverse (w := Wd) (wellFormed_placeGates hd hlen hW hwf) i


/-! ## Two indices with the same fields

A component specification is an equation between basis indices, and an assembly
proves its own claim by exhibiting the field values.  Turning one into the other
needs extensionality: two indices inside the register with the same fields are
the same index. -/

/-- A layout separates indices. -/
theorem eq_of_read {L : Layout} {i j : Nat}
    (hi : i < 2 ^ Layout.width L) (hj : j < 2 ^ Layout.width L)
    (h : ∀ k, k < L.length → L.read i k = L.read j k) : i = j := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < Layout.width L
  · obtain ⟨k, c, hk, hc, rfl⟩ := exists_field L b hb
    have he := congrArg (fun z => Nat.testBit z c) (h k hk)
    simpa [Layout.read, testBit_readField, hc] using he
  · have hle : Layout.width L ≤ b := by omega
    have hpow : ∀ z, z < 2 ^ Layout.width L → z.testBit b = false := fun z hz =>
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) hle))
    rw [hpow i hi, hpow j hj]


/-- A placement lands outside a range when every block it names does.  An
assembly copies its answer into a field the components must not touch, and this
is how that is discharged for a whole family of steps at once. -/
theorem place_avoids {L : Layout} {W : Wiring} {lo hi : Nat}
    (hlen : L.length ≤ W.length)
    (h : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ lo ∨ hi ≤ W.getD j 0) :
    ∀ q, q < Layout.width L → place L W q < lo ∨ hi ≤ place L W q := by
  intro q hq
  obtain ⟨j, b, hj, hb, rfl⟩ := exists_field L q hq
  rw [place_field L W j b (by omega) hb]
  rcases h j hj with hh | hh
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The gate form. -/
theorem placeGates_avoids {L : Layout} {W : Wiring} {gs : List RGate} {lo hi : Nat}
    (hlen : L.length ≤ W.length)
    (hwf : ∀ g ∈ gs, g.wellFormed (Layout.width L) = true)
    (h : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ lo ∨ hi ≤ W.getD j 0) :
    ∀ g ∈ gs.map (RGate.map (place L W)), ∀ q ∈ g.wires, q < lo ∨ hi ≤ q := by
  intro g hg q hq
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  have hlt : q' < Layout.width L := by
    have := hwf g' hg'
    cases g' <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega
  exact place_avoids hlen h q' hlt


end Reversible
end VQ
