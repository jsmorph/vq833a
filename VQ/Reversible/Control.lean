/-
Coherent control of a reversible circuit.

The source circuit occupies its declared low wires.  Its external control is
the next wire, and one reusable clean wire above the control decomposes every
three-control NOT into three Toffolis.  The transformation returns that wire to
zero after each source gate, so one wire suffices for the complete circuit.
-/
import VQ.Reversible.Denote
import VQ.Reversible.Place
import VQ.Reversible.ArithmeticSpec
import VQ.Reversible.Chain
import VQ.Circuit.Compose

namespace VQ
namespace Reversible

/-- The coherent control of one reversible gate.  `w` is both the source width
and the external control wire, while `w + 1` is a reusable clean decomposition
wire.  The `ccx` case computes the conjunction of the external control and the
first source control, uses it, and erases it. -/
def controlGate (w : Nat) : RGate → List RGate
  | .x q => [.cx w q]
  | .cx a b => [.ccx w a b]
  | .ccx a b c => [.ccx w a (w + 1), .ccx (w + 1) b c, .ccx w a (w + 1)]

/-- Gatewise coherent control of a source list.  Flattening preserves source
order and places each compute-use-uncompute block contiguously.  The same clean
wire can therefore serve every source Toffoli. -/
def controlGates (w : Nat) (gs : List RGate) : List RGate :=
  gs.flatMap (controlGate w)

/-- A source circuit with an external quantum control and one clean
decomposition wire.  The two added wires occur above the complete source
register.  No classical branch or measurement participates in this operation. -/
def control (r : RCircuit) : RCircuit :=
  { width := r.width + 2, gates := controlGates r.width r.gates }

/-! ## Well-formedness -/

theorem controlGate_wellFormed {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) :
    (controlGate w g).all (RGate.wellFormed (w + 2)) = true := by
  cases g <;> simp_all [controlGate, RGate.wellFormed] <;> omega

theorem control_wellFormed {r : RCircuit} (hr : r.wellFormed = true) :
    (control r).wellFormed = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨s, hs, hgs⟩ := List.exists_of_mem_flatMap hg
  exact List.all_eq_true.mp
    (controlGate_wellFormed (RCircuit.wellFormed_mem hr hs)) g hgs

/-! ## Basis-index action -/

theorem not_mem_wires_of_wellFormed {g : RGate} {w b : Nat}
    (hg : g.wellFormed w = true) (hb : w ≤ b) : b ∉ g.wires := by
  cases g <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega

/-- One transformed gate has the source action under a set external control and
the identity action under a clear control.  The decomposition wire must start
clear.  The three-Toffoli clause returns it to that state before the block ends. -/
theorem actGates_controlGate {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) {i : Nat} (hs : i.testBit (w + 1) = false) :
    actGates (controlGate w g) i = if i.testBit w then g.act i else i := by
  cases g with
  | x q =>
      simp [controlGate, actGates, RGate.act]
  | cx a b =>
      by_cases hctl : i.testBit w = true <;>
        by_cases ha : i.testBit a = true <;>
        simp [controlGate, actGates, RGate.act, hctl, ha]
  | ccx a b c =>
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := hg
      let s := w + 1
      let g₁ := RGate.ccx w a s
      let g₂ := RGate.ccx s b c
      have hg₁ : g₁.wellFormed (w + 2) = true := by
        simp [g₁, s, RGate.wellFormed]
        omega
      change g₁.act (g₂.act (g₁.act i)) =
        if i.testBit w then (RGate.ccx a b c).act i else i
      by_cases hca : (i.testBit w && i.testBit a) = true
      · obtain ⟨hctl, hA⟩ : i.testBit w = true ∧ i.testBit a = true := by
          simpa only [Bool.and_eq_true] using hca
        have hfirst : g₁.act i = i ^^^ (1 <<< s) := by
          change (if i.testBit w && i.testBit a then i ^^^ (1 <<< s) else i) = _
          rw [if_pos hca]
        have hjs : (g₁.act i).testBit s = true := by
          rw [hfirst, Semantics.testBit_xor_self, hs]
          rfl
        have hjb : (g₁.act i).testBit b = i.testBit b := by
          rw [hfirst, RGate.testBit_xor_of_ne (show b ≠ s by simp [s]; omega)]
        by_cases hB : i.testBit b = true
        · have hsecond : g₂.act (g₁.act i) = g₁.act i ^^^ (1 <<< c) := by
            change (if (g₁.act i).testBit s && (g₁.act i).testBit b then
              g₁.act i ^^^ (1 <<< c) else g₁.act i) = _
            rw [if_pos (by simp [hjs, hjb, hB])]
          have hkw : (g₂.act (g₁.act i)).testBit w = true := by
            rw [hsecond, RGate.testBit_xor_of_ne (Nat.ne_of_gt hc), hfirst,
              RGate.testBit_xor_of_ne (show w ≠ s by simp [s]), hctl]
          have hka : (g₂.act (g₁.act i)).testBit a = true := by
            rw [hsecond, RGate.testBit_xor_of_ne hac, hfirst,
              RGate.testBit_xor_of_ne (show a ≠ s by simp [s]; omega), hA]
          rw [show g₁.act (g₂.act (g₁.act i)) =
              g₂.act (g₁.act i) ^^^ (1 <<< s) by
                change (if (g₂.act (g₁.act i)).testBit w &&
                  (g₂.act (g₁.act i)).testBit a then
                  g₂.act (g₁.act i) ^^^ (1 <<< s) else g₂.act (g₁.act i)) = _
                rw [if_pos (by simp [hkw, hka])]]
          rw [hsecond, hfirst,
            show (i ^^^ (1 <<< s)) ^^^ (1 <<< c) =
              (i ^^^ (1 <<< c)) ^^^ (1 <<< s) by ac_rfl,
            RGate.xor_cancel]
          simp [hctl, RGate.act, hA, hB]
        · have hB' : i.testBit b = false := Bool.eq_false_iff.mpr hB
          have hsecond : g₂.act (g₁.act i) = g₁.act i := by
            change (if (g₁.act i).testBit s && (g₁.act i).testBit b then
              g₁.act i ^^^ (1 <<< c) else g₁.act i) = _
            rw [if_neg (by simp [hjs, hjb, hB'])]
          rw [hsecond, RGate.act_act hg₁]
          simp [hctl, RGate.act, hA, hB']
      · have hfirst : g₁.act i = i := by
          change (if i.testBit w && i.testBit a then i ^^^ (1 <<< s) else i) = _
          rw [if_neg hca]
        have hsecond : g₂.act (g₁.act i) = i := by
          rw [hfirst]
          change (if i.testBit s && i.testBit b then i ^^^ (1 <<< c) else i) = _
          rw [if_neg (by simp [s, hs])]
        rw [hsecond, hfirst]
        by_cases hctl : i.testBit w = true
        · have hA : i.testBit a = false := by
            cases hbit : i.testBit a with
            | false => rfl
            | true =>
                exfalso
                exact hca (by simp [hctl, hbit])
          simp [hctl, RGate.act, hA]
        · have hctl' : i.testBit w = false := Bool.eq_false_iff.mpr hctl
          simp [hctl']

/-- The transformed list coherently selects one of two actions.  Every source
gate is below `w`, so neither arm changes the external control.  Induction is
valid with one shared decomposition wire because each transformed gate clears
it before the next block starts. -/
theorem actGates_controlGates {w : Nat} {gs : List RGate}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) {i : Nat}
    (hs : i.testBit (w + 1) = false) :
    actGates (controlGates w gs) i =
      if i.testBit w then actGates gs i else i := by
  induction gs generalizing i with
  | nil =>
      simp only [controlGates, List.flatMap_nil, actGates_nil]
      split <;> rfl
  | cons g gs ih =>
      change actGates (controlGate w g ++ controlGates w gs) i = _
      rw [actGates_append, actGates_controlGate (hgs g List.mem_cons_self) hs]
      by_cases hctl : i.testBit w = true
      · rw [if_pos hctl]
        have hw : w ∉ g.wires :=
          not_mem_wires_of_wellFormed (hgs g List.mem_cons_self) (Nat.le_refl w)
        have hscratch : w + 1 ∉ g.wires :=
          not_mem_wires_of_wellFormed (hgs g List.mem_cons_self) (by omega)
        have hctl' : (g.act i).testBit w = true := by
          rw [RGate.testBit_act_of_not_mem hw, hctl]
        have hs' : (g.act i).testBit (w + 1) = false := by
          rw [RGate.testBit_act_of_not_mem hscratch, hs]
        rw [ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) hs',
          if_pos hctl', if_pos hctl, actGates_cons]
      · have hctl' : i.testBit w = false := Bool.eq_false_iff.mpr hctl
        simp only [hctl', Bool.false_eq_true, if_false]
        rw [ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) hs]
        simp [hctl']

/-- The circuit-level action theorem.  The source circuit and identity occur as
the two arms of one reversible circuit, selected by a qubit that the circuit
preserves.  The theorem assumes only source well-formedness and a clear
decomposition wire. -/
theorem act_control {r : RCircuit} (hr : r.wellFormed = true) {i : Nat}
    (hs : i.testBit (r.width + 1) = false) :
    act (control r) i = if i.testBit r.width then act r i else i :=
  actGates_controlGates (fun _ hg => RCircuit.wellFormed_mem hr hg) hs

theorem control_preserves_control {r : RCircuit} (hr : r.wellFormed = true) {i : Nat}
    (hs : i.testBit (r.width + 1) = false) :
    (act (control r) i).testBit r.width = i.testBit r.width := by
  rw [act_control hr hs]
  split
  · exact testBit_actGates_of_outside
      (fun g hg => not_mem_wires_of_wellFormed
        (RCircuit.wellFormed_mem hr hg) (Nat.le_refl r.width)) i
  · rfl

theorem control_cleans_scratch {r : RCircuit} (hr : r.wellFormed = true) {i : Nat}
    (hs : i.testBit (r.width + 1) = false) :
    (act (control r) i).testBit (r.width + 1) = false := by
  rw [act_control hr hs]
  split
  · rw [show (act r i).testBit (r.width + 1) = i.testBit (r.width + 1) from
      testBit_actGates_of_outside
        (fun g hg => not_mem_wires_of_wellFormed
          (RCircuit.wellFormed_mem hr hg) (by omega)) i, hs]
  · exact hs

/-! ## Controlled addition -/

theorem wire_lt_of_wellFormed {g : RGate} {w q : Nat}
    (hg : g.wellFormed w = true) (hq : q ∈ g.wires) : q < w := by
  cases g <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega

/-- Coherent control carries any verified wrapped adder into the controlled
specification when its declared width matches the adder layout.  The proof runs
the source theorem on the low register and proves that the two added wires
remain quantum data in the wider index.  `VQ.Semantics.ReversibleControl` proves
the corresponding phase-one amplitude action. -/
theorem control_addsWrap {ws n : Nat} {r : RCircuit}
    (hwidth : r.width = (adderLayout n ws).width)
    (hr : r.wellFormed = true) (hadd : AddsWrap ws n r) :
    ControlledAddsWrap ws n (control r) := by
  intro enabled a b i hi h₀ h₁ h₂ h₃ h₄
  have hw : r.width = 2 * n + ws := by
    have h := hwidth
    simp [adderLayout, Layout.width] at h
    omega
  have hfull : (controlledAdderLayout n ws).width = r.width + 2 := by
    simp [controlledAdderLayout, Layout.width, hw]
    omega
  have hcontrolRead : readField i r.width 1 = if enabled = true then 1 else 0 := by
    change readField i (n + (n + ws)) 1 = _ at h₃
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₃
  have hscratchRead : readField i (r.width + 1) 1 = 0 := by
    change readField i (n + (n + (ws + 1))) 1 = 0 at h₄
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₄
  have hscratch : i.testBit (r.width + 1) = false := by
    rw [readField_one_eq_if] at hscratchRead
    cases h : i.testBit (r.width + 1) <;> simp_all
  rw [act_control hr hscratch]
  cases enabled with
  | false =>
      have hcontrol : i.testBit r.width = false := by
        simp only [Bool.false_eq_true, if_false] at hcontrolRead
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      simp [hcontrol]
  | true =>
      simp only [if_true] at hcontrolRead ⊢
      have hcontrol : i.testBit r.width = true := by
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      rw [hcontrol]
      let lo := readField i 0 r.width
      have hlo : lo < 2 ^ (adderLayout n ws).width := by
        rw [← hwidth]
        exact readField_lt i 0 r.width
      have hlo₀ : (adderLayout n ws).read lo 0 = a := by
        change readField lo 0 n = a
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₀
      have hlo₁ : (adderLayout n ws).read lo 1 = b := by
        change readField lo n n = b
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₁
      have hlo₂ : (adderLayout n ws).read lo 2 = 0 := by
        change readField lo (n + n) ws = 0
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₂
      have hbase := addsWrap_read hadd hlo hlo₀ hlo₁ hlo₂
      have hwires : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < r.width := by
        intro g hg q hq
        exact wire_lt_of_wellFormed (RCircuit.wellFormed_mem hr hg) hq
      have hlow : readField (act r i) 0 r.width = act r lo := by
        exact readField_actGates_low hwires i
      have hfield₀ : (controlledAdderLayout n ws).read (act r i) 0 = a := by
        change readField (act r i) 0 n = a
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.1
      have hfield₁ : (controlledAdderLayout n ws).read (act r i) 1 =
          (a + b) % 2 ^ n := by
        change readField (act r i) n n = _
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.1
      have hfield₂ : (controlledAdderLayout n ws).read (act r i) 2 = 0 := by
        change readField (act r i) (n + n) ws = 0
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.2
      have hact : act r i < 2 ^ (controlledAdderLayout n ws).width := by
        apply actGates_lt
        · intro g hg
          apply RGate.wellFormed_mono (w := r.width)
            (w' := (controlledAdderLayout n ws).width)
          · rw [hfull]
            omega
          · exact RCircuit.wellFormed_mem hr hg
        · exact hi
      have hout : (controlledAdderLayout n ws).write i 1
          ((a + b) % 2 ^ n) < 2 ^ (controlledAdderLayout n ws).width :=
        Layout.write_lt hi
      apply Layout.ext hact hout
      intro k hk
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
        simp [controlledAdderLayout] at hk
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · rw [Layout.read_write_ne (by decide), hfield₀, h₀]
      · rw [hfield₁, Layout.read_write_self]
        exact Nat.mod_lt _ (Nat.two_pow_pos n)
      · rw [Layout.read_write_ne (by decide), hfield₂, h₂]
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + ws)) 1 =
          readField i (n + (n + ws)) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width) (len := 1)
          (fun g hg q hq => Or.inl (hwires g hg q hq)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + (ws + 1))) 1 =
          readField i (n + (n + (ws + 1))) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width + 1) (len := 1)
          (fun g hg q hq => Or.inl (by have := hwires g hg q hq; omega)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep

/-- Coherent control carries a verified modular adder into the controlled
specification when its declared width matches the adder layout.  The circuit
preserves the source and coherent control.  It returns both workspace fields to
zero. -/
theorem control_addsMod {m ws n : Nat} {r : RCircuit}
    (hwidth : r.width = (adderLayout n ws).width)
    (hr : r.wellFormed = true) (hadd : AddsMod m ws n r) :
    ControlledAddsMod m ws n (control r) := by
  intro enabled a b i hi h₀ h₁ h₂ h₃ h₄ hm ha hb
  have hw : r.width = 2 * n + ws := by
    have h := hwidth
    simp [adderLayout, Layout.width] at h
    omega
  have hfull : (controlledAdderLayout n ws).width = r.width + 2 := by
    simp [controlledAdderLayout, Layout.width, hw]
    omega
  have hcontrolRead : readField i r.width 1 = if enabled = true then 1 else 0 := by
    change readField i (n + (n + ws)) 1 = _ at h₃
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₃
  have hscratchRead : readField i (r.width + 1) 1 = 0 := by
    change readField i (n + (n + (ws + 1))) 1 = 0 at h₄
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₄
  have hscratch : i.testBit (r.width + 1) = false := by
    rw [readField_one_eq_if] at hscratchRead
    cases h : i.testBit (r.width + 1) <;> simp_all
  rw [act_control hr hscratch]
  cases enabled with
  | false =>
      have hcontrol : i.testBit r.width = false := by
        simp only [Bool.false_eq_true, if_false] at hcontrolRead
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      simp [hcontrol]
  | true =>
      simp only [if_true] at hcontrolRead ⊢
      have hcontrol : i.testBit r.width = true := by
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      rw [hcontrol]
      let lo := readField i 0 r.width
      have hlo : lo < 2 ^ (adderLayout n ws).width := by
        rw [← hwidth]
        exact readField_lt i 0 r.width
      have hlo₀ : (adderLayout n ws).read lo 0 = a := by
        change readField lo 0 n = a
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₀
      have hlo₁ : (adderLayout n ws).read lo 1 = b := by
        change readField lo n n = b
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₁
      have hlo₂ : (adderLayout n ws).read lo 2 = 0 := by
        change readField lo (n + n) ws = 0
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₂
      have hbase := addsMod_read hadd hlo hlo₀ hlo₁ hlo₂ ha hb hm
      have hwires : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < r.width := by
        intro g hg q hq
        exact wire_lt_of_wellFormed (RCircuit.wellFormed_mem hr hg) hq
      have hlow : readField (act r i) 0 r.width = act r lo := by
        exact readField_actGates_low hwires i
      have hfield₀ : (controlledAdderLayout n ws).read (act r i) 0 = a := by
        change readField (act r i) 0 n = a
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.1
      have hfield₁ : (controlledAdderLayout n ws).read (act r i) 1 =
          (a + b) % m := by
        change readField (act r i) n n = _
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.1
      have hfield₂ : (controlledAdderLayout n ws).read (act r i) 2 = 0 := by
        change readField (act r i) (n + n) ws = 0
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.2
      have hact : act r i < 2 ^ (controlledAdderLayout n ws).width := by
        apply actGates_lt
        · intro g hg
          apply RGate.wellFormed_mono (w := r.width)
            (w' := (controlledAdderLayout n ws).width)
          · rw [hfull]
            omega
          · exact RCircuit.wellFormed_mem hr hg
        · exact hi
      have hout : (controlledAdderLayout n ws).write i 1
          ((a + b) % m) < 2 ^ (controlledAdderLayout n ws).width :=
        Layout.write_lt hi
      apply Layout.ext hact hout
      intro k hk
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
        simp [controlledAdderLayout] at hk
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · rw [Layout.read_write_ne (by decide), hfield₀, h₀]
      · rw [hfield₁, Layout.read_write_self]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm
      · rw [Layout.read_write_ne (by decide), hfield₂, h₂]
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + ws)) 1 =
          readField i (n + (n + ws)) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width) (len := 1)
          (fun g hg q hq => Or.inl (hwires g hg q hq)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + (ws + 1))) 1 =
          readField i (n + (n + (ws + 1))) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width + 1) (len := 1)
          (fun g hg q hq => Or.inl (by have := hwires g hg q hq; omega)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep

/-- Coherent control carries a verified modular subtractor into the controlled
specification when its declared width matches the adder layout.  The circuit
preserves the source and coherent control.  It returns both workspace fields to
zero. -/
theorem control_subsMod {m ws n : Nat} {r : RCircuit}
    (hwidth : r.width = (adderLayout n ws).width)
    (hr : r.wellFormed = true) (hsub : SubsMod m ws n r) :
    ControlledSubsMod m ws n (control r) := by
  intro enabled a b i hi h₀ h₁ h₂ h₃ h₄ hm ha hb
  have hw : r.width = 2 * n + ws := by
    have h := hwidth
    simp [adderLayout, Layout.width] at h
    omega
  have hfull : (controlledAdderLayout n ws).width = r.width + 2 := by
    simp [controlledAdderLayout, Layout.width, hw]
    omega
  have hcontrolRead : readField i r.width 1 = if enabled = true then 1 else 0 := by
    change readField i (n + (n + ws)) 1 = _ at h₃
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₃
  have hscratchRead : readField i (r.width + 1) 1 = 0 := by
    change readField i (n + (n + (ws + 1))) 1 = 0 at h₄
    simpa [hw, Nat.two_mul, Nat.add_assoc] using h₄
  have hscratch : i.testBit (r.width + 1) = false := by
    rw [readField_one_eq_if] at hscratchRead
    cases h : i.testBit (r.width + 1) <;> simp_all
  rw [act_control hr hscratch]
  cases enabled with
  | false =>
      have hcontrol : i.testBit r.width = false := by
        simp only [Bool.false_eq_true, if_false] at hcontrolRead
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      simp [hcontrol]
  | true =>
      simp only [if_true] at hcontrolRead ⊢
      have hcontrol : i.testBit r.width = true := by
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      rw [hcontrol]
      let lo := readField i 0 r.width
      have hlo : lo < 2 ^ (adderLayout n ws).width := by
        rw [← hwidth]
        exact readField_lt i 0 r.width
      have hlo₀ : (adderLayout n ws).read lo 0 = a := by
        change readField lo 0 n = a
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₀
      have hlo₁ : (adderLayout n ws).read lo 1 = b := by
        change readField lo n n = b
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₁
      have hlo₂ : (adderLayout n ws).read lo 2 = 0 := by
        change readField lo (n + n) ws = 0
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledAdderLayout, Layout.read, Layout.offset, Layout.size]
          using h₂
      have hbase := subsMod_read hsub hlo hlo₀ hlo₁ hlo₂ hm ha hb
      have hwires : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < r.width := by
        intro g hg q hq
        exact wire_lt_of_wellFormed (RCircuit.wellFormed_mem hr hg) hq
      have hlow : readField (act r i) 0 r.width = act r lo := by
        exact readField_actGates_low hwires i
      have hfield₀ : (controlledAdderLayout n ws).read (act r i) 0 = a := by
        change readField (act r i) 0 n = a
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.1
      have hfield₁ : (controlledAdderLayout n ws).read (act r i) 1 =
          (b + (m - a)) % m := by
        change readField (act r i) n n = _
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.1
      have hfield₂ : (controlledAdderLayout n ws).read (act r i) 2 = 0 := by
        change readField (act r i) (n + n) ws = 0
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hbase.2.2
      have hact : act r i < 2 ^ (controlledAdderLayout n ws).width := by
        apply actGates_lt
        · intro g hg
          apply RGate.wellFormed_mono (w := r.width)
            (w' := (controlledAdderLayout n ws).width)
          · rw [hfull]
            omega
          · exact RCircuit.wellFormed_mem hr hg
        · exact hi
      have hout : (controlledAdderLayout n ws).write i 1
          ((b + (m - a)) % m) < 2 ^ (controlledAdderLayout n ws).width :=
        Layout.write_lt hi
      apply Layout.ext hact hout
      intro k hk
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
        simp [controlledAdderLayout] at hk
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · rw [Layout.read_write_ne (by decide), hfield₀, h₀]
      · rw [hfield₁, Layout.read_write_self]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm
      · rw [Layout.read_write_ne (by decide), hfield₂, h₂]
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + ws)) 1 =
          readField i (n + (n + ws)) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width) (len := 1)
          (fun g hg q hq => Or.inl (hwires g hg q hq)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (n + (ws + 1))) 1 =
          readField i (n + (n + (ws + 1))) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width + 1) (len := 1)
          (fun g hg q hq => Or.inl (by have := hwires g hg q hq; omega)) i
        simpa [hw, Nat.two_mul, Nat.add_assoc] using hkeep

/-- Coherent control carries a verified modular negator into the controlled
specification when its declared width matches the constant-operation layout. -/
theorem control_negatesMod {m ws n : Nat} {r : RCircuit}
    (hwidth : r.width = (constLayout n ws).width)
    (hr : r.wellFormed = true) (hneg : NegatesMod m ws n r) :
    ControlledNegatesMod m ws n (control r) := by
  intro enabled a i hi h₀ h₁ h₂ h₃ hm ha
  have hw : r.width = n + ws := by
    have h := hwidth
    simp [constLayout, Layout.width] at h
    exact h
  have hfull : (controlledConstLayout n ws).width = r.width + 2 := by
    simp [controlledConstLayout, Layout.width, hw]
    omega
  have hcontrolRead : readField i r.width 1 =
      if enabled = true then 1 else 0 := by
    change readField i (n + ws) 1 = _ at h₂
    simpa [hw] using h₂
  have hscratchRead : readField i (r.width + 1) 1 = 0 := by
    change readField i (n + (ws + 1)) 1 = 0 at h₃
    simpa [hw, Nat.add_assoc] using h₃
  have hscratch : i.testBit (r.width + 1) = false := by
    rw [readField_one_eq_if] at hscratchRead
    cases h : i.testBit (r.width + 1) <;> simp_all
  rw [act_control hr hscratch]
  cases enabled with
  | false =>
      have hcontrol : i.testBit r.width = false := by
        simp only [Bool.false_eq_true, if_false] at hcontrolRead
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      simp [hcontrol]
  | true =>
      simp only [if_true] at hcontrolRead ⊢
      have hcontrol : i.testBit r.width = true := by
        rw [readField_one_eq_if] at hcontrolRead
        cases h : i.testBit r.width <;> simp_all
      rw [hcontrol]
      let lo := readField i 0 r.width
      have hlo : lo < 2 ^ (constLayout n ws).width := by
        rw [← hwidth]
        exact readField_lt i 0 r.width
      have hlo₀ : (constLayout n ws).read lo 0 = a := by
        change readField lo 0 n = a
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledConstLayout, Layout.read, Layout.offset, Layout.size]
          using h₀
      have hlo₁ : (constLayout n ws).read lo 1 = 0 := by
        change readField lo n ws = 0
        rw [show lo = readField i 0 r.width from rfl,
          readField_readField_zero (by omega)]
        simpa [controlledConstLayout, Layout.read, Layout.offset, Layout.size]
          using h₁
      have hbase := negatesMod_read hneg hlo hlo₀ hlo₁ hm ha
      have hwires : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < r.width := by
        intro g hg q hq
        exact wire_lt_of_wellFormed (RCircuit.wellFormed_mem hr hg) hq
      have hlow : readField (act r i) 0 r.width = act r lo := by
        exact readField_actGates_low hwires i
      have hfield₀ : (controlledConstLayout n ws).read (act r i) 0 =
          (m - a) % m := by
        change readField (act r i) 0 n = _
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [constLayout, Layout.read, Layout.offset, Layout.size] using hbase.1
      have hfield₁ : (controlledConstLayout n ws).read (act r i) 1 = 0 := by
        change readField (act r i) n ws = 0
        rw [← readField_readField_zero (i := act r i) (W := r.width) (by omega),
          hlow]
        simpa [constLayout, Layout.read, Layout.offset, Layout.size] using hbase.2
      have hact : act r i < 2 ^ (controlledConstLayout n ws).width := by
        apply actGates_lt
        · intro g hg
          apply RGate.wellFormed_mono (w := r.width)
            (w' := (controlledConstLayout n ws).width)
          · rw [hfull]
            omega
          · exact RCircuit.wellFormed_mem hr hg
        · exact hi
      have hout : (controlledConstLayout n ws).write i 0 ((m - a) % m) <
          2 ^ (controlledConstLayout n ws).width := Layout.write_lt hi
      apply Layout.ext hact hout
      intro k hk
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
        simp [controlledConstLayout] at hk
        omega
      rcases hcases with rfl | rfl | rfl | rfl
      · rw [hfield₀, Layout.read_write_self]
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm
      · rw [Layout.read_write_ne (by decide), hfield₁, h₁]
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + ws) 1 =
          readField i (n + ws) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width) (len := 1)
          (fun g hg q hq => Or.inl (hwires g hg q hq)) i
        simpa [hw] using hkeep
      · rw [Layout.read_write_ne (by decide)]
        change readField (actGates r.gates i) (n + (ws + 1)) 1 =
          readField i (n + (ws + 1)) 1
        have hkeep := readField_actGates_of_outside
          (off := r.width + 1) (len := 1)
          (fun g hg q hq => Or.inl (by have := hwires g hg q hq; omega)) i
        simpa [hw, Nat.add_assoc] using hkeep

/-! ## Exact structural counts -/

/-- Source `X` gates become controlled-NOT gates.  The predicate remains local
to the control transformation because the reversible resource API otherwise
needs only `isCx` and `isCcx`.  It also makes the three transformed source gate
kinds visible in separate exact formulas. -/
def RGate.isX : RGate → Bool
  | .x _ => true
  | _ => false

theorem length_controlGates (w : Nat) : ∀ gs : List RGate,
    (controlGates w gs).length = gs.length + 2 * gs.countP RGate.isCcx := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [controlGates, List.flatMap_cons, List.length_append]
      rw [show List.flatMap (controlGate w) gs = controlGates w gs from rfl, ih,
        List.length_cons, List.countP_cons]
      cases g <;> simp [controlGate, RGate.isCcx] <;> omega

theorem ccx_controlGates (w : Nat) : ∀ gs : List RGate,
    (controlGates w gs).countP RGate.isCcx =
      gs.countP RGate.isCx + 3 * gs.countP RGate.isCcx := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [controlGates, List.flatMap_cons, List.countP_append]
      rw [show List.flatMap (controlGate w) gs = controlGates w gs from rfl, ih,
        List.countP_cons, List.countP_cons]
      cases g <;> simp [controlGate, List.countP_cons, RGate.isCx, RGate.isCcx] <;> omega

theorem cx_controlGates (w : Nat) : ∀ gs : List RGate,
    (controlGates w gs).countP RGate.isCx = gs.countP RGate.isX := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [controlGates, List.flatMap_cons, List.countP_append]
      rw [show List.flatMap (controlGate w) gs = controlGates w gs from rfl, ih,
        List.countP_cons]
      cases g <;> simp [controlGate, RGate.isX, RGate.isCx] <;> omega

theorem x_controlGates (w : Nat) : ∀ gs : List RGate,
    (controlGates w gs).countP RGate.isX = 0 := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [controlGates, List.flatMap_cons, List.countP_append]
      rw [show List.flatMap (controlGate w) gs = controlGates w gs from rfl, ih]
      cases g <;> rfl

theorem toffoliCount_compile_control (r : RCircuit) :
    Circuit.toffoliCount (compile (control r)) =
      r.gates.countP RGate.isCx + 3 * r.gates.countP RGate.isCcx := by
  rw [toffoliCount_compile, control, ccx_controlGates]

theorem cnotCount_compile_control (r : RCircuit) :
    Circuit.cnotCount (compile (control r)) = r.gates.countP RGate.isX := by
  rw [cnotCount_compile, control, cx_controlGates]

theorem cliffordCount_compile_control (r : RCircuit) :
    Circuit.cliffordCount (compile (control r)) =
      r.gates.length + r.gates.countP RGate.isCx +
        5 * r.gates.countP RGate.isCcx := by
  rw [cliffordCount_compile, control, length_controlGates, ccx_controlGates]
  omega

theorem gateCount_compile_control (r : RCircuit) :
    Circuit.gateCount (compile (control r)) =
      r.gates.length + 2 * r.gates.countP RGate.isCx +
        8 * r.gates.countP RGate.isCcx := by
  rw [gateCount_compile, control, length_controlGates, ccx_controlGates]
  omega

end Reversible
end VQ
