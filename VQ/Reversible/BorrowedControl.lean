import VQ.Reversible.Control

namespace VQ.Reversible.BorrowedControl

def triple (a b c target scratch : Nat) : List RGate :=
  [.ccx a b scratch, .ccx scratch c target,
   .ccx a b scratch, .ccx scratch c target]

theorem triple_act {a b c target scratch : Nat}
    (has : a ≠ scratch) (hbs : b ≠ scratch) (hcs : c ≠ scratch)
    (hat : a ≠ target) (hbt : b ≠ target) (hct : c ≠ target)
    (hst : scratch ≠ target) (i : Nat) :
    actGates (triple a b c target scratch) i =
      if i.testBit a && i.testBit b && i.testBit c then
        i ^^^ (1 <<< target) else i := by
  have hcancel (n : Nat) :
      ((n ^^^ (1 <<< scratch)) ^^^ (1 <<< target)) ^^^ (1 <<< scratch) =
        n ^^^ (1 <<< target) := by
    rw [show ((n ^^^ (1 <<< scratch)) ^^^ (1 <<< target)) ^^^
        (1 <<< scratch) =
        ((n ^^^ (1 <<< target)) ^^^ (1 <<< scratch)) ^^^ (1 <<< scratch) by
          ac_rfl, RGate.xor_cancel]
  cases ha : i.testBit a <;> cases hb : i.testBit b <;>
    cases hc : i.testBit c <;> cases hs : i.testBit scratch <;>
    simp [triple, actGates, RGate.act, ha, hb, hc, hs,
      RGate.testBit_xor_of_ne has, RGate.testBit_xor_of_ne hbs,
      RGate.testBit_xor_of_ne hcs, RGate.testBit_xor_of_ne hst,
      RGate.testBit_xor_of_ne hat, RGate.testBit_xor_of_ne hbt,
      RGate.testBit_xor_of_ne hct, RGate.xor_cancel, hcancel]

def gate (w : Nat) : RGate → List RGate
  | .x q => [.cx w q]
  | .cx a b => [.ccx w a b]
  | .ccx a b c => triple w a b c (w + 1)

def gates (w : Nat) (gs : List RGate) : List RGate :=
  gs.flatMap (gate w)

theorem gate_wellFormed {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) :
    (gate w g).all (RGate.wellFormed (w + 2)) = true := by
  cases g <;> simp_all [gate, triple, RGate.wellFormed] <;> omega

theorem gate_act {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) (i : Nat) :
    actGates (gate w g) i = if i.testBit w then g.act i else i := by
  cases g with
  | x q => simp [gate, actGates, RGate.act]
  | cx a b =>
      cases hw : i.testBit w <;> cases ha : i.testBit a <;>
        simp [gate, actGates, RGate.act, hw, ha]
  | ccx a b c =>
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := hg
      rw [gate, triple_act (by omega) (by omega) (by omega)
        (by omega) hac hbc (by omega)]
      cases i.testBit w <;> simp [RGate.act]

theorem gates_act {w : Nat} {gs : List RGate}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) (i : Nat) :
    actGates (gates w gs) i =
      if i.testBit w then actGates gs i else i := by
  induction gs generalizing i with
  | nil => simp [gates, actGates_nil]
  | cons g gs ih =>
      change actGates (gate w g ++ gates w gs) i = _
      rw [actGates_append, gate_act (hgs g List.mem_cons_self)]
      have htail := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
      cases hw : i.testBit w with
      | false => simp [hw, ih htail]
      | true =>
          have hw' : (g.act i).testBit w = true := by
            rw [RGate.testBit_act_of_not_mem
              (not_mem_wires_of_wellFormed
                (hgs g List.mem_cons_self) (Nat.le_refl w)), hw]
          simp only [↓reduceIte, ih htail, hw', actGates_cons]

theorem gates_wellFormed {w : Nat} {gs : List RGate}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) :
    (gates w gs).all (RGate.wellFormed (w + 2)) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨s, hs, hg⟩ := List.exists_of_mem_flatMap hg
  exact List.all_eq_true.mp (gate_wellFormed (hgs s hs)) g hg

theorem gate_preserves_borrowed {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) (i : Nat) :
    (actGates (gate w g) i).testBit (w + 1) = i.testBit (w + 1) := by
  rw [gate_act hg]
  split
  · exact RGate.testBit_act_of_not_mem
      (not_mem_wires_of_wellFormed hg (by omega)) i
  · rfl

theorem gate_eq_clear_control {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) {i : Nat}
    (hs : i.testBit (w + 1) = false) :
    actGates (gate w g) i = actGates (controlGate w g) i := by
  rw [gate_act hg, actGates_controlGate hg hs]

theorem gate_ccx {w : Nat} {g : RGate} :
    (gate w g).countP RGate.isCcx =
      (if g.isCx then 1 else 0) + (if g.isCcx then 4 else 0) := by
  cases g <;> rfl

theorem gates_ccx (w : Nat) (gs : List RGate) :
    (gates w gs).countP RGate.isCcx =
      gs.countP RGate.isCx + 4 * gs.countP RGate.isCcx := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [gates, List.flatMap_cons, List.countP_append] at *
      rw [gate_ccx, ih]
      cases g <;> simp [List.countP_cons, RGate.isCx, RGate.isCcx] <;> omega

end VQ.Reversible.BorrowedControl
