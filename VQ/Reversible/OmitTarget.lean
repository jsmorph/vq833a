import VQ.Reversible.BorrowedEquivalence

namespace VQ.Reversible.OmitTarget

def target : RGate → Nat
  | .x q => q
  | .cx _ q => q
  | .ccx _ _ q => q

def controlsAvoid (q : Nat) : RGate → Bool
  | .x _ => true
  | .cx a _ => decide (a ≠ q)
  | .ccx a b _ => decide (a ≠ q ∧ b ≠ q)

def gates (q : Nat) (gs : List RGate) : List RGate :=
  gs.filter (fun g => decide (target g ≠ q))

theorem avoids {q : Nat} {g : RGate} (hc : controlsAvoid q g = true)
    (ht : target g ≠ q) : q ∉ g.wires := by
  cases g <;> simp_all [controlsAvoid, target, RGate.wires, ne_comm]

private theorem overwrite_xor (q I value : Nat) :
    writeField (I ^^^ (1 <<< q)) q 1 value = writeField I q 1 value := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k = q
  · subst k
    rw [testBit_writeField_inside (by omega) (by omega),
      testBit_writeField_inside (by omega) (by omega)]
  · rw [testBit_writeField_outside (by omega),
      testBit_writeField_outside (by omega), RGate.testBit_xor_of_ne hk]

theorem gate_projection {q : Nat} {g : RGate}
    (hc : controlsAvoid q g = true) (I value : Nat) :
    actGates (gates q [g]) (writeField I q 1 value) =
      writeField (g.act I) q 1 value := by
  by_cases ht : target g = q
  · cases g with
    | x k =>
      have : k = q := ht
      subst k
      simp [gates, target, actGates, RGate.act, overwrite_xor]
    | cx a k =>
      have : k = q := ht
      subst k
      rw [show gates q [.cx a q] = [] by simp [gates, target], actGates_nil]
      change writeField I q 1 value =
        writeField (if I.testBit a then I ^^^ (1 <<< q) else I) q 1 value
      split <;> simp [overwrite_xor]
    | ccx a b k =>
      have : k = q := ht
      subst k
      rw [show gates q [.ccx a b q] = [] by simp [gates, target], actGates_nil]
      change writeField I q 1 value =
        writeField (if I.testBit a && I.testBit b then I ^^^ (1 <<< q) else I) q 1 value
      split <;> simp [overwrite_xor]
  · have hn := avoids hc ht
    have he := actGates_write_of_outside
      (gs := [g]) (off := q) (len := 1) (v := value)
      (fun a ha k hk => by
        have hag : a = g := by simpa using ha
        subst a
        have : k ≠ q := by intro he; subst k; exact hn hk
        omega) I
    simpa [gates, ht, actGates] using he

theorem projection {q : Nat} {gs : List RGate}
    (hc : gs.all (controlsAvoid q) = true) (I value : Nat) :
    actGates (gates q gs) (writeField I q 1 value) =
      writeField (actGates gs I) q 1 value := by
  induction gs generalizing I with
  | nil => rfl
  | cons g gs ih =>
    have hh : controlsAvoid q g = true ∧ gs.all (controlsAvoid q) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hc
    have hd : gates q (g :: gs) = gates q [g] ++ gates q gs := by
      exact List.filter_append [g] gs
    rw [hd, actGates_append, gate_projection hh.1, ih hh.2, actGates_cons]

theorem gates_avoid {q : Nat} {gs : List RGate}
    (hc : gs.all (controlsAvoid q) = true) : ∀ g ∈ gates q gs, q ∉ g.wires := by
  intro g hg
  obtain ⟨hmem, ht⟩ := List.mem_filter.mp hg
  exact avoids (List.all_eq_true.mp hc g hmem) (of_decide_eq_true ht)

theorem gates_wellFormed {q w : Nat} {gs : List RGate}
    (h : gs.all (RGate.wellFormed w) = true) :
    (gates q gs).all (RGate.wellFormed w) = true :=
  List.all_eq_true.mpr (fun g hg => List.all_eq_true.mp h g (List.mem_filter.mp hg).1)

theorem act_eq {q : Nat} {gs : List RGate}
    (hc : gs.all (controlsAvoid q) = true) (I : Nat) :
    actGates (gates q gs) I =
      writeField (actGates gs (writeField I q 1 0)) q 1 (bitValue I q) := by
  have h := projection hc (writeField I q 1 0) (bitValue I q)
  rw [writeField_writeField, write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I q))] at h
  exact h

theorem eq_of_preserved {q : Nat} {gs : List RGate} {I : Nat}
    (hc : gs.all (controlsAvoid q) = true)
    (hp : bitValue (actGates gs I) q = bitValue I q) :
    actGates (gates q gs) I = actGates gs I := by
  have h := projection hc I (bitValue I q)
  rw [write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I q))] at h
  rw [h]
  apply write_of_bitValue
  rw [Nat.mod_eq_of_lt (bitValue_lt I q), hp]

end VQ.Reversible.OmitTarget
