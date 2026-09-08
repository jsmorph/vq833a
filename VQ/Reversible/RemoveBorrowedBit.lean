import VQ.Reversible.BorrowedEquivalence
import VQ.Reversible.Chain
import VQ.Reversible.Control

namespace VQ.Reversible.RemoveBorrowedBit

def insert (q I : Nat) : Nat :=
  readField I 0 q ||| ((I >>> q) <<< (q + 1))

def erase (q I : Nat) : Nat :=
  readField I 0 q ||| ((I >>> (q + 1)) <<< q)

def lower (q k : Nat) : Nat := if k < q then k else k - 1

def raise (q k : Nat) : Nat := if k < q then k else k + 1

theorem testBit_insert (q I k : Nat) :
    (insert q I).testBit k =
      if k < q then I.testBit k else if k = q then false else I.testBit (k - 1) := by
  by_cases hk : k < q
  · simp [insert, testBit_readField, hk, show ¬q + 1 ≤ k by omega]
  · by_cases he : k = q
    · subst k
      simp [insert, testBit_readField, show ¬q + 1 ≤ q by omega]
    · have h : q + 1 ≤ k := by omega
      simp [insert, testBit_readField, hk, he, h]
      congr 1
      omega

theorem testBit_erase (q I k : Nat) : (erase q I).testBit k = I.testBit (raise q k) := by
  by_cases hk : k < q
  · simp [erase, raise, testBit_readField, hk, show ¬q ≤ k by omega]
  · have h : q ≤ k := by omega
    simp [erase, raise, testBit_readField, hk, h]
    congr 1
    omega

theorem insert_clear (q I : Nat) : (insert q I).testBit q = false := by
  simp [testBit_insert]

theorem testBit_insert_of_ne {q k : Nat} (h : k ≠ q) (I : Nat) :
    (insert q I).testBit k = I.testBit (lower q k) := by
  by_cases hk : k < q <;> simp [testBit_insert, lower, hk, h]

theorem erase_insert (q I : Nat) : erase q (insert q I) = I := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_erase, testBit_insert]
  by_cases hk : k < q
  · simp [raise, hk]
  · simp [raise, hk, show ¬k + 1 < q by omega, show k + 1 ≠ q by omega]

theorem insert_erase {q I : Nat} (h : I.testBit q = false) : insert q (erase q I) = I := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_insert]
  by_cases hk : k < q
  · simp [hk, testBit_erase, raise]
  · by_cases he : k = q
    · subst k; simp [h]
    · simp [hk, he, testBit_erase, raise, show ¬k - 1 < q by omega]
      congr 1
      omega

theorem read_insert_below {q off len : Nat} (h : off + len ≤ q) (I : Nat) :
    readField (insert q I) off len = readField I off len := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_readField]
  by_cases hk : k < len
  · rw [testBit_insert, if_pos (by omega)]
  · simp [hk]

theorem erase_write_below {q off len : Nat} (h : off + len ≤ q) (I value : Nat) :
    erase q (writeField I off len value) = writeField (erase q I) off len value := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_erase]
  by_cases hk : k < q
  · rw [raise, if_pos hk]
    by_cases hf : off ≤ k ∧ k < off + len
    · rw [testBit_writeField_inside hf.1 hf.2, testBit_writeField_inside hf.1 hf.2]
    · rw [testBit_writeField_outside (by omega), testBit_writeField_outside (by omega),
        testBit_erase, raise, if_pos hk]
  · rw [raise, if_neg hk, testBit_writeField_outside (Or.inr (by omega)),
      testBit_writeField_outside (Or.inr (by omega)), testBit_erase, raise, if_neg hk]

theorem read_insert_above {q off len : Nat} (h : q < off) (I : Nat) :
    readField (insert q I) off len = readField I (off - 1) len := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_readField]
  by_cases hk : k < len
  · rw [testBit_insert, if_neg (by omega), if_neg (by omega)]
    congr 2
    omega
  · simp [hk]

theorem read_insert_ending {q off len : Nat} (h : off + len = q) (I : Nat) :
    readField (insert q I) off (len + 1) = readField I off len := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_readField]
  by_cases hk : k < len
  · simp [hk, show k < len + 1 by omega, testBit_insert, show off + k < q by omega]
  · by_cases he : k = len
    · subst k
      simp [h, testBit_insert]
    · simp [hk, show ¬k < len + 1 by omega]

theorem erase_write_above {q off len : Nat} (h : q < off) (I value : Nat) :
    erase q (writeField I off len value) =
      writeField (erase q I) (off - 1) len value := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_erase]
  by_cases hk : k < q
  · rw [raise, if_pos hk, testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl (by omega)), testBit_erase, raise, if_pos hk]
  · rw [raise, if_neg hk]
    by_cases hf : off - 1 ≤ k ∧ k < off - 1 + len
    · rw [testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_inside hf.1 hf.2]
      congr 1
      omega
    · rw [testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega), testBit_erase, raise, if_neg hk]

theorem insert_write_below {q off len : Nat} (h : off + len ≤ q) (I value : Nat) :
    insert q (writeField I off len value) = writeField (insert q I) off len value := by
  have he := congrArg (insert q) (erase_write_below h (insert q I) value)
  rw [erase_insert, insert_erase (by
    rw [testBit_writeField_outside (Or.inr h), insert_clear])] at he
  exact he.symm

theorem insert_write_above {q off len : Nat} (h : q < off) (I value : Nat) :
    insert q (writeField I (off - 1) len value) = writeField (insert q I) off len value := by
  have he := congrArg (insert q) (erase_write_above (len := len) h (insert q I) value)
  rw [erase_insert, insert_erase (by
    rw [testBit_writeField_outside (Or.inl h), insert_clear])] at he
  exact he.symm

theorem raise_lower {q k : Nat} (h : k ≠ q) : raise q (lower q k) = k := by
  by_cases hk : k < q
  · simp [lower, raise, hk]
  · simp [lower, raise, hk, show ¬k - 1 < q by omega]
    omega

theorem lower_raise (q k : Nat) : lower q (raise q k) = k := by
  by_cases hk : k < q
  · simp [lower, raise, hk]
  · simp [lower, raise, hk, show ¬k + 1 < q by omega]

theorem erase_xor {q k : Nat} (h : k ≠ q) (I : Nat) :
    erase q (I ^^^ (1 <<< k)) = erase q I ^^^ (1 <<< lower q k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_erase, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  have he : (k = raise q j) ↔ lower q k = j := by
    constructor
    · intro he; rw [he, lower_raise]
    · intro he; rw [← he, raise_lower h]
  simp only [he]

theorem gate_erase {q : Nat} {g : RGate} (h : q ∉ g.wires) (I : Nat) :
    (g.map (lower q)).act (erase q I) = erase q (g.act I) := by
  cases g with
  | x k =>
    have hk : k ≠ q := by simpa [RGate.wires, ne_comm] using h
    exact (erase_xor hk I).symm
  | cx a b =>
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RGate.map, RGate.act, testBit_erase, raise_lower (Ne.symm h.1)]
    cases I.testBit a <;> simp [erase_xor (Ne.symm h.2)]
  | ccx a b c =>
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RGate.map, RGate.act, testBit_erase, raise_lower (Ne.symm h.1),
      raise_lower (Ne.symm h.2.1)]
    cases I.testBit a <;> cases I.testBit b <;> simp [erase_xor (Ne.symm h.2.2)]

theorem gates_erase {q : Nat} {gs : List RGate}
    (h : ∀ g ∈ gs, q ∉ g.wires) (I : Nat) :
    actGates (gs.map (RGate.map (lower q))) (erase q I) = erase q (actGates gs I) := by
  induction gs generalizing I with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, actGates_cons]
    rw [gate_erase (h g List.mem_cons_self)]
    exact ih (fun k hk => h k (List.mem_cons_of_mem g hk)) (g.act I)

theorem lower_lt {q w k : Nat} (hq : q ≤ w) (hk : k < w + 1) (hne : k ≠ q) :
    lower q k < w := by
  unfold lower
  split <;> omega

theorem lower_inj {q a b : Nat} (ha : a ≠ q) (hb : b ≠ q)
    (h : lower q a = lower q b) : a = b := by
  have he := congrArg (raise q) h
  rwa [raise_lower ha, raise_lower hb] at he

theorem gate_wellFormed {q w : Nat} {g : RGate} (hq : q ≤ w)
    (h : g.wellFormed (w + 1) = true) (hn : q ∉ g.wires) :
    (g.map (lower q)).wellFormed w = true := by
  cases g with
  | x k =>
    simp only [RGate.map, RGate.wellFormed, decide_eq_true_eq] at h ⊢
    exact lower_lt hq h (by simpa [RGate.wires, ne_comm] using hn)
  | cx a b =>
    simp only [RGate.map, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    have hn' : a ≠ q ∧ b ≠ q := by simpa [RGate.wires, ne_comm] using hn
    exact ⟨⟨lower_lt hq ha hn'.1, lower_lt hq hb hn'.2⟩,
      fun he => hab (lower_inj hn'.1 hn'.2 he)⟩
  | ccx a b c =>
    simp only [RGate.map, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := h
    have hn' : a ≠ q ∧ b ≠ q ∧ c ≠ q := by simpa [RGate.wires, ne_comm] using hn
    exact ⟨⟨⟨⟨⟨lower_lt hq ha hn'.1, lower_lt hq hb hn'.2.1⟩,
      lower_lt hq hc hn'.2.2⟩, fun he => hab (lower_inj hn'.1 hn'.2.1 he)⟩,
      fun he => hbc (lower_inj hn'.2.1 hn'.2.2 he)⟩,
      fun he => hac (lower_inj hn'.1 hn'.2.2 he)⟩

theorem gates_wellFormed {q w : Nat} {gs : List RGate} (hq : q ≤ w)
    (h : gs.all (RGate.wellFormed (w + 1)) = true) (hn : ∀ g ∈ gs, q ∉ g.wires) :
    (gs.map (RGate.map (lower q))).all (RGate.wellFormed w) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hg
  exact gate_wellFormed hq (List.all_eq_true.mp h source hsource) (hn source hsource)

def Equivalent (q : Nat) (old replacement : List RGate) : Prop :=
  ∀ I, insert q (actGates replacement I) = actGates old (insert q I)

theorem Equivalent.act_eq {q : Nat} {old replacement : List RGate}
    (h : Equivalent q old replacement) (I : Nat) :
    actGates replacement I = erase q (actGates old (insert q I)) := by
  have he := congrArg (erase q) (h I)
  rwa [erase_insert] at he

theorem append {q : Nat} {old₁ old₂ new₁ new₂ : List RGate}
    (h₁ : Equivalent q old₁ new₁) (h₂ : Equivalent q old₂ new₂) :
    Equivalent q (old₁ ++ old₂) (new₁ ++ new₂) := by
  intro I
  simp only [actGates_append]
  rw [h₂, h₁]

theorem gate_equivalent {q : Nat} {g : RGate} (h : q ∉ g.wires) :
    Equivalent q [g] [g.map (lower q)] := by
  intro I
  simp only [actGates_cons, actGates_nil]
  have he := gate_erase h (insert q I)
  rw [erase_insert] at he
  rw [he]
  apply insert_erase
  rw [RGate.testBit_act_of_not_mem h, insert_clear]

theorem gates_equivalent {q : Nat} {gs : List RGate} (h : ∀ g ∈ gs, q ∉ g.wires) :
    Equivalent q gs (gs.map (RGate.map (lower q))) := by
  induction gs with
  | nil => intro I; rfl
  | cons g gs ih =>
    exact append (gate_equivalent (h g List.mem_cons_self))
      (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)))

theorem reverse {q w v : Nat} {old replacement : List RGate}
    (h : Equivalent q old replacement)
    (hold : old.all (RGate.wellFormed w) = true)
    (hnew : replacement.all (RGate.wellFormed v) = true) :
    Equivalent q old.reverse replacement.reverse := by
  intro I
  have he := h (actGates replacement.reverse I)
  have hn := actGates_reverse (gs := replacement.reverse)
    (by simpa only [List.all_reverse] using hnew) I
  rw [List.reverse_reverse] at hn
  rw [hn] at he
  have he' := congrArg (actGates old.reverse) he
  rw [actGates_reverse hold] at he'
  exact he'.symm

private theorem low_insert (q I : Nat) :
    readField (writeField I q 1 0) 0 (q + 1) = readField (insert q I) 0 (q + 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_readField, Nat.zero_add]
  by_cases hk : k < q + 1
  · simp only [hk, decide_true, Bool.true_and, testBit_insert]
    by_cases hl : k < q
    · rw [if_pos hl, testBit_writeField_outside (Or.inl hl)]
    · have he : k = q := by omega
      subst k
      rw [testBit_writeField_inside (by omega) (by omega)]
      simp
  · simp [hk]

theorem borrowed_core {q : Nat} {old replacement : List RGate}
    (h : BorrowedEquivalent q old replacement)
    (hold : old.all (RGate.wellFormed (q + 1)) = true)
    (hnew : replacement.all (RGate.wellFormed (q + 1)) = true) :
    Equivalent q old replacement := by
  intro I
  have ho : ∀ g ∈ old, ∀ k ∈ g.wires, k < q + 1 := fun g hg _ hk =>
    wire_lt_of_wellFormed (List.all_eq_true.mp hold g hg) hk
  have hn : ∀ g ∈ replacement, ∀ k ∈ g.wires, k < q + 1 := fun g hg _ hk =>
    wire_lt_of_wellFormed (List.all_eq_true.mp hnew g hg) hk
  have he : readField (actGates old (writeField I q 1 0)) 0 (q + 1) =
      readField (actGates old (insert q I)) 0 (q + 1) := by
    rw [readField_actGates_low ho, readField_actGates_low ho, low_insert]
  have heb (k : Nat) (hk : k ≤ q) :
      (actGates old (writeField I q 1 0)).testBit k =
        (actGates old (insert q I)).testBit k := by
    have hb := congrArg (fun J => J.testBit k) he
    simpa only [testBit_readField, Nat.zero_add, show k < q + 1 by omega,
      decide_true, Bool.true_and] using hb
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_insert]
  by_cases hk : k < q
  · rw [if_pos hk]
    have hp := congrArg (fun J => J.testBit k) (h.projected I)
    rw [testBit_writeField_outside (Or.inl hk)] at hp
    exact hp.trans (heb k (by omega))
  · rw [if_neg hk]
    by_cases heq : k = q
    · subst k
      rw [if_pos rfl]
      have hp := congrArg (fun J => J.testBit q) (h.projected I)
      rw [testBit_writeField_inside (by omega) (by omega)] at hp
      have hz : Nat.testBit 0 (q - q) = false := by simp
      rw [hz] at hp
      exact hp.trans (heb q (by omega))
    · rw [if_neg heq]
      rw [testBit_actGates_of_outside (gs := old) (fun g hg hmem => by
        have hb := ho g hg k hmem; omega)]
      rw [testBit_insert, if_neg hk, if_neg heq]
      by_cases hborrow : k - 1 = q
      · rw [hborrow, h.preserved]
      · exact testBit_actGates_of_outside (fun g hg hmem => by
          have hb := hn g hg (k - 1) hmem; omega) I

end VQ.Reversible.RemoveBorrowedBit
