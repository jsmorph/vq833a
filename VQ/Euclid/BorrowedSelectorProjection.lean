import VQ.Euclid.BorrowedSelector
import VQ.Reversible.BorrowedPlacement

namespace VQ.Euclid.BorrowedSelector

open Reversible

private theorem clear_below {gs : List RGate} {q : Nat}
    (h : ∀ g ∈ gs, ∀ k ∈ g.wires, k < q) (I : Nat) :
    writeField (actGates gs I) q 1 0 = actGates gs (writeField I q 1 0) :=
  (actGates_write_of_outside (fun g hg k hk => Or.inl (h g hg k hk)) I).symm

theorem conjunction_clear (controls : List Nat) (scratch target I : Nat)
    (hn : controls.Nodup) (hb : ∀ q ∈ controls, q < scratch)
    (ht : target < scratch) (hts : target ∉ controls) :
    writeField (actGates (conjunction controls scratch target) I)
        (scratch + (controls.length - 3)) 1 0 =
      actGates (Selector.conjunction controls scratch target)
        (writeField I (scratch + (controls.length - 3)) 1 0) := by
  induction controls, scratch, target using conjunction.induct generalizing I with
  | case1 scratch target =>
    rw [conjunction, Selector.conjunction]
    apply clear_below
    intro g hg k hk
    simp only [List.mem_singleton] at hg
    subst g
    simp [RGate.wires] at hk
    subst k
    simpa using ht
  | case2 a scratch target =>
    rw [conjunction, Selector.conjunction]
    apply clear_below
    intro g hg k hk
    simp only [List.mem_singleton] at hg
    subst g
    simp [RGate.wires] at hk
    rcases hk with rfl | rfl
    · simpa using hb k (by simp)
    · simpa using ht
  | case3 a b scratch target =>
    rw [conjunction, Selector.conjunction]
    apply clear_below
    intro g hg k hk
    simp only [List.mem_singleton] at hg
    subst g
    simp [RGate.wires] at hk
    rcases hk with rfl | rfl | rfl
    · simpa using hb k (by simp)
    · simpa using hb k (by simp)
    · simpa using ht
  | case4 a b c scratch target =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hc := hb c (by simp)
    have hnew : scratchClear [a, b, c] scratch I := by
      intro j hj
      simp at hj
    have hold : Selector.scratchClear [a, b, c] scratch
        (writeField I scratch 1 0) := by
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      simp only [Nat.add_zero]
      rw [testBit_writeField_inside (by omega) (by omega)]
      simp
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self, Nat.add_zero]
    rw [conjunction_act _ _ _ _ hn hb ht hts hnew,
      Selector.conjunction_act _ _ _ _ hn hb ht hts hold]
    simp only [Selector.allSet, List.all_cons, List.all_nil, Bool.and_true,
      testBit_writeField_outside (Or.inl ha),
      testBit_writeField_outside (Or.inl hb'),
      testBit_writeField_outside (Or.inl hc)]
    split
    · exact (xor_writeField_of_outside (Or.inl ht)).symm
    · rfl
  | case5 a b c d rest scratch target ih =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hn' : (scratch :: c :: d :: rest).Nodup := by
      rw [List.nodup_cons]
      exact ⟨fun hs => Nat.lt_irrefl scratch (hb scratch (by simp [hs])), hn.tail.tail⟩
    have hbelow : ∀ q ∈ scratch :: c :: d :: rest, q < scratch + 1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · have h := hb q (by simp [hq]); omega
    have htarget : target ∉ scratch :: c :: d :: rest := by
      intro hq
      rcases List.mem_cons.mp hq with hq | hq
      · omega
      · exact hts (by simp [hq])
    have hrec := fun i => ih i hn' hbelow (by omega) htarget
    have hq : scratch + ((a :: b :: c :: d :: rest).length - 3) =
        scratch + 1 + ((scratch :: c :: d :: rest).length - 3) := by simp; omega
    have hgate : ∀ g ∈ [RGate.ccx a b scratch], ∀ k ∈ g.wires,
        k < scratch + 1 + ((scratch :: c :: d :: rest).length - 3) := by
      intro g hg k hk
      simp only [List.mem_singleton] at hg
      subst g
      simp [RGate.wires] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    rw [hq]
    simp only [conjunction, Selector.conjunction, actGates_append]
    rw [clear_below hgate, hrec, clear_below hgate]
    simp only [Selector.conjunction, actGates_append]

theorem conjunction_preserves (controls : List Nat) (scratch target I : Nat)
    (hn : controls.Nodup) (hb : ∀ q ∈ controls, q < scratch)
    (ht : target < scratch) (hts : target ∉ controls) :
    (actGates (conjunction controls scratch target) I).testBit
        (scratch + (controls.length - 3)) =
      I.testBit (scratch + (controls.length - 3)) := by
  induction controls, scratch, target using conjunction.induct generalizing I with
  | case1 scratch target =>
    apply testBit_actGates_of_outside
    intro g hg
    simp [conjunction] at hg
    subst g
    simp [RGate.wires]
    omega
  | case2 a scratch target =>
    have ha := hb a (by simp)
    apply testBit_actGates_of_outside
    intro g hg
    simp [conjunction] at hg
    subst g
    simp [RGate.wires]
    omega
  | case3 a b scratch target =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    apply testBit_actGates_of_outside
    intro g hg
    simp [conjunction] at hg
    subst g
    simp [RGate.wires]
    omega
  | case4 a b c scratch target =>
    have hnew : scratchClear [a, b, c] scratch I := by
      intro j hj
      simp at hj
    rw [conjunction_act _ _ _ _ hn hb ht hts hnew]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self, Nat.add_zero]
    split
    · exact RGate.testBit_xor_of_ne (by omega) I
    · rfl
  | case5 a b c d rest scratch target ih =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hn' : (scratch :: c :: d :: rest).Nodup := by
      rw [List.nodup_cons]
      exact ⟨fun hs => Nat.lt_irrefl scratch (hb scratch (by simp [hs])), hn.tail.tail⟩
    have hbelow : ∀ q ∈ scratch :: c :: d :: rest, q < scratch + 1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · have h := hb q (by simp [hq]); omega
    have htarget : target ∉ scratch :: c :: d :: rest := by
      intro hq
      rcases List.mem_cons.mp hq with hq | hq
      · omega
      · exact hts (by simp [hq])
    have hrec := fun i => ih i hn' hbelow (by omega) htarget
    have hq : scratch + ((a :: b :: c :: d :: rest).length - 3) =
        scratch + 1 + ((scratch :: c :: d :: rest).length - 3) := by simp; omega
    have hgate : ∀ g ∈ [RGate.ccx a b scratch],
        scratch + 1 + ((scratch :: c :: d :: rest).length - 3) ∉ g.wires := by
      intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      simp [RGate.wires]
      omega
    rw [hq]
    simp only [conjunction, actGates_append]
    rw [testBit_actGates_of_outside hgate, hrec, testBit_actGates_of_outside hgate]

private theorem zero_masks : Selector.masks 511 9 = [] := by decide

theorem zero_test_clear (I : Nat) :
    writeField (actGates (gates 511 9) I) 16 1 0 =
      actGates (Selector.gates 511 9) (writeField I 16 1 0) := by
  have h := conjunction_clear (List.range 9) 10 9 I (by decide)
    (by intro q hq; simp at hq; omega) (by decide) (by decide)
  simpa only [gates, Selector.gates, zero_masks, List.reverse_nil,
    List.nil_append, List.append_nil, Selector.scratchOffset, Selector.flagWire,
    List.length_range] using h

theorem zero_test_preserves (I : Nat) :
    (actGates (gates 511 9) I).testBit 16 = I.testBit 16 := by
  have h := conjunction_preserves (List.range 9) 10 9 I (by decide)
    (by intro q hq; simp at hq; omega) (by decide) (by decide)
  simpa only [gates, zero_masks, List.reverse_nil, List.nil_append, List.append_nil,
    Selector.scratchOffset, Selector.flagWire, List.length_range] using h

theorem zero_test_old_wellFormed :
    (Selector.gates 511 9).all (RGate.wellFormed 17) = true := by
  simp [Selector.gates, zero_masks, Selector.scratchOffset, Selector.flagWire,
    List.range_succ, Selector.conjunction, RGate.wellFormed]

end VQ.Euclid.BorrowedSelector
