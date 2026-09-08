import VQ.Reversible.Wiring
import VQ.Reversible.Bit

namespace VQ.Reversible

theorem gatherBits_write_bit {f : Nat → Nat} {w k : Nat}
    (hinj : ∀ a b, a < w → b < w → f a = f b → a = b)
    (hk : k < w) (I v : Nat) :
    gatherBits f w (writeField I (f k) 1 v) =
      writeField (gatherBits f w I) k 1 v := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < w
  · by_cases hbk : b = k
    · subst b
      rw [testBit_gatherBits, testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_inside (by omega) (by omega)]
      simp [hk]
    · have hfb : f b ≠ f k := fun h => hbk (hinj b k hb hk h)
      rw [testBit_gatherBits, testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega), testBit_gatherBits]
  · rw [testBit_writeField_outside (by omega), testBit_gatherBits,
      testBit_gatherBits]
    simp [hb]

theorem actGates_map_clear_bit {gs hs : List RGate} {f : Nat → Nat} {w k : Nat}
    (hinj : ∀ a b, a < w → b < w → f a = f b → a = b)
    (hgs : ∀ g ∈ gs, g.wellFormed w = true)
    (hhs : ∀ g ∈ hs, g.wellFormed w = true)
    (hk : k < w)
    (ha : ∀ i, writeField (actGates gs i) k 1 0 =
      actGates hs (writeField i k 1 0)) (I : Nat) :
    writeField (actGates (gs.map (RGate.map f)) I) (f k) 1 0 =
      actGates (hs.map (RGate.map f)) (writeField I (f k) 1 0) := by
  have h := ha (gatherBits f w I)
  rw [← gatherBits_actGates hinj hgs,
    ← gatherBits_write_bit hinj hk,
    ← gatherBits_write_bit hinj hk,
    ← gatherBits_actGates hinj hhs] at h
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : ∃ q, q < w ∧ f q = b
  · obtain ⟨q, hq, rfl⟩ := hb
    have h' := congrArg (fun i => i.testBit q) h
    simpa only [testBit_gatherBits, hq, decide_true, Bool.true_and] using h'
  · have hout : ∀ q, q < w → f q ≠ b := fun q hq he => hb ⟨q, hq, he⟩
    have hkb := hout k hk
    rw [testBit_writeField_outside (by omega),
      testBit_actGates_map_of_outside hgs hout,
      testBit_actGates_map_of_outside hhs hout,
      testBit_writeField_outside (by omega)]

theorem actGates_map_preserves_bit {gs : List RGate} {f : Nat → Nat} {w k : Nat}
    (hinj : ∀ a b, a < w → b < w → f a = f b → a = b)
    (hgs : ∀ g ∈ gs, g.wellFormed w = true)
    (hk : k < w)
    (ha : ∀ i, (actGates gs i).testBit k = i.testBit k) (I : Nat) :
    (actGates (gs.map (RGate.map f)) I).testBit (f k) = I.testBit (f k) := by
  have h := congrArg (fun i => i.testBit k) (gatherBits_actGates hinj hgs I)
  simpa only [testBit_gatherBits, hk, decide_true, Bool.true_and, ha] using h

theorem actGates_reverse_clear_bit {gs hs : List RGate} {w v k : Nat}
    (hgs : gs.all (RGate.wellFormed w) = true)
    (hhs : hs.all (RGate.wellFormed v) = true)
    (ha : ∀ i, writeField (actGates gs i) k 1 0 =
      actGates hs (writeField i k 1 0)) (I : Nat) :
    writeField (actGates gs.reverse I) k 1 0 =
      actGates hs.reverse (writeField I k 1 0) := by
  have hn := actGates_reverse (gs := gs.reverse) (by simpa using hgs) I
  simp only [List.reverse_reverse] at hn
  have h := ha (actGates gs.reverse I)
  rw [hn] at h
  have h' := congrArg (actGates hs.reverse) h
  rw [actGates_reverse hhs] at h'
  exact h'.symm

theorem actGates_reverse_preserves_bit {gs : List RGate} {w k : Nat}
    (hgs : gs.all (RGate.wellFormed w) = true)
    (ha : ∀ i, (actGates gs i).testBit k = i.testBit k) (I : Nat) :
    (actGates gs.reverse I).testBit k = I.testBit k := by
  have hn := actGates_reverse (gs := gs.reverse) (by simpa using hgs) I
  simp only [List.reverse_reverse] at hn
  have h := ha (actGates gs.reverse I)
  rw [hn] at h
  exact h.symm

theorem eq_write_of_clear_bit {f g : Nat → Nat} {k I : Nat}
    (hc : writeField (f I) k 1 0 = g (writeField I k 1 0))
    (hp : (f I).testBit k = I.testBit k) :
    f I = writeField (g (writeField I k 1 0)) k 1 (bitValue I k) := by
  rw [← hc, ← readField_one]
  have hr : readField (f I) k 1 = readField I k 1 := by
    simp only [readField_one, bitValue, hp]
  rw [← hr, writeField_writeField, writeField_read]

end VQ.Reversible
