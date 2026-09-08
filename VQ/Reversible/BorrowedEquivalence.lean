import VQ.Reversible.BorrowedPlacement

namespace VQ.Reversible

structure BorrowedEquivalent (q : Nat) (old replacement : List RGate) : Prop where
  projected : ∀ I, writeField (actGates replacement I) q 1 0 =
    actGates old (writeField I q 1 0)
  preserved : ∀ I, (actGates replacement I).testBit q = I.testBit q

namespace BorrowedEquivalent

theorem nil (q : Nat) : BorrowedEquivalent q [] [] :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem append {q : Nat} {old₁ old₂ new₁ new₂ : List RGate}
    (h₁ : BorrowedEquivalent q old₁ new₁) (h₂ : BorrowedEquivalent q old₂ new₂) :
    BorrowedEquivalent q (old₁ ++ old₂) (new₁ ++ new₂) := by
  constructor <;> intro I <;> simp only [actGates_append]
  · rw [h₂.projected, h₁.projected]
  · rw [h₂.preserved, h₁.preserved]

theorem of_avoids {q : Nat} {gs : List RGate} (h : ∀ g ∈ gs, q ∉ g.wires) :
    BorrowedEquivalent q gs gs := by
  constructor
  · intro I
    symm
    apply actGates_write_of_outside
    intro g hg k hk
    have hne : k ≠ q := by intro he; subst k; exact h g hg hk
    omega
  · exact testBit_actGates_of_outside h

theorem of_below {q : Nat} {gs : List RGate}
    (h : ∀ g ∈ gs, ∀ k ∈ g.wires, k < q) : BorrowedEquivalent q gs gs :=
  of_avoids (fun g hg hk => Nat.lt_irrefl q (h g hg q hk))

theorem reverse {q w v : Nat} {old replacement : List RGate}
    (h : BorrowedEquivalent q old replacement)
    (hold : old.all (RGate.wellFormed w) = true)
    (hnew : replacement.all (RGate.wellFormed v) = true) :
    BorrowedEquivalent q old.reverse replacement.reverse :=
  ⟨actGates_reverse_clear_bit hnew hold h.projected,
    actGates_reverse_preserves_bit hnew h.preserved⟩

theorem map {q w : Nat} {old replacement : List RGate} {f : Nat → Nat}
    (h : BorrowedEquivalent q old replacement)
    (hinj : ∀ a b, a < w → b < w → f a = f b → a = b)
    (hold : ∀ g ∈ old, g.wellFormed w = true)
    (hnew : ∀ g ∈ replacement, g.wellFormed w = true) (hq : q < w) :
    BorrowedEquivalent (f q) (old.map (RGate.map f)) (replacement.map (RGate.map f)) :=
  ⟨actGates_map_clear_bit hinj hnew hold hq h.projected,
    actGates_map_preserves_bit hinj hnew hq h.preserved⟩

theorem act_eq {q : Nat} {old replacement : List RGate}
    (h : BorrowedEquivalent q old replacement) (I : Nat) :
    actGates replacement I =
      writeField (actGates old (writeField I q 1 0)) q 1 (bitValue I q) :=
  eq_write_of_clear_bit (h.projected I) (h.preserved I)

theorem eq_on_clear {q : Nat} {old replacement : List RGate} {I : Nat}
    (h : BorrowedEquivalent q old replacement) (hc : I.testBit q = false) :
    actGates replacement I = actGates old I := by
  have hi : bitValue I q = 0 := (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hc
  have ho : bitValue (actGates replacement I) q = 0 :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).1 ((h.preserved I).trans hc)
  have he := h.projected I
  rw [write_of_bitValue (by simpa only [Nat.zero_mod] using ho.symm),
    write_of_bitValue (by simpa only [Nat.zero_mod] using hi.symm)] at he
  exact he

end BorrowedEquivalent

end VQ.Reversible
