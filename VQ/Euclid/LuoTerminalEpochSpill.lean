/-
Terminal-epoch spill used by the Luo companion generator.
-/
import VQ.Reversible.Permutation

namespace VQ.Euclid.LuoTerminalEpochSpill

open Reversible

def storeGates (terminal epoch quotient : Nat) : List RGate :=
  [.cx terminal quotient] ++ fredkin terminal epoch quotient

def restoreGates (terminal epoch quotient : Nat) : List RGate :=
  (storeGates terminal epoch quotient).reverse

theorem storeGates_explicit (terminal epoch quotient : Nat) :
    storeGates terminal epoch quotient =
      [.cx terminal quotient, .cx quotient epoch,
        .ccx terminal epoch quotient, .cx quotient epoch] := by
  rfl

theorem restoreGates_explicit (terminal epoch quotient : Nat) :
    restoreGates terminal epoch quotient =
      [.cx quotient epoch, .ccx terminal epoch quotient,
        .cx quotient epoch, .cx terminal quotient] := by
  rfl

theorem storeGates_off
    {terminal epoch quotient i : Nat}
    (hte : terminal ≠ epoch) (_htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient)
    (hterminal : bitValue i terminal = 0) :
    actGates (storeGates terminal epoch quotient) i = i := by
  have hcx : RGate.act (.cx terminal quotient) i = i := by
    rw [act_cx_write, hterminal, Nat.add_zero]
    exact write_of_bitValue (by
      have hbit := bitValue_lt i quotient
      omega)
  rw [storeGates, actGates_append, actGates_cons, actGates_nil, hcx]
  exact fredkin_off heq hte hterminal

theorem storeGates_on
    {terminal epoch quotient i : Nat}
    (hte : terminal ≠ epoch) (htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient)
    (hterminal : bitValue i terminal = 1)
    (hquotient : bitValue i quotient = 1) :
    actGates (storeGates terminal epoch quotient) i =
      writeField (writeField i epoch 1 0) quotient 1 (bitValue i epoch) := by
  let toggled := writeField i quotient 1 0
  have hcx : RGate.act (.cx terminal quotient) i = toggled := by
    rw [act_cx_write, hquotient, hterminal]
  have hterminalToggled : bitValue toggled terminal = 1 := by
    simp only [toggled]
    rw [bitValue_write_ne htq]
    exact hterminal
  have hquotientToggled : bitValue toggled quotient = 0 := by
    simp [toggled, bitValue_write_self]
  have hepochToggled : bitValue toggled epoch = bitValue i epoch := by
    simp only [toggled]
    rw [bitValue_write_ne heq]
  rw [storeGates, actGates_append, actGates_cons, actGates_nil, hcx,
    fredkin_on heq hte htq hterminalToggled,
    hquotientToggled, hepochToggled]
  simp only [toggled]
  rw [writeField_comm
      (i := i) (o₁ := quotient) (n₁ := 1) (v := 0)
      (o₂ := epoch) (n₂ := 1) (u := 0) (by omega),
    writeField_writeField]

theorem storeGates_epoch_clear
    {terminal epoch quotient i : Nat}
    (hte : terminal ≠ epoch) (htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient)
    (hterminal : bitValue i terminal = 1)
    (hquotient : bitValue i quotient = 1) :
    bitValue (actGates (storeGates terminal epoch quotient) i) epoch = 0 := by
  rw [storeGates_on hte htq heq hterminal hquotient,
    bitValue_write_ne heq, bitValue_write_self]

theorem storeGates_quotient
    {terminal epoch quotient i : Nat}
    (hte : terminal ≠ epoch) (htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient)
    (hterminal : bitValue i terminal = 1)
    (hquotient : bitValue i quotient = 1) :
    bitValue (actGates (storeGates terminal epoch quotient) i) quotient =
      bitValue i epoch := by
  rw [storeGates_on hte htq heq hterminal hquotient,
    bitValue_write_self]
  exact Nat.mod_eq_of_lt (bitValue_lt i epoch)

theorem storeGates_wellFormed
    {terminal epoch quotient total : Nat}
    (ht : terminal < total) (he : epoch < total) (hq : quotient < total)
    (hte : terminal ≠ epoch) (htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient) :
    (storeGates terminal epoch quotient).all
      (RGate.wellFormed total) = true := by
  simp [storeGates, RGate.wellFormed, fredkin, ht, he, hq, hte, htq, heq,
    Ne.symm heq]

theorem restore_store
    {terminal epoch quotient total i : Nat}
    (ht : terminal < total) (he : epoch < total) (hq : quotient < total)
    (hte : terminal ≠ epoch) (htq : terminal ≠ quotient)
    (heq : epoch ≠ quotient) :
    actGates (restoreGates terminal epoch quotient)
        (actGates (storeGates terminal epoch quotient) i) = i := by
  exact actGates_reverse
    (storeGates_wellFormed ht he hq hte htq heq) i

theorem storeGates_length (terminal epoch quotient : Nat) :
    (storeGates terminal epoch quotient).length = 4 := by
  simp [storeGates, fredkin]

theorem storeGates_ccx (terminal epoch quotient : Nat) :
    (storeGates terminal epoch quotient).countP RGate.isCcx = 1 := by
  simp [storeGates, fredkin, List.countP_cons, RGate.isCcx]

theorem storeGates_cx (terminal epoch quotient : Nat) :
    (storeGates terminal epoch quotient).countP RGate.isCx = 3 := by
  simp [storeGates, fredkin, List.countP_cons, RGate.isCx]

end VQ.Euclid.LuoTerminalEpochSpill
