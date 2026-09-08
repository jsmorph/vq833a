import VQ.Curve.Secp256k1SevenCarry

namespace VQ.Curve.Secp256k1SevenCarry

open Reversible PackedReversibleSecp256k1

def cleared (I : Nat) : Nat := writeField I (carryWire 7) 1 0

structure Workspace (I : Nat) : Prop where
  constant : readField I constantOffset chunkWidth = 0
  output : bitValue I probeOutputWire = 0
  scratch : I.testBit scratchWire = false
  zeroCarry : bitValue I zeroCarryWire = 0
  carries : ∀ chunk, chunk < 7 → bitValue I (carryWire chunk) = 0

theorem read_cleared {off len : Nat} (h : off + len ≤ carryWire 7) (I : Nat) :
    readField (cleared I) off len = readField I off len :=
  readField_writeField_of_disjoint (Or.inr h)

theorem bit_cleared {k : Nat} (h : k < carryWire 7) (I : Nat) :
    bitValue (cleared I) k = bitValue I k :=
  bitValue_write_ne (Nat.ne_of_lt h)

theorem Workspace.clear_carries {I : Nat} (h : Workspace I) :
    ∀ chunk, chunk < 8 → bitValue (cleared I) (carryWire chunk) = 0 := by
  intro chunk hc
  by_cases he : chunk = 7
  · subst chunk
    rw [cleared, bitValue_write_self]
  · rw [bit_cleared (by simp only [carryWire]; omega)]
    exact h.carries chunk (by omega)

theorem restore_cleared (I : Nat) :
    writeField (cleared I) (carryWire 7) 1 (bitValue I (carryWire 7)) = I := by
  rw [cleared, writeField_writeField]
  exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I (carryWire 7)))

theorem restore_written {off len : Nat} (h : off + len ≤ carryWire 7) (I value : Nat) :
    writeField (writeField (cleared I) off len value)
        (carryWire 7) 1 (bitValue I (carryWire 7)) =
      writeField I off len value := by
  rw [writeField_comm (Or.inl h), restore_cleared]

theorem detection_act {I x : Nat}
    (hx : readField I targetOffset wordWidth = x)
    (h : Workspace I) (hone : bitValue I oneWire = 0) :
    actGates detectionGates I =
      writeField I reductionWire 1
        ((bitValue I reductionWire + (gap + x) / 2 ^ wordWidth) % 2) := by
  have hs : (cleared I).testBit scratchWire = false := by
    rw [cleared, testBit_writeField_outside (Or.inl (by decide))]
    exact h.scratch
  have hold := PackedReversibleSecp256k1.detectionGates_act
    (i := cleared I) (x := x)
    ((read_cleared (by decide) I).trans hx)
    ((read_cleared (by decide) I).trans h.constant)
    ((bit_cleared (by decide) I).trans h.output)
    ((bit_cleared (by decide) I).trans hone) hs
    ((bit_cleared (by decide) I).trans h.zeroCarry) h.clear_carries
  have he := detection_equiv.act_eq I
  change actGates detectionGates I =
    writeField (actGates PackedReversibleSecp256k1.detectionGates (cleared I))
      (carryWire 7) 1 (bitValue I (carryWire 7)) at he
  rw [hold, bit_cleared (by decide), restore_written (by decide)] at he
  exact he

theorem correction_enabled {I x : Nat}
    (hx : readField I targetOffset wordWidth = x)
    (h : Workspace I) (hcontrol : bitValue I reductionWire = 1) :
    actGates correctionGates I = writeField I targetOffset wordWidth (gap + x) := by
  have hs : (cleared I).testBit scratchWire = false := by
    rw [cleared, testBit_writeField_outside (Or.inl (by decide))]
    exact h.scratch
  have hold := PackedReversibleSecp256k1.correctionGates_enabled
    (i := cleared I) (x := x)
    ((read_cleared (by decide) I).trans hx)
    ((read_cleared (by decide) I).trans h.constant)
    ((bit_cleared (by decide) I).trans h.output)
    ((bit_cleared (by decide) I).trans hcontrol) hs
    ((bit_cleared (by decide) I).trans h.zeroCarry) h.clear_carries
  have he := OmitTarget.act_eq correction_controlsAvoid I
  change actGates correctionGates I =
    writeField (actGates PackedReversibleSecp256k1.correctionGates (cleared I))
      (carryWire 7) 1 (bitValue I (carryWire 7)) at he
  rw [hold, restore_written (by decide)] at he
  exact he

theorem correction_disabled {I : Nat}
    (h : Workspace I) (hcontrol : bitValue I reductionWire = 0) :
    actGates correctionGates I = I := by
  have hs : (cleared I).testBit scratchWire = false := by
    rw [cleared, testBit_writeField_outside (Or.inl (by decide))]
    exact h.scratch
  have hold := PackedReversibleSecp256k1.correctionGates_disabled
    (i := cleared I)
    ((read_cleared (by decide) I).trans h.constant)
    ((bit_cleared (by decide) I).trans h.output)
    ((bit_cleared (by decide) I).trans hcontrol) hs
    ((bit_cleared (by decide) I).trans h.zeroCarry) h.clear_carries
  have he := OmitTarget.act_eq correction_controlsAvoid I
  change actGates correctionGates I =
    writeField (actGates PackedReversibleSecp256k1.correctionGates (cleared I))
      (carryWire 7) 1 (bitValue I (carryWire 7)) at he
  rw [hold, restore_cleared] at he
  exact he

end VQ.Curve.Secp256k1SevenCarry
