/-
Extended terminal padding in the 571-wire Euclidean layout.
-/
import VQ.Euclid.PackedPhaseFourRound
import VQ.Euclid.PackedOwnershipOperands
import VQ.Euclid.TerminalPadding

namespace VQ
namespace Euclid
namespace PackedTerminalEpoch

open Reversible

def localLayout : Layout := TerminalPadding.layout 259 9

def wiring : Wiring :=
  [PackedStepLayout.workTwoOffset, PackedStepLayout.shiftOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.poolOffset + 1,
    PackedStepLayout.poolOffset + 10, PackedStepLayout.extensionWire]

def paddingGates : List RGate :=
  PackedStepLayout.placed localLayout wiring (TerminalPadding.gates 259 9)

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, TerminalPadding.layout, wiring, Layout.size,
      PackedStepLayout.workTwoOffset, PackedStepLayout.shiftOffset,
      PackedStepLayout.poolOffset, PackedStepLayout.extensionWire]

theorem wiring_bound : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤ PackedStepLayout.width := by
  decide +kernel

theorem paddingGates_wellFormed :
    paddingGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  exact wellFormed_placeGates wiring_disjoint (by decide) wiring_bound
    (fun g hg => List.all_eq_true.mp
      (TerminalPadding.gates_wellFormed (by norm_num)) g hg)

def input (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

theorem input_field (j I : Nat) (hj : j < wiring.length) :
    localLayout.read (input I) j =
      readField I (wiring.getD j 0) (localLayout.size j) := by
  exact read_gatherBits localLayout wiring j I hj

theorem input_work (I : Nat) :
    readField (input I) TerminalPadding.workOffset 259 =
      readField I PackedStepLayout.workTwoOffset 259 := by
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.workOffset, Layout.read, Layout.offset, Layout.size] using
      input_field 0 I (by decide)

theorem input_low (I : Nat) :
    readField (input I) (TerminalPadding.lowOffset 259) 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.lowOffset, Layout.read, Layout.offset, Layout.size] using
      input_field 1 I (by decide)

theorem input_control (I : Nat) :
    bitValue (input I) (TerminalPadding.controlWire 259 9) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.controlWire, Layout.read, Layout.offset, Layout.size] using
      input_field 2 I (by decide)

theorem input_scratch (I : Nat) :
    readField (input I) (TerminalPadding.scratchOffset 259 9) 9 =
      readField I (PackedStepLayout.poolOffset + 1) 9 := by
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.scratchOffset, Layout.read, Layout.offset, Layout.size] using
      input_field 3 I (by decide)

theorem input_wrapped (I : Nat) :
    bitValue (input I) (TerminalPadding.wrappedWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 10) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.wrappedWire, Layout.read, Layout.offset, Layout.size] using
      input_field 4 I (by decide)

theorem input_epoch (I : Nat) :
    bitValue (input I) (TerminalPadding.epochWire 259 9) =
      bitValue I PackedStepLayout.extensionWire := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, TerminalPadding.layout,
    TerminalPadding.epochWire, Layout.read, Layout.offset, Layout.size] using
      input_field 5 I (by decide)

def nextLow (I : Nat) : Nat :=
  (readField I PackedStepLayout.shiftOffset 9 +
    bitValue I PackedStepLayout.poolOffset) % 2 ^ 9

def wrapped (I : Nat) : Nat := if nextLow I = 0 then 1 else 0

def nextEpoch (I : Nat) : Nat :=
  (bitValue I PackedStepLayout.extensionWire +
    bitValue I PackedStepLayout.poolOffset * wrapped I) % 2

def terminalNextLow (I : Nat) : Nat :=
  (readField I PackedStepLayout.shiftOffset 9 + 1) % 2 ^ 9

def terminalWrapped (I : Nat) : Nat :=
  if terminalNextLow I = 0 then 1 else 0

def terminalNextEpoch (I : Nat) : Nat :=
  (bitValue I PackedStepLayout.extensionWire + terminalWrapped I) % 2

def entryOut (I : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField I PackedStepLayout.workTwoOffset 259
          (rotateRightValue 259
            (readField I PackedStepLayout.workTwoOffset 259)))
        PackedStepLayout.shiftOffset 9 (terminalNextLow I))
      PackedStepLayout.extensionWire 1 0)
    PackedStepLayout.signWire 1 (terminalNextEpoch I)

def roundOut (I : Nat) : Nat :=
  writeField
    (writeField (entryOut I) PackedStepLayout.extensionWire 1
      (terminalNextEpoch I))
    PackedStepLayout.signWire 1 0

def terminalSelectorGates : List RGate :=
  Placed.selectorGates (encodedZero 8) 8
    PackedStepLayout.lengthRPrimeOffset PackedStepLayout.poolOffset
    (PackedStepLayout.poolOffset + 1)

def lowSelectorGates : List RGate :=
  Placed.selectorGates (encodedZero 9) 9
    PackedStepLayout.shiftOffset PackedStepLayout.poolOffset
    (PackedStepLayout.poolOffset + 1)

def epochSwapGates : List RGate :=
  fredkin PackedStepLayout.poolOffset PackedStepLayout.extensionWire
    PackedStepLayout.signWire

def entryGates : List RGate :=
  terminalSelectorGates ++ paddingGates ++ epochSwapGates ++
    [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] ++
    terminalSelectorGates.reverse ++
    PackedPhaseFourPrefix.preShiftBlock ++
    terminalSelectorGates ++
    [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] ++
    terminalSelectorGates.reverse

def prefixRemainderGates : List RGate :=
  PackedPhaseFourPrefix.remainderBlocks ++
    PackedPhaseFourPrefix.quotientIncrementBlock ++
    PackedPhaseFourPrefix.swapBlock ++
    PackedPhaseFourPrefix.quotientDecrementBlock

def phaseCorrectionCore : List RGate :=
  [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
      (PackedStepLayout.poolOffset + 10),
    .ccx (PackedStepLayout.poolOffset + 10) PackedStepLayout.poolOffset
      PackedStepLayout.phaseOneWire,
    .ccx (PackedStepLayout.poolOffset + 10) PackedStepLayout.poolOffset
      PackedStepLayout.phaseTwoWire,
    .ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
      (PackedStepLayout.poolOffset + 10)]

def phaseCorrectionGates : List RGate :=
  PackedPhaseFourPrefix.rPrimeSelectorGates ++ lowSelectorGates ++
    phaseCorrectionCore ++ lowSelectorGates.reverse ++
    PackedPhaseFourPrefix.rPrimeSelectorGates.reverse

def phaseGates : List RGate :=
  PackedStepLayout.phaseGates ++ phaseCorrectionGates

def ownershipMaskGates : List RGate :=
  [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
      (PackedStepLayout.poolOffset + 12)] ++
    fredkin (PackedStepLayout.poolOffset + 12)
      PackedOwnership.controlWire PackedStepLayout.phaseOneWire ++
    [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
      (PackedStepLayout.poolOffset + 12)]

def ownershipBodyGates : List RGate :=
  PackedOwnership.phaseClearGates ++ PackedSwapLength.gates ++
    PackedOwnership.phaseRestoreGates ++ PackedOwnership.iterationGates

def ownershipRestoreControlGates : List RGate :=
  Phase.negativeAndGates PackedStepLayout.signWire
    PackedStepLayout.phaseTwoWire PackedStepLayout.extensionWire

def ownershipRestoreGates : List RGate :=
  ownershipRestoreControlGates ++
    fredkin PackedStepLayout.extensionWire
      PackedOwnership.controlWire PackedStepLayout.phaseOneWire ++
    ownershipRestoreControlGates.reverse

def ownershipGates : List RGate :=
  PackedPhaseFourPrefix.rPrimeSelectorGates ++
    PackedOwnership.prepareGates ++ ownershipMaskGates ++
    PackedPhaseFourPrefix.rPrimeSelectorGates.reverse ++
    ownershipBodyGates ++ ownershipRestoreGates ++
    PackedOwnership.prepareGates

def exitGates : List RGate :=
  terminalSelectorGates ++ epochSwapGates ++ terminalSelectorGates.reverse

def gates : List RGate :=
  entryGates ++ prefixRemainderGates ++
    PackedStepLayout.coefficientGates ++ PackedShift.postShiftGates ++
    phaseGates ++ ownershipGates ++ exitGates

def roundsGates : Nat → List RGate
  | 0 => []
  | rounds + 1 => gates ++ roundsGates rounds

theorem roundsGates_add (left right : Nat) :
    roundsGates (left + right) = roundsGates left ++ roundsGates right := by
  induction left with
  | zero => simp only [Nat.zero_add, roundsGates, List.nil_append]
  | succ left ih =>
      simp only [Nat.succ_add, roundsGates, ih, List.append_assoc]

private theorem terminalSelector_disjoint :
    Wiring.Disjoint (Selector.layout 8)
      (Placed.selectorWiring PackedStepLayout.lengthRPrimeOffset
        PackedStepLayout.poolOffset (PackedStepLayout.poolOffset + 1)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Selector.layout, Placed.selectorWiring, Layout.size,
      PackedStepLayout.lengthRPrimeOffset, PackedStepLayout.poolOffset]

private theorem lowSelector_disjoint :
    Wiring.Disjoint (Selector.layout 9)
      (Placed.selectorWiring PackedStepLayout.shiftOffset
        PackedStepLayout.poolOffset (PackedStepLayout.poolOffset + 1)) := by
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Selector.layout, Placed.selectorWiring, Layout.size,
      PackedStepLayout.shiftOffset, PackedStepLayout.poolOffset]

theorem terminalSelectorGates_wellFormed :
    terminalSelectorGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  apply Placed.selector_wellFormed terminalSelector_disjoint
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;> decide +kernel

theorem lowSelectorGates_wellFormed :
    lowSelectorGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  apply Placed.selector_wellFormed lowSelector_disjoint
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;> decide +kernel

private theorem prefixParts_wellFormed :
    PackedPhaseFourPrefix.preShiftBlock.all
        (RGate.wellFormed PackedStepLayout.width) = true ∧
      prefixRemainderGates.all
        (RGate.wellFormed PackedStepLayout.width) = true := by
  have hprefix : PackedPhaseFourPrefix.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedPhaseFourPrefix.circuit, RCircuit.wellFormed] using
      PackedPhaseFourPrefix.circuit_wellFormed
  simp only [PackedPhaseFourPrefix.gates, prefixRemainderGates,
    List.all_append, Bool.and_eq_true] at hprefix ⊢
  exact ⟨hprefix.1.1.1.1,
    ⟨⟨⟨hprefix.1.1.1.2, hprefix.1.1.2⟩, hprefix.1.2⟩, hprefix.2⟩⟩

private theorem postShiftGates_wellFormed :
    PackedShift.postShiftGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simpa [PackedShift.postShiftCircuit, RCircuit.wellFormed] using
    PackedShift.postShiftCircuit_wellFormed

private theorem swapLengthGates_wellFormed :
    PackedSwapLength.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simpa [PackedSwapLength.circuit, RCircuit.wellFormed] using
    PackedSwapLength.circuit_wellFormed

private theorem smallGates_wellFormed :
    epochSwapGates.all (RGate.wellFormed PackedStepLayout.width) = true ∧
      phaseCorrectionCore.all
        (RGate.wellFormed PackedStepLayout.width) = true ∧
      ownershipMaskGates.all
        (RGate.wellFormed PackedStepLayout.width) = true ∧
      ownershipRestoreGates.all
        (RGate.wellFormed PackedStepLayout.width) = true := by
  decide +kernel

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  have hentryControl :
      (RGate.cx PackedStepLayout.poolOffset
        PackedStepLayout.phaseOneWire).wellFormed
          PackedStepLayout.width = true := by
    decide +kernel
  have hentry : entryGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [entryGates, terminalSelectorGates_wellFormed,
      paddingGates_wellFormed, smallGates_wellFormed.1,
      prefixParts_wellFormed.1, hentryControl, List.all_reverse]
  have hphaseCorrection : phaseCorrectionGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [phaseCorrectionGates,
      PackedPhaseFourPrefix.rPrimeSelector_wellFormed,
      lowSelectorGates_wellFormed, smallGates_wellFormed.2.1,
      List.all_reverse]
  have hphase : phaseGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [phaseGates, PackedStepLayout.phase_wellFormed, hphaseCorrection]
  have hownershipBody : ownershipBodyGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [ownershipBodyGates, PackedOwnership.phaseClearGates_wellFormed,
      swapLengthGates_wellFormed,
      PackedOwnership.phaseRestoreGates_wellFormed,
      PackedOwnership.iterationGates_wellFormed]
  have hownership : ownershipGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [ownershipGates,
      PackedPhaseFourPrefix.rPrimeSelector_wellFormed,
      PackedOwnership.prepareGates_wellFormed,
      smallGates_wellFormed.2.2.1, hownershipBody,
      smallGates_wellFormed.2.2.2, List.all_reverse]
  have hexit : exitGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simp [exitGates, terminalSelectorGates_wellFormed,
      smallGates_wellFormed.1, List.all_reverse]
  simp [gates, hentry, prefixParts_wellFormed.2,
    PackedStepLayout.coefficient_wellFormed, postShiftGates_wellFormed,
    hphase, hownership, hexit]

theorem roundsGates_wellFormed (rounds : Nat) :
    (roundsGates rounds).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp [roundsGates, gates_wellFormed, ih]

theorem roundsGates_avoids_from (rounds offset : Nat)
    (hoffset : PackedStepLayout.width ≤ offset) :
    ∀ g ∈ roundsGates rounds, ∀ q ∈ g.wires, offset ≤ q → False := by
  intro g hg q hq hqOffset
  have hgwf := List.all_eq_true.mp (roundsGates_wellFormed rounds) g hg
  have hqWidth := wire_lt_of_wellFormed hgwf hq
  omega

theorem terminalSelectorGates_on
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates terminalSelectorGates I =
      writeField I PackedStepLayout.poolOffset 1 1 := by
  rw [terminalSelectorGates,
    Placed.selector_act terminalSelector_disjoint hscratch]
  norm_num [hsource, hflag, encodedZero]

theorem terminalSelectorGates_off
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates terminalSelectorGates I = I := by
  rw [terminalSelectorGates,
    Placed.selector_act terminalSelector_disjoint hscratch,
    Nat.mod_eq_of_lt (encodedZero_lt 8), if_neg hsource, hflag]
  norm_num
  exact write_of_bitValue (by simpa using hflag.symm)

theorem terminalSelectorGates_reverse_on
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hflag : bitValue I PackedStepLayout.poolOffset = 1)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates terminalSelectorGates.reverse I =
      writeField I PackedStepLayout.poolOffset 1 0 := by
  let J := writeField I PackedStepLayout.poolOffset 1 0
  have hJsource : readField J PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hsource]
  have hJflag : bitValue J PackedStepLayout.poolOffset = 0 := by
    simp [J, bitValue_write_self]
  have hJscratch :
      readField J (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hscratch]
  have hforward := terminalSelectorGates_on hJsource hJflag hJscratch
  have hcancel := actGates_reverse terminalSelectorGates_wellFormed J
  have hwrite : writeField J PackedStepLayout.poolOffset 1 1 = I := by
    simp only [J, writeField_writeField]
    exact write_of_bitValue (by simpa using hflag.symm)
  rw [hforward, hwrite] at hcancel
  exact hcancel

theorem terminalSelectorGates_reverse_off
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates terminalSelectorGates.reverse I = I := by
  have hforward := terminalSelectorGates_off hsource hflag hscratch
  have hcancel := actGates_reverse terminalSelectorGates_wellFormed I
  rw [hforward] at hcancel
  exact hcancel

theorem lowSelectorGates_on
    {I : Nat}
    (hsource : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates lowSelectorGates I =
      writeField I PackedStepLayout.poolOffset 1 1 := by
  rw [lowSelectorGates, Placed.selector_act lowSelector_disjoint hscratch]
  norm_num [hsource, hflag, encodedZero]

theorem lowSelectorGates_off
    {I : Nat}
    (hsource : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates lowSelectorGates I = I := by
  rw [lowSelectorGates, Placed.selector_act lowSelector_disjoint hscratch,
    Nat.mod_eq_of_lt (encodedZero_lt 9), if_neg hsource, hflag]
  norm_num
  exact write_of_bitValue (by simpa using hflag.symm)

theorem lowSelectorGates_reverse_on
    {I : Nat}
    (hsource : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hflag : bitValue I PackedStepLayout.poolOffset = 1)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates lowSelectorGates.reverse I =
      writeField I PackedStepLayout.poolOffset 1 0 := by
  let J := writeField I PackedStepLayout.poolOffset 1 0
  have hJsource : readField J PackedStepLayout.shiftOffset 9 =
      encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hsource]
  have hJflag : bitValue J PackedStepLayout.poolOffset = 0 := by
    simp [J, bitValue_write_self]
  have hJscratch :
      readField J (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hscratch]
  have hforward := lowSelectorGates_on hJsource hJflag hJscratch
  have hcancel := actGates_reverse lowSelectorGates_wellFormed J
  have hwrite : writeField J PackedStepLayout.poolOffset 1 1 = I := by
    simp only [J, writeField_writeField]
    exact write_of_bitValue (by simpa using hflag.symm)
  rw [hforward, hwrite] at hcancel
  exact hcancel

theorem lowSelectorGates_reverse_off
    {I : Nat}
    (hsource : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hflag : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates lowSelectorGates.reverse I = I := by
  have hforward := lowSelectorGates_off hsource hflag hscratch
  have hcancel := actGates_reverse lowSelectorGates_wellFormed I
  rw [hforward] at hcancel
  exact hcancel

theorem rPrimeSelectorGates_reverse_on
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse I =
      writeField I PackedStepLayout.extensionWire 1 0 := by
  let J := writeField I PackedStepLayout.extensionWire 1 0
  have hJsource : readField J PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hsource]
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp [J, bitValue_write_self]
  have hJscratch :
      readField J (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hscratch]
  have hforward := PackedPhaseFourPrefix.rPrimeSelector_on_zero
    hJsource hJextension hJscratch
  have hcancel := actGates_reverse
    PackedPhaseFourPrefix.rPrimeSelector_wellFormed J
  have hwrite : writeField J PackedStepLayout.extensionWire 1 1 = I := by
    simp only [J, writeField_writeField]
    exact write_of_bitValue (by simpa using hextension.symm)
  rw [hforward, hwrite] at hcancel
  exact hcancel

theorem rPrimeSelectorGates_reverse_off
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 8 = 0) :
    actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse I = I := by
  have hforward := PackedPhaseFourPrefix.rPrimeSelector_identity
    hsource hextension hscratch
  have hcancel := actGates_reverse
    PackedPhaseFourPrefix.rPrimeSelector_wellFormed I
  rw [hforward] at hcancel
  exact hcancel

theorem paddingGates_identity_control_off
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    actGates paddingGates I = I := by
  let J := input I
  have hlocalControl :
      bitValue J (TerminalPadding.controlWire 259 9) = 0 := by
    simpa [J] using (input_control I).trans hcontrol
  have hlocalScratch :
      readField J (TerminalPadding.scratchOffset 259 9) 9 = 0 := by
    simpa [J] using (input_scratch I).trans hscratch
  have hlocalWrapped :
      bitValue J (TerminalPadding.wrappedWire 259 9) = 0 := by
    simpa [J] using (input_wrapped I).trans hwrapped
  have hlocal := TerminalPadding.gates_identity_control_off
    (workWidth := 259) (shiftWidth := 9) (i := J)
    (by norm_num) hlocalControl hlocalScratch hlocalWrapped
  have hlocal' :
      actGates (TerminalPadding.gates 259 9) (input I) =
        actGates [] (input I) := by
    simpa only [J, actGates_nil] using hlocal
  have hplaced := actGates_placed_congr
    (gs := TerminalPadding.gates 259 9) (hs := [])
    wiring_disjoint (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      (TerminalPadding.circuit_wellFormed (by norm_num)) hg)
    (by intro g hg; simp at hg) I
    (by simpa [input] using hlocal')
  simpa [paddingGates, PackedStepLayout.placed, localLayout, wiring,
    actGates_nil]
    using hplaced

theorem paddingGates_act
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    actGates paddingGates I =
      writeField
        (writeField
          (writeField
            (writeField I PackedStepLayout.workTwoOffset 259
              (rotateRightValue 259
                (readField I PackedStepLayout.workTwoOffset 259)))
            PackedStepLayout.shiftOffset 9 (nextLow I))
          (PackedStepLayout.poolOffset + 10) 1 0)
        PackedStepLayout.extensionWire 1 (nextEpoch I) := by
  let J := input I
  have hlocalControl :
      bitValue J (TerminalPadding.controlWire 259 9) = 1 := by
    simpa [J] using (input_control I).trans hcontrol
  have hlocalScratch :
      readField J (TerminalPadding.scratchOffset 259 9) 9 = 0 := by
    simpa [J] using (input_scratch I).trans hscratch
  have hlocalWrapped :
      bitValue J (TerminalPadding.wrappedWire 259 9) = 0 := by
    simpa [J] using (input_wrapped I).trans hwrapped
  have hlocal := TerminalPadding.gates_act
    (workWidth := 259) (shiftWidth := 9) (i := J)
    (by norm_num) hlocalControl hlocalScratch hlocalWrapped
  have hnextLow : TerminalPadding.nextLow 259 9 J = nextLow I := by
    unfold TerminalPadding.nextLow nextLow
    rw [show readField J (TerminalPadding.lowOffset 259) 9 =
          readField I PackedStepLayout.shiftOffset 9 by
        simpa [J] using input_low I,
      show bitValue J (TerminalPadding.controlWire 259 9) =
          bitValue I PackedStepLayout.poolOffset by
        simpa [J] using input_control I]
  have hwrappedValue : TerminalPadding.wrapped 259 9 J = wrapped I := by
    simp [TerminalPadding.wrapped, wrapped, hnextLow]
  have hnextEpoch : TerminalPadding.nextEpoch 259 9 J = nextEpoch I := by
    unfold TerminalPadding.nextEpoch nextEpoch
    rw [show bitValue J (TerminalPadding.epochWire 259 9) =
          bitValue I PackedStepLayout.extensionWire by
        simpa [J] using input_epoch I,
      show bitValue J (TerminalPadding.controlWire 259 9) =
          bitValue I PackedStepLayout.poolOffset by
        simpa [J] using input_control I,
      hwrappedValue]
  have hworkJ :
      readField J TerminalPadding.workOffset 259 =
        readField I PackedStepLayout.workTwoOffset 259 := by
    simpa [J] using input_work I
  have hworkJ' :
      readField J 0 259 =
        readField I PackedStepLayout.workTwoOffset 259 := by
    simpa [TerminalPadding.workOffset] using hworkJ
  have hwrite :
      actGates (TerminalPadding.gates 259 9) J =
        localLayout.write
          (localLayout.write
            (localLayout.write
              (localLayout.write J 0
                (rotateRightValue 259
                  (readField I PackedStepLayout.workTwoOffset 259)))
              1 (nextLow I))
            4 0)
          5 (nextEpoch I) := by
    rw [hlocal]
    simp [TerminalPadding.out, localLayout, TerminalPadding.layout,
      Layout.write, Layout.offset, Layout.size, TerminalPadding.workOffset,
      TerminalPadding.lowOffset, TerminalPadding.wrappedWire,
      TerminalPadding.epochWire, hworkJ', hnextLow, hnextEpoch, Nat.add_comm]
  have hplaced := actGates_placed_write₄
    (gs := TerminalPadding.gates 259 9) (L := localLayout) (W := wiring)
    (k₁ := 0) (k₂ := 1) (k₃ := 4) (k₄ := 5)
    (v₁ := rotateRightValue 259
      (readField I PackedStepLayout.workTwoOffset 259))
    (v₂ := nextLow I) (v₃ := 0) (v₄ := nextEpoch I)
    wiring_disjoint (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      (TerminalPadding.circuit_wellFormed (by norm_num)) hg)
    (by simpa [J, input] using hwrite)
  simpa [paddingGates, PackedStepLayout.placed, localLayout, wiring,
    TerminalPadding.layout, Layout.size] using hplaced

theorem entryGates_act_terminal
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates entryGates I = entryOut I := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let S := writeField I PackedStepLayout.poolOffset 1 1
  have hselect : actGates terminalSelectorGates I = S := by
    simpa [S] using terminalSelectorGates_on hsource hflag hscratch8
  have hScontrol : bitValue S PackedStepLayout.poolOffset = 1 := by
    simp [S, bitValue_write_self]
  have hSscratch :
      readField S (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hSwrapped :
      bitValue S (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hSlow :
      readField S PackedStepLayout.shiftOffset 9 =
        readField I PackedStepLayout.shiftOffset 9 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide)]
  have hSwork :
      readField S PackedStepLayout.workTwoOffset 259 =
        readField I PackedStepLayout.workTwoOffset 259 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide)]
  have hSepoch : bitValue S PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire := by
    simp only [S]
    rw [bitValue_write_ne (by decide)]
  have hnextLow : nextLow S = terminalNextLow I := by
    simp [nextLow, terminalNextLow, hSlow, hScontrol]
  have hwrappedValue : wrapped S = terminalWrapped I := by
    simp [wrapped, terminalWrapped, hnextLow]
  have hnextEpoch : nextEpoch S = terminalNextEpoch I := by
    simp [nextEpoch, terminalNextEpoch, hSepoch, hScontrol, hwrappedValue]
  let P :=
    writeField
      (writeField
        (writeField
          (writeField S PackedStepLayout.workTwoOffset 259
            (rotateRightValue 259
              (readField S PackedStepLayout.workTwoOffset 259)))
          PackedStepLayout.shiftOffset 9 (terminalNextLow I))
        (PackedStepLayout.poolOffset + 10) 1 0)
      PackedStepLayout.extensionWire 1 (terminalNextEpoch I)
  have hpadding : actGates paddingGates S = P := by
    rw [paddingGates_act hScontrol hSscratch hSwrapped]
    simp [P, hnextLow, hnextEpoch]
  have hPcontrol : bitValue P PackedStepLayout.poolOffset = 1 := by
    simp only [P]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide)]
    exact hScontrol
  have hPextension : bitValue P PackedStepLayout.extensionWire =
      terminalNextEpoch I := by
    simp only [P]
    rw [bitValue_write_self]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  have hPsign : bitValue P PackedStepLayout.signWire = 0 := by
    simp only [P]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide)]
    simp only [S]
    rw [bitValue_write_ne (by decide), hsign]
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide), hsource]
  have hPscratch8 :
      readField P (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [S]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hscratch8
  have hSpool : readField S PackedStepLayout.poolOffset 13 = 1 := by
    simp only [S]
    have hsub :
        writeField I PackedStepLayout.poolOffset 1 1 =
          writeField I PackedStepLayout.poolOffset 13
            (writeField (readField I PackedStepLayout.poolOffset 13) 0 1 1) := by
      simpa using writeField_subfield
        (i := I) (outerOffset := PackedStepLayout.poolOffset)
        (outerWidth := 13) (innerOffset := 0) (innerWidth := 1)
        (value := 1) (by decide)
    rw [hsub, readField_writeField, hpool]
    norm_num [writeField]
  have hPpool : readField P PackedStepLayout.poolOffset 13 = 1 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (by decide)]
    rw [writeField_subfield
        (outerOffset := PackedStepLayout.poolOffset)
        (outerWidth := 13) (innerOffset := 10) (innerWidth := 1)
        (value := 0) (by decide),
      readField_writeField,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hSpool]
    decide +kernel
  let E := writeField
    (writeField P PackedStepLayout.extensionWire 1 0)
    PackedStepLayout.signWire 1 (terminalNextEpoch I)
  have hswap : actGates epochSwapGates P = E := by
    rw [epochSwapGates,
      fredkin_on (by decide) (by decide) (by decide) hPcontrol,
      hPextension, hPsign]
  let C := writeField E PackedStepLayout.phaseOneWire 1 1
  have hcx : actGates
      [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] E = C := by
    rw [actGates_cons, actGates_nil, act_cx_write]
    have hEcontrol : bitValue E PackedStepLayout.poolOffset = 1 := by
      simp only [E]
      rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
        hPcontrol]
    have hEphaseOne : bitValue E PackedStepLayout.phaseOneWire = 0 := by
      simp only [E]
      rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide)]
      simp only [P]
      rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
        bitValue_write_out (by decide), bitValue_write_out (by decide)]
      simp only [S]
      rw [bitValue_write_ne (by decide), hphaseOne]
    simp [C, hEcontrol, hEphaseOne]
  have hCsource : readField C PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [C, E]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hPsource]
  have hCcontrol : bitValue C PackedStepLayout.poolOffset = 1 := by
    simp only [C, E]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide)]
    exact hPcontrol
  have hCscratch :
      readField C (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [C, E]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hPscratch8]
  have hCpool : readField C PackedStepLayout.poolOffset 13 = 1 := by
    simp only [C, E]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hPpool]
  let D := writeField C PackedStepLayout.poolOffset 1 0
  have hunselect : actGates terminalSelectorGates.reverse C = D := by
    simpa [D] using
      terminalSelectorGates_reverse_on hCsource hCcontrol hCscratch
  have hDphaseOne : bitValue D PackedStepLayout.phaseOneWire = 1 := by
    simp only [D]
    rw [bitValue_write_ne (by decide)]
    simp [C, bitValue_write_self]
  have hDpool : readField D PackedStepLayout.poolOffset 13 = 0 := by
    simp only [D]
    have hsub :
        writeField C PackedStepLayout.poolOffset 1 0 =
          writeField C PackedStepLayout.poolOffset 13
            (writeField (readField C PackedStepLayout.poolOffset 13) 0 1 0) := by
      simpa using writeField_subfield
        (i := C) (outerOffset := PackedStepLayout.poolOffset)
        (outerWidth := 13) (innerOffset := 0) (innerWidth := 1)
        (value := 0) (by decide)
    rw [hsub, readField_writeField, hCpool]
    decide +kernel
  have hIpool10 : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hclearPool0 : writeField I PackedStepLayout.poolOffset 1 0 = I := by
    exact write_of_bitValue (by simpa using hflag.symm)
  have hclearPool10 :
      writeField I (PackedStepLayout.poolOffset + 10) 1 0 = I := by
    exact write_of_bitValue (by simpa using hIpool10.symm)
  have hDform :
      D = writeField (entryOut I) PackedStepLayout.phaseOneWire 1 1 := by
    simp only [D, C, E, P, S, entryOut]
    rw [writeField_comm
        (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.signWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.poolOffset + 10) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.shiftOffset) (n₁ := 9)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.workTwoOffset) (n₁ := 259)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_writeField, writeField_writeField, hclearPool0]
    rw [writeField_comm
        (o₁ := PackedStepLayout.shiftOffset) (n₁ := 9)
        (o₂ := PackedStepLayout.poolOffset + 10) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.workTwoOffset) (n₁ := 259)
        (o₂ := PackedStepLayout.poolOffset + 10) (n₂ := 1) (by decide),
      hclearPool10, hSwork]
  have hpreshift :
      actGates PackedPhaseFourPrefix.preShiftBlock D = D :=
    PackedPhaseFourPrefix.preShiftBlock_identity hDphaseOne hDpool
  have hDsource : readField D PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [D]
    rw [readField_writeField_of_disjoint (by decide), hCsource]
  have hDcontrol : bitValue D PackedStepLayout.poolOffset = 0 := by
    simp [D, bitValue_write_self]
  have hDscratch :
      readField D (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    exact readField_sub_zero (by omega) (by omega) hDpool
  let F := writeField D PackedStepLayout.poolOffset 1 1
  have hselectAgain : actGates terminalSelectorGates D = F := by
    simpa [F] using
      terminalSelectorGates_on hDsource hDcontrol hDscratch
  let G := writeField F PackedStepLayout.phaseOneWire 1 0
  have hcxAgain : actGates
      [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] F = G := by
    rw [actGates_cons, actGates_nil, act_cx_write]
    have hFcontrol : bitValue F PackedStepLayout.poolOffset = 1 := by
      simp [F, bitValue_write_self]
    have hFphaseOne : bitValue F PackedStepLayout.phaseOneWire = 1 := by
      simp only [F]
      rw [bitValue_write_ne (by decide), hDphaseOne]
    simp [G, hFcontrol, hFphaseOne]
  have hGsource : readField G PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [G, F]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hDsource]
  have hGcontrol : bitValue G PackedStepLayout.poolOffset = 1 := by
    simp only [G, F]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hGscratch :
      readField G (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [G, F]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hDscratch]
  have hfinal : actGates terminalSelectorGates.reverse G = entryOut I := by
    rw [terminalSelectorGates_reverse_on hGsource hGcontrol hGscratch]
    simp only [G, F, hDform]
    rw [writeField_overwrite_alternating_of_disjoint (by decide)]
    have hOutPhase : bitValue (entryOut I) PackedStepLayout.phaseOneWire = 0 := by
      simp only [entryOut]
      rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
        bitValue_write_out (by decide), bitValue_write_out (by decide),
        hphaseOne]
    have hOutPool : bitValue (entryOut I) PackedStepLayout.poolOffset = 0 := by
      simp only [entryOut]
      rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
        bitValue_write_out (by decide), bitValue_write_out (by decide), hflag]
    rw [show writeField (entryOut I) PackedStepLayout.phaseOneWire 1 0 =
        entryOut I by exact write_of_bitValue (by simpa using hOutPhase.symm)]
    exact write_of_bitValue (by simpa using hOutPool.symm)
  simp only [entryGates, actGates_append]
  rw [hselect, hpadding, hswap, hcx, hunselect, hpreshift,
    hselectAgain, hcxAgain, hfinal]

theorem entryGates_act_live
    {I : Nat}
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (hsourceAfter :
      readField
          (actGates PackedPhaseFourPrefix.preShiftBlock I)
          PackedStepLayout.lengthRPrimeOffset 8 ≠ encodedZero 8)
    (hpoolAfter :
      readField
          (actGates PackedPhaseFourPrefix.preShiftBlock I)
          PackedStepLayout.poolOffset 13 = 0) :
    actGates entryGates I =
      actGates PackedPhaseFourPrefix.preShiftBlock I := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch9 :
      readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hselect : actGates terminalSelectorGates I = I :=
    terminalSelectorGates_off hsource hflag hscratch8
  have hpadding : actGates paddingGates I = I :=
    paddingGates_identity_control_off hflag hscratch9 hwrapped
  have hswap : actGates epochSwapGates I = I := by
    rw [epochSwapGates, fredkin_off (by decide) (by decide) hflag]
  have hcx : actGates
      [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] I = I := by
    rw [actGates_cons, actGates_nil, act_cx_write, hflag, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.phaseOneWire),
      ← readField_one, writeField_read]
  have hunselect : actGates terminalSelectorGates.reverse I = I :=
    terminalSelectorGates_reverse_off hsource hflag hscratch8
  let P := actGates PackedPhaseFourPrefix.preShiftBlock I
  have hPflag : bitValue P PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpoolAfter
  have hPscratch8 :
      readField P (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpoolAfter
  have hselectAgain : actGates terminalSelectorGates P = P :=
    terminalSelectorGates_off hsourceAfter hPflag hPscratch8
  have hcxAgain : actGates
      [.cx PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire] P = P := by
    rw [actGates_cons, actGates_nil, act_cx_write, hPflag, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt P PackedStepLayout.phaseOneWire),
      ← readField_one, writeField_read]
  have hunselectAgain : actGates terminalSelectorGates.reverse P = P :=
    terminalSelectorGates_reverse_off hsourceAfter hPflag hPscratch8
  simp only [entryGates, actGates_append]
  rw [hselect, hpadding, hswap, hcx, hunselect, show
      actGates PackedPhaseFourPrefix.preShiftBlock I = P by rfl,
    hselectAgain, hcxAgain, hunselectAgain]

theorem basePhaseGates_act_terminal
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8) :
    actGates PackedStepLayout.phaseGates I =
      writeField
        (writeField
          (writeField I PackedStepLayout.phaseOneWire 1
            (if readField I PackedStepLayout.shiftOffset 9 = encodedZero 9
              then 1 else 0))
          PackedStepLayout.phaseTwoWire 1
            (if readField I PackedStepLayout.shiftOffset 9 = encodedZero 9
              then 1 else 0))
        PackedStepLayout.signWire 1
          (bitValue I PackedStepLayout.signWire) := by
  rw [PackedPhase.gates_act hextension htail]
  have hzeroQ : CompactPhase.zeroQValue (PackedPhase.input I) = 1 := by
    simp [CompactPhase.zeroQValue, PackedPhase.input_lengthQ, hlengthQ]
  have hzeroRPrime :
      CompactPhase.zeroRPrimeValue (PackedPhase.input I) = 1 := by
    simp [CompactPhase.zeroRPrimeValue, PackedPhase.input_lengthRPrime,
      hlengthRPrime]
  have hcondition :
      CompactPhase.conditionValue (PackedPhase.input I) = 0 := by
    simp [CompactPhase.conditionValue, hzeroRPrime]
  have hphaseOneValue : PackedPhase.phaseOneValue I =
      if readField I PackedStepLayout.shiftOffset 9 = encodedZero 9
        then 1 else 0 := by
    by_cases hzero :
        readField I PackedStepLayout.shiftOffset 9 = encodedZero 9 <;>
      simp [PackedPhase.phaseOneValue, CompactPhase.phase1Value,
        CompactPhase.zeroShiftValue, PackedPhase.input_phaseOne,
        PackedPhase.input_shift, hphaseOne, hzero]
  have hphaseTwoValue : PackedPhase.phaseTwoValue I =
      if readField I PackedStepLayout.shiftOffset 9 = encodedZero 9
        then 1 else 0 := by
    by_cases hzero :
        readField I PackedStepLayout.shiftOffset 9 = encodedZero 9 <;>
      simp [PackedPhase.phaseTwoValue, CompactPhase.phase2Value,
        CompactPhase.middlePhase2Value, CompactPhase.zeroShiftValue,
        PackedPhase.input_phaseTwo, PackedPhase.input_shift, hphaseTwo,
        hcondition, hzero]
  have hsignValue : PackedPhase.signValue I =
      bitValue I PackedStepLayout.signWire := by
    simp [PackedPhase.signValue, CompactPhase.signValue,
      CompactPhase.middlePhase2Value, PackedPhase.input_sign, hcondition,
      Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.signWire)]
  simp [PackedPhase.output, hphaseOneValue, hphaseTwoValue, hsignValue]

theorem phaseCorrectionCore_identity_low_off
    {I : Nat}
    (hflag : bitValue I PackedStepLayout.poolOffset = 0) :
    actGates phaseCorrectionCore I = I := by
  let A : RGate := .ccx PackedStepLayout.extensionWire
    PackedStepLayout.signWire (PackedStepLayout.poolOffset + 10)
  let B : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire
  let C : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseTwoWire
  let J := A.act I
  have hJflag : bitValue J PackedStepLayout.poolOffset = 0 := by
    simp only [J, A, act_ccx_write]
    rw [bitValue_write_ne (by decide), hflag]
  have hB : B.act J = J := by
    simp only [B, act_ccx_write]
    apply write_of_bitValue
    simp [hJflag, Nat.mod_eq_of_lt
      (bitValue_lt J PackedStepLayout.phaseOneWire)]
  have hC : C.act J = J := by
    simp only [C, act_ccx_write]
    apply write_of_bitValue
    simp [hJflag, Nat.mod_eq_of_lt
      (bitValue_lt J PackedStepLayout.phaseTwoWire)]
  have hA : A.act J = I := by
    exact A.act_act (w := PackedStepLayout.width) (by decide +kernel) I
  simp only [phaseCorrectionCore, actGates_cons, actGates_nil]
  change A.act (C.act (B.act (A.act I))) = I
  rw [show A.act I = J by rfl, hB, hC, hA]

theorem phaseCorrectionCore_identity_extension_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    actGates phaseCorrectionCore I = I := by
  let A : RGate := .ccx PackedStepLayout.extensionWire
    PackedStepLayout.signWire (PackedStepLayout.poolOffset + 10)
  let B : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire
  let C : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseTwoWire
  have hA : A.act I = I := by
    simp only [A, act_ccx_write, hextension]
    simp only [zero_mul, Nat.add_zero]
    rw [← readField_one,
      Nat.mod_eq_of_lt
        (readField_lt I (PackedStepLayout.poolOffset + 10) 1),
      writeField_read]
  have hB : B.act I = I := by
    simp only [B, act_ccx_write, hwrapped]
    simp only [zero_mul, Nat.add_zero]
    rw [← readField_one,
      Nat.mod_eq_of_lt
        (readField_lt I PackedStepLayout.phaseOneWire 1),
      writeField_read]
  have hC : C.act I = I := by
    simp only [C, act_ccx_write, hwrapped]
    simp only [zero_mul, Nat.add_zero]
    rw [← readField_one,
      Nat.mod_eq_of_lt
        (readField_lt I PackedStepLayout.phaseTwoWire 1),
      writeField_read]
  simp only [phaseCorrectionCore, actGates_cons, actGates_nil]
  change A.act (C.act (B.act (A.act I))) = I
  rw [hA, hB, hC]
  exact hA

theorem phaseCorrectionGates_identity_live
    {I : Nat}
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates phaseCorrectionGates I = I := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = I :=
    PackedPhaseFourPrefix.rPrimeSelector_identity
      hlengthRPrime hextension hscratch8
  let L := actGates lowSelectorGates I
  have hlowAvoidsExtension :
      ∀ g ∈ lowSelectorGates, ∀ q ∈ g.wires,
        q < PackedStepLayout.extensionWire ∨
          PackedStepLayout.extensionWire + 1 ≤ q := by
    decide +kernel
  have hlowAvoidsWrapped :
      ∀ g ∈ lowSelectorGates, ∀ q ∈ g.wires,
        q < PackedStepLayout.poolOffset + 10 ∨
          PackedStepLayout.poolOffset + 10 + 1 ≤ q := by
    decide +kernel
  have hLextension : bitValue L PackedStepLayout.extensionWire = 0 := by
    rw [← readField_one,
      readField_actGates_of_outside hlowAvoidsExtension I,
      readField_one, hextension]
  have hLwrapped : bitValue L (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one,
      readField_actGates_of_outside hlowAvoidsWrapped I,
      readField_one, hwrapped]
  have hcore : actGates phaseCorrectionCore L = L :=
    phaseCorrectionCore_identity_extension_off hLextension hLwrapped
  have hlowCancel : actGates lowSelectorGates.reverse L = I := by
    simpa only [L] using actGates_reverse lowSelectorGates_wellFormed I
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse I = I :=
    rPrimeSelectorGates_reverse_off hlengthRPrime hextension hscratch8
  simp only [phaseCorrectionGates, actGates_append]
  rw [hrPrimeSelect, show actGates lowSelectorGates I = L by rfl,
    hcore, hlowCancel, hrPrimeReverse]

theorem phaseCorrectionCore_act_low_on
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hflag : bitValue I PackedStepLayout.poolOffset = 1)
    (hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates phaseCorrectionCore I =
      writeField
        (writeField I PackedStepLayout.phaseOneWire 1 0)
        PackedStepLayout.phaseTwoWire 1 0 := by
  let A : RGate := .ccx PackedStepLayout.extensionWire
    PackedStepLayout.signWire (PackedStepLayout.poolOffset + 10)
  let B : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseOneWire
  let C : RGate := .ccx (PackedStepLayout.poolOffset + 10)
    PackedStepLayout.poolOffset PackedStepLayout.phaseTwoWire
  let J := writeField I (PackedStepLayout.poolOffset + 10) 1 1
  have hAfirst : A.act I = J := by
    simp [A, J, act_ccx_write, hextension, hsign, hwrapped]
  have hJwrapped : bitValue J (PackedStepLayout.poolOffset + 10) = 1 := by
    simp [J, bitValue_write_self]
  have hJflag : bitValue J PackedStepLayout.poolOffset = 1 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hflag]
  have hJphaseOne : bitValue J PackedStepLayout.phaseOneWire = 1 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hphaseOne]
  let K := writeField J PackedStepLayout.phaseOneWire 1 0
  have hB : B.act J = K := by
    simp [B, K, act_ccx_write, hJwrapped, hJflag, hJphaseOne]
  have hKwrapped : bitValue K (PackedStepLayout.poolOffset + 10) = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide), hJwrapped]
  have hKflag : bitValue K PackedStepLayout.poolOffset = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide), hJflag]
  have hKphaseTwo : bitValue K PackedStepLayout.phaseTwoWire = 1 := by
    simp only [K, J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hphaseTwo]
  let L := writeField K PackedStepLayout.phaseTwoWire 1 0
  have hC : C.act K = L := by
    simp [C, L, act_ccx_write, hKwrapped, hKflag, hKphaseTwo]
  have hLwrapped : bitValue L (PackedStepLayout.poolOffset + 10) = 1 := by
    simp only [L]
    rw [bitValue_write_ne (by decide), hKwrapped]
  have hLextension : bitValue L PackedStepLayout.extensionWire = 1 := by
    simp only [L, K, J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hextension]
  have hLsign : bitValue L PackedStepLayout.signWire = 1 := by
    simp only [L, K, J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hsign]
  let O := writeField L (PackedStepLayout.poolOffset + 10) 1 0
  have hAlast : A.act L = O := by
    simp [A, O, act_ccx_write, hLwrapped, hLextension, hLsign]
  have hclearWrapped :
      writeField I (PackedStepLayout.poolOffset + 10) 1 0 = I :=
    write_of_bitValue (by simpa using hwrapped.symm)
  simp only [phaseCorrectionCore, actGates_cons, actGates_nil]
  change A.act (C.act (B.act (A.act I))) = _
  rw [hAfirst, hB, hC, hAlast]
  simp only [O, L, K, J]
  rw [writeField_comm
      (o₁ := PackedStepLayout.phaseTwoWire) (n₁ := 1)
      (o₂ := PackedStepLayout.poolOffset + 10) (n₂ := 1) (by decide),
    writeField_comm
      (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
      (o₂ := PackedStepLayout.poolOffset + 10) (n₂ := 1) (by decide),
    writeField_writeField, hclearWrapped]

theorem phaseCorrectionGates_identity_low_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates phaseCorrectionGates I = I := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hRshift :
      readField R PackedStepLayout.shiftOffset 9 ≠ encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hshift
  have hRflag : bitValue R PackedStepLayout.poolOffset = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hflag]
  have hRscratch8 :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hscratch8]
  have hRscratch9 :
      readField R (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hpool
  have hlowSelect : actGates lowSelectorGates R = R :=
    lowSelectorGates_off hRshift hRflag hRscratch9
  have hcore : actGates phaseCorrectionCore R = R :=
    phaseCorrectionCore_identity_low_off hRflag
  have hlowReverse : actGates lowSelectorGates.reverse R = R :=
    lowSelectorGates_reverse_off hRshift hRflag hRscratch9
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse R =
        writeField R PackedStepLayout.extensionWire 1 0 :=
    rPrimeSelectorGates_reverse_on hRlengthRPrime hRextension hRscratch8
  have hrestore : writeField R PackedStepLayout.extensionWire 1 0 = I := by
    simp only [R, writeField_writeField]
    exact write_of_bitValue (by simpa using hextension.symm)
  simp only [phaseCorrectionGates, actGates_append]
  rw [hrPrimeSelect, hlowSelect, hcore, hlowReverse, hrPrimeReverse,
    hrestore]

theorem phaseCorrectionGates_act_low_on
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 1)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates phaseCorrectionGates I =
      writeField
        (writeField I PackedStepLayout.phaseOneWire 1 0)
        PackedStepLayout.phaseTwoWire 1 0 := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch9 :
      readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hwrapped : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRsign : bitValue R PackedStepLayout.signWire = 1 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hsign]
  have hRphaseOne : bitValue R PackedStepLayout.phaseOneWire = 1 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseOne]
  have hRphaseTwo : bitValue R PackedStepLayout.phaseTwoWire = 1 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseTwo]
  have hRshift :
      readField R PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hRflag : bitValue R PackedStepLayout.poolOffset = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hflag]
  have hRscratch9 :
      readField R (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hscratch9]
  have hRwrapped : bitValue R (PackedStepLayout.poolOffset + 10) = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hwrapped]
  let T := writeField R PackedStepLayout.poolOffset 1 1
  have hlowSelect : actGates lowSelectorGates R = T := by
    simpa [T] using lowSelectorGates_on hRshift hRflag hRscratch9
  have hTextension : bitValue T PackedStepLayout.extensionWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRextension]
  have hTsign : bitValue T PackedStepLayout.signWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRsign]
  have hTflag : bitValue T PackedStepLayout.poolOffset = 1 := by
    simp [T, bitValue_write_self]
  have hTwrapped : bitValue T (PackedStepLayout.poolOffset + 10) = 0 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRwrapped]
  have hTphaseOne : bitValue T PackedStepLayout.phaseOneWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRphaseOne]
  have hTphaseTwo : bitValue T PackedStepLayout.phaseTwoWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRphaseTwo]
  let U := writeField
    (writeField T PackedStepLayout.phaseOneWire 1 0)
    PackedStepLayout.phaseTwoWire 1 0
  have hcore : actGates phaseCorrectionCore T = U := by
    simpa [U] using phaseCorrectionCore_act_low_on hTextension hTsign
      hTflag hTwrapped hTphaseOne hTphaseTwo
  have hUshift :
      readField U PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [U, T]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hRshift]
  have hUflag : bitValue U PackedStepLayout.poolOffset = 1 := by
    simp only [U, T]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_self]
  have hUscratch9 :
      readField U (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    simp only [U, T]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hRscratch9]
  let V := writeField U PackedStepLayout.poolOffset 1 0
  have hlowReverse : actGates lowSelectorGates.reverse U = V := by
    simpa [V] using lowSelectorGates_reverse_on hUshift hUflag hUscratch9
  have hVextension : bitValue V PackedStepLayout.extensionWire = 1 := by
    simp only [V, U, T]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hRextension]
  have hVlengthRPrime :
      readField V PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [V, U, T, R]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hVscratch8 :
      readField V (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [V, U, T]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hRscratch9
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse V =
        writeField V PackedStepLayout.extensionWire 1 0 :=
    rPrimeSelectorGates_reverse_on hVlengthRPrime hVextension hVscratch8
  have hclearExtension :
      writeField I PackedStepLayout.extensionWire 1 0 = I :=
    write_of_bitValue (by simpa using hextension.symm)
  have hclearFlag : writeField I PackedStepLayout.poolOffset 1 0 = I :=
    write_of_bitValue (by simpa using hflag.symm)
  have hfinal :
      writeField V PackedStepLayout.extensionWire 1 0 =
        writeField
          (writeField I PackedStepLayout.phaseOneWire 1 0)
          PackedStepLayout.phaseTwoWire 1 0 := by
    simp only [V, U, T, R]
    rw [writeField_comm
        (o₁ := PackedStepLayout.poolOffset) (n₁ := 1)
        (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.phaseTwoWire) (n₁ := 1)
        (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
        (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.poolOffset) (n₁ := 1)
        (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
      writeField_writeField, hclearExtension]
    rw [writeField_comm
        (o₁ := PackedStepLayout.phaseTwoWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_writeField, hclearFlag]
  simp only [phaseCorrectionGates, actGates_append]
  rw [hrPrimeSelect, hlowSelect, hcore, hlowReverse, hrPrimeReverse,
    hfinal]

theorem phaseGates_identity_terminal_low_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates phaseGates I = I := by
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hbase := basePhaseGates_act_terminal hextension htail hphaseOne
    hphaseTwo hlengthQ hlengthRPrime
  have hbaseIdentity : actGates PackedStepLayout.phaseGates I = I := by
    rw [hbase, if_neg hshift]
    have hp1 : writeField I PackedStepLayout.phaseOneWire 1 0 = I :=
      write_of_bitValue (by simpa using hphaseOne.symm)
    rw [hp1]
    have hp2 : writeField I PackedStepLayout.phaseTwoWire 1 0 = I :=
      write_of_bitValue (by simpa using hphaseTwo.symm)
    rw [hp2]
    exact write_of_bitValue
      (Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.signWire))
  have hcorrection := phaseCorrectionGates_identity_low_off
    hextension hlengthRPrime hshift hpool
  simp only [phaseGates, actGates_append]
  rw [hbaseIdentity, hcorrection]

theorem phaseGates_identity_terminal_low_on
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates phaseGates I = I := by
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let J := writeField
    (writeField
      (writeField I PackedStepLayout.phaseOneWire 1 1)
      PackedStepLayout.phaseTwoWire 1 1)
    PackedStepLayout.signWire 1 1
  have hbase : actGates PackedStepLayout.phaseGates I = J := by
    rw [basePhaseGates_act_terminal hextension htail hphaseOne hphaseTwo
      hlengthQ hlengthRPrime, if_pos hshift]
    simp only [J]
    rw [hsign]
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hextension]
  have hJsign : bitValue J PackedStepLayout.signWire = 1 := by
    simp [J, bitValue_write_self]
  have hJphaseOne : bitValue J PackedStepLayout.phaseOneWire = 1 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_self]
  have hJphaseTwo : bitValue J PackedStepLayout.phaseTwoWire = 1 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hJlengthRPrime :
      readField J PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hJshift :
      readField J PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hshift]
  have hJpool : readField J PackedStepLayout.poolOffset 13 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hpool]
  have hcorrection := phaseCorrectionGates_act_low_on hJextension hJsign
    hJphaseOne hJphaseTwo hJlengthRPrime hJshift hJpool
  have hclearPhaseOne :
      writeField I PackedStepLayout.phaseOneWire 1 0 = I :=
    write_of_bitValue (by simpa using hphaseOne.symm)
  have hclearPhaseTwo :
      writeField I PackedStepLayout.phaseTwoWire 1 0 = I :=
    write_of_bitValue (by simpa using hphaseTwo.symm)
  have hsetSign : writeField I PackedStepLayout.signWire 1 1 = I :=
    write_of_bitValue (by simpa using hsign.symm)
  have hrestore :
      writeField
          (writeField J PackedStepLayout.phaseOneWire 1 0)
          PackedStepLayout.phaseTwoWire 1 0 = I := by
    simp only [J]
    rw [writeField_comm
        (o₁ := PackedStepLayout.signWire) (n₁ := 1)
        (o₂ := PackedStepLayout.phaseOneWire) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.phaseTwoWire) (n₁ := 1)
        (o₂ := PackedStepLayout.phaseOneWire) (n₂ := 1) (by decide),
      writeField_writeField,
      writeField_comm
        (o₁ := PackedStepLayout.signWire) (n₁ := 1)
        (o₂ := PackedStepLayout.phaseTwoWire) (n₂ := 1) (by decide),
      writeField_writeField, hclearPhaseOne, hclearPhaseTwo, hsetSign]
  simp only [phaseGates, actGates_append]
  rw [hbase, hcorrection, hrestore]

theorem ownershipMaskGates_act
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hscratch : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates ownershipMaskGates I =
      writeField
        (writeField I PackedOwnership.controlWire 1
          (bitValue I PackedStepLayout.phaseOneWire))
        PackedStepLayout.phaseOneWire 1
          (bitValue I PackedOwnership.controlWire) := by
  let A : RGate := .ccx PackedStepLayout.extensionWire
    PackedStepLayout.signWire (PackedStepLayout.poolOffset + 12)
  let J := writeField I (PackedStepLayout.poolOffset + 12) 1 1
  have hAfirst : actGates [A] I = J := by
    simp only [actGates_cons, actGates_nil, A, act_ccx_write]
    simp [J, hextension, hsign, hscratch]
  have hJscratch : bitValue J (PackedStepLayout.poolOffset + 12) = 1 := by
    simp [J, bitValue_write_self]
  have hJcontrol : bitValue J PackedOwnership.controlWire =
      bitValue I PackedOwnership.controlWire := by
    simp only [J]
    rw [bitValue_write_ne (by decide)]
  have hJphaseOne : bitValue J PackedStepLayout.phaseOneWire =
      bitValue I PackedStepLayout.phaseOneWire := by
    simp only [J]
    rw [bitValue_write_ne (by decide)]
  let K := writeField
    (writeField J PackedOwnership.controlWire 1
      (bitValue I PackedStepLayout.phaseOneWire))
    PackedStepLayout.phaseOneWire 1
      (bitValue I PackedOwnership.controlWire)
  have hswap : actGates
      (fredkin (PackedStepLayout.poolOffset + 12)
        PackedOwnership.controlWire PackedStepLayout.phaseOneWire) J = K := by
    rw [fredkin_on (by decide) (by decide) (by decide) hJscratch]
    simp [K, hJcontrol, hJphaseOne]
  have hKextension : bitValue K PackedStepLayout.extensionWire = 1 := by
    simp only [K, J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hextension]
  have hKsign : bitValue K PackedStepLayout.signWire = 1 := by
    simp only [K, J]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hsign]
  have hKscratch : bitValue K (PackedStepLayout.poolOffset + 12) = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hJscratch]
  let O := writeField K (PackedStepLayout.poolOffset + 12) 1 0
  have hAlast : actGates [A] K = O := by
    simp only [actGates_cons, actGates_nil, A, act_ccx_write]
    simp [O, hKextension, hKsign, hKscratch]
  have hclearScratch :
      writeField I (PackedStepLayout.poolOffset + 12) 1 0 = I :=
    write_of_bitValue (by simpa using hscratch.symm)
  simp only [ownershipMaskGates, actGates_append]
  rw [show actGates
        [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
          (PackedStepLayout.poolOffset + 12)] I = J by
      simpa [A] using hAfirst,
    hswap,
    show actGates
        [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
          (PackedStepLayout.poolOffset + 12)] K = O by
      simpa [A] using hAlast]
  simp only [O, K, J]
  rw [writeField_comm
      (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
      (o₂ := PackedStepLayout.poolOffset + 12) (n₂ := 1) (by decide),
    writeField_comm
      (o₁ := PackedOwnership.controlWire) (n₁ := 1)
      (o₂ := PackedStepLayout.poolOffset + 12) (n₂ := 1) (by decide),
    writeField_writeField, hclearScratch]

theorem ownershipBodyGates_identity_control_off
    {I : Nat}
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates ownershipBodyGates I = I := by
  let P := actGates PackedOwnership.phaseClearGates I
  have hPcontrol : bitValue P PackedOwnership.controlWire = 0 := by
    simp only [P, PackedOwnership.phaseClearGates, actGates_cons,
      actGates_nil]
    rw [act_cx_write, act_x_write, bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hcontrol]
  have hPtail : readField P (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    dsimp only [P]
    rw [readField_actGates_of_outside, htail]
    intro g hg q hq
    simp [PackedOwnership.phaseClearGates] at hg
    rcases hg with rfl | rfl <;>
      simp [RGate.wires, PackedOwnership.controlWire,
        PackedStepLayout.poolOffset, PackedStepLayout.phaseOneWire] at hq ⊢ <;>
      omega
  have hswap : actGates PackedSwapLength.gates P = P :=
    PackedSwapLength.gates_inactive hPcontrol hPtail
  have hphaseRestore : actGates PackedOwnership.phaseRestoreGates P = I := by
    change actGates PackedOwnership.phaseClearGates.reverse
      (actGates PackedOwnership.phaseClearGates I) = I
    exact actGates_reverse PackedOwnership.phaseClearGates_wellFormed I
  have hiteration : actGates PackedOwnership.iterationGates I = I :=
    PackedOwnership.iterationGates_inactive hcontrol
  simp only [ownershipBodyGates, actGates_append]
  change actGates PackedOwnership.iterationGates
    (actGates PackedOwnership.phaseRestoreGates
      (actGates PackedSwapLength.gates P)) = I
  rw [hswap, hphaseRestore, hiteration]

theorem prepareGates_identity_shift_off
    {I : Nat}
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates PackedOwnership.prepareGates I = I := by
  have hzeroQ : bitValue I PackedOwnership.zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroShift : bitValue I PackedOwnership.zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (by simp [PackedOwnership.zeroShiftWire])
      (by simp [PackedOwnership.zeroShiftWire]) htail
  have hscratch : readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hzeroShiftValue : PackedOwnership.zeroShiftValue I = 0 := by
    unfold PackedOwnership.zeroShiftValue Phase.selectorValue
    rw [if_neg hshift]
  rw [PackedOwnership.prepareGates_act hzeroQ hzeroShift hscratch,
    PackedOwnership.controlPrepared, hcontrol, hzeroShiftValue, Nat.mul_zero,
    Nat.add_zero, Nat.zero_mod]
  exact write_of_bitValue (by simpa using hcontrol.symm)

theorem ownershipMaskGates_identity_zero_pair
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 1)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hscratch : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates ownershipMaskGates I = I := by
  have hsignBound := bitValue_lt I PackedStepLayout.signWire
  rcases (show bitValue I PackedStepLayout.signWire = 0 ∨
      bitValue I PackedStepLayout.signWire = 1 by omega) with hsign | hsign
  · let A : RGate := .ccx PackedStepLayout.extensionWire
      PackedStepLayout.signWire (PackedStepLayout.poolOffset + 12)
    have hA : actGates [A] I = I := by
      simp only [actGates_cons, actGates_nil, A, act_ccx_write]
      apply write_of_bitValue
      simp [hsign, Nat.mod_eq_of_lt
        (bitValue_lt I (PackedStepLayout.poolOffset + 12))]
    have hswap : actGates
        (fredkin (PackedStepLayout.poolOffset + 12)
          PackedOwnership.controlWire PackedStepLayout.phaseOneWire) I = I :=
      fredkin_off (by decide) (by decide) hscratch
    simp only [ownershipMaskGates, actGates_append]
    rw [show actGates
          [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
            (PackedStepLayout.poolOffset + 12)] I = I by
        simpa [A] using hA,
      hswap,
      show actGates
          [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
            (PackedStepLayout.poolOffset + 12)] I = I by
        simpa [A] using hA]
  · rw [ownershipMaskGates_act hextension hsign hscratch, hphaseOne,
      hcontrol]
    have hcontrolWrite :
        writeField I PackedOwnership.controlWire 1 0 = I :=
      write_of_bitValue (by simpa using hcontrol.symm)
    rw [hcontrolWrite]
    exact write_of_bitValue (by simpa using hphaseOne.symm)

theorem ownershipMaskGates_identity_extension_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hscratch : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates ownershipMaskGates I = I := by
  let A : RGate := .ccx PackedStepLayout.extensionWire
    PackedStepLayout.signWire (PackedStepLayout.poolOffset + 12)
  have hA : actGates [A] I = I := by
    simp only [actGates_cons, actGates_nil, A, act_ccx_write, hextension]
    simp only [zero_mul, Nat.add_zero]
    rw [← readField_one,
      Nat.mod_eq_of_lt
        (readField_lt I (PackedStepLayout.poolOffset + 12) 1),
      writeField_read]
  have hswap : actGates
      (fredkin (PackedStepLayout.poolOffset + 12)
        PackedOwnership.controlWire PackedStepLayout.phaseOneWire) I = I :=
    fredkin_off (by decide) (by decide) hscratch
  simp only [ownershipMaskGates, actGates_append]
  rw [show actGates
        [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
          (PackedStepLayout.poolOffset + 12)] I = I by
      simpa [A] using hA,
    hswap,
    show actGates
        [.ccx PackedStepLayout.extensionWire PackedStepLayout.signWire
          (PackedStepLayout.poolOffset + 12)] I = I by
      simpa [A] using hA]

theorem ownershipRestoreGates_act_on
    {I : Nat}
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates ownershipRestoreGates I =
      writeField
        (writeField I PackedOwnership.controlWire 1
          (bitValue I PackedStepLayout.phaseOneWire))
        PackedStepLayout.phaseOneWire 1
          (bitValue I PackedOwnership.controlWire) := by
  let S := writeField I PackedStepLayout.extensionWire 1 1
  have hcompute : actGates ownershipRestoreControlGates I = S := by
    rw [ownershipRestoreControlGates,
      Phase.negativeAnd_act (by decide) (by decide)]
    simp [Phase.negativeAndOut, S, hsign, hphaseTwo, hextension]
  have hSscratch : bitValue S PackedStepLayout.extensionWire = 1 := by
    simp [S, bitValue_write_self]
  have hScontrol : bitValue S PackedOwnership.controlWire =
      bitValue I PackedOwnership.controlWire := by
    simp only [S]
    rw [bitValue_write_ne (by decide)]
  have hSphaseOne : bitValue S PackedStepLayout.phaseOneWire =
      bitValue I PackedStepLayout.phaseOneWire := by
    simp only [S]
    rw [bitValue_write_ne (by decide)]
  let K := writeField
    (writeField S PackedOwnership.controlWire 1
      (bitValue I PackedStepLayout.phaseOneWire))
    PackedStepLayout.phaseOneWire 1
      (bitValue I PackedOwnership.controlWire)
  have hswap : actGates
      (fredkin PackedStepLayout.extensionWire
        PackedOwnership.controlWire PackedStepLayout.phaseOneWire) S = K := by
    rw [fredkin_on (by decide) (by decide) (by decide) hSscratch]
    simp [K, hScontrol, hSphaseOne]
  have hKsign : bitValue K PackedStepLayout.signWire = 1 := by
    simp only [K, S]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hsign]
  have hKphaseTwo : bitValue K PackedStepLayout.phaseTwoWire = 0 := by
    simp only [K, S]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hphaseTwo]
  have hKscratch : bitValue K PackedStepLayout.extensionWire = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hSscratch]
  let U := writeField K PackedStepLayout.extensionWire 1 0
  have huncompute :
      actGates ownershipRestoreControlGates.reverse K = U := by
    have hreverse : ownershipRestoreControlGates.reverse =
        ownershipRestoreControlGates := by
      rfl
    rw [hreverse, ownershipRestoreControlGates,
      Phase.negativeAnd_act (by decide) (by decide)]
    simp [Phase.negativeAndOut, U, hKsign, hKphaseTwo, hKscratch]
  have hclearScratch :
      writeField I PackedStepLayout.extensionWire 1 0 = I :=
    write_of_bitValue (by simpa using hextension.symm)
  simp only [ownershipRestoreGates, actGates_append]
  rw [hcompute, hswap, huncompute]
  simp only [U, K, S]
  rw [writeField_comm
      (o₁ := PackedStepLayout.phaseOneWire) (n₁ := 1)
      (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
    writeField_comm
      (o₁ := PackedOwnership.controlWire) (n₁ := 1)
      (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
    writeField_writeField, hclearScratch]

theorem ownershipRestoreGates_identity_marker_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hmarker : bitValue I PackedStepLayout.signWire = 0 ∨
      bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates ownershipRestoreGates I = I := by
  have hcompute : actGates ownershipRestoreControlGates I = I := by
    rw [ownershipRestoreControlGates,
      Phase.negativeAnd_act (by decide) (by decide)]
    have hclear : writeField I PackedStepLayout.extensionWire 1 0 = I :=
      write_of_bitValue (by simpa using hextension.symm)
    rcases hmarker with hsign | hphaseTwo
    · simpa [Phase.negativeAndOut, hsign, hextension] using hclear
    · simpa [Phase.negativeAndOut, hphaseTwo, hextension] using hclear
  have hswap : actGates
      (fredkin PackedStepLayout.extensionWire
        PackedOwnership.controlWire PackedStepLayout.phaseOneWire) I = I :=
    fredkin_off (by decide) (by decide) hextension
  have huncompute : actGates ownershipRestoreControlGates.reverse I = I := by
    have hreverse : ownershipRestoreControlGates.reverse =
        ownershipRestoreControlGates := by
      rfl
    rw [hreverse, hcompute]
  simp only [ownershipRestoreGates, actGates_append]
  rw [hcompute, hswap, huncompute]

theorem ownershipRestoreGates_identity_zero_pair
    {I : Nat}
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates ownershipRestoreGates I = I := by
  have hsignBound := bitValue_lt I PackedStepLayout.signWire
  have hphaseTwoBound := bitValue_lt I PackedStepLayout.phaseTwoWire
  rcases (show bitValue I PackedStepLayout.signWire = 0 ∨
      bitValue I PackedStepLayout.signWire = 1 by omega) with hsign | hsign
  · exact ownershipRestoreGates_identity_marker_off hextension (Or.inl hsign)
  · rcases (show bitValue I PackedStepLayout.phaseTwoWire = 0 ∨
        bitValue I PackedStepLayout.phaseTwoWire = 1 by omega) with
      hphaseTwo | hphaseTwo
    · rw [ownershipRestoreGates_act_on hsign hphaseTwo hextension,
        hphaseOne, hcontrol]
      have hcontrolWrite : writeField I PackedOwnership.controlWire 1 0 = I :=
        write_of_bitValue (by simpa using hcontrol.symm)
      rw [hcontrolWrite]
      exact write_of_bitValue (by simpa using hphaseOne.symm)
    · exact ownershipRestoreGates_identity_marker_off hextension
        (Or.inr hphaseTwo)

theorem prepareGates_preserves_sign (I : Nat) :
    bitValue (actGates PackedOwnership.prepareGates I)
        PackedStepLayout.signWire =
      bitValue I PackedStepLayout.signWire := by
  have havoids :
      ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
        q < PackedStepLayout.signWire ∨
          PackedStepLayout.signWire + 1 ≤ q := by
    exact PackedOwnershipOperands.prepareGates_avoids_sign
  rw [← readField_one,
    readField_actGates_of_outside havoids I, readField_one]

theorem prepareGates_preserves_phaseTwo (I : Nat) :
    bitValue (actGates PackedOwnership.prepareGates I)
        PackedStepLayout.phaseTwoWire =
      bitValue I PackedStepLayout.phaseTwoWire := by
  have havoids :
      ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
        q < PackedStepLayout.phaseTwoWire ∨
          PackedStepLayout.phaseTwoWire + 1 ≤ q := by
    exact PackedOwnershipOperands.prepareGates_avoids_phaseTwo
  rw [← readField_one,
    readField_actGates_of_outside havoids I, readField_one]

theorem prepareGates_preserves_extension (I : Nat) :
    bitValue (actGates PackedOwnership.prepareGates I)
        PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire := by
  have havoids :
      ∀ g ∈ PackedOwnership.prepareGates, ∀ q ∈ g.wires,
        q < PackedStepLayout.extensionWire ∨
          PackedStepLayout.extensionWire + 1 ≤ q := by
    exact PackedOwnershipOperands.prepareGates_avoids_extension
  rw [← readField_one,
    readField_actGates_of_outside havoids I, readField_one]

theorem ownershipGates_act_live
    {I O : Nat}
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hresult : actGates PackedOwnership.gates I = O)
    (hresultExtension : bitValue O PackedStepLayout.extensionWire = 0)
    (hresultMarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1) :
    actGates ownershipGates I = actGates PackedOwnership.gates I := by
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = I :=
    PackedPhaseFourPrefix.rPrimeSelector_identity
      hlengthRPrime hextension hscratch8
  have hzeroQ : bitValue I PackedOwnership.zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroShift : bitValue I PackedOwnership.zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (by simp [PackedOwnership.zeroShiftWire])
      (by simp [PackedOwnership.zeroShiftWire]) htail
  have hscratch :
      readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  let J := PackedOwnership.controlPrepared I
  have hprepare : actGates PackedOwnership.prepareGates I = J := by
    simpa [J] using PackedOwnership.prepareGates_act
      hzeroQ hzeroShift hscratch
  have hJlengthRPrime :
      readField J PackedStepLayout.lengthRPrimeOffset 8 ≠ encodedZero 8 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hlengthRPrime
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [bitValue_write_ne (by decide), hextension]
  have hJscratch8 :
      readField J (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide), hscratch8]
  have hJscratch12 : bitValue J (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) htail
  have hmask : actGates ownershipMaskGates J = J :=
    ownershipMaskGates_identity_extension_off hJextension hJscratch12
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse J = J :=
    rPrimeSelectorGates_reverse_off hJlengthRPrime hJextension hJscratch8
  have hdecomp : actGates PackedOwnership.gates I =
      actGates PackedOwnership.prepareGates
        (actGates ownershipBodyGates
          (actGates PackedOwnership.prepareGates I)) := by
    simp only [PackedOwnership.gates, ownershipBodyGates, actGates_append]
  let K := actGates ownershipBodyGates J
  have hKform : K =
      actGates PackedOwnership.iterationGates
        (actGates PackedOwnership.phaseRestoreGates
          (actGates PackedSwapLength.gates
            (actGates PackedOwnership.phaseClearGates J))) := by
    simp only [K, ownershipBodyGates, actGates_append]
  have hresult' : actGates PackedOwnership.prepareGates K = O := by
    have h := hresult
    rw [hdecomp, hprepare] at h
    exact h
  have hKextension : bitValue K PackedStepLayout.extensionWire = 0 := by
    have h := congrArg
      (fun X => bitValue X PackedStepLayout.extensionWire) hresult'
    rw [prepareGates_preserves_extension K, hresultExtension] at h
    exact h
  have hKmarker : bitValue K PackedStepLayout.signWire = 0 ∨
      bitValue K PackedStepLayout.phaseTwoWire = 1 := by
    rcases hresultMarker with hsign | hphaseTwo
    · left
      have h := congrArg
        (fun X => bitValue X PackedStepLayout.signWire) hresult'
      rw [prepareGates_preserves_sign K, hsign] at h
      exact h
    · right
      have h := congrArg
        (fun X => bitValue X PackedStepLayout.phaseTwoWire) hresult'
      rw [prepareGates_preserves_phaseTwo K, hphaseTwo] at h
      exact h
  have hrestore : actGates ownershipRestoreGates K = K :=
    ownershipRestoreGates_identity_marker_off hKextension hKmarker
  simp only [ownershipGates, actGates_append]
  rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse]
  change actGates PackedOwnership.prepareGates
      (actGates ownershipRestoreGates
        (actGates ownershipBodyGates J)) =
    actGates PackedOwnership.gates I
  rw [show actGates ownershipBodyGates J = K by rfl, hrestore]
  simp only [PackedOwnership.gates, actGates_append]
  rw [hprepare]
  rw [← hKform]

theorem ownershipGates_identity_terminal_low_on
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates ownershipGates I = I := by
  have hcontrol : bitValue I PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRsign : bitValue R PackedStepLayout.signWire = 1 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hsign]
  have hRphaseOne : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseOne]
  have hRcontrol : bitValue R PackedOwnership.controlWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hcontrol]
  have hRlengthQ : readField R PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthQ]
  have hRlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hRshift : readField R PackedStepLayout.shiftOffset 9 =
      encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hRtail : readField R (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hRscratch8 :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hRtail
  let T := writeField R PackedOwnership.controlWire 1 1
  have hprepare : actGates PackedOwnership.prepareGates R = T := by
    simpa [T] using PackedOwnership.prepareGates_enable hRcontrol
      hRlengthQ hRshift hRtail
  have hTextension : bitValue T PackedStepLayout.extensionWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRextension]
  have hTsign : bitValue T PackedStepLayout.signWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRsign]
  have hTcontrol : bitValue T PackedOwnership.controlWire = 1 := by
    simp [T, bitValue_write_self]
  have hTphaseOne : bitValue T PackedStepLayout.phaseOneWire = 0 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRphaseOne]
  have hTscratch : bitValue T (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hRtail
  let M := writeField
    (writeField T PackedOwnership.controlWire 1 0)
    PackedStepLayout.phaseOneWire 1 1
  have hmask : actGates ownershipMaskGates T = M := by
    rw [ownershipMaskGates_act hTextension hTsign hTscratch,
      hTphaseOne, hTcontrol]
  have hMextension : bitValue M PackedStepLayout.extensionWire = 1 := by
    simp only [M]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hTextension]
  have hMsign : bitValue M PackedStepLayout.signWire = 1 := by
    simp only [M]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide), hTsign]
  have hMcontrol : bitValue M PackedOwnership.controlWire = 0 := by
    simp only [M]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hMphaseOne : bitValue M PackedStepLayout.phaseOneWire = 1 := by
    simp [M, bitValue_write_self]
  have hMtail : readField M (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide), hRtail]
  have hMlengthRPrime :
      readField M PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide), hRlengthRPrime]
  have hMscratch8 :
      readField M (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hMtail
  let U := writeField M PackedStepLayout.extensionWire 1 0
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse M = U := by
    simpa [U] using rPrimeSelectorGates_reverse_on hMlengthRPrime
      hMextension hMscratch8
  have hUcontrol : bitValue U PackedOwnership.controlWire = 0 := by
    simp only [U]
    rw [bitValue_write_ne (by decide), hMcontrol]
  have hUphaseOne : bitValue U PackedStepLayout.phaseOneWire = 1 := by
    simp only [U]
    rw [bitValue_write_ne (by decide), hMphaseOne]
  have hUphaseTwo : bitValue U PackedStepLayout.phaseTwoWire = 0 := by
    simp only [U, M, T, R]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hphaseTwo]
  have hUsign : bitValue U PackedStepLayout.signWire = 1 := by
    simp only [U]
    rw [bitValue_write_ne (by decide), hMsign]
  have hUextension : bitValue U PackedStepLayout.extensionWire = 0 := by
    simp [U, bitValue_write_self]
  have hUtail : readField U (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [U]
    rw [readField_writeField_of_disjoint (by decide), hMtail]
  have hbody : actGates ownershipBodyGates U = U :=
    ownershipBodyGates_identity_control_off hUcontrol hUtail
  let N := writeField
    (writeField M PackedOwnership.controlWire 1 1)
    PackedStepLayout.phaseOneWire 1 0
  have hN : N = T := by
    simp only [N, M]
    rw [writeField_overwrite_alternating_of_disjoint (by decide)]
    have hcontrolWrite :
        writeField T PackedOwnership.controlWire 1 1 = T :=
      write_of_bitValue (by simpa using hTcontrol.symm)
    rw [hcontrolWrite]
    exact write_of_bitValue (by simpa using hTphaseOne.symm)
  let V := writeField
    (writeField U PackedOwnership.controlWire 1 1)
    PackedStepLayout.phaseOneWire 1 0
  have hrestoreControl : actGates ownershipRestoreGates U = V := by
    simpa [V, hUphaseOne, hUcontrol] using
      ownershipRestoreGates_act_on hUsign hUphaseTwo hUextension
  have hV : V = writeField T PackedStepLayout.extensionWire 1 0 := by
    simp only [V, U]
    rw [writeField_comm
        (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
        (o₂ := PackedOwnership.controlWire) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
        (o₂ := PackedStepLayout.phaseOneWire) (n₂ := 1) (by decide)]
    change writeField N PackedStepLayout.extensionWire 1 0 =
      writeField T PackedStepLayout.extensionWire 1 0
    rw [hN]
  have hrestore : writeField R PackedStepLayout.extensionWire 1 0 = I := by
    simp only [R, writeField_writeField]
    exact write_of_bitValue (by simpa using hextension.symm)
  let W := writeField I PackedOwnership.controlWire 1 1
  have hVW : V = W := by
    rw [hV]
    simp only [T]
    rw [writeField_comm
        (o₁ := PackedOwnership.controlWire) (n₁ := 1)
        (o₂ := PackedStepLayout.extensionWire) (n₂ := 1) (by decide),
      hrestore]
  have hWcontrol : bitValue W PackedOwnership.controlWire = 1 := by
    simp [W, bitValue_write_self]
  have hWlengthQ : readField W PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    simp only [W]
    rw [readField_writeField_of_disjoint (by decide), hlengthQ]
  have hWshift : readField W PackedStepLayout.shiftOffset 9 =
      encodedZero 9 := by
    simp only [W]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hWtail : readField W (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [W]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hprepareAgain : actGates PackedOwnership.prepareGates W =
      writeField W PackedOwnership.controlWire 1 0 :=
    PackedOwnership.prepareGates_disable hWcontrol hWlengthQ hWshift hWtail
  have hdisable : writeField W PackedOwnership.controlWire 1 0 = I := by
    simp only [W, writeField_writeField]
    exact write_of_bitValue (by simpa using hcontrol.symm)
  simp only [ownershipGates, actGates_append]
  rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse, hbody,
    hrestoreControl, hVW, hprepareAgain, hdisable]

theorem ownershipGates_identity_terminal_low_off
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates ownershipGates I = I := by
  have hcontrol : bitValue I PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRcontrol : bitValue R PackedOwnership.controlWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hcontrol]
  have hRphaseOne : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseOne]
  have hRlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hRshift :
      readField R PackedStepLayout.shiftOffset 9 ≠ encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hshift
  have hRtail : readField R (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hRscratch8 :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hRtail
  have hRscratch : bitValue R (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hRtail
  have hprepare : actGates PackedOwnership.prepareGates R = R :=
    prepareGates_identity_shift_off hRcontrol hRshift hRtail
  have hmask : actGates ownershipMaskGates R = R :=
    ownershipMaskGates_identity_zero_pair hRextension hRcontrol hRphaseOne
      hRscratch
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse R =
        writeField R PackedStepLayout.extensionWire 1 0 :=
    rPrimeSelectorGates_reverse_on hRlengthRPrime hRextension hRscratch8
  have hrestore : writeField R PackedStepLayout.extensionWire 1 0 = I := by
    simp only [R, writeField_writeField]
    exact write_of_bitValue (by simpa using hextension.symm)
  have hbody : actGates ownershipBodyGates I = I :=
    ownershipBodyGates_identity_control_off hcontrol htail
  have hrestoreControl : actGates ownershipRestoreGates I = I :=
    ownershipRestoreGates_identity_zero_pair hcontrol hphaseOne hextension
  have hprepareAgain : actGates PackedOwnership.prepareGates I = I :=
    prepareGates_identity_shift_off hcontrol hshift htail
  simp only [ownershipGates, actGates_append]
  rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse, hrestore,
    hbody, hrestoreControl, hprepareAgain]

theorem exitGates_identity_live
    {I : Nat}
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates exitGates I = I := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hselect : actGates terminalSelectorGates I = I :=
    terminalSelectorGates_off hlengthRPrime hflag hscratch8
  have hswap : actGates epochSwapGates I = I := by
    rw [epochSwapGates, fredkin_off (by decide) (by decide) hflag]
  have hreverse : actGates terminalSelectorGates.reverse I = I :=
    terminalSelectorGates_reverse_off hlengthRPrime hflag hscratch8
  simp only [exitGates, actGates_append]
  rw [hselect, hswap, hreverse]

theorem exitGates_act_terminal
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates exitGates I =
      writeField
        (writeField I PackedStepLayout.extensionWire 1
          (bitValue I PackedStepLayout.signWire))
        PackedStepLayout.signWire 1 0 := by
  have hflag : bitValue I PackedStepLayout.poolOffset = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let S := writeField I PackedStepLayout.poolOffset 1 1
  have hselect : actGates terminalSelectorGates I = S := by
    simpa [S] using terminalSelectorGates_on hlengthRPrime hflag hscratch8
  have hScontrol : bitValue S PackedStepLayout.poolOffset = 1 := by
    simp [S, bitValue_write_self]
  have hSextension : bitValue S PackedStepLayout.extensionWire = 0 := by
    simp only [S]
    rw [bitValue_write_ne (by decide), hextension]
  have hSsign : bitValue S PackedStepLayout.signWire =
      bitValue I PackedStepLayout.signWire := by
    simp only [S]
    rw [bitValue_write_ne (by decide)]
  let E := writeField
    (writeField S PackedStepLayout.extensionWire 1
      (bitValue I PackedStepLayout.signWire))
    PackedStepLayout.signWire 1 0
  have hswap : actGates epochSwapGates S = E := by
    rw [epochSwapGates,
      fredkin_on (by decide) (by decide) (by decide) hScontrol,
      hSextension, hSsign]
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8 := by
    simp only [E, S]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hEcontrol : bitValue E PackedStepLayout.poolOffset = 1 := by
    simp only [E, S]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_self]
  have hEscratch8 :
      readField E (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [E, S]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hscratch8]
  have hreverse : actGates terminalSelectorGates.reverse E =
      writeField E PackedStepLayout.poolOffset 1 0 :=
    terminalSelectorGates_reverse_on hEsource hEcontrol hEscratch8
  have hclearFlag : writeField I PackedStepLayout.poolOffset 1 0 = I :=
    write_of_bitValue (by simpa using hflag.symm)
  have hfinal : writeField E PackedStepLayout.poolOffset 1 0 =
      writeField
        (writeField I PackedStepLayout.extensionWire 1
          (bitValue I PackedStepLayout.signWire))
        PackedStepLayout.signWire 1 0 := by
    simp only [E, S]
    rw [writeField_comm
        (o₁ := PackedStepLayout.signWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_comm
        (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
        (o₂ := PackedStepLayout.poolOffset) (n₂ := 1) (by decide),
      writeField_writeField, hclearFlag]
  simp only [exitGates, actGates_append]
  rw [hselect, hswap, hreverse, hfinal]

theorem exitGates_identity_clean
    {I : Nat}
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates exitGates I = I := by
  by_cases hlengthRPrime :
      readField I PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8
  · rw [exitGates_act_terminal hextension hlengthRPrime hpool]
    have hclearExtension :
        writeField I PackedStepLayout.extensionWire 1 0 = I :=
      write_of_bitValue (by simpa using hextension.symm)
    rw [hsign, hclearExtension]
    exact write_of_bitValue (by simpa using hsign.symm)
  · exact exitGates_identity_live hlengthRPrime hpool

theorem gates_act_terminal
    {I : Nat}
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9)
    (hepoch : terminalNextLow I = encodedZero 9 →
      terminalNextEpoch I = 1) :
    actGates gates I = roundOut I := by
  let E := entryOut I
  have hentry : actGates entryGates I = E := by
    simpa [E] using entryGates_act_terminal hlengthRPrime hphaseOne hsign hpool
  have hEphaseOne : bitValue E PackedStepLayout.phaseOneWire = 0 := by
    simp only [E, entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      hphaseOne]
  have hEphaseTwo : bitValue E PackedStepLayout.phaseTwoWire = 0 := by
    simp only [E, entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      hphaseTwo]
  have hEextension : bitValue E PackedStepLayout.extensionWire = 0 := by
    simp only [E, entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hElengthQ : readField E PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    simp only [E, entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthQ]
  have hElengthRPrime :
      readField E PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [E, entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hnextLowBound : terminalNextLow I < 2 ^ 9 := by
    unfold terminalNextLow
    exact Nat.mod_lt _ (by norm_num)
  have hEshift : readField E PackedStepLayout.shiftOffset 9 =
      terminalNextLow I := by
    simp only [E, entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), readField_writeField,
      Nat.mod_eq_of_lt hnextLowBound]
  have hnextEpochBound : terminalNextEpoch I < 2 := by
    unfold terminalNextEpoch
    exact Nat.mod_lt _ (by norm_num)
  have hEsign : bitValue E PackedStepLayout.signWire = terminalNextEpoch I := by
    simp only [E, entryOut]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hnextEpochBound]
  have hEpool : readField E PackedStepLayout.poolOffset 13 = 0 := by
    simp only [E, entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hpool]
  have hEtfit : readField E PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9 := by
    simp only [E, entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact htfit
  have hprefix : actGates prefixRemainderGates E = E := by
    simp only [prefixRemainderGates, actGates_append]
    rw [PackedPhaseFourPrefix.remainderBlocks_identity_terminal
        hEphaseOne hEphaseTwo hElengthRPrime hEextension hEpool,
      PackedPhaseFourPrefix.quotientIncrementBlock_identity_phaseZero
        hEphaseTwo hEpool,
      PackedPhaseFourPrefix.swapBlock_identity_phaseZero
        hEphaseOne hEphaseTwo hEpool,
      PackedPhaseFourPrefix.quotientDecrementBlock_identity_phaseZero
        hEphaseOne hEpool]
  have hcoefficient : actGates PackedStepLayout.coefficientGates E = E :=
    PackedCoefficient.gates_identity_phaseZero hEphaseOne hEphaseTwo
      hEextension hEpool hEtfit
  have hpostShift : actGates PackedShift.postShiftGates E = E :=
    PackedShift.postShiftGates_identity_phaseOneClear hEphaseOne
      (readField_sub_zero (by omega) (by omega) hEpool)
  have hphase : actGates phaseGates E = E := by
    by_cases hlow : terminalNextLow I = encodedZero 9
    · exact phaseGates_identity_terminal_low_on hEextension
        (by rw [hEsign, hepoch hlow]) hEphaseOne hEphaseTwo hElengthQ
        hElengthRPrime (by simpa [hEshift] using hlow) hEpool
    · exact phaseGates_identity_terminal_low_off hEextension hEphaseOne
        hEphaseTwo hElengthQ hElengthRPrime
        (by simpa [hEshift] using hlow) hEpool
  have hownership : actGates ownershipGates E = E := by
    by_cases hlow : terminalNextLow I = encodedZero 9
    · exact ownershipGates_identity_terminal_low_on hEextension
        (by rw [hEsign, hepoch hlow]) hEphaseOne hEphaseTwo hElengthQ
        hElengthRPrime (by simpa [hEshift] using hlow) hEpool
    · exact ownershipGates_identity_terminal_low_off hEextension hEphaseOne
        hElengthRPrime (by simpa [hEshift] using hlow) hEpool
  have hexit : actGates exitGates E = roundOut I := by
    rw [exitGates_act_terminal hEextension hElengthRPrime hEpool]
    simp only [E, roundOut]
    rw [hEsign]
  simp only [gates, actGates_append]
  rw [hentry, hprefix, hcoefficient, hpostShift, hphase, hownership, hexit]

end PackedTerminalEpoch
end Euclid
end VQ
