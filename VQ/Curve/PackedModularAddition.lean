import VQ.Curve.PackedModularProduct
import VQ.Program.Place
import VQ.Reversible.Wiring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace VQ.Curve.PackedModularAddition

open Algebra Reversible Semantics
open VQ.Curve.PackedModularProduct

def targetOffset : Nat := 0

def targetExtensionWire (width : Nat) : Nat := width

def sourceOffset (width : Nat) : Nat := width + 1

def sourceExtensionWire (width : Nat) : Nat := 2 * width + 1

def carryInWire (width : Nat) : Nat := 2 * width + 2

def carryOutWire (width : Nat) : Nat := 2 * width + 3

def scratchWire (width : Nat) : Nat := 2 * width + 4

def reductionWire (width : Nat) : Nat := 2 * width + 5

def controlWire (width : Nat) : Nat := 2 * width + 6

def width (wordWidth : Nat) : Nat := 2 * wordWidth + 7

def variableLayout (wordWidth : Nat) : Layout :=
  [wordWidth, wordWidth, 1, 1, 1, 1]

def variableWiring (wordWidth : Nat) : Wiring :=
  [sourceOffset wordWidth, targetOffset, carryInWire wordWidth,
    reductionWire wordWidth, controlWire wordWidth, scratchWire wordWidth]

def variableAddGates (wordWidth : Nat) : List RGate :=
  (controlledCarryCircuit wordWidth).gates.map
    (RGate.map (place (variableLayout wordWidth) (variableWiring wordWidth)))

theorem variableLayout_width (wordWidth : Nat) :
    (variableLayout wordWidth).width = 2 * wordWidth + 4 := by
  simp [variableLayout, Layout.width]
  omega

theorem variableWiring_disjoint (wordWidth : Nat) :
    Wiring.Disjoint (variableLayout wordWidth) (variableWiring wordWidth) := by
  intro j k hj hk hne
  simp [variableWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [sourceOffset, targetOffset, carryInWire, reductionWire,
      controlWire, scratchWire, variableLayout, variableWiring,
      Layout.size] <;> omega

theorem variableAddGates_wellFormed {wordWidth : Nat}
    (hwidth : 0 < wordWidth) :
    (variableAddGates wordWidth).all
      (RGate.wellFormed (width wordWidth)) = true := by
  apply wellFormed_placeGates
    (variableWiring_disjoint wordWidth)
  · simp [variableLayout, variableWiring]
  · intro j hj
    simp [variableLayout] at hj
    interval_cases j <;>
      simp [variableWiring, width, sourceOffset, targetOffset,
        carryInWire, reductionWire, controlWire, scratchWire,
        variableLayout, Layout.size] <;> omega
  · intro gate hgate
    have hwf := controlledCarryCircuit_wellFormed hwidth
    have hlocalWidth : (controlledCarryCircuit wordWidth).width =
        (variableLayout wordWidth).width := by
      simp [controlledCarryCircuit, Reversible.control,
        Adder.carryCircuit, variableLayout, Layout.width]
      omega
    rw [← hlocalWidth]
    exact List.all_eq_true.mp
      (by simpa [RCircuit.wellFormed] using hwf) gate hgate

def selectedSource (wordWidth i : Nat) : Nat :=
  if i.testBit (controlWire wordWidth) then
    readField i (sourceOffset wordWidth) wordWidth
  else 0

theorem reconstructedPrefix_eq
    {original constant wordWidth result count : Nat}
    (hstate : CarryReconstructedState original constant wordWidth result)
    (hcount : count ≤ wordWidth) :
    readField result 0 count + 2 ^ count * addCarry constant original count =
      readField original 0 count + readField constant 0 count := by
  induction count with
  | zero => simp [readField_size_zero, addCarry]
  | succ bit ih =>
      have hbit : bit < wordWidth := by omega
      have ih' := ih (by omega)
      let sumBit := bitValue original bit + bitValue constant bit +
        addCarry constant original bit
      have hdivision : sumBit % 2 + 2 * (sumBit / 2) = sumBit := by
        exact Nat.mod_add_div sumBit 2
      have hresultBit : bitValue result bit = sumBit % 2 := by
        simpa [targetWire, sumBit] using hstate.2.1 bit hbit
      rw [readField_high, readField_high, readField_high,
        Nat.zero_add, hresultBit]
      change
        readField result 0 bit + 2 ^ bit * (sumBit % 2) +
            2 ^ (bit + 1) * (sumBit / 2) =
          readField original 0 bit + 2 ^ bit * bitValue original bit +
            (readField constant 0 bit + 2 ^ bit * bitValue constant bit)
      rw [Nat.pow_succ]
      calc
        readField result 0 bit + 2 ^ bit * (sumBit % 2) +
              (2 ^ bit * 2) * (sumBit / 2) =
            readField result 0 bit +
              2 ^ bit * (sumBit % 2 + 2 * (sumBit / 2)) := by ring
        _ = readField result 0 bit + 2 ^ bit * sumBit := by rw [hdivision]
        _ = (readField result 0 bit +
              2 ^ bit * addCarry constant original bit) +
              2 ^ bit * bitValue original bit +
              2 ^ bit * bitValue constant bit := by
            simp only [sumBit]
            ring
        _ = (readField original 0 bit + readField constant 0 bit) +
              2 ^ bit * bitValue original bit +
              2 ^ bit * bitValue constant bit := by rw [ih']
        _ = readField original 0 bit + 2 ^ bit * bitValue original bit +
              (readField constant 0 bit +
                2 ^ bit * bitValue constant bit) := by ring

theorem reconstructedTarget_eq
    {original constant wordWidth result : Nat}
    (hstate : CarryReconstructedState original constant wordWidth result) :
    readField result 0 wordWidth =
      (readField original 0 wordWidth +
        readField constant 0 wordWidth) % 2 ^ wordWidth := by
  have hprefix := reconstructedPrefix_eq hstate (Nat.le_refl wordWidth)
  have hmod := congrArg (fun value => value % 2 ^ wordWidth) hprefix
  simpa [Nat.add_mod, Nat.mul_mod,
    Nat.mod_eq_of_lt (readField_lt result 0 wordWidth)] using hmod

theorem reconstructedState_eq
    {original constant wordWidth result : Nat}
    (hstate : CarryReconstructedState original constant wordWidth result)
    (horiginal : original < 2 ^ adderWidth wordWidth)
    (hresult : result < 2 ^ adderWidth wordWidth)
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0) :
    result = writeField original 0 wordWidth
      ((readField original 0 wordWidth +
        readField constant 0 wordWidth) % 2 ^ wordWidth) := by
  have hwidth := hstate.1
  have hsucc : wordWidth - 1 + 1 = wordWidth := by omega
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases htarget : q < wordWidth
  · have hread := congrArg (fun value => value.testBit q)
      (reconstructedTarget_eq hstate)
    rw [testBit_writeField_inside (off := 0) (n := wordWidth)
      (Nat.zero_le q) (by omega)]
    simpa [testBit_readField, htarget, Nat.testBit_mod_two_pow] using hread
  · by_cases hdirty : q < 2 * wordWidth
    · have hbit : q - wordWidth < wordWidth := by omega
      rw [testBit_writeField_outside (Or.inr (by omega))]
      apply testBit_eq_of_bitValue_eq
      simpa [dirtyWire, show wordWidth + (q - wordWidth) = q by omega] using
        hstate.2.2.1 (q - wordWidth) hbit
    · by_cases hlocal : q < adderWidth wordWidth
      · have hq : q = 2 * wordWidth ∨ q = 2 * wordWidth + 1 ∨
            q = 2 * wordWidth + 2 := by
          simp [adderWidth] at hlocal
          omega
        rw [testBit_writeField_outside (Or.inr (by omega))]
        apply testBit_eq_of_bitValue_eq
        rcases hq with rfl | rfl | rfl
        · rcases Nat.mod_two_eq_zero_or_one (wordWidth - 1) with hmod | hmod
          · have hresultZero := hstate.2.2.2.1
            have horiginalZero := hcarry
            simpa [carryWire, hmod] using hresultZero.trans horiginalZero.symm
          · have hresultZero := hstate.2.2.2.2.1
            have horiginalZero := hcarry
            have hwordMod : wordWidth % 2 = 0 := by
              calc
                wordWidth % 2 = ((wordWidth - 1) + 1) % 2 := by
                  congr 1
                  omega
                _ = 0 := by simp [Nat.add_mod, hmod]
            simpa [spareWire, carryWire, hmod, hwordMod, hsucc] using
              hresultZero.trans horiginalZero.symm
        · rcases Nat.mod_two_eq_zero_or_one (wordWidth - 1) with hmod | hmod
          · have hresultZero := hstate.2.2.2.2.1
            have horiginalZero := hspare
            have hwordMod : wordWidth % 2 = 1 := by
              calc
                wordWidth % 2 = ((wordWidth - 1) + 1) % 2 := by
                  congr 1
                  omega
                _ = 1 := by simp [Nat.add_mod, hmod]
            simpa [spareWire, carryWire, hmod, hwordMod, hsucc] using
              hresultZero.trans horiginalZero.symm
          · have hresultZero := hstate.2.2.2.1
            have horiginalZero := hspare
            simpa [spareWire, carryWire, hmod] using
              hresultZero.trans horiginalZero.symm
        · have hresultZero := hstate.2.2.2.2.2
          have horiginalZero := hancilla
          simpa [ancillaWire] using hresultZero.trans horiginalZero.symm
      · have hpow : 2 ^ adderWidth wordWidth ≤ 2 ^ q :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (hresult.trans_le hpow),
          testBit_writeField_outside (Or.inr (by omega)),
          Nat.testBit_lt_two_pow (horiginal.trans_le hpow)]

theorem reconstructedControlledState_eq
    {original constant wordWidth result : Nat}
    (hstate : CarryReconstructedState original constant wordWidth result)
    (horiginal : original < 2 ^ (2 * wordWidth + 4))
    (hresult : result < 2 ^ (2 * wordWidth + 4))
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0)
    (hcontrol : bitValue result (constantControlWire wordWidth) =
      bitValue original (constantControlWire wordWidth)) :
    result = writeField original 0 wordWidth
      ((readField original 0 wordWidth +
        readField constant 0 wordWidth) % 2 ^ wordWidth) := by
  have hwidth := hstate.1
  have hsucc : wordWidth - 1 + 1 = wordWidth := by omega
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases htarget : q < wordWidth
  · have hread := congrArg (fun value => value.testBit q)
      (reconstructedTarget_eq hstate)
    rw [testBit_writeField_inside (off := 0) (n := wordWidth)
      (Nat.zero_le q) (by omega)]
    simpa [testBit_readField, htarget, Nat.testBit_mod_two_pow] using hread
  · by_cases hdirty : q < 2 * wordWidth
    · have hbit : q - wordWidth < wordWidth := by omega
      rw [testBit_writeField_outside (Or.inr (by omega))]
      apply testBit_eq_of_bitValue_eq
      simpa [dirtyWire, show wordWidth + (q - wordWidth) = q by omega] using
        hstate.2.2.1 (q - wordWidth) hbit
    · by_cases hwork : q < constantControlWire wordWidth
      · have hq : q = 2 * wordWidth ∨ q = 2 * wordWidth + 1 ∨
            q = 2 * wordWidth + 2 := by
          simp [constantControlWire, adderWidth] at hwork
          omega
        rw [testBit_writeField_outside (Or.inr (by omega))]
        apply testBit_eq_of_bitValue_eq
        rcases hq with rfl | rfl | rfl
        · rcases Nat.mod_two_eq_zero_or_one (wordWidth - 1) with hmod | hmod
          · simpa [carryWire, hmod] using
              hstate.2.2.2.1.trans hcarry.symm
          · have hwordMod : wordWidth % 2 = 0 := by
              calc
                wordWidth % 2 = ((wordWidth - 1) + 1) % 2 := by
                  congr 1
                  omega
                _ = 0 := by simp [Nat.add_mod, hmod]
            simpa [spareWire, carryWire, hmod, hwordMod, hsucc] using
              hstate.2.2.2.2.1.trans hcarry.symm
        · rcases Nat.mod_two_eq_zero_or_one (wordWidth - 1) with hmod | hmod
          · have hwordMod : wordWidth % 2 = 1 := by
              calc
                wordWidth % 2 = ((wordWidth - 1) + 1) % 2 := by
                  congr 1
                  omega
                _ = 1 := by simp [Nat.add_mod, hmod]
            simpa [spareWire, carryWire, hmod, hwordMod, hsucc] using
              hstate.2.2.2.2.1.trans hspare.symm
          · simpa [spareWire, carryWire, hmod] using
              hstate.2.2.2.1.trans hspare.symm
        · simpa [ancillaWire] using hstate.2.2.2.2.2.trans hancilla.symm
      · by_cases hcontrolWire : q = constantControlWire wordWidth
        · subst q
          rw [testBit_writeField_outside (Or.inr (by
            simp [constantControlWire, adderWidth]
            omega))]
          exact testBit_eq_of_bitValue_eq hcontrol
        · have hhigh : 2 * wordWidth + 4 ≤ q := by
            have hgt : constantControlWire wordWidth < q := by omega
            simp [constantControlWire, adderWidth] at hgt
            omega
          have hpow : 2 ^ (2 * wordWidth + 4) ≤ 2 ^ q :=
            Nat.pow_le_pow_right (by omega) hhigh
          rw [Nat.testBit_lt_two_pow (hresult.trans_le hpow),
            testBit_writeField_outside (Or.inr (by omega)),
            Nat.testBit_lt_two_pow (horiginal.trans_le hpow)]

theorem copiedIndex_lt {value dirty i totalWidth : Nat}
    (hdirty : dirty < totalWidth) (hi : i < 2 ^ totalWidth) :
    copiedIndex value dirty i < 2 ^ totalWidth := by
  unfold copiedIndex
  split
  · apply Nat.xor_lt_two_pow hi
    simpa [Nat.one_shiftLeft] using
      Nat.pow_lt_pow_of_lt (by omega : 1 < 2) hdirty
  · exact hi

theorem outputIndex_lt {value dirty i totalWidth : Nat}
    (hvalue : value < totalWidth) (hdirty : dirty < totalWidth)
    (hi : i < 2 ^ totalWidth) :
    outputIndex value dirty i < 2 ^ totalWidth := by
  exact Lookup3.writeBit_lt hvalue (copiedIndex_lt hdirty hi)

theorem carryStepOut_lt {constant wordWidth bit i : Nat}
    (hbit : bit < wordWidth) (hi : i < 2 ^ adderWidth wordWidth) :
    carryStepOut constant wordWidth bit i < 2 ^ adderWidth wordWidth := by
  have hgates : ∀ gate ∈ carryStepGates constant wordWidth bit,
      gate.wellFormed (adderWidth wordWidth) = true :=
    List.all_eq_true.mp (carryStepGates_wellFormed hbit)
  have hj := actGates_lt hgates hi
  simp only [carryStepOut]
  split
  · exact hj
  · exact outputIndex_lt (carryWire_lt wordWidth bit)
      (by simp [dirtyWire, adderWidth]; omega) hj

theorem carryPrefixOut_lt {constant wordWidth count i : Nat}
    (hcount : count ≤ wordWidth) (hi : i < 2 ^ adderWidth wordWidth) :
    carryPrefixOut constant wordWidth count i < 2 ^ adderWidth wordWidth := by
  induction count generalizing i with
  | zero => exact hi
  | succ count ih =>
      exact carryStepOut_lt (by omega) (ih (by omega) hi)

theorem carryTopOut_lt {constant wordWidth i : Nat}
    (hwidth : 2 ≤ wordWidth) (hi : i < 2 ^ adderWidth wordWidth) :
    carryTopOut constant wordWidth i < 2 ^ adderWidth wordWidth := by
  have hgates : ∀ gate ∈ carryTopGates constant wordWidth,
      gate.wellFormed (adderWidth wordWidth) = true :=
    List.all_eq_true.mp (carryTopGates_wellFormed hwidth)
  have hj := actGates_lt hgates hi
  exact outputIndex_lt (carryWire_lt wordWidth (wordWidth - 1))
    (by simp [dirtyWire, adderWidth]; omega) hj

theorem carryChainOut_lt {constant wordWidth i : Nat}
    (hwidth : 2 ≤ wordWidth) (hi : i < 2 ^ adderWidth wordWidth) :
    carryChainOut constant wordWidth i < 2 ^ adderWidth wordWidth := by
  exact carryTopOut_lt hwidth
    (carryPrefixOut_lt (by omega) hi)

theorem constantAddOps_reconstructed
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (adderWidth wordWidth)
      (constantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    let chainOut := carryChainOut constant wordWidth original
    let result := actGates (carryReconstructionGates constant wordWidth) chainOut
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (wordWidth - 1) •
        basis result ∧
      CarryReconstructedState original constant wordWidth result := by
  refine ⟨constantAddOps_mask hl hwidth hcarry hspare hancilla rec creg hb, ?_⟩
  exact carryReconstructionGates_state
    (carryChainOut_state hwidth hcarry hspare hancilla)

theorem constantAddOps_exact
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (horiginal : original < 2 ^ adderWidth wordWidth)
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (adderWidth wordWidth)
      (constantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (wordWidth - 1) •
      basis (writeField original 0 wordWidth
        ((readField original 0 wordWidth +
          readField constant 0 wordWidth) % 2 ^ wordWidth)) := by
  obtain ⟨hmask, hstate⟩ := constantAddOps_reconstructed
    hl hwidth hcarry hspare hancilla rec creg hb
  let chainOut := carryChainOut constant wordWidth original
  let result := actGates (carryReconstructionGates constant wordWidth) chainOut
  have hchainOut : chainOut < 2 ^ adderWidth wordWidth :=
    carryChainOut_lt hwidth horiginal
  have hresult : result < 2 ^ adderWidth wordWidth := by
    apply actGates_lt _ hchainOut
    exact List.all_eq_true.mp (carryReconstructionGates_wellFormed hwidth)
  rw [hmask, reconstructedState_eq hstate horiginal hresult
    hcarry hspare hancilla]

theorem replaceBits_id_writeField_sourceIndex
    {localWidth fieldWidth original value : Nat}
    (hfit : fieldWidth ≤ localWidth) :
    replaceBits id localWidth
        (writeField (sourceIndex id localWidth original) 0 fieldWidth value)
        original =
      writeField original 0 fieldWidth value := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hlocal : q < localWidth
  · have hreplace := testBit_replaceBits (f := id)
      (source := writeField (sourceIndex id localWidth original) 0 fieldWidth value)
      (ambient := original) hlocal (by
        intro x y _ _ hxy
        exact hxy)
    simp only [id_eq] at hreplace
    rw [hreplace]
    by_cases hfield : q < fieldWidth
    · rw [testBit_writeField_inside (Nat.zero_le q) (by omega),
        testBit_writeField_inside (Nat.zero_le q) (by omega)]
    · rw [testBit_writeField_outside (Or.inr (by omega)),
        testBit_writeField_outside (Or.inr (by omega)),
        testBit_sourceIndex hlocal]
      simp only [id_eq]
  · rw [testBit_replaceBits_outside (by
        intro q' hq' heq
        simp only [id_eq] at heq
        omega),
      testBit_writeField_outside (Or.inr (by omega))]

theorem replaceBits_writeField_sourceIndex
    {f : Nat → Nat} {localWidth fieldWidth original value : Nat}
    (hinj : ∀ x y, x < localWidth → y < localWidth → f x = f y → x = y)
    (hfield : ∀ q, q < fieldWidth → f q = q)
    (hfit : fieldWidth ≤ localWidth) :
    replaceBits f localWidth
        (writeField (sourceIndex f localWidth original) 0 fieldWidth value)
        original =
      writeField original 0 fieldWidth value := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases himage : ∃ r, r < localWidth ∧ f r = q
  · obtain ⟨r, hr, rfl⟩ := himage
    rw [testBit_replaceBits hr hinj]
    by_cases hrfield : r < fieldWidth
    · rw [testBit_writeField_inside (Nat.zero_le r) (by omega),
        hfield r hrfield,
        testBit_writeField_inside (Nat.zero_le r) (by omega)]
    · have houtside : fieldWidth ≤ f r := by
        by_contra hlt
        have hfr : f r < fieldWidth := by omega
        have hf := hfield (f r) hfr
        have hre : r = f r := hinj r (f r) hr
          (hfr.trans_le hfit) hf.symm
        rw [hre] at hrfield
        exact hrfield hfr
      rw [testBit_writeField_outside (Or.inr (by omega)),
        testBit_sourceIndex hr,
        testBit_writeField_outside (Or.inr (by omega))]
  · rw [testBit_replaceBits_outside (by
        intro r hr heq
        exact himage ⟨r, hr, heq.symm⟩)]
    by_cases hq : q < fieldWidth
    · exact (himage ⟨q, hq.trans_le hfit, hfield q hq⟩).elim
    · rw [testBit_writeField_outside (Or.inr (by omega))]

def widenedConstantAddOps (constant wordWidth : Nat) : List Op :=
  Op.relabelAll id (constantAddOps constant (wordWidth + 1))

theorem widenedConstantAddOps_exact
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 1 ≤ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hspare : bitValue original (carryOutWire wordWidth) = 0)
    (hancilla : bitValue original (scratchWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (widenedConstantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ wordWidth •
      basis (writeField original 0 (wordWidth + 1)
        ((readField original 0 (wordWidth + 1) +
          readField constant 0 (wordWidth + 1)) % 2 ^ (wordWidth + 1))) := by
  let localWidth := adderWidth (wordWidth + 1)
  let localOriginal := sourceIndex id localWidth original
  have hlocalCarry : bitValue localOriginal
      (carryWire (wordWidth + 1) 0) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by
      simp [localWidth, adderWidth, carryWire])]
    have hc := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hcarry
    simpa only [id_eq, carryWire, carryInWire, Nat.mul_add, Nat.mul_one,
      Nat.add_zero] using hc
  have hlocalSpare : bitValue localOriginal
      (spareWire (wordWidth + 1) 0) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by
      simp [localWidth, adderWidth, spareWire, carryWire])]
    have hs := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hspare
    simpa only [id_eq, spareWire, carryWire, carryOutWire, Nat.mul_add,
      Nat.mul_one, Nat.add_zero, Nat.one_mod] using hs
  have hlocalAncilla : bitValue localOriginal
      (ancillaWire (wordWidth + 1)) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by
      simp [localWidth, adderWidth, ancillaWire])]
    have ha := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hancilla
    simpa only [id_eq, ancillaWire, scratchWire, Nat.mul_add, Nat.mul_one,
      Nat.add_zero] using ha
  have hrun := runOps_relabel
    (level := level) (width := localWidth) (totalWidth := width wordWidth)
    (inputBits := 0) (cbits := wordWidth) (f := id) (ambient := original)
    (ops := constantAddOps constant (wordWidth + 1))
    (b := Branch.mk rec creg (basis localOriginal) input)
    (by
      intro q hq
      simp [localWidth, adderWidth, width] at hq ⊢
      omega)
    (by
      intro x y _ _ hxy
      exact hxy)
    (constantAddOps_wellFormed hl (by omega))
    (wfVec_basis (sourceIndex_lt id localWidth original))
  rw [placeBranch_sourceIndex_basis (d := deg level)
    (by
      intro x y _ _ hxy
      exact hxy) rec creg input] at hrun
  change runOps level (width wordWidth)
      (widenedConstantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input) = _ at hrun
  rw [hrun] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := List.mem_map.mp hb
  have hlocal := constantAddOps_exact hl (by omega)
    (sourceIndex_lt id localWidth original)
    hlocalCarry hlocalSpare hlocalAncilla rec creg hlocalBranch
  let localResult := writeField localOriginal 0 (wordWidth + 1)
    ((readField localOriginal 0 (wordWidth + 1) +
      readField constant 0 (wordWidth + 1)) % 2 ^ (wordWidth + 1))
  have hlocalResult : localResult < 2 ^ localWidth := by
    exact writeField_lt (by simp [localWidth, adderWidth]; omega)
      (sourceIndex_lt id localWidth original)
  change placeVec id localWidth original localBranch.state = _
  rw [hlocal, placeVec_smul, placeVec_basis hlocalResult]
  have hread : readField localOriginal 0 (wordWidth + 1) =
      readField original 0 (wordWidth + 1) := by
    exact readField_sourceIndex (by simp [localWidth, adderWidth]; omega)
      (by simp)
  rw [show localResult = writeField localOriginal 0 (wordWidth + 1)
        ((readField original 0 (wordWidth + 1) +
          readField constant 0 (wordWidth + 1)) % 2 ^ (wordWidth + 1)) by
      simp only [localResult, hread],
    replaceBits_id_writeField_sourceIndex
      (localWidth := localWidth) (by simp [localWidth, adderWidth]; omega)]
  rfl

theorem controlledConstantAddOps_target
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * wordWidth + 4)
      (controlledConstantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    let result :=
      actGates (controlledCarryReconstructionGates constant wordWidth)
        (controlledCarryChainOut constant wordWidth original)
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (wordWidth - 1) •
        basis result ∧
      readField result 0 wordWidth =
        (readField original 0 wordWidth +
          readField
            (selectedConstant constant
              (constantControlWire wordWidth) original)
            0 wordWidth) % 2 ^ wordWidth := by
  obtain ⟨hmask, hstate⟩ := controlledConstantAddOps_reconstructed
    hl hwidth hcarry hspare hancilla rec creg hb
  exact ⟨hmask, reconstructedTarget_eq hstate⟩

theorem controlledCarryStepOut_lt {constant wordWidth bit i : Nat}
    (hbit : bit < wordWidth) (hi : i < 2 ^ (2 * wordWidth + 4)) :
    controlledCarryStepOut constant wordWidth bit i <
      2 ^ (2 * wordWidth + 4) := by
  have hgates : ∀ gate ∈ controlledCarryStepGates constant wordWidth bit,
      gate.wellFormed (2 * wordWidth + 4) = true :=
    List.all_eq_true.mp (controlledCarryStepGates_wellFormed hbit)
  have hj := actGates_lt hgates hi
  simp only [controlledCarryStepOut]
  split
  · exact hj
  · exact outputIndex_lt (by simp [carryWire]; omega)
      (by simp [dirtyWire]; omega) hj

theorem controlledCarryPrefixOut_lt {constant wordWidth count i : Nat}
    (hcount : count ≤ wordWidth) (hi : i < 2 ^ (2 * wordWidth + 4)) :
    controlledCarryPrefixOut constant wordWidth count i <
      2 ^ (2 * wordWidth + 4) := by
  induction count generalizing i with
  | zero => exact hi
  | succ count ih =>
      exact controlledCarryStepOut_lt (by omega) (ih (by omega) hi)

theorem controlledCarryTopOut_lt {constant wordWidth i : Nat}
    (hwidth : 2 ≤ wordWidth) (hi : i < 2 ^ (2 * wordWidth + 4)) :
    controlledCarryTopOut constant wordWidth i <
      2 ^ (2 * wordWidth + 4) := by
  have hgates : ∀ gate ∈ controlledCarryTopGates constant wordWidth,
      gate.wellFormed (2 * wordWidth + 4) = true :=
    List.all_eq_true.mp (controlledCarryTopGates_wellFormed hwidth)
  have hj := actGates_lt hgates hi
  exact outputIndex_lt (by simp [carryWire]; omega)
    (by simp [dirtyWire]; omega) hj

theorem controlledCarryChainOut_lt {constant wordWidth i : Nat}
    (hwidth : 2 ≤ wordWidth) (hi : i < 2 ^ (2 * wordWidth + 4)) :
    controlledCarryChainOut constant wordWidth i <
      2 ^ (2 * wordWidth + 4) := by
  exact controlledCarryTopOut_lt hwidth
    (controlledCarryPrefixOut_lt (by omega) hi)

theorem controlledConstantAddOps_exact
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (horiginal : original < 2 ^ (2 * wordWidth + 4))
    (hcarry : bitValue original (carryWire wordWidth 0) = 0)
    (hspare : bitValue original (spareWire wordWidth 0) = 0)
    (hancilla : bitValue original (ancillaWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * wordWidth + 4)
      (controlledConstantAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (wordWidth - 1) •
      basis (writeField original 0 wordWidth
        ((readField original 0 wordWidth +
          readField
            (selectedConstant constant (constantControlWire wordWidth) original)
            0 wordWidth) % 2 ^ wordWidth)) := by
  obtain ⟨hmask, hstate⟩ := controlledConstantAddOps_reconstructed
    hl hwidth hcarry hspare hancilla rec creg hb
  let chainOut := controlledCarryChainOut constant wordWidth original
  let result := actGates
    (controlledCarryReconstructionGates constant wordWidth) chainOut
  have hchainOut : chainOut < 2 ^ (2 * wordWidth + 4) :=
    controlledCarryChainOut_lt hwidth horiginal
  have hresult : result < 2 ^ (2 * wordWidth + 4) := by
    apply actGates_lt _ hchainOut
    exact List.all_eq_true.mp
      (controlledCarryReconstructionGates_wellFormed hwidth)
  have hcontrol : bitValue result (constantControlWire wordWidth) =
      bitValue original (constantControlWire wordWidth) := by
    unfold bitValue
    rw [show result = actGates
        (controlledCarryReconstructionGates constant wordWidth) chainOut by rfl,
      controlledCarryReconstructionGates_act hwidth]
    have houtside := testBit_actGates_of_outside
      (gs := carryReconstructionGates
        (selectedConstant constant (constantControlWire wordWidth) chainOut)
        wordWidth)
      (b := constantControlWire wordWidth)
      (fun gate hgate hwire => by
        have hwf := List.all_eq_true.mp
          (carryReconstructionGates_wellFormed hwidth) gate hgate
        have hlt := wire_lt_of_wellFormed hwf hwire
        simp [constantControlWire] at hlt)
      chainOut
    rw [houtside, controlledCarryChainOut_control hwidth]
  rw [hmask, reconstructedControlledState_eq hstate horiginal hresult
    hcarry hspare hancilla hcontrol]

theorem variableAddGates_act {wordWidth i : Nat}
    (hwidth : 0 < wordWidth)
    (hcarryIn : bitValue i (carryInWire wordWidth) = 0)
    (hscratch : bitValue i (scratchWire wordWidth) = 0) :
    actGates (variableAddGates wordWidth) i =
      writeField
        (writeField i (targetOffset) wordWidth
          ((selectedSource wordWidth i + readField i targetOffset wordWidth) %
            2 ^ wordWidth))
        (reductionWire wordWidth) 1
          ((bitValue i (reductionWire wordWidth) +
            (selectedSource wordWidth i +
              readField i targetOffset wordWidth) / 2 ^ wordWidth) % 2) := by
  let L := variableLayout wordWidth
  let W := variableWiring wordWidth
  let gathered := gatherBits (place L W) L.width i
  have hsource : readField gathered 0 wordWidth =
      readField i (sourceOffset wordWidth) wordWidth := by
    simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
      Layout.size] using readField_gatherBits L W 0 i (by simp [W, variableWiring])
  have htarget : readField gathered wordWidth wordWidth =
      readField i targetOffset wordWidth := by
    simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
      Layout.size] using readField_gatherBits L W 1 i (by simp [W, variableWiring])
  have hcarry : bitValue gathered (2 * wordWidth) =
      bitValue i (carryInWire wordWidth) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 2 i (by simp [W, variableWiring])
  have hout : bitValue gathered (2 * wordWidth + 1) =
      bitValue i (reductionWire wordWidth) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 3 i (by simp [W, variableWiring])
  have hcontrol : gathered.testBit (2 * wordWidth + 2) =
      i.testBit (controlWire wordWidth) := by
    apply testBit_eq_of_bitValue_eq
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 4 i (by simp [W, variableWiring])
  have hlocalScratch : gathered.testBit (2 * wordWidth + 3) = false := by
    have hs := readField_gatherBits L W 5 i (by simp [W, variableWiring])
    have hsvalue : bitValue gathered (2 * wordWidth + 3) =
        bitValue i (scratchWire wordWidth) := by
      rw [← readField_one, ← readField_one]
      simpa [gathered, L, W, variableLayout, variableWiring, Layout.offset,
        Layout.size, two_mul, Nat.add_assoc] using hs
    exact (testBit_eq_false_iff_bitValue_eq_zero gathered
      (2 * wordWidth + 3)).mpr (by rw [hsvalue, hscratch])
  have hlocal := controlledCarryCircuit_act hwidth hlocalScratch
  apply actGates_placed_write₂
    (L := L) (W := W) (k₁ := 1) (k₂ := 3)
    (variableWiring_disjoint wordWidth)
    (by simp [L, W, variableLayout, variableWiring])
    (by simp [L, variableLayout])
    (by simp [L, variableLayout])
    (by decide)
    (fun gate hgate => List.all_eq_true.mp
      (by
        have hwf := controlledCarryCircuit_wellFormed hwidth
        have hlocalWidth : (controlledCarryCircuit wordWidth).width =
            L.width := by
          simp [L, controlledCarryCircuit, Reversible.control,
            Adder.carryCircuit, variableLayout, Layout.width]
          omega
        rw [← hlocalWidth]
        simpa [RCircuit.wellFormed] using hwf) gate hgate)
  change act (controlledCarryCircuit wordWidth) gathered = _
  rw [hlocal, hcontrol]
  by_cases hc : i.testBit (controlWire wordWidth) = true
  · rw [if_pos hc]
    simp only [Layout.write, L, variableLayout, Layout.offset, Layout.size]
    rw [hsource, htarget, hcarry, hout, hcarryIn]
    simp [selectedSource, hc, two_mul, Nat.add_assoc]
    rfl
  · have hc' : i.testBit (controlWire wordWidth) = false :=
      Bool.eq_false_iff.mpr hc
    rw [if_neg hc]
    simp only [Layout.write, L, variableLayout, Layout.offset, Layout.size]
    simp only [selectedSource, hc', Bool.false_eq_true, if_false, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (readField_lt i targetOffset wordWidth),
      Nat.div_eq_of_lt (readField_lt i targetOffset wordWidth)]
    simp only [Nat.add_zero]
    change gathered = writeField
      (writeField gathered wordWidth wordWidth
        (readField i targetOffset wordWidth))
      (wordWidth + (wordWidth + 1)) 1
        (bitValue i (reductionWire wordWidth) % 2)
    rw [← htarget, writeField_read]
    rw [Nat.mod_eq_of_lt (bitValue_lt i (reductionWire wordWidth)),
      ← hout, ← readField_one]
    have hoff : wordWidth + (wordWidth + 1) = 2 * wordWidth + 1 := by omega
    rw [hoff, writeField_read]

def compareLayout (wordWidth : Nat) : Layout := [wordWidth, wordWidth, 1, 1]

def compareWiring (wordWidth : Nat) : Wiring :=
  [sourceOffset wordWidth, targetOffset, carryInWire wordWidth,
    scratchWire wordWidth]

def compareComputeGates (wordWidth : Nat) : List RGate :=
  (Adder.carryGates wordWidth).reverse.map
    (RGate.map (place (compareLayout wordWidth) (compareWiring wordWidth)))

def flagEraseGates (wordWidth : Nat) : List RGate :=
  let compute := compareComputeGates wordWidth
  compute ++
    [.ccx (controlWire wordWidth) (scratchWire wordWidth)
      (reductionWire wordWidth)] ++
    compute.reverse

theorem compareLayout_width (wordWidth : Nat) :
    (compareLayout wordWidth).width = 2 * wordWidth + 2 := by
  simp [compareLayout, Layout.width]
  omega

theorem compareWiring_disjoint (wordWidth : Nat) :
    Wiring.Disjoint (compareLayout wordWidth) (compareWiring wordWidth) := by
  intro j k hj hk hne
  simp [compareWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [sourceOffset, targetOffset, carryInWire, scratchWire,
      compareLayout, compareWiring, Layout.size] <;> omega

theorem compareComputeGates_wellFormed {wordWidth : Nat}
    (hwidth : 0 < wordWidth) :
    (compareComputeGates wordWidth).all
      (RGate.wellFormed (width wordWidth)) = true := by
  apply wellFormed_placeGates
    (compareWiring_disjoint wordWidth)
  · simp [compareLayout, compareWiring]
  · intro j hj
    simp [compareLayout] at hj
    interval_cases j <;>
      simp [compareWiring, width, sourceOffset, targetOffset,
        carryInWire, scratchWire, compareLayout, Layout.size] <;> omega
  · intro gate hgate
    have hwf := Adder.carryCircuit_wellFormed hwidth
    have hlocalWidth : (Adder.carryCircuit wordWidth).width =
        (compareLayout wordWidth).width := by
      simp [Adder.carryCircuit, compareLayout, Layout.width]
      omega
    rw [← hlocalWidth]
    exact List.all_eq_true.mp
      (by simpa [RCircuit.wellFormed, Adder.carryCircuit] using hwf) gate
        (List.mem_reverse.mp hgate)

theorem compareComputeGates_avoids_reduction {wordWidth : Nat}
    (hwidth : 0 < wordWidth) :
    ∀ gate ∈ compareComputeGates wordWidth, ∀ q ∈ gate.wires,
      q < reductionWire wordWidth ∨ reductionWire wordWidth + 1 ≤ q := by
  apply placeGates_avoids
  · simp [compareLayout, compareWiring]
  · intro gate hgate
    have hwf := Adder.carryCircuit_wellFormed hwidth
    have hlocalWidth : (Adder.carryCircuit wordWidth).width =
        (compareLayout wordWidth).width := by
      simp [Adder.carryCircuit, compareLayout, Layout.width]
      omega
    rw [← hlocalWidth]
    exact List.all_eq_true.mp
      (by simpa [RCircuit.wellFormed, Adder.carryCircuit] using hwf) gate
        (List.mem_reverse.mp hgate)
  · intro j hj
    simp [compareLayout] at hj
    interval_cases j <;>
      simp [compareWiring, reductionWire, sourceOffset, targetOffset,
        carryInWire, scratchWire, compareLayout, Layout.size] <;> omega

theorem compareComputeGates_scratch {wordWidth i : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue i (carryInWire wordWidth) = 0)
    (hscratch : bitValue i (scratchWire wordWidth) = 0) :
    bitValue (actGates (compareComputeGates wordWidth) i)
        (scratchWire wordWidth) =
      Adder.borrow
        (readField i (sourceOffset wordWidth) wordWidth)
        (readField i targetOffset wordWidth) := by
  let L := compareLayout wordWidth
  let W := compareWiring wordWidth
  let gathered := gatherBits (place L W) L.width i
  have hsource : readField gathered 0 wordWidth =
      readField i (sourceOffset wordWidth) wordWidth := by
    simpa [gathered, L, W, compareLayout, compareWiring, Layout.offset,
      Layout.size] using readField_gatherBits L W 0 i
        (by simp [W, compareWiring])
  have htarget : readField gathered wordWidth wordWidth =
      readField i targetOffset wordWidth := by
    simpa [gathered, L, W, compareLayout, compareWiring, Layout.offset,
      Layout.size] using readField_gatherBits L W 1 i
        (by simp [W, compareWiring])
  have hlocalCarry : bitValue gathered (2 * wordWidth) = 0 := by
    calc
      bitValue gathered (2 * wordWidth) =
          bitValue i (carryInWire wordWidth) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, W, compareLayout, compareWiring, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 2 i (by simp [W, compareWiring])
      _ = 0 := hcarry
  have hlocalScratch : bitValue gathered (2 * wordWidth + 1) = 0 := by
    calc
      bitValue gathered (2 * wordWidth + 1) =
          bitValue i (scratchWire wordWidth) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, W, compareLayout, compareWiring, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 3 i (by simp [W, compareWiring])
      _ = 0 := hscratch
  have hlocal := Adder.carryGates_reverse_act hwidth hlocalCarry
  rw [← readField_one]
  have hplaced := readField_actGates_placed
    (gs := (Adder.carryGates wordWidth).reverse) (L := L) (W := W)
    (k := 3) (q := 0) (len := 1) (I := i)
    (compareWiring_disjoint wordWidth)
    (by simp [L, W, compareLayout, compareWiring])
    (by simp [L, compareLayout])
    (fun gate hgate => List.all_eq_true.mp
      (by
        have hwf := Adder.carryCircuit_wellFormed hwidth
        have hlocalWidth : (Adder.carryCircuit wordWidth).width = L.width := by
          simp [L, Adder.carryCircuit, compareLayout, Layout.width]
          omega
        rw [← hlocalWidth]
        simpa [RCircuit.wellFormed, Adder.carryCircuit] using hwf) gate
          (List.mem_reverse.mp hgate))
    (by simp [L, compareLayout, Layout.size])
  have hplaced' :
      readField (actGates (compareComputeGates wordWidth) i)
          (scratchWire wordWidth) 1 =
        readField
          (actGates (Adder.carryGates wordWidth).reverse gathered)
          (2 * wordWidth + 1) 1 := by
    simpa [compareComputeGates, gathered, L, W, compareLayout, compareWiring,
      Layout.offset, Layout.size, two_mul, Nat.add_assoc] using hplaced
  rw [hplaced']
  change readField
      (actGates (Adder.carryGates wordWidth).reverse gathered)
      (2 * wordWidth + 1) 1 = _
  rw [hlocal, readField_one, bitValue_write_self]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega)), hlocalScratch, Nat.zero_add]
  have hborrow : Adder.borrow
      (readField gathered 0 wordWidth)
      (readField gathered wordWidth wordWidth) < 2 := by
    unfold Adder.borrow
    split <;> omega
  rw [Nat.mod_eq_of_lt hborrow, hsource, htarget]

theorem flagEraseGates_wellFormed {wordWidth : Nat}
    (hwidth : 0 < wordWidth) :
    (flagEraseGates wordWidth).all
      (RGate.wellFormed (width wordWidth)) = true := by
  simp only [flagEraseGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, List.all_reverse, Bool.and_eq_true]
  refine ⟨⟨compareComputeGates_wellFormed hwidth, ?_⟩,
    compareComputeGates_wellFormed hwidth⟩
  simp [RGate.wellFormed, width, controlWire, scratchWire, reductionWire]

theorem flagEraseGates_act {wordWidth i : Nat}
    (hwidth : 0 < wordWidth)
    (hcarry : bitValue i (carryInWire wordWidth) = 0)
    (hscratch : bitValue i (scratchWire wordWidth) = 0) :
    actGates (flagEraseGates wordWidth) i =
      writeField i (reductionWire wordWidth) 1
        ((bitValue i (reductionWire wordWidth) +
          bitValue i (controlWire wordWidth) *
            Adder.borrow
              (readField i (sourceOffset wordWidth) wordWidth)
              (readField i targetOffset wordWidth)) % 2) := by
  let compute := compareComputeGates wordWidth
  have hcopy : ∀ j,
      actGates
          [.ccx (controlWire wordWidth) (scratchWire wordWidth)
            (reductionWire wordWidth)] j =
        writeField j (reductionWire wordWidth) 1
          ((bitValue j (reductionWire wordWidth) +
            bitValue j (controlWire wordWidth) *
              bitValue j (scratchWire wordWidth)) % 2) := by
    intro j
    simp only [actGates_cons, actGates_nil, act_ccx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute)
    (cp := [.ccx (controlWire wordWidth) (scratchWire wordWidth)
      (reductionWire wordWidth)])
    (w := width wordWidth) (off := reductionWire wordWidth) (len := 1)
    (f := fun j =>
      (bitValue j (reductionWire wordWidth) +
        bitValue j (controlWire wordWidth) *
          bitValue j (scratchWire wordWidth)) % 2)
    (compareComputeGates_wellFormed hwidth)
    (compareComputeGates_avoids_reduction hwidth) hcopy i
  have hlocalWf : ∀ gate ∈ (Adder.carryGates wordWidth).reverse,
      gate.wellFormed (compareLayout wordWidth).width = true := by
    intro gate hgate
    have hwf := Adder.carryCircuit_wellFormed hwidth
    have hlocalWidth : (Adder.carryCircuit wordWidth).width =
        (compareLayout wordWidth).width := by
      simp [Adder.carryCircuit, compareLayout, Layout.width]
      omega
    rw [← hlocalWidth]
    exact List.all_eq_true.mp
      (by simpa [RCircuit.wellFormed, Adder.carryCircuit] using hwf) gate
        (List.mem_reverse.mp hgate)
  have hflag : bitValue (actGates compute i) (reductionWire wordWidth) =
      bitValue i (reductionWire wordWidth) := by
    unfold bitValue
    rw [show compute = (Adder.carryGates wordWidth).reverse.map
      (RGate.map (place (compareLayout wordWidth)
        (compareWiring wordWidth))) by rfl,
      testBit_actGates_map_of_outside hlocalWf]
    intro q hq
    have hplace := place_lt
      (L := compareLayout wordWidth) (W := compareWiring wordWidth)
      (Wd := reductionWire wordWidth)
      (by simp [compareLayout, compareWiring])
      (by
        intro j hj
        simp [compareLayout] at hj
        interval_cases j <;>
          simp [compareWiring, reductionWire, sourceOffset, targetOffset,
            carryInWire, scratchWire, compareLayout, Layout.size] <;> omega)
      q hq
    omega
  have hcontrol : bitValue (actGates compute i) (controlWire wordWidth) =
      bitValue i (controlWire wordWidth) := by
    unfold bitValue
    rw [show compute = (Adder.carryGates wordWidth).reverse.map
      (RGate.map (place (compareLayout wordWidth)
        (compareWiring wordWidth))) by rfl,
      testBit_actGates_map_of_outside hlocalWf]
    intro q hq
    have hplace := place_lt
      (L := compareLayout wordWidth) (W := compareWiring wordWidth)
      (Wd := controlWire wordWidth)
      (by simp [compareLayout, compareWiring])
      (by
        intro j hj
        simp [compareLayout] at hj
        interval_cases j <;>
          simp [compareWiring, controlWire, sourceOffset, targetOffset,
            carryInWire, scratchWire, compareLayout, Layout.size] <;> omega)
      q hq
    omega
  change actGates (compute ++ _ ++ compute.reverse) i = _
  rw [hsandwich, hflag, hcontrol,
    compareComputeGates_scratch hwidth hcarry hscratch]

def correctionMap (wordWidth q : Nat) : Nat :=
  if q < wordWidth then q
  else if q < 2 * wordWidth then q + 1
  else q + 2

def correctionAddOps (constant wordWidth : Nat) : List Op :=
  Op.relabelAll (correctionMap wordWidth)
    (controlledConstantAddOps constant wordWidth)

def modularAddOps (modulus wordWidth : Nat) : List Op :=
  gateOps (variableAddGates wordWidth) ++
    widenedConstantAddOps (2 ^ wordWidth - modulus) wordWidth ++
    gateOps [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)] ++
    widenedConstantAddOps modulus wordWidth ++
    gateOps [.x (targetExtensionWire wordWidth)] ++
    correctionAddOps (2 ^ wordWidth - modulus) wordWidth ++
    gateOps (flagEraseGates wordWidth)

def variableIndex (wordWidth original : Nat) : Nat :=
  actGates (variableAddGates wordWidth) original

def firstComparisonIndex (modulus wordWidth original : Nat) : Nat :=
  writeField (variableIndex wordWidth original) 0 (wordWidth + 1)
    ((readField (variableIndex wordWidth original) 0 (wordWidth + 1) +
      readField (2 ^ wordWidth - modulus) 0 (wordWidth + 1)) %
      2 ^ (wordWidth + 1))

def copiedReductionIndex (modulus wordWidth original : Nat) : Nat :=
  actGates [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)]
    (firstComparisonIndex modulus wordWidth original)

def secondComparisonIndex (modulus wordWidth original : Nat) : Nat :=
  writeField (copiedReductionIndex modulus wordWidth original) 0
    (wordWidth + 1)
    ((readField (copiedReductionIndex modulus wordWidth original) 0
          (wordWidth + 1) +
        readField modulus 0 (wordWidth + 1)) % 2 ^ (wordWidth + 1))

def clearedExtensionIndex (modulus wordWidth original : Nat) : Nat :=
  actGates [.x (targetExtensionWire wordWidth)]
    (secondComparisonIndex modulus wordWidth original)

def correctedIndex (modulus wordWidth original : Nat) : Nat :=
  let state := clearedExtensionIndex modulus wordWidth original
  writeField state 0 wordWidth
    ((readField state 0 wordWidth +
      readField
        (selectedConstant (2 ^ wordWidth - modulus)
          (reductionWire wordWidth) state) 0 wordWidth) % 2 ^ wordWidth)

def modularAddIndex (modulus wordWidth original : Nat) : Nat :=
  actGates (flagEraseGates wordWidth)
    (correctedIndex modulus wordWidth original)

def WorkspaceClear (wordWidth i : Nat) : Prop :=
  bitValue i (carryInWire wordWidth) = 0 ∧
  bitValue i (carryOutWire wordWidth) = 0 ∧
  bitValue i (scratchWire wordWidth) = 0

theorem WorkspaceClear.writeTarget {wordWidth i len value : Nat}
    (hfit : len ≤ carryInWire wordWidth)
    (hclear : WorkspaceClear wordWidth i) :
    WorkspaceClear wordWidth (writeField i 0 len value) := by
  rcases hclear with ⟨hcarry, hspare, hscratch⟩
  refine ⟨?_, ?_, ?_⟩ <;> rw [← readField_one]
  · rw [readField_writeField_of_disjoint (Or.inl (by simpa using hfit)),
      readField_one, hcarry]
  · rw [readField_writeField_of_disjoint (Or.inl (by
        simp [carryInWire, carryOutWire] at hfit ⊢
        omega)), readField_one, hspare]
  · rw [readField_writeField_of_disjoint (Or.inl (by
        simp [carryInWire, scratchWire] at hfit ⊢
        omega)), readField_one, hscratch]

theorem WorkspaceClear.writeReduction {wordWidth i value : Nat}
    (hclear : WorkspaceClear wordWidth i) :
    WorkspaceClear wordWidth
      (writeField i (reductionWire wordWidth) 1 value) := by
  rcases hclear with ⟨hcarry, hspare, hscratch⟩
  refine ⟨?_, ?_, ?_⟩ <;> rw [← readField_one]
  · rw [readField_writeField_of_disjoint (Or.inr (by
        simp [carryInWire, reductionWire])), readField_one, hcarry]
  · rw [readField_writeField_of_disjoint (Or.inr (by
        simp [carryOutWire, reductionWire])), readField_one, hspare]
  · rw [readField_writeField_of_disjoint (Or.inr (by
        simp [scratchWire, reductionWire])), readField_one, hscratch]

theorem WorkspaceClear.copyReduction {wordWidth i : Nat}
    (hclear : WorkspaceClear wordWidth i) :
    WorkspaceClear wordWidth
      (actGates [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)]
        i) := by
  simpa only [actGates_cons, actGates_nil, act_cx_write] using
    hclear.writeReduction (wordWidth := wordWidth)

theorem WorkspaceClear.clearExtension {wordWidth i : Nat}
    (hclear : WorkspaceClear wordWidth i) :
    WorkspaceClear wordWidth
      (actGates [.x (targetExtensionWire wordWidth)] i) := by
  rcases hclear with ⟨hcarry, hspare, hscratch⟩
  simp only [actGates_cons, actGates_nil, act_x_write]
  refine ⟨?_, ?_, ?_⟩ <;> rw [← readField_one]
  · rw [readField_writeField_of_disjoint (Or.inl (by
        simp [targetExtensionWire, carryInWire]
        omega)), readField_one, hcarry]
  · rw [readField_writeField_of_disjoint (Or.inl (by
        simp [targetExtensionWire, carryOutWire]
        omega)), readField_one, hspare]
  · rw [readField_writeField_of_disjoint (Or.inl (by
        simp [targetExtensionWire, scratchWire]
        omega)), readField_one, hscratch]

theorem mem_runOps_smul_basis
    {level totalWidth : Nat} {amplitude : Algebra.Dy (deg level)}
    {index : Nat} {ops : List Op} {start finish : Branch (deg level)}
    (hstate : start.state = amplitude • basis index)
    (hmem : finish ∈ runOps level totalWidth ops start) :
    ∃ normalized,
      normalized ∈ runOps level totalWidth ops
        { start with state := basis index } ∧
      finish = smulBranch amplitude normalized := by
  cases start with
  | mk outcomes creg state input =>
      change state = amplitude • basis index at hstate
      subst state
      change finish ∈ runOps level totalWidth ops
        (smulBranch amplitude
          (Branch.mk outcomes creg (basis index) input)) at hmem
      rw [(runOps_smul level totalWidth).2, List.mem_map] at hmem
      obtain ⟨normalized, hnormalized, rfl⟩ := hmem
      exact ⟨normalized, hnormalized, rfl⟩

theorem gateOps_smul_basis_state
    {level totalWidth : Nat} {amplitude : Algebra.Dy (deg level)}
    {index : Nat} {gates : List RGate} {start finish : Branch (deg level)}
    (hl : 3 ≤ level)
    (hwf : gates.all (RGate.wellFormed totalWidth) = true)
    (hstate : start.state = amplitude • basis index)
    (hmem : finish ∈ runOps level totalWidth (gateOps gates) start) :
    finish.state = amplitude • basis (actGates gates index) := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    mem_runOps_smul_basis hstate hmem
  cases normalized with
  | mk rec creg state input =>
      rw [gateOps_basis_run hl hwf, List.mem_singleton] at hnormalized
      rw [hfinish, hnormalized]
      rfl

theorem correctionMap_lt {wordWidth q : Nat}
    (hq : q < 2 * wordWidth + 4) :
    correctionMap wordWidth q < width wordWidth := by
  by_cases hlow : q < wordWidth
  · simp [correctionMap, hlow, width]
    omega
  · by_cases hmiddle : q < 2 * wordWidth
    · simp [correctionMap, hlow, hmiddle, width]
      omega
    · simp [correctionMap, hlow, hmiddle, width]
      omega

theorem correctionMap_injective {wordWidth x y : Nat}
    (hx : x < 2 * wordWidth + 4) (hy : y < 2 * wordWidth + 4)
    (hmap : correctionMap wordWidth x = correctionMap wordWidth y) :
    x = y := by
  by_cases hxlow : x < wordWidth <;>
    by_cases hxmiddle : x < 2 * wordWidth <;>
      by_cases hylow : y < wordWidth <;>
        by_cases hymiddle : y < 2 * wordWidth <;>
          simp [correctionMap, hxlow, hxmiddle, hylow, hymiddle] at hmap <;>
          omega

theorem correctionAddOps_exact
    {level constant wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcarry : bitValue original (carryInWire wordWidth) = 0)
    (hspare : bitValue original (carryOutWire wordWidth) = 0)
    (hancilla : bitValue original (scratchWire wordWidth) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (correctionAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (wordWidth - 1) •
      basis (writeField original 0 wordWidth
        ((readField original 0 wordWidth +
          readField
            (selectedConstant constant (reductionWire wordWidth) original)
            0 wordWidth) % 2 ^ wordWidth)) := by
  let localWidth := 2 * wordWidth + 4
  let f := correctionMap wordWidth
  let localOriginal := sourceIndex f localWidth original
  have hmapCarry : f (carryWire wordWidth 0) = carryInWire wordWidth := by
    simp [f, correctionMap, carryWire, carryInWire]
    omega
  have hmapSpare : f (spareWire wordWidth 0) = carryOutWire wordWidth := by
    simp [f, correctionMap, spareWire, carryWire, carryOutWire]
    omega
  have hmapAncilla : f (ancillaWire wordWidth) = scratchWire wordWidth := by
    simp [f, correctionMap, ancillaWire, scratchWire]
    omega
  have hmapControl : f (constantControlWire wordWidth) =
      reductionWire wordWidth := by
    simp [f, correctionMap, constantControlWire, adderWidth, reductionWire]
    omega
  have hlocalCarry : bitValue localOriginal (carryWire wordWidth 0) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by simp [localWidth, carryWire])]
    have hc := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hcarry
    rw [hmapCarry]
    exact hc
  have hlocalSpare : bitValue localOriginal (spareWire wordWidth 0) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by simp [localWidth, spareWire, carryWire])]
    have hs := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hspare
    rw [hmapSpare]
    exact hs
  have hlocalAncilla : bitValue localOriginal (ancillaWire wordWidth) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp
    rw [testBit_sourceIndex (by simp [localWidth, ancillaWire])]
    have ha := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hancilla
    rw [hmapAncilla]
    exact ha
  have hrun := runOps_relabel
    (level := level) (width := localWidth) (totalWidth := width wordWidth)
    (inputBits := 0) (cbits := wordWidth - 1) (f := f) (ambient := original)
    (ops := controlledConstantAddOps constant wordWidth)
    (b := Branch.mk rec creg (basis localOriginal) input)
    (by
      intro q hq
      exact correctionMap_lt hq)
    (by
      intro x y hx hy
      exact correctionMap_injective hx hy)
    (controlledConstantAddOps_wellFormed hl hwidth)
    (wfVec_basis (sourceIndex_lt f localWidth original))
  rw [placeBranch_sourceIndex_basis (d := deg level)
    (by
      intro x y hx hy
      exact correctionMap_injective hx hy) rec creg input] at hrun
  change runOps level (width wordWidth)
      (correctionAddOps constant wordWidth)
      (Branch.mk rec creg (basis original) input) = _ at hrun
  rw [hrun] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := List.mem_map.mp hb
  have hlocal := controlledConstantAddOps_exact hl hwidth
    (sourceIndex_lt f localWidth original)
    hlocalCarry hlocalSpare hlocalAncilla rec creg hlocalBranch
  have hread : readField localOriginal 0 wordWidth =
      readField original 0 wordWidth := by
    exact readField_sourceIndex (by simp [localWidth]; omega) (by
      intro q hq
      simp [f, correctionMap, hq])
  have hcontrolBit : localOriginal.testBit (constantControlWire wordWidth) =
      original.testBit (reductionWire wordWidth) := by
    rw [testBit_sourceIndex (by
      simp [localWidth, constantControlWire, adderWidth])]
    rw [hmapControl]
  have hselected : selectedConstant constant (constantControlWire wordWidth)
      localOriginal = selectedConstant constant (reductionWire wordWidth)
        original := by
    unfold selectedConstant
    rw [hcontrolBit]
  let localResult := writeField localOriginal 0 wordWidth
    ((readField localOriginal 0 wordWidth +
      readField
        (selectedConstant constant (constantControlWire wordWidth)
          localOriginal) 0 wordWidth) % 2 ^ wordWidth)
  have hlocalResult : localResult < 2 ^ localWidth :=
    writeField_lt (by simp [localWidth]; omega)
      (sourceIndex_lt f localWidth original)
  change placeVec f localWidth original localBranch.state = _
  rw [hlocal, placeVec_smul, placeVec_basis hlocalResult]
  rw [show localResult = writeField localOriginal 0 wordWidth
        ((readField original 0 wordWidth +
          readField
            (selectedConstant constant (reductionWire wordWidth) original)
            0 wordWidth) % 2 ^ wordWidth) by
      simp only [localResult, hread, hselected],
    replaceBits_writeField_sourceIndex
      (f := f) (localWidth := localWidth)
      (by
        intro x y hx hy
        exact correctionMap_injective hx hy)
      (by
        intro q hq
        simp [f, correctionMap, hq])
      (by simp [localWidth]; omega)]

theorem widenedConstantAddOps_wellFormed
    {level constant wordWidth cbits : Nat}
    (hl : 3 ≤ level) (hwidth : 1 ≤ wordWidth)
    (hcbits : wordWidth ≤ cbits) :
    Program.opsWellFormed level (width wordWidth) 0 cbits
      (widenedConstantAddOps constant wordWidth) = true := by
  apply Program.opsWellFormed_relabel
    (w := adderWidth (wordWidth + 1)) (f := id)
  · intro q hq
    simp [adderWidth, width] at hq ⊢
    omega
  · intro x y _ _ hxy
    exact hxy
  · exact Lookup.MeasuredUncompute.opsWellFormed_cbits_mono hcbits _
      (constantAddOps_wellFormed hl (by omega))

theorem correctionAddOps_wellFormed
    {level constant wordWidth cbits : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcbits : wordWidth - 1 ≤ cbits) :
    Program.opsWellFormed level (width wordWidth) 0 cbits
      (correctionAddOps constant wordWidth) = true := by
  apply Program.opsWellFormed_relabel
    (w := 2 * wordWidth + 4) (f := correctionMap wordWidth)
  · exact fun _ hq => correctionMap_lt hq
  · exact fun _ _ hx hy => correctionMap_injective hx hy
  · exact Lookup.MeasuredUncompute.opsWellFormed_cbits_mono hcbits _
      (controlledConstantAddOps_wellFormed hl hwidth)

theorem modularAddOps_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    Program.opsWellFormed level (width wordWidth) 0 wordWidth
      (modularAddOps modulus wordWidth) = true := by
  simp only [modularAddOps, Program.opsWellFormed_append]
  have hvariable := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := variableAddGates wordWidth)
    hl (variableAddGates_wellFormed (by omega))
  have hfirst := widenedConstantAddOps_wellFormed
    (constant := 2 ^ wordWidth - modulus) (wordWidth := wordWidth)
    (cbits := wordWidth)
    hl (by omega) (Nat.le_refl _)
  have hcopy := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)])
    hl (by
      simp [RGate.wellFormed, width, targetExtensionWire, reductionWire]
      omega)
  have hsecond := widenedConstantAddOps_wellFormed
    (constant := modulus) (wordWidth := wordWidth)
    (cbits := wordWidth)
    hl (by omega) (Nat.le_refl _)
  have hclear := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := [.x (targetExtensionWire wordWidth)])
    hl (by
      simp [RGate.wellFormed, width, targetExtensionWire]
      omega)
  have hcorrection := correctionAddOps_wellFormed
    (constant := 2 ^ wordWidth - modulus) (wordWidth := wordWidth)
    (cbits := wordWidth)
    hl hwidth (by omega)
  have herase := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := flagEraseGates wordWidth)
    hl (flagEraseGates_wellFormed (by omega))
  simp [gateOps, hvariable, hfirst, hcopy, hsecond, hclear, hcorrection,
    herase]

theorem correctedIndex_workspace
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    WorkspaceClear wordWidth (correctedIndex modulus wordWidth original) := by
  have hvariable : WorkspaceClear wordWidth
      (variableIndex wordWidth original) := by
    rw [variableIndex,
      variableAddGates_act hwidth hworkspace.1 hworkspace.2.2]
    exact ((hworkspace.writeTarget (len := wordWidth) (by
      simp [carryInWire]
      omega)).writeReduction)
  have hfirst : WorkspaceClear wordWidth
      (firstComparisonIndex modulus wordWidth original) :=
    hvariable.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  have hcopied : WorkspaceClear wordWidth
      (copiedReductionIndex modulus wordWidth original) :=
    hfirst.copyReduction
  have hsecond : WorkspaceClear wordWidth
      (secondComparisonIndex modulus wordWidth original) :=
    hcopied.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  have hcleared : WorkspaceClear wordWidth
      (clearedExtensionIndex modulus wordWidth original) :=
    hsecond.clearExtension
  exact hcleared.writeTarget (len := wordWidth) (by
    simp [carryInWire]
    omega)

theorem modularAddIndex_workspace
    {modulus wordWidth original : Nat}
    (hwidth : 0 < wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    WorkspaceClear wordWidth (modularAddIndex modulus wordWidth original) := by
  have hcorrected := correctedIndex_workspace (modulus := modulus)
    hwidth hworkspace
  rw [modularAddIndex,
    flagEraseGates_act hwidth hcorrected.1 hcorrected.2.2]
  exact hcorrected.writeReduction

theorem correctedIndex_testBit_of_ge_targetExtension
    {modulus wordWidth original q : Nat}
    (hwidth : 0 < wordWidth)
    (hworkspace : WorkspaceClear wordWidth original)
    (hge : wordWidth + 1 ≤ q)
    (hreduction : q ≠ reductionWire wordWidth) :
    (correctedIndex modulus wordWidth original).testBit q =
      original.testBit q := by
  rw [correctedIndex,
    testBit_writeField_outside (Or.inr (by omega)),
    clearedExtensionIndex, actGates_cons, actGates_nil, act_x_write,
    testBit_writeField_outside (Or.inr (by
      simpa only [targetExtensionWire] using hge)),
    secondComparisonIndex,
    testBit_writeField_outside (off := 0)
      (n := wordWidth + 1) (b := q) (Or.inr (by
        simpa only [Nat.zero_add] using hge)),
    copiedReductionIndex, actGates_cons, actGates_nil, act_cx_write,
    testBit_writeField_outside (by
      simp only [reductionWire] at hreduction ⊢
      omega),
    firstComparisonIndex,
    testBit_writeField_outside (off := 0)
      (n := wordWidth + 1) (b := q) (Or.inr (by
        simpa only [Nat.zero_add] using hge)),
    variableIndex,
    variableAddGates_act hwidth hworkspace.1 hworkspace.2.2,
    testBit_writeField_outside (by
      simp only [reductionWire] at hreduction ⊢
      omega),
    testBit_writeField_outside (off := targetOffset) (n := wordWidth)
      (b := q) (Or.inr (by
        simp only [targetOffset, Nat.zero_add]
        omega))]

theorem modularAddOps_exact
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hworkspace : WorkspaceClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (modularAddOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (modularAddIndex modulus wordWidth original) := by
  let a := Algebra.Dy.invSqrt2 (deg level)
  simp only [modularAddOps, List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b0, hb0, hb⟩ := hb
  rw [gateOps_basis_run hl
    (variableAddGates_wellFormed (by omega)), List.mem_singleton] at hb0
  subst b0
  have hvariable : actGates (variableAddGates wordWidth) original =
      variableIndex wordWidth original := by
    rfl
  have hvariableClear : WorkspaceClear wordWidth
      (variableIndex wordWidth original) := by
    rw [← hvariable,
      variableAddGates_act (by omega) hworkspace.1 hworkspace.2.2]
    exact ((hworkspace.writeTarget (len := wordWidth) (by
      simp [carryInWire]
      omega)).writeReduction)
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b1, hb1, hb⟩ := hb
  have hb1state : b1.state = a ^ wordWidth •
      basis (firstComparisonIndex modulus wordWidth original) := by
    simpa only [a, firstComparisonIndex] using
      widenedConstantAddOps_exact hl (by omega)
        hvariableClear.1 hvariableClear.2.1 hvariableClear.2.2
        rec creg hb1
  have hfirstClear : WorkspaceClear wordWidth
      (firstComparisonIndex modulus wordWidth original) := by
    exact hvariableClear.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b2, hb2, hb⟩ := hb
  have hb2state : b2.state = a ^ wordWidth •
      basis (copiedReductionIndex modulus wordWidth original) := by
    simpa only [copiedReductionIndex] using
      gateOps_smul_basis_state hl
        (gates :=
          [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)])
        (by
          simp [RGate.wellFormed, width, targetExtensionWire, reductionWire]
          omega)
        hb1state hb2
  have hcopiedClear : WorkspaceClear wordWidth
      (copiedReductionIndex modulus wordWidth original) :=
    hfirstClear.copyReduction
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b3, hb3, hb⟩ := hb
  obtain ⟨b3normalized, hb3normalized, hb3eq⟩ :=
    mem_runOps_smul_basis hb2state hb3
  cases b3normalized with
  | mk rec3 creg3 state3 input3 =>
      have hnormalized3 := widenedConstantAddOps_exact hl (by omega)
        hcopiedClear.1 hcopiedClear.2.1 hcopiedClear.2.2
        b2.outcomes b2.creg hb3normalized
      change state3 = a ^ wordWidth •
        basis (secondComparisonIndex modulus wordWidth original) at hnormalized3
      have hb3state : b3.state = (a ^ wordWidth * a ^ wordWidth) •
          basis (secondComparisonIndex modulus wordWidth original) := by
        rw [hb3eq]
        simp only [smulBranch]
        rw [hnormalized3, Vec.smul_smul]
      have hsecondClear : WorkspaceClear wordWidth
          (secondComparisonIndex modulus wordWidth original) := by
        exact hcopiedClear.writeTarget (len := wordWidth + 1) (by
          simp [carryInWire]
          omega)
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨b4, hb4, hb⟩ := hb
      have hb4state : b4.state = (a ^ wordWidth * a ^ wordWidth) •
          basis (clearedExtensionIndex modulus wordWidth original) := by
        simpa only [clearedExtensionIndex] using
          gateOps_smul_basis_state hl
            (gates := [.x (targetExtensionWire wordWidth)])
            (by
              simp [RGate.wellFormed, width, targetExtensionWire]
              omega)
            hb3state hb4
      have hclearedClear : WorkspaceClear wordWidth
          (clearedExtensionIndex modulus wordWidth original) :=
        hsecondClear.clearExtension
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨b5, hb5, hb⟩ := hb
      obtain ⟨b5normalized, hb5normalized, hb5eq⟩ :=
        mem_runOps_smul_basis hb4state hb5
      cases b5normalized with
      | mk rec5 creg5 state5 input5 =>
          have hnormalized5 := correctionAddOps_exact hl hwidth
            hclearedClear.1 hclearedClear.2.1 hclearedClear.2.2
            b4.outcomes b4.creg hb5normalized
          change state5 = a ^ (wordWidth - 1) •
            basis (correctedIndex modulus wordWidth original) at hnormalized5
          have hb5state : b5.state =
              ((a ^ wordWidth * a ^ wordWidth) * a ^ (wordWidth - 1)) •
                basis (correctedIndex modulus wordWidth original) := by
            rw [hb5eq]
            simp only [smulBranch]
            rw [hnormalized5, Vec.smul_smul]
          have hcorrectedClear : WorkspaceClear wordWidth
              (correctedIndex modulus wordWidth original) := by
            exact hclearedClear.writeTarget (len := wordWidth) (by
              simp [carryInWire]
              omega)
          have hbstate : b.state =
              ((a ^ wordWidth * a ^ wordWidth) * a ^ (wordWidth - 1)) •
                basis (modularAddIndex modulus wordWidth original) := by
            simpa only [modularAddIndex] using
              gateOps_smul_basis_state hl
                (gates := flagEraseGates wordWidth)
                (flagEraseGates_wellFormed (by omega))
                hb5state hb
          rw [hbstate]
          congr 1
          rw [← Algebra.Dy.pow_add, ← Algebra.Dy.pow_add]
          congr 1
          omega

end VQ.Curve.PackedModularAddition
