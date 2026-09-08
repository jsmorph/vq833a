import VQ.Euclid.StepBlocks
import VQ.Euclid.StepDomain

namespace VQ
namespace Euclid
namespace StepState

open Reversible

theorem Internal.three_mul (n : Nat) : 3 * n = n + (n + n) := by omega

open Internal

def encoded (n lengthWidth shiftWidth : Nat) (s : State) : Nat :=
  encode n lengthWidth shiftWidth
    (StepLayout.auxWidth lengthWidth shiftWidth) s

def CoefficientCallWindow
    (n lengthWidth shiftWidth U C : Nat) : Prop :=
  let P := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C
  (∃ left right : Fin U,
      left ≤ right ∧
        StepPlaced.CoefficientPreparedFrame
          n lengthWidth shiftWidth C P left right) ∨
    StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth P)

def CoefficientPairWindow
    (n lengthWidth shiftWidth U J : Nat) : Prop :=
  let Csub := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) J
  let B := actGates
    (Step.coefficientSubBlock n lengthWidth shiftWidth) J
  let F := actGates
    (Step.coefficientFlip n lengthWidth shiftWidth) B
  let Cadd := actGates
    (Step.coefficientAddControl n lengthWidth shiftWidth) F
  CoefficientCallWindow n lengthWidth shiftWidth U Csub ∧
    CoefficientCallWindow n lengthWidth shiftWidth U Cadd

theorem coefficientCallWindow_active
    {n lengthWidth shiftWidth U C : Nat} {left right : Fin U}
    (hleft : left ≤ right)
    (hframe :
      StepPlaced.CoefficientPreparedFrame n lengthWidth shiftWidth C
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C)
        left right) :
    CoefficientCallWindow n lengthWidth shiftWidth U C := by
  exact Or.inl ⟨left, right, hleft, hframe⟩

theorem coefficientCallWindow_inactive
    {n lengthWidth shiftWidth U C : Nat}
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C))) :
    CoefficientCallWindow n lengthWidth shiftWidth U C := by
  exact Or.inr h

theorem encoded_lt (n lengthWidth shiftWidth : Nat) (s : State) :
    encoded n lengthWidth shiftWidth s <
      2 ^ (StepLayout.layout n lengthWidth shiftWidth).width := by
  exact encode_lt n lengthWidth shiftWidth
    (StepLayout.auxWidth lengthWidth shiftWidth) s

theorem Internal.read_encoded (n lengthWidth shiftWidth : Nat)
    (s : State) (k : Nat) :
    (StepLayout.layout n lengthWidth shiftWidth).read
        (encoded n lengthWidth shiftWidth s) k =
      ([encodeWork1 n s, encodeWork2 n s,
        encodeLength lengthWidth s.lenT,
        encodeLength lengthWidth s.lenQ,
        encodeLength lengthWidth s.lenRPrime,
        encodeLength shiftWidth s.shift,
        boolValue s.phase1, boolValue s.phase2, boolValue s.iter,
        boolValue s.sign, 0, 0].getD k 0) %
        2 ^ (StepLayout.layout n lengthWidth shiftWidth).size k := by
  simpa [encoded, VQ.Euclid.encode, StepLayout.layout] using
    Layout.read_pack (StepLayout.layout n lengthWidth shiftWidth)
      [encodeWork1 n s, encodeWork2 n s,
       encodeLength lengthWidth s.lenT,
       encodeLength lengthWidth s.lenQ,
       encodeLength lengthWidth s.lenRPrime,
       encodeLength shiftWidth s.shift,
       boolValue s.phase1, boolValue s.phase2, boolValue s.iter,
       boolValue s.sign, 0, 0] k

theorem read_work1 (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s) StepLayout.work1Offset
        (workWidth n) =
      encodeWork1 n s % 2 ^ workWidth n := by
  simpa [StepLayout.layout, layout, StepLayout.work1Offset,
    Layout.read, Layout.offset, Layout.size, two_mul, Nat.add_assoc] using
    read_encoded n lengthWidth shiftWidth s 0

theorem read_work2 (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.work2Offset n) (workWidth n) =
      encodeWork2 n s := by
  have h := read_encoded n lengthWidth shiftWidth s 1
  have hfit : encodeWork2 n s < 2 ^ workWidth n := by
    simpa [encodeWork2] using
      rotatePositionsLeft_lt (workWidth n) s.shift (encodeWork2Raw n s)
  simp [StepLayout.layout, layout, Layout.size] at h
  rw [Nat.mod_eq_of_lt hfit] at h
  simpa [StepLayout.layout, layout, StepLayout.work2Offset,
    Layout.read, Layout.offset, Layout.size, two_mul, Nat.add_assoc] using h

theorem read_lenT (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT := by
  have h := read_encoded n lengthWidth shiftWidth s 2
  simpa [StepLayout.layout, layout, StepLayout.lenTOffset,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (encodeLength_lt lengthWidth s.lenT), two_mul,
    Nat.add_assoc] using h

theorem read_lenQ (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenQ := by
  have h := read_encoded n lengthWidth shiftWidth s 3
  simpa [StepLayout.layout, layout, StepLayout.lenQOffset,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (encodeLength_lt lengthWidth s.lenQ), two_mul,
    Nat.add_assoc] using h

theorem read_lenRPrime (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
  have h := read_encoded n lengthWidth shiftWidth s 4
  simpa [StepLayout.layout, layout, StepLayout.lenRPrimeOffset,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (encodeLength_lt lengthWidth s.lenRPrime), two_mul,
    Nat.add_assoc] using h

theorem read_lenRPrime_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hterminal : Terminal s) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth % 2 ^ lengthWidth := by
  rw [read_lenRPrime]
  simp [encodeLength, hterminal.2.1,
    Nat.mod_eq_of_lt (encodedZero_lt lengthWidth)]

theorem read_lenRPrime_live
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hrPrime : 0 < s.rPrime) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth % 2 ^ lengthWidth := by
  rw [read_lenRPrime, Nat.mod_eq_of_lt (encodedZero_lt lengthWidth)]
  intro heq
  have hfit : s.lenRPrime < 2 ^ lengthWidth := hpacked.2.2.2.2.1
  have hdecoded := decode_encodeLength hfit
  rw [heq] at hdecoded
  have hlen : s.lenRPrime = bitLength s.rPrime := hpacked.2.1
  simp [decodeLength, encodedZero] at hdecoded
  have hpositive := bitLength_pos hrPrime
  omega

theorem read_shift (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      encodeLength shiftWidth s.shift := by
  have h := read_encoded n lengthWidth shiftWidth s 5
  simpa [StepLayout.layout, layout, StepLayout.shiftOffset,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (encodeLength_lt shiftWidth s.shift), two_mul,
    three_mul, Nat.add_assoc] using h

theorem read_shift_narrow
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hwidths : lengthWidth ≤ shiftWidth)
    (hfit : s.shift < 2 ^ lengthWidth) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.shift := by
  calc
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.shiftOffset n lengthWidth) lengthWidth =
        readField
          (readField (encoded n lengthWidth shiftWidth s)
            (StepLayout.shiftOffset n lengthWidth) shiftWidth)
          0 lengthWidth := by
      rw [readField_readField (by simpa using hwidths), Nat.add_zero]
    _ = readField (encodeLength shiftWidth s.shift) 0 lengthWidth := by
      rw [read_shift]
    _ = encodeLength lengthWidth s.shift := by
      simpa [readField] using encodeLength_mod_of_le hwidths hfit

theorem Internal.boolValue_lt (b : Bool) : boolValue b < 2 := by
  cases b <;> simp [boolValue]

theorem read_phase1 (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (encoded n lengthWidth shiftWidth s)
        (StepLayout.phase1Wire n lengthWidth shiftWidth) =
      boolValue s.phase1 := by
  have h := read_encoded n lengthWidth shiftWidth s 6
  simpa [StepLayout.layout, layout, StepLayout.phase1Wire,
    StepLayout.shiftOffset, Layout.read, Layout.offset, Layout.size,
    readField_one, Nat.mod_eq_of_lt (boolValue_lt s.phase1), two_mul,
    three_mul, Nat.add_assoc] using h

theorem read_phase2 (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (encoded n lengthWidth shiftWidth s)
        (StepLayout.phase2Wire n lengthWidth shiftWidth) =
      boolValue s.phase2 := by
  have h := read_encoded n lengthWidth shiftWidth s 7
  simpa [StepLayout.layout, layout, StepLayout.phase2Wire,
    StepLayout.phase1Wire, StepLayout.shiftOffset, Layout.read, Layout.offset,
    Layout.size, readField_one,
    Nat.mod_eq_of_lt (boolValue_lt s.phase2), two_mul, three_mul,
    Nat.add_assoc] using h

theorem read_iter (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (encoded n lengthWidth shiftWidth s)
        (StepLayout.iterWire n lengthWidth shiftWidth) =
      boolValue s.iter := by
  have h := read_encoded n lengthWidth shiftWidth s 8
  simpa [StepLayout.layout, layout, StepLayout.iterWire,
    StepLayout.phase1Wire, StepLayout.shiftOffset, Layout.read, Layout.offset,
    Layout.size, readField_one,
    Nat.mod_eq_of_lt (boolValue_lt s.iter), two_mul, three_mul,
    Nat.add_assoc] using h

theorem read_sign (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (encoded n lengthWidth shiftWidth s)
        (StepLayout.signWire n lengthWidth shiftWidth) =
      boolValue s.sign := by
  have h := read_encoded n lengthWidth shiftWidth s 9
  simpa [StepLayout.layout, layout, StepLayout.signWire,
    StepLayout.phase1Wire, StepLayout.shiftOffset, Layout.read, Layout.offset,
    Layout.size, readField_one,
    Nat.mod_eq_of_lt (boolValue_lt s.sign), two_mul, three_mul,
    Nat.add_assoc] using h

theorem read_control (n lengthWidth shiftWidth : Nat) (s : State) :
    bitValue (encoded n lengthWidth shiftWidth s)
        (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
  have h := read_encoded n lengthWidth shiftWidth s 10
  simpa [StepLayout.layout, layout, StepLayout.controlWire,
    StepLayout.phase1Wire, StepLayout.shiftOffset, Layout.read, Layout.offset,
    Layout.size, readField_one, two_mul, three_mul, Nat.add_assoc] using h

theorem read_aux (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (encoded n lengthWidth shiftWidth s)
        (StepLayout.auxOffset n lengthWidth shiftWidth)
        (StepLayout.auxWidth lengthWidth shiftWidth) = 0 := by
  have h := read_encoded n lengthWidth shiftWidth s 11
  simpa [StepLayout.layout, layout, StepLayout.auxOffset,
    StepLayout.phase1Wire, StepLayout.shiftOffset, Layout.read, Layout.offset,
    Layout.size, two_mul, three_mul, Nat.add_assoc] using h

theorem encoded_write_shift_work2_of_lenQ_zero
    (n lengthWidth shiftWidth newShift : Nat) (s : State)
    (hlenQ : s.lenQ = 0) :
    let L := StepLayout.layout n lengthWidth shiftWidth
    L.write
        (L.write (encoded n lengthWidth shiftWidth s) 5
          (encodeLength shiftWidth newShift))
        1
        (rotatePositionsLeft (workWidth n) newShift (encodeWork2Raw n s)) =
      encoded n lengthWidth shiftWidth { s with shift := newShift } := by
  dsimp only
  let L := StepLayout.layout n lengthWidth shiftWidth
  let newWork2 :=
    rotatePositionsLeft (workWidth n) newShift (encodeWork2Raw n s)
  have hshiftFit : encodeLength shiftWidth newShift < 2 ^ L.size 5 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size] using
      encodeLength_lt shiftWidth newShift
  have hwork2Fit : newWork2 < 2 ^ L.size 1 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size, newWork2] using
      rotatePositionsLeft_lt (workWidth n) newShift (encodeWork2Raw n s)
  have hreads := read_write_two (l := L)
    (i := encoded n lengthWidth shiftWidth s)
    (k₁ := 5) (v₁ := encodeLength shiftWidth newShift)
    (k₂ := 1) (v₂ := newWork2) (by decide) hshiftFit hwork2Fit
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt
      (encoded_lt n lengthWidth shiftWidth s)))
    (encoded_lt n lengthWidth shiftWidth { s with shift := newShift })
  intro k hk
  have hk' : k < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hk
  interval_cases k
  · rw [hreads.2.2 0 (by decide) (by decide),
      read_encoded, read_encoded]
    simp [encodeWork1, hlenQ, reverseBits]
  · rw [hreads.2.1, read_encoded]
    change rotatePositionsLeft (workWidth n) newShift
        (encodeWork2Raw n s) =
      rotatePositionsLeft (workWidth n) newShift
          (encodeWork2Raw n s) % 2 ^ workWidth n
    rw [Nat.mod_eq_of_lt (rotatePositionsLeft_lt
      (workWidth n) newShift (encodeWork2Raw n s))]
  · rw [hreads.2.2 2 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 3 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 4 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.1, read_encoded]
    change encodeLength shiftWidth newShift =
      encodeLength shiftWidth newShift % 2 ^ shiftWidth
    rw [Nat.mod_eq_of_lt (encodeLength_lt shiftWidth newShift)]
  · rw [hreads.2.2 6 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 7 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 8 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 9 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 10 (by decide) (by decide),
      read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 11 (by decide) (by decide),
      read_encoded, read_encoded]
    simp

theorem read_aux_subfield
    {n lengthWidth shiftWidth off width : Nat} {s : State}
    (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
    (hhi : off + width ≤ StepLayout.auxOffset n lengthWidth shiftWidth +
      StepLayout.auxWidth lengthWidth shiftWidth) :
    readField (encoded n lengthWidth shiftWidth s) off width = 0 := by
  exact readField_sub_zero hlo hhi (read_aux n lengthWidth shiftWidth s)

theorem Internal.read_aux_bit
    {n lengthWidth shiftWidth q : Nat} {s : State}
    (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ q)
    (hhi : q + 1 ≤ StepLayout.auxOffset n lengthWidth shiftWidth +
      StepLayout.auxWidth lengthWidth shiftWidth) :
    bitValue (encoded n lengthWidth shiftWidth s) q = 0 := by
  rw [← readField_one]
  exact read_aux_subfield hlo hhi

theorem controlClean (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.ControlClean n lengthWidth shiftWidth
      (encoded n lengthWidth shiftWidth s) := by
  refine ⟨read_control n lengthWidth shiftWidth s, ?_, ?_, ?_⟩ <;>
    apply read_aux_bit <;>
    simp only [StepLayout.temporaryWire, StepLayout.plusWire,
      StepLayout.minusWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth,
      StepLayout.selectorWidth] <;>
    omega

theorem Internal.preShiftControl_read
    {n lengthWidth shiftWidth I off width : Nat}
    (hplus : StepLayout.plusWire n lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ StepLayout.plusWire n lengthWidth shiftWidth)
    (hminus : StepLayout.minusWire n lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ StepLayout.minusWire n lengthWidth shiftWidth) :
    readField
        (actGates (Step.preShiftControl n lengthWidth shiftWidth) I)
        off width =
      readField I off width := by
  rw [StepBlocks.preShiftControl_act, StepBlocks.preShiftControlOut]
  simp only [Phase.ccxOut, StepControl.negativeOut]
  rw [readField_writeField_of_disjoint hminus,
    readField_writeField_of_disjoint hplus]

theorem Internal.writeField_zero_of_bitValue_zero
    {I q : Nat} (h : bitValue I q = 0) :
    writeField I q 1 0 = I := by
  rw [← h, ← readField_one, writeField_read]

theorem Internal.encodedRemainderScratchClean
    (n lengthWidth shiftWidth : Nat) (s : State) :
    StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
      (encoded n lengthWidth shiftWidth s) := by
  constructor
  · apply read_aux_subfield
    · simp [StepLayout.leftOffset]
    · simp [StepLayout.leftOffset, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · apply read_aux_subfield
    · simp [StepLayout.rightOffset]
    · simp [StepLayout.rightOffset, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · exact (controlClean n lengthWidth shiftWidth s).control
  · apply read_aux_bit
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · apply read_aux_bit <;>
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;> omega
  · apply read_aux_bit <;>
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;> omega
  · apply read_aux_bit <;>
      simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;> omega
  · apply read_aux_subfield
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth]
      omega
  · apply read_aux_bit <;>
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth] <;> omega

theorem Internal.encoded_write_phase_sign
    (n lengthWidth shiftWidth : Nat) (s : State)
    (newPhase1 newPhase2 newSign : Bool) :
    let L := StepLayout.layout n lengthWidth shiftWidth
    L.write
        (L.write
          (L.write (encoded n lengthWidth shiftWidth s) 6
            (boolValue newPhase1))
          7 (boolValue newPhase2))
        9 (boolValue newSign) =
      encoded n lengthWidth shiftWidth
        { s with
          phase1 := newPhase1
          phase2 := newPhase2
          sign := newSign } := by
  dsimp only
  let L := StepLayout.layout n lengthWidth shiftWidth
  have hp1Fit : boolValue newPhase1 < 2 ^ L.size 6 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size] using
      boolValue_lt newPhase1
  have hp2Fit : boolValue newPhase2 < 2 ^ L.size 7 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size] using
      boolValue_lt newPhase2
  have hsignFit : boolValue newSign < 2 ^ L.size 9 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.size] using
      boolValue_lt newSign
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt (Layout.write_lt
      (encoded_lt n lengthWidth shiftWidth s))))
    (encoded_lt n lengthWidth shiftWidth
      { s with
        phase1 := newPhase1
        phase2 := newPhase2
        sign := newSign })
  intro j hj
  have hj' : j < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hj
  interval_cases j
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp [encodeWork1]
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp [encodeWork2, encodeWork2Raw]
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_self hp1Fit,
      read_encoded]
    simp [StepLayout.layout, VQ.Euclid.layout, Layout.size,
      Nat.mod_eq_of_lt (boolValue_lt newPhase1)]
  · rw [Layout.read_write_ne (by decide), Layout.read_write_self hp2Fit,
      read_encoded]
    simp [StepLayout.layout, VQ.Euclid.layout, Layout.size,
      Nat.mod_eq_of_lt (boolValue_lt newPhase2)]
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_self hsignFit, read_encoded]
    simp [StepLayout.layout, VQ.Euclid.layout, Layout.size,
      Nat.mod_eq_of_lt (boolValue_lt newSign)]
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      read_encoded, read_encoded]
    simp

theorem rPrimeZeroSelectorGates_act_live
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hrPrime : 0 < s.rPrime) :
    actGates (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth s := by
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hpool : readField (encoded n lengthWidth shiftWidth s)
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    apply read_aux_subfield
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth]
      omega
  have hzero : bitValue (encoded n lengthWidth shiftWidth s)
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply read_aux_subfield
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxWidth]
      omega
  rw [StepPlaced.rPrimeZeroSelectorGates_act hpool,
    if_neg (read_lenRPrime_live hpacked hrPrime)]
  exact write_of_bitValue (by simp [hzero])

theorem Internal.remainderScratchClean_write_sign
    {n lengthWidth shiftWidth I value : Nat}
    (h : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth I) :
    StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
      (writeField I (StepLayout.signWire n lengthWidth shiftWidth) 1 value) := by
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hread (off width : Nat) (hoff : sign + 1 ≤ off) :
      readField (writeField I sign 1 value) off width =
        readField I off width := by
    rw [readField_writeField_of_disjoint (Or.inl hoff)]
  have hbit (q : Nat) (hq : sign + 1 ≤ q) :
      bitValue (writeField I sign 1 value) q = bitValue I q := by
    simpa [readField_one] using hread q 1 hq
  constructor
  · exact (hread _ _ (by
        simp [sign, StepLayout.signWire, StepLayout.leftOffset,
          StepLayout.auxOffset])).trans h.left
  · exact (hread _ _ (by
        simp [sign, StepLayout.signWire, StepLayout.rightOffset,
          StepLayout.auxOffset]
        omega)).trans h.right
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.controlWire])).trans
      h.control
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega)).trans h.carry
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.accumulatorWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)).trans h.accumulator
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.leftFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)).trans h.leftFlag
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.rightFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)).trans h.rightFlag
  · exact (hread _ _ (by
        simp [sign, StepLayout.signWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)).trans h.pool
  · exact (hbit _ (by
        simp [sign, StepLayout.signWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega)).trans h.cellScratch

theorem Internal.remainderScratchClean_write_work2
    {n lengthWidth shiftWidth I value : Nat}
    (h : StepBlocks.RemainderScratchClean n lengthWidth shiftWidth I) :
    StepBlocks.RemainderScratchClean n lengthWidth shiftWidth
      (writeField I (StepLayout.work2Offset n) (workWidth n) value) := by
  let work2 := StepLayout.work2Offset n
  have hread (off width : Nat) (hoff : work2 + workWidth n ≤ off) :
      readField (writeField I work2 (workWidth n) value) off width =
        readField I off width := by
    rw [readField_writeField_of_disjoint (Or.inl hoff)]
  have hbit (q : Nat) (hq : work2 + workWidth n ≤ q) :
      bitValue (writeField I work2 (workWidth n) value) q = bitValue I q := by
    simpa [readField_one] using hread q 1 hq
  constructor
  · exact (hread _ _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.leftOffset,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)).trans h.left
  · exact (hread _ _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.rightOffset,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)).trans h.right
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)).trans h.control
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)).trans h.carry
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.accumulatorWire,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)).trans h.accumulator
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.leftFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)).trans h.leftFlag
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.rightFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)).trans h.rightFlag
  · exact (hread _ _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)).trans h.pool
  · exact (hbit _ (by
        simp [work2, StepLayout.work2Offset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)).trans h.cellScratch

theorem Internal.postShiftControl_read
    {n lengthWidth shiftWidth I off width : Nat}
    (hplus : StepLayout.plusWire n lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ StepLayout.plusWire n lengthWidth shiftWidth)
    (hminus : StepLayout.minusWire n lengthWidth shiftWidth + 1 ≤ off ∨
      off + width ≤ StepLayout.minusWire n lengthWidth shiftWidth) :
    readField
        (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)
        off width =
      readField I off width := by
  rw [StepBlocks.postShiftControl_act, StepBlocks.postShiftControlOut]
  simp only [Phase.ccxOut]
  rw [readField_writeField_of_disjoint hminus,
    readField_writeField_of_disjoint hplus]


end StepState
end Euclid
end VQ
