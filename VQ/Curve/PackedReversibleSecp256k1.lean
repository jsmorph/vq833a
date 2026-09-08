import VQ.Curve.Field
import VQ.Curve.PackedReversibleGapCorrection

namespace VQ.Curve.PackedReversibleSecp256k1

open Reversible
open VQ.Curve.PackedReversibleGapCorrection

def wordWidth : Nat := 256

def chunkWidth : Nat := 33

def finalChunkWidth : Nat := 25

def gap : Nat := 2 ^ 32 + 977

def targetOffset : Nat := 0

def sourceOffset : Nat := 256

def controlWire : Nat := 512

def zeroCarryWire : Nat := 513

def reductionWire : Nat := 514

def scratchWire : Nat := 515

def constantOffset : Nat := 516

def probeOutputWire : Nat := 549

def oneWire : Nat := 550

def carryWire (chunk : Nat) : Nat := 551 + chunk

def width : Nat := 559

def chunkOffset (chunk : Nat) : Nat := 33 * chunk

def chunkWidthAt (chunk : Nat) : Nat := if chunk < 7 then 33 else 25

def chunkCarryIn (chunk : Nat) : Nat :=
  if chunk = 0 then zeroCarryWire else carryWire (chunk - 1)

def chunkWiring (chunk control : Nat) : Wiring :=
  probeWiring constantOffset (chunkOffset chunk) (chunkCarryIn chunk)
    probeOutputWire control scratchWire (carryWire chunk)

def additionWiring (chunk : Nat) : Wiring :=
  probeWiring constantOffset (chunkOffset chunk) (chunkCarryIn chunk)
    (carryWire chunk) reductionWire scratchWire probeOutputWire

def borrowWiring (chunk control : Nat) : Wiring :=
  probeWiring constantOffset (chunkOffset chunk) zeroCarryWire
    probeOutputWire control scratchWire (carryWire chunk)

def detectionChunkGates (chunk : Nat) : List RGate :=
  placedCarryProbeGates (if chunk = 0 then gap else 0)
    (chunkWidthAt chunk) (chunkWiring chunk oneWire)

def additionChunkGates (chunk : Nat) : List RGate :=
  placedChunkAddGates (if chunk = 0 then gap else 0)
    (chunkWidthAt chunk) (additionWiring chunk)

def borrowChunkGates (chunk : Nat) : List RGate :=
  placedBorrowProbeGates (if chunk = 0 then gap else 1)
    (chunkWidthAt chunk)
    (borrowWiring chunk
      (if chunk = 0 then reductionWire else chunkCarryIn chunk))

def detectionChunks : List RGate :=
  detectionChunkGates 0 ++ detectionChunkGates 1 ++
    detectionChunkGates 2 ++ detectionChunkGates 3 ++
    detectionChunkGates 4 ++ detectionChunkGates 5 ++
    detectionChunkGates 6 ++ detectionChunkGates 7

def detectionComputeGates : List RGate := [.x oneWire] ++ detectionChunks

def detectionGates : List RGate :=
  detectionComputeGates ++ [.cx (carryWire 7) reductionWire] ++
    detectionComputeGates.reverse

def additionChunks : List RGate :=
  additionChunkGates 0 ++ additionChunkGates 1 ++
    additionChunkGates 2 ++ additionChunkGates 3 ++
    additionChunkGates 4 ++ additionChunkGates 5 ++
    additionChunkGates 6 ++ additionChunkGates 7

def borrowChunks : List RGate :=
  borrowChunkGates 7 ++ borrowChunkGates 6 ++
    borrowChunkGates 5 ++ borrowChunkGates 4 ++
    borrowChunkGates 3 ++ borrowChunkGates 2 ++
    borrowChunkGates 1 ++ borrowChunkGates 0

def correctionGates : List RGate := additionChunks ++ borrowChunks

def carry0 (x : Nat) : Nat :=
  (gap + x % 2 ^ chunkWidth) / 2 ^ chunkWidth

def carry1 (x : Nat) : Nat :=
  (x / 2 ^ chunkWidth % 2 ^ chunkWidth + carry0 x) / 2 ^ chunkWidth

def carry2 (x : Nat) : Nat :=
  (x / 2 ^ (2 * chunkWidth) % 2 ^ chunkWidth + carry1 x) /
    2 ^ chunkWidth

def carry3 (x : Nat) : Nat :=
  (x / 2 ^ (3 * chunkWidth) % 2 ^ chunkWidth + carry2 x) /
    2 ^ chunkWidth

def carry4 (x : Nat) : Nat :=
  (x / 2 ^ (4 * chunkWidth) % 2 ^ chunkWidth + carry3 x) /
    2 ^ chunkWidth

def carry5 (x : Nat) : Nat :=
  (x / 2 ^ (5 * chunkWidth) % 2 ^ chunkWidth + carry4 x) /
    2 ^ chunkWidth

def carry6 (x : Nat) : Nat :=
  (x / 2 ^ (6 * chunkWidth) % 2 ^ chunkWidth + carry5 x) /
    2 ^ chunkWidth

def carry7 (x : Nat) : Nat :=
  (x / 2 ^ (7 * chunkWidth) % 2 ^ finalChunkWidth + carry6 x) /
    2 ^ finalChunkWidth

def detectedState (i x : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField
          (writeField
            (writeField
              (writeField
                (writeField i (carryWire 0) 1 (carry0 x))
                (carryWire 1) 1 (carry1 x))
              (carryWire 2) 1 (carry2 x))
            (carryWire 3) 1 (carry3 x))
          (carryWire 4) 1 (carry4 x))
        (carryWire 5) 1 (carry5 x))
      (carryWire 6) 1 (carry6 x))
    (carryWire 7) 1 (carry7 x)

def chunkDigit (x chunk : Nat) : Nat :=
  x / 2 ^ chunkOffset chunk % 2 ^ chunkWidthAt chunk

def chunkAddend (chunk : Nat) : Nat := if chunk = 0 then gap else 0

def chunkCarryValue (x chunk : Nat) : Nat :=
  match chunk with
  | 0 => carry0 x
  | 1 => carry1 x
  | 2 => carry2 x
  | 3 => carry3 x
  | 4 => carry4 x
  | 5 => carry5 x
  | 6 => carry6 x
  | 7 => carry7 x
  | _ => 0

def chunkIncomingCarryValue (x chunk : Nat) : Nat :=
  if chunk = 0 then 0 else chunkCarryValue x (chunk - 1)

def chunkResult (x chunk : Nat) : Nat :=
  (chunkAddend chunk + chunkDigit x chunk +
    chunkIncomingCarryValue x chunk) % 2 ^ chunkWidthAt chunk

def addedPrefix (i x : Nat) : Nat → Nat
  | 0 => i
  | chunk + 1 =>
      writeField
        (writeField (addedPrefix i x chunk)
          (chunkOffset chunk) (chunkWidthAt chunk)
          (chunkResult x chunk))
        (carryWire chunk) 1 (chunkCarryValue x chunk)

def addedState (i x : Nat) : Nat := addedPrefix i x 8

def clearedState (i x : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField
          (writeField
            (writeField
              (writeField
                (writeField (addedState i x) (carryWire 7) 1 0)
                (carryWire 6) 1 0)
              (carryWire 5) 1 0)
            (carryWire 4) 1 0)
          (carryWire 3) 1 0)
        (carryWire 2) 1 0)
      (carryWire 1) 1 0)
    (carryWire 0) 1 0

theorem gap_eq : gap = 2 ^ wordWidth - Curve.p := by
  decide +kernel

theorem gap_lt : gap < 2 ^ chunkWidth := by
  decide +kernel

private theorem carry_split {base c x : Nat} (hbase : 0 < base) :
    x / base + (c + x % base) / base = (c + x) / base := by
  calc
    x / base + (c + x % base) / base =
        (base * (x / base) + (c + x % base)) / base := by
      rw [Nat.mul_add_div hbase]
    _ = (c + (base * (x / base) + x % base)) / base := by
      congr 1
      omega
    _ = (c + x) / base := by rw [Nat.div_add_mod]

private theorem carry_lift {base c k total x : Nat} (hbase : 0 < base)
    (h : x / k + c = total / k) :
    x / (k * base) + (x / k % base + c) / base =
      total / (k * base) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  calc
    x / k / base + (x / k % base + c) / base =
        x / k / base + (c + x / k % base) / base := by
      rw [Nat.add_comm (x / k % base) c]
    _ = (c + x / k) / base := carry_split hbase
    _ = (x / k + c) / base := by rw [Nat.add_comm]
    _ = total / k / base := by rw [h]

private theorem carry_lt_two {a b base : Nat} (ha : a < base)
    (hb : b < base) (hbase : 0 < base) : (a + b) / base < 2 := by
  apply (Nat.div_lt_iff_lt_mul hbase).2
  omega

theorem carry0_lt_two (x : Nat) : carry0 x < 2 := by
  apply carry_lt_two gap_lt (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (Nat.two_pow_pos chunkWidth)

private theorem two_lt_chunkBase : 2 < 2 ^ chunkWidth := by
  decide +kernel

private theorem two_lt_finalChunkBase : 2 < 2 ^ finalChunkWidth := by
  decide +kernel

theorem carry1_lt_two (x : Nat) : carry1 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry0_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry2_lt_two (x : Nat) : carry2 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry1_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry3_lt_two (x : Nat) : carry3 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry2_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry4_lt_two (x : Nat) : carry4 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry3_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry5_lt_two (x : Nat) : carry5 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry4_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry6_lt_two (x : Nat) : carry6 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (lt_trans (carry5_lt_two x) two_lt_chunkBase)
    (Nat.two_pow_pos chunkWidth)

theorem carry7_lt_two (x : Nat) : carry7 x < 2 := by
  apply carry_lt_two (Nat.mod_lt _ (Nat.two_pow_pos finalChunkWidth))
    (lt_trans (carry6_lt_two x) two_lt_finalChunkBase)
    (Nat.two_pow_pos finalChunkWidth)

theorem carry7_eq_overflow {x : Nat} (hx : x < 2 ^ wordWidth) :
    carry7 x = (gap + x) / 2 ^ wordWidth := by
  have h0 : x / 2 ^ chunkWidth + carry0 x =
      (gap + x) / 2 ^ chunkWidth := by
    simpa [carry0] using
      (carry_split (c := gap) (x := x) (Nat.two_pow_pos chunkWidth))
  have h1 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ chunkWidth) (c := carry0 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) h0
  have h2 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ (2 * chunkWidth)) (c := carry1 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) (by
      simpa [carry1, chunkWidth] using h1)
  have h3 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ (3 * chunkWidth)) (c := carry2 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) (by
      simpa [carry2, chunkWidth] using h2)
  have h4 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ (4 * chunkWidth)) (c := carry3 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) (by
      simpa [carry3, chunkWidth] using h3)
  have h5 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ (5 * chunkWidth)) (c := carry4 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) (by
      simpa [carry4, chunkWidth] using h4)
  have h6 := carry_lift (base := 2 ^ chunkWidth)
    (k := 2 ^ (6 * chunkWidth)) (c := carry5 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos chunkWidth) (by
      simpa [carry5, chunkWidth] using h5)
  have h7 := carry_lift (base := 2 ^ finalChunkWidth)
    (k := 2 ^ (7 * chunkWidth)) (c := carry6 x) (total := gap + x)
    (x := x) (Nat.two_pow_pos finalChunkWidth) (by
      simpa [carry6, chunkWidth] using h6)
  have hfinal : x / 2 ^ wordWidth + carry7 x =
      (gap + x) / 2 ^ wordWidth := by
    simpa [carry7, chunkWidth, finalChunkWidth, wordWidth] using h7
  have hxquot : x / 2 ^ wordWidth = 0 := Nat.div_eq_of_lt hx
  simpa [hxquot] using hfinal

theorem carry0_prefix (x : Nat) :
    x / 2 ^ chunkWidth + carry0 x =
      (gap + x) / 2 ^ chunkWidth := by
  simpa [carry0] using
    (carry_split (c := gap) (x := x) (Nat.two_pow_pos chunkWidth))

theorem carry1_prefix (x : Nat) :
    x / 2 ^ (2 * chunkWidth) + carry1 x =
      (gap + x) / 2 ^ (2 * chunkWidth) := by
  simpa [carry1, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ chunkWidth)
      (c := carry0 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry0_prefix x))

theorem carry2_prefix (x : Nat) :
    x / 2 ^ (3 * chunkWidth) + carry2 x =
      (gap + x) / 2 ^ (3 * chunkWidth) := by
  simpa [carry2, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ (2 * chunkWidth))
      (c := carry1 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry1_prefix x))

theorem carry3_prefix (x : Nat) :
    x / 2 ^ (4 * chunkWidth) + carry3 x =
      (gap + x) / 2 ^ (4 * chunkWidth) := by
  simpa [carry3, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ (3 * chunkWidth))
      (c := carry2 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry2_prefix x))

theorem carry4_prefix (x : Nat) :
    x / 2 ^ (5 * chunkWidth) + carry4 x =
      (gap + x) / 2 ^ (5 * chunkWidth) := by
  simpa [carry4, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ (4 * chunkWidth))
      (c := carry3 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry3_prefix x))

theorem carry5_prefix (x : Nat) :
    x / 2 ^ (6 * chunkWidth) + carry5 x =
      (gap + x) / 2 ^ (6 * chunkWidth) := by
  simpa [carry5, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ (5 * chunkWidth))
      (c := carry4 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry4_prefix x))

theorem carry6_prefix (x : Nat) :
    x / 2 ^ (7 * chunkWidth) + carry6 x =
      (gap + x) / 2 ^ (7 * chunkWidth) := by
  simpa [carry6, chunkWidth] using
    (carry_lift (base := 2 ^ chunkWidth) (k := 2 ^ (6 * chunkWidth))
      (c := carry5 x) (total := gap + x) (x := x)
      (Nat.two_pow_pos chunkWidth) (carry5_prefix x))

theorem chunkResult_eq_sumDigit {x chunk : Nat} (hchunk : chunk < 8) :
    chunkResult x chunk =
      (gap + x) / 2 ^ chunkOffset chunk % 2 ^ chunkWidthAt chunk := by
  interval_cases chunk
  · simp [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkOffset, chunkWidthAt]
  · have hp := carry0_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry1_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry2_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry3_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry4_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry5_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 8589934592) hp
  · have hp := carry6_prefix x
    norm_num [chunkWidth] at hp
    simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt]
      using congrArg (fun z => z % 33554432) hp

private theorem previous_carry_eq_one
    {base digit previous : Nat}
    (hbase : 1 < base) (hdigit : digit < base) (hprevious : previous < 2)
    (hcarry : (digit + previous) / base = 1) :
    previous = 1 ∧ (digit + previous) % base = 0 := by
  have hsplit := Nat.mod_add_div (digit + previous) base
  have hremainder := Nat.mod_lt (digit + previous) (by omega : 0 < base)
  rw [hcarry, Nat.mul_one] at hsplit
  omega

private theorem borrow_after_constant_carry
    {base constant digit : Nat}
    (hbase : 0 < base) (hconstant : constant < base)
    (hdigit : digit < base) (hcarry : (constant + digit) / base = 1) :
    Adder.borrow constant ((constant + digit) % base) = 1 := by
  have hsplit := Nat.mod_add_div (constant + digit) base
  rw [hcarry, Nat.mul_one] at hsplit
  unfold Adder.borrow
  rw [if_pos]
  omega

private theorem borrow_after_unit_carry
    {base digit : Nat} (hbase : 1 < base) (hdigit : digit < base)
    (hcarry : (digit + 1) / base = 1) :
    Adder.borrow 1 ((digit + 1) % base) = 1 := by
  have hsplit := Nat.mod_add_div (digit + 1) base
  have hremainder := Nat.mod_lt (digit + 1) (by omega : 0 < base)
  rw [hcarry, Nat.mul_one] at hsplit
  have hzero : (digit + 1) % base = 0 := by omega
  simp [Adder.borrow, hzero]

private theorem borrow_after_constant_eq_carry
    {base constant digit : Nat}
    (hbase : 0 < base) (hconstant : constant < base)
    (hdigit : digit < base) :
    Adder.borrow constant ((constant + digit) % base) =
      (constant + digit) / base := by
  have hcarry : (constant + digit) / base < 2 :=
    carry_lt_two hconstant hdigit hbase
  interval_cases hquotient : (constant + digit) / base
  · have hsplit := Nat.mod_add_div (constant + digit) base
    rw [hquotient, Nat.mul_zero, Nat.add_zero] at hsplit
    simp [Adder.borrow, hsplit]
  · exact borrow_after_constant_carry hbase hconstant hdigit hquotient

private theorem borrow_after_unit_eq_carry
    {base digit : Nat}
    (hbase : 1 < base) (hdigit : digit < base) :
    Adder.borrow 1 ((digit + 1) % base) = (digit + 1) / base := by
  have hcarry : (digit + 1) / base < 2 :=
    carry_lt_two hdigit (by omega) (by omega)
  interval_cases hquotient : (digit + 1) / base
  · have hsplit := Nat.mod_add_div (digit + 1) base
    rw [hquotient, Nat.mul_zero, Nat.add_zero] at hsplit
    simp [Adder.borrow, hsplit]
  · exact borrow_after_unit_carry hbase hdigit hquotient

private theorem controlled_borrow_after_unit_eq_carry
    {base digit incoming : Nat}
    (hbase : 1 < base) (hdigit : digit < base) (hincoming : incoming < 2) :
    (if incoming = 1 then
        Adder.borrow 1 ((digit + incoming) % base)
      else 0) =
      (digit + incoming) / base := by
  interval_cases incoming
  · simp [Nat.div_eq_of_lt hdigit]
  · simp only [if_true]
    exact borrow_after_unit_eq_carry hbase hdigit

theorem carries_eq_one_of_overflow {x : Nat}
    (hoverflow : carry7 x = 1) :
    carry0 x = 1 ∧ carry1 x = 1 ∧ carry2 x = 1 ∧ carry3 x = 1 ∧
      carry4 x = 1 ∧ carry5 x = 1 ∧ carry6 x = 1 := by
  have h6 : carry6 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_finalChunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos finalChunkWidth))
      (carry6_lt_two x) (by simpa [carry7] using hoverflow)).1
  have h5 : carry5 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry5_lt_two x) (by simpa [carry6] using h6)).1
  have h4 : carry4 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry4_lt_two x) (by simpa [carry5] using h5)).1
  have h3 : carry3 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry3_lt_two x) (by simpa [carry4] using h4)).1
  have h2 : carry2 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry2_lt_two x) (by simpa [carry3] using h3)).1
  have h1 : carry1 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry1_lt_two x) (by simpa [carry2] using h2)).1
  have h0 : carry0 x = 1 :=
    (previous_carry_eq_one
      (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
      (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
      (carry0_lt_two x) (by simpa [carry1] using h1)).1
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem borrows_eq_one_of_overflow {x : Nat}
    (hoverflow : carry7 x = 1) :
    Adder.borrow gap
        ((gap + x % 2 ^ chunkWidth) % 2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ chunkWidth % 2 ^ chunkWidth + carry0 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (2 * chunkWidth) % 2 ^ chunkWidth + carry1 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (3 * chunkWidth) % 2 ^ chunkWidth + carry2 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (4 * chunkWidth) % 2 ^ chunkWidth + carry3 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (5 * chunkWidth) % 2 ^ chunkWidth + carry4 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (6 * chunkWidth) % 2 ^ chunkWidth + carry5 x) %
          2 ^ chunkWidth) = 1 ∧
      Adder.borrow 1
        ((x / 2 ^ (7 * chunkWidth) % 2 ^ finalChunkWidth + carry6 x) %
          2 ^ finalChunkWidth) = 1 := by
  rcases carries_eq_one_of_overflow hoverflow with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hb0 := borrow_after_constant_carry
    (Nat.two_pow_pos chunkWidth) gap_lt
    (Nat.mod_lt x (Nat.two_pow_pos chunkWidth))
    (by simpa [carry0] using h0)
  have hb1 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry1, h0] using h1)
  have hb2 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry2, h1] using h2)
  have hb3 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry3, h2] using h3)
  have hb4 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry4, h3] using h4)
  have hb5 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry5, h4] using h5)
  have hb6 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos chunkWidth))
    (by simpa [carry6, h5] using h6)
  have hb7 := borrow_after_unit_carry
    (lt_trans (by omega : 1 < 2) two_lt_finalChunkBase)
    (Nat.mod_lt _ (Nat.two_pow_pos finalChunkWidth))
    (by simpa [carry7, h6] using hoverflow)
  exact ⟨hb0, by simpa [h0] using hb1, by simpa [h1] using hb2,
    by simpa [h2] using hb3, by simpa [h3] using hb4,
    by simpa [h4] using hb5, by simpa [h5] using hb6,
    by simpa [h6] using hb7⟩

theorem readField_targetChunk {i x chunk : Nat} (hchunk : chunk < 8)
    (hx : readField i targetOffset wordWidth = x) :
    readField i (chunkOffset chunk) (chunkWidthAt chunk) =
      x / 2 ^ chunkOffset chunk % 2 ^ chunkWidthAt chunk := by
  have hfit : chunkOffset chunk + chunkWidthAt chunk ≤ wordWidth := by
    interval_cases chunk <;>
      simp [chunkOffset, chunkWidthAt, chunkWidth, finalChunkWidth, wordWidth]
  calc
    readField i (chunkOffset chunk) (chunkWidthAt chunk) =
        readField (readField i targetOffset wordWidth)
          (chunkOffset chunk) (chunkWidthAt chunk) := by
      simpa [targetOffset] using (readField_readField_zero hfit).symm
    _ = readField x (chunkOffset chunk) (chunkWidthAt chunk) := by rw [hx]
    _ = x / 2 ^ chunkOffset chunk % 2 ^ chunkWidthAt chunk := by
      simp [readField, Nat.shiftRight_eq_div_pow]

structure DetectionStable (i x : Nat) : Prop where
  target : readField i targetOffset wordWidth = x
  constant : readField i constantOffset chunkWidth = 0
  output : bitValue i probeOutputWire = 0
  one : bitValue i oneWire = 1
  scratch : i.testBit scratchWire = false

structure CorrectionStable (i : Nat) : Prop where
  constant : readField i constantOffset chunkWidth = 0
  output : bitValue i probeOutputWire = 0
  reduction : bitValue i reductionWire = 1
  scratch : i.testBit scratchWire = false
  zeroCarry : bitValue i zeroCarryWire = 0

theorem CorrectionStable.writeTarget {i chunk value : Nat}
    (h : CorrectionStable i) (hchunk : chunk < 8) :
    CorrectionStable
      (writeField i (chunkOffset chunk) (chunkWidthAt chunk) value) := by
  have hfit : chunkOffset chunk + chunkWidthAt chunk ≤ wordWidth := by
    interval_cases chunk <;>
      simp [chunkOffset, chunkWidthAt, wordWidth]
  unfold wordWidth at hfit
  constructor
  · rw [readField_writeField_of_disjoint (Or.inl (by
      unfold constantOffset
      omega))]
    exact h.constant
  · rw [bitValue_write_out (by
      unfold probeOutputWire
      omega)]
    exact h.output
  · rw [bitValue_write_out (by
      unfold reductionWire
      omega)]
    exact h.reduction
  · rw [testBit_writeField_outside (Or.inr (by
      unfold scratchWire
      omega))]
    exact h.scratch
  · rw [bitValue_write_out (by
      unfold zeroCarryWire
      omega)]
    exact h.zeroCarry

theorem CorrectionStable.writeCarry {i chunk value : Nat}
    (h : CorrectionStable i) :
    CorrectionStable (writeField i (carryWire chunk) 1 value) := by
  constructor
  · rw [readField_writeField_of_disjoint (Or.inr (by
      unfold carryWire constantOffset chunkWidth
      omega))]
    exact h.constant
  · rw [bitValue_write_ne (by
      unfold carryWire probeOutputWire
      omega)]
    exact h.output
  · rw [bitValue_write_ne (by
      unfold carryWire reductionWire
      omega)]
    exact h.reduction
  · rw [testBit_writeField_outside (Or.inl (by
      unfold carryWire scratchWire
      omega))]
    exact h.scratch
  · rw [bitValue_write_ne (by
      unfold carryWire zeroCarryWire
      omega)]
    exact h.zeroCarry

theorem chunkCarryValue_lt_two {x chunk : Nat} (hchunk : chunk < 8) :
    chunkCarryValue x chunk < 2 := by
  interval_cases chunk <;>
    simp only [chunkCarryValue] <;>
    first
    | exact carry0_lt_two x
    | exact carry1_lt_two x
    | exact carry2_lt_two x
    | exact carry3_lt_two x
    | exact carry4_lt_two x
    | exact carry5_lt_two x
    | exact carry6_lt_two x
    | exact carry7_lt_two x

theorem chunkCarryValue_eq_div {x chunk : Nat} (hchunk : chunk < 8) :
    chunkCarryValue x chunk =
      (chunkAddend chunk + chunkDigit x chunk +
        chunkIncomingCarryValue x chunk) / 2 ^ chunkWidthAt chunk := by
  interval_cases chunk <;>
    simp [chunkCarryValue, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkOffset, chunkWidthAt, chunkWidth,
      finalChunkWidth, carry0, carry1, carry2, carry3, carry4, carry5,
      carry6, carry7]

theorem readField_chunkAddend {chunk : Nat} (hchunk : chunk < 8) :
    readField (chunkAddend chunk) 0 (chunkWidthAt chunk) =
      chunkAddend chunk := by
  interval_cases chunk <;>
    simp [chunkAddend, chunkWidthAt, readField,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt
        (by simpa [chunkWidth] using gap_lt)]

theorem CorrectionStable.constantChunk {i chunk : Nat}
    (h : CorrectionStable i) (hchunk : chunk < 8) :
    readField i constantOffset (chunkWidthAt chunk) = 0 := by
  by_cases hlast : chunk = 7
  · subst chunk
    exact readField_narrow (by decide) h.constant
  · have hlt : chunk < 7 := by omega
    simpa [chunkWidthAt, hlt, chunkWidth] using h.constant

theorem addedPrefix_stable {i x n : Nat}
    (h : CorrectionStable i) (hn : n ≤ 8) :
    CorrectionStable (addedPrefix i x n) := by
  induction n with
  | zero => simpa [addedPrefix] using h
  | succ n ih =>
      have hnlt : n < 8 := by omega
      rw [addedPrefix]
      exact ((ih (by omega)).writeTarget hnlt).writeCarry

theorem readField_addedPrefix_future {i x n chunk : Nat}
    (hn : n ≤ chunk) (hchunk : chunk < 8) :
    readField (addedPrefix i x n) (chunkOffset chunk) (chunkWidthAt chunk) =
      readField i (chunkOffset chunk) (chunkWidthAt chunk) := by
  induction n generalizing chunk with
  | zero => simp [addedPrefix]
  | succ n ih =>
      have hnlt : n < 8 := by omega
      rw [addedPrefix,
        readField_writeField_of_disjoint (by
          interval_cases n <;> interval_cases chunk <;> decide +kernel),
        readField_writeField_of_disjoint (by
          interval_cases n <;> interval_cases chunk <;> decide +kernel)]
      exact ih (by omega) hchunk

theorem bitValue_addedPrefix_future {i x n chunk : Nat}
    (hn : n ≤ chunk) (hchunk : chunk < 8) :
    bitValue (addedPrefix i x n) (carryWire chunk) =
      bitValue i (carryWire chunk) := by
  induction n generalizing chunk with
  | zero => simp [addedPrefix]
  | succ n ih =>
      have hnlt : n < 8 := by omega
      rw [addedPrefix, bitValue_write_ne (by
        unfold carryWire
        omega), bitValue_write_out (by
          interval_cases n <;> interval_cases chunk <;> decide +kernel)]
      exact ih (by omega) hchunk

theorem bitValue_addedPrefix_previous {i x n : Nat}
    (hnpos : 0 < n) (hn : n ≤ 8) :
    bitValue (addedPrefix i x n) (carryWire (n - 1)) =
      chunkCarryValue x (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  rw [addedPrefix, bitValue_write_self,
    Nat.mod_eq_of_lt (chunkCarryValue_lt_two (by omega))]

theorem readField_addedPrefix_written {i x n chunk : Nat}
    (hchunk : chunk < n) (hn : n ≤ 8) :
    readField (addedPrefix i x n) (chunkOffset chunk) (chunkWidthAt chunk) =
      chunkResult x chunk := by
  induction n generalizing chunk with
  | zero => omega
  | succ n ih =>
      have hnlt : n < 8 := by omega
      rw [addedPrefix]
      by_cases heq : chunk = n
      · subst chunk
        rw [readField_writeField_of_disjoint (by
          interval_cases n <;> decide +kernel),
          readField_writeField_self (by
            unfold chunkResult
            exact Nat.mod_lt _ (Nat.two_pow_pos (chunkWidthAt n)))]
      · rw [readField_writeField_of_disjoint (by
          interval_cases n <;> interval_cases chunk <;> decide +kernel),
          readField_writeField_of_disjoint (by
            interval_cases n <;> interval_cases chunk <;>
              simp_all [chunkOffset, chunkWidthAt])]
        exact ih (by omega) (by omega)

theorem bitValue_addedPrefix_written {i x n chunk : Nat}
    (hchunk : chunk < n) (hn : n ≤ 8) :
    bitValue (addedPrefix i x n) (carryWire chunk) =
      chunkCarryValue x chunk := by
  induction n generalizing chunk with
  | zero => omega
  | succ n ih =>
      have hnlt : n < 8 := by omega
      rw [addedPrefix]
      by_cases heq : chunk = n
      · subst chunk
        rw [bitValue_write_self,
          Nat.mod_eq_of_lt (chunkCarryValue_lt_two hnlt)]
      · rw [bitValue_write_ne (by
          unfold carryWire
          omega), bitValue_write_out (Or.inr (by
            have hfit : chunkOffset n + chunkWidthAt n ≤ wordWidth := by
              interval_cases n <;>
                simp [chunkOffset, chunkWidthAt, wordWidth]
            have hafter : wordWidth ≤ carryWire chunk := by
              unfold wordWidth carryWire
              omega
            exact hfit.trans hafter))]
        exact ih (by omega) (by omega)

theorem readField_addedState {i x chunk : Nat} (hchunk : chunk < 8) :
    readField (addedState i x) (chunkOffset chunk) (chunkWidthAt chunk) =
      chunkResult x chunk := by
  exact readField_addedPrefix_written hchunk (by decide)

theorem bitValue_addedState {i x chunk : Nat} (hchunk : chunk < 8) :
    bitValue (addedState i x) (carryWire chunk) = chunkCarryValue x chunk := by
  exact bitValue_addedPrefix_written hchunk (by decide)

private theorem testBit_addedState_target_chunk
    {i x b chunk : Nat}
    (hchunk : chunk < 8)
    (hlo : chunkOffset chunk ≤ b)
    (hhi : b < chunkOffset chunk + chunkWidthAt chunk) :
    (addedState i x).testBit b = (gap + x).testBit b := by
  have hread :
      readField (addedState i x) (chunkOffset chunk) (chunkWidthAt chunk) =
        readField (gap + x) (chunkOffset chunk) (chunkWidthAt chunk) := by
    rw [readField_addedState hchunk, chunkResult_eq_sumDigit hchunk]
    simp [readField, Nat.shiftRight_eq_div_pow]
  have hbit := congrArg (fun z => z.testBit (b - chunkOffset chunk)) hread
  simpa [testBit_readField, show b - chunkOffset chunk < chunkWidthAt chunk by omega,
    show chunkOffset chunk + (b - chunkOffset chunk) = b by omega] using hbit

theorem testBit_addedState_target {i x b : Nat} (hb : b < wordWidth) :
    (addedState i x).testBit b = (gap + x).testBit b := by
  by_cases h0 : b < 33
  · exact testBit_addedState_target_chunk (chunk := 0) (by decide)
      (by simp [chunkOffset]) (by simpa [chunkOffset, chunkWidthAt] using h0)
  by_cases h1 : b < 66
  · exact testBit_addedState_target_chunk (chunk := 1) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h1)
  by_cases h2 : b < 99
  · exact testBit_addedState_target_chunk (chunk := 2) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h2)
  by_cases h3 : b < 132
  · exact testBit_addedState_target_chunk (chunk := 3) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h3)
  by_cases h4 : b < 165
  · exact testBit_addedState_target_chunk (chunk := 4) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h4)
  by_cases h5 : b < 198
  · exact testBit_addedState_target_chunk (chunk := 5) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h5)
  by_cases h6 : b < 231
  · exact testBit_addedState_target_chunk (chunk := 6) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [chunkOffset, chunkWidthAt] using h6)
  · exact testBit_addedState_target_chunk (chunk := 7) (by decide)
      (by simp [chunkOffset]; omega)
      (by simpa [wordWidth, chunkOffset, chunkWidthAt] using hb)

theorem readField_clearedState_target (i x : Nat) :
    readField (clearedState i x) targetOffset wordWidth =
      (gap + x) % 2 ^ wordWidth := by
  simp only [clearedState]
  rw [readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel)]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, Nat.testBit_mod_two_pow]
  by_cases hb : b < wordWidth
  · simpa [hb, targetOffset] using
      (testBit_addedState_target (i := i) (x := x) hb)
  · simp [hb]

private theorem testBit_addedPrefix_above
    {i x n b : Nat}
    (hn : n ≤ 8)
    (hb : wordWidth ≤ b)
    (hcarries : ∀ chunk, chunk < n → b ≠ carryWire chunk) :
    (addedPrefix i x n).testBit b = i.testBit b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < 8 := by omega
      have hfit : chunkOffset n + chunkWidthAt n ≤ wordWidth := by
        interval_cases n <;> simp [chunkOffset, chunkWidthAt, wordWidth]
      rw [addedPrefix,
        testBit_writeField_outside (by
          have hne := hcarries n (by omega)
          omega),
        testBit_writeField_outside (Or.inr (hfit.trans hb))]
      exact ih (by omega) (fun chunk hchunk => hcarries chunk (by omega))

theorem testBit_clearedState_above
    {i x b : Nat}
    (hb : wordWidth ≤ b)
    (hcarries : ∀ chunk, chunk < 8 → b ≠ carryWire chunk) :
    (clearedState i x).testBit b = i.testBit b := by
  simp only [clearedState]
  rw [testBit_writeField_outside (by
      have h := hcarries 0 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 1 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 2 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 3 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 4 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 5 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 6 (by decide)
      omega),
    testBit_writeField_outside (by
      have h := hcarries 7 (by decide)
      omega)]
  exact testBit_addedPrefix_above (n := 8) (by decide) hb hcarries

theorem testBit_clearedState_carry {i x chunk : Nat} (hchunk : chunk < 8) :
    (clearedState i x).testBit (carryWire chunk) = false := by
  interval_cases chunk <;>
    simp [clearedState, carryWire, testBit_writeField_inside,
      testBit_writeField_outside]

theorem clearedState_eq_writeField
    {i x : Nat}
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    clearedState i x = writeField i targetOffset wordWidth (gap + x) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < wordWidth
  · rw [testBit_writeField_inside (by simp [targetOffset]) (by
      simpa [targetOffset] using hb)]
    have hread := congrArg (fun z => z.testBit b)
      (readField_clearedState_target i x)
    simpa [testBit_readField, hb, targetOffset, Nat.testBit_mod_two_pow]
      using hread
  · rw [testBit_writeField_outside (Or.inr (by
      simp [targetOffset]
      omega))]
    by_cases hcarry : ∃ chunk, chunk < 8 ∧ b = carryWire chunk
    · obtain ⟨chunk, hchunk, rfl⟩ := hcarry
      rw [testBit_clearedState_carry hchunk]
      exact (testBit_eq_false_iff_bitValue_eq_zero i (carryWire chunk)).2
        (hcarries chunk hchunk) |>.symm
    · exact testBit_clearedState_above (by omega)
        (fun chunk hchunk heq => hcarry ⟨chunk, hchunk, heq⟩)

theorem readField_borrowAddend {chunk : Nat} (hchunk : chunk < 8) :
    readField (if chunk = 0 then gap else 1) 0 (chunkWidthAt chunk) =
      if chunk = 0 then gap else 1 := by
  interval_cases chunk <;>
    simp [chunkWidthAt, readField, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by simpa [chunkWidth] using gap_lt)]

theorem borrow_chunkResult_eq_one {x chunk : Nat}
    (hchunk : chunk < 8) (hoverflow : carry7 x = 1) :
    Adder.borrow (if chunk = 0 then gap else 1) (chunkResult x chunk) = 1 := by
  rcases borrows_eq_one_of_overflow hoverflow with
    ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  interval_cases chunk <;>
    simp_all [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      chunkWidth, finalChunkWidth]

theorem borrow_chunkResult_eq_carry {x chunk : Nat}
    (hchunk : chunk < 8) :
    (if chunk = 0 then Adder.borrow gap (chunkResult x chunk)
      else if chunkIncomingCarryValue x chunk = 1 then
        Adder.borrow 1 (chunkResult x chunk)
      else 0) = chunkCarryValue x chunk := by
  interval_cases chunk
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry0, chunkWidth, Nat.add_mod]
      using borrow_after_constant_eq_carry
        (Nat.two_pow_pos chunkWidth) gap_lt
        (Nat.mod_lt x (Nat.two_pow_pos chunkWidth))
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry1, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ chunkWidth) (Nat.two_pow_pos chunkWidth))
        (carry0_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry2, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ (2 * chunkWidth))
          (Nat.two_pow_pos chunkWidth)) (carry1_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry3, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ (3 * chunkWidth))
          (Nat.two_pow_pos chunkWidth)) (carry2_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry4, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ (4 * chunkWidth))
          (Nat.two_pow_pos chunkWidth)) (carry3_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry5, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ (5 * chunkWidth))
          (Nat.two_pow_pos chunkWidth)) (carry4_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry6, chunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_chunkBase)
        (Nat.mod_lt (x / 2 ^ (6 * chunkWidth))
          (Nat.two_pow_pos chunkWidth)) (carry5_lt_two x)
  · simpa [chunkResult, chunkAddend, chunkDigit,
      chunkIncomingCarryValue, chunkCarryValue, chunkOffset, chunkWidthAt,
      carry7, chunkWidth, finalChunkWidth, Nat.add_mod]
      using controlled_borrow_after_unit_eq_carry
        (lt_trans (by omega : 1 < 2) two_lt_finalChunkBase)
        (Nat.mod_lt (x / 2 ^ (7 * chunkWidth))
          (Nat.two_pow_pos finalChunkWidth)) (carry6_lt_two x)

theorem DetectionStable.writeCarry {i x chunk value : Nat}
    (h : DetectionStable i x) :
    DetectionStable (writeField i (carryWire chunk) 1 value) x := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      right
      unfold carryWire targetOffset wordWidth
      omega)]
    exact h.target
  · rw [readField_writeField_of_disjoint (by
      right
      unfold carryWire constantOffset chunkWidth
      omega)]
    exact h.constant
  · rw [bitValue_write_ne (by
      unfold carryWire probeOutputWire
      omega)]
    exact h.output
  · rw [bitValue_write_ne (by
      unfold carryWire oneWire
      omega)]
    exact h.one
  · rw [testBit_writeField_outside (by
      left
      unfold carryWire scratchWire
      omega)]
    exact h.scratch

theorem chunkWidthAt_positive {chunk : Nat} (hchunk : chunk < 8) :
    0 < chunkWidthAt chunk := by
  simp [chunkWidthAt]
  split <;> omega

set_option maxHeartbeats 1000000 in
theorem chunkWiring_disjoint {chunk control : Nat}
    (hchunk : chunk < 8)
    (hcontrol : control = oneWire ∨ control = reductionWire) :
    Wiring.Disjoint (probeLayout (chunkWidthAt chunk))
      (chunkWiring chunk control) := by
  interval_cases chunk <;> rcases hcontrol with rfl | rfl <;>
    intro j k hj hk hne <;>
    simp [probeLayout, chunkWidthAt, chunkWiring, probeWiring, chunkOffset,
      chunkCarryIn, carryWire, constantOffset, probeOutputWire, oneWire,
      reductionWire, zeroCarryWire, scratchWire, Layout.size] at hj hk ⊢ <;>
    interval_cases j <;> interval_cases k <;>
      simp [probeLayout, chunkWidthAt, chunkWiring, probeWiring, chunkOffset,
        chunkCarryIn, carryWire, constantOffset, probeOutputWire, oneWire,
        reductionWire, zeroCarryWire, scratchWire, Layout.size] at * <;>
      omega

set_option maxHeartbeats 1000000 in
theorem borrowWiring_disjoint {chunk control : Nat}
    (hchunk : chunk < 8)
    (hcontrol : control = reductionWire ∨
      (chunk ≠ 0 ∧ control = chunkCarryIn chunk)) :
    Wiring.Disjoint (probeLayout (chunkWidthAt chunk))
      (borrowWiring chunk control) := by
  interval_cases chunk <;>
    rcases hcontrol with rfl | ⟨hzero, rfl⟩ <;>
    intro j k hj hk hne <;>
    simp [probeLayout, chunkWidthAt, borrowWiring, probeWiring, chunkOffset,
      chunkCarryIn, carryWire, constantOffset, probeOutputWire,
      reductionWire, zeroCarryWire, scratchWire, Layout.size] at hj hk ⊢ <;>
    interval_cases j <;> interval_cases k <;>
      simp [probeLayout, chunkWidthAt, borrowWiring, probeWiring, chunkOffset,
        chunkCarryIn, carryWire, constantOffset, probeOutputWire,
        reductionWire, zeroCarryWire, scratchWire, Layout.size] at * <;>
      omega

set_option maxHeartbeats 1000000 in
theorem additionWiring_disjoint {chunk : Nat} (hchunk : chunk < 8) :
    Wiring.Disjoint (probeLayout (chunkWidthAt chunk))
      (additionWiring chunk) := by
  interval_cases chunk <;>
    intro j k hj hk hne <;>
    simp [probeLayout, chunkWidthAt, additionWiring, probeWiring, chunkOffset,
      chunkCarryIn, carryWire, constantOffset, probeOutputWire,
      reductionWire, zeroCarryWire, scratchWire, Layout.size] at hj hk ⊢ <;>
    interval_cases j <;> interval_cases k <;>
      simp [chunkWidthAt, additionWiring, probeWiring, chunkOffset,
        chunkCarryIn, carryWire, constantOffset, probeOutputWire,
        reductionWire, zeroCarryWire, scratchWire, Layout.size] at * <;>
      omega

theorem chunkWiring_length (chunk control : Nat) :
    (probeLayout (chunkWidthAt chunk)).length ≤
      (chunkWiring chunk control).length := by
  simp [probeLayout, chunkWiring, probeWiring]

theorem borrowWiring_length (chunk control : Nat) :
    (probeLayout (chunkWidthAt chunk)).length ≤
      (borrowWiring chunk control).length := by
  simp [probeLayout, borrowWiring, probeWiring]

theorem additionWiring_length (chunk : Nat) :
    (probeLayout (chunkWidthAt chunk)).length ≤
      (additionWiring chunk).length := by
  simp [probeLayout, additionWiring, probeWiring]

theorem chunkWiring_bound {chunk control j : Nat}
    (hchunk : chunk < 8)
    (hcontrol : control = oneWire ∨ control = reductionWire)
    (hj : j < (probeLayout (chunkWidthAt chunk)).length) :
    (chunkWiring chunk control).getD j 0 +
        Layout.size (probeLayout (chunkWidthAt chunk)) j ≤ width := by
  interval_cases chunk <;> rcases hcontrol with rfl | rfl <;>
    simp [probeLayout] at hj <;> interval_cases j <;> decide +kernel

theorem borrowWiring_bound {chunk control j : Nat}
    (hchunk : chunk < 8)
    (hcontrol : control = reductionWire ∨
      (chunk ≠ 0 ∧ control = chunkCarryIn chunk))
    (hj : j < (probeLayout (chunkWidthAt chunk)).length) :
    (borrowWiring chunk control).getD j 0 +
        Layout.size (probeLayout (chunkWidthAt chunk)) j ≤ width := by
  interval_cases chunk <;>
    rcases hcontrol with rfl | ⟨hzero, rfl⟩ <;>
    simp [probeLayout] at hj <;> interval_cases j <;> decide +kernel

theorem additionWiring_bound {chunk j : Nat}
    (hchunk : chunk < 8)
    (hj : j < (probeLayout (chunkWidthAt chunk)).length) :
    (additionWiring chunk).getD j 0 +
        Layout.size (probeLayout (chunkWidthAt chunk)) j ≤ width := by
  interval_cases chunk <;>
    simp [probeLayout] at hj <;> interval_cases j <;> decide +kernel

theorem detectionChunkGates_wellFormed {chunk : Nat} (hchunk : chunk < 8) :
    (detectionChunkGates chunk).all (RGate.wellFormed width) = true := by
  apply placedCarryProbeGates_wellFormed
    (chunkWidthAt_positive hchunk)
    (chunkWiring_disjoint hchunk (Or.inl rfl))
    (chunkWiring_length chunk oneWire)
  exact fun j hj => chunkWiring_bound hchunk (Or.inl rfl) hj

theorem additionChunkGates_wellFormed {chunk : Nat} (hchunk : chunk < 8) :
    (additionChunkGates chunk).all (RGate.wellFormed width) = true := by
  apply placedChunkAddGates_wellFormed
    (chunkWidthAt_positive hchunk)
    (additionWiring_disjoint hchunk)
    (additionWiring_length chunk)
  exact fun j hj => additionWiring_bound hchunk hj

theorem borrowChunkGates_wellFormed {chunk : Nat} (hchunk : chunk < 8) :
    (borrowChunkGates chunk).all (RGate.wellFormed width) = true := by
  by_cases hzero : chunk = 0
  · subst chunk
    simp only [borrowChunkGates, if_pos rfl]
    apply placedBorrowProbeGates_wellFormed (by decide +kernel)
      (borrowWiring_disjoint (by omega) (Or.inl rfl))
      (borrowWiring_length 0 reductionWire)
    exact fun j hj =>
      borrowWiring_bound (by omega) (Or.inl rfl) hj
  · simp only [borrowChunkGates, if_neg hzero]
    apply placedBorrowProbeGates_wellFormed
      (chunkWidthAt_positive hchunk)
      (borrowWiring_disjoint hchunk (Or.inr ⟨hzero, rfl⟩))
      (borrowWiring_length chunk (chunkCarryIn chunk))
    exact fun j hj =>
      borrowWiring_bound hchunk (Or.inr ⟨hzero, rfl⟩) hj

theorem detectionChunkGates_act
    {chunk i : Nat} {enabled : Bool}
    (hchunk : chunk < 8)
    (hsource : readField i constantOffset (chunkWidthAt chunk) = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i oneWire = if enabled = true then 1 else 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates (detectionChunkGates chunk) i =
      writeField i (carryWire chunk) 1
        ((bitValue i (carryWire chunk) +
          if enabled = true then
            (readField (if chunk = 0 then gap else 0) 0
                (chunkWidthAt chunk) +
              readField i (chunkOffset chunk) (chunkWidthAt chunk) +
              bitValue i (chunkCarryIn chunk)) /
                2 ^ chunkWidthAt chunk
          else 0) % 2) := by
  simpa [detectionChunkGates, chunkWiring, probeWiring] using
    (placedCarryProbeGates_act
      (value := if chunk = 0 then gap else 0)
      (width := chunkWidthAt chunk) (W := chunkWiring chunk oneWire)
      (i := i) (enabled := enabled)
      (chunkWidthAt_positive hchunk)
      (chunkWiring_disjoint hchunk (Or.inl rfl))
      (chunkWiring_length chunk oneWire)
      hsource houtput hcontrol hscratch)

theorem additionChunkGates_act
    {chunk i : Nat} {enabled : Bool}
    (hchunk : chunk < 8)
    (hsource : readField i constantOffset (chunkWidthAt chunk) = 0)
    (hcontrol : bitValue i reductionWire =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates (additionChunkGates chunk) i =
      if enabled = true then
        writeField
          (writeField i (chunkOffset chunk) (chunkWidthAt chunk)
            ((readField (if chunk = 0 then gap else 0) 0
                (chunkWidthAt chunk) +
              readField i (chunkOffset chunk) (chunkWidthAt chunk) +
              bitValue i (chunkCarryIn chunk)) %
                2 ^ chunkWidthAt chunk))
          (carryWire chunk) 1
            ((bitValue i (carryWire chunk) +
              (readField (if chunk = 0 then gap else 0) 0
                  (chunkWidthAt chunk) +
                readField i (chunkOffset chunk) (chunkWidthAt chunk) +
                bitValue i (chunkCarryIn chunk)) /
                  2 ^ chunkWidthAt chunk) % 2)
      else i := by
  simpa [additionChunkGates, additionWiring, probeWiring] using
    (placedChunkAddGates_act
      (value := if chunk = 0 then gap else 0)
      (width := chunkWidthAt chunk) (W := additionWiring chunk)
      (i := i) (enabled := enabled)
      (chunkWidthAt_positive hchunk)
      (additionWiring_disjoint hchunk)
      (additionWiring_length chunk)
      hsource hcontrol hscratch)

theorem borrowChunkGates_act
    {chunk i : Nat} {enabled : Bool}
    (hchunk : chunk < 8)
    (hsource : readField i constantOffset (chunkWidthAt chunk) = 0)
    (hcarry : bitValue i zeroCarryWire = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i
        (if chunk = 0 then reductionWire else chunkCarryIn chunk) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates (borrowChunkGates chunk) i =
      writeField i (carryWire chunk) 1
        ((bitValue i (carryWire chunk) +
          if enabled = true then
            Adder.borrow
              (readField (if chunk = 0 then gap else 1) 0
                (chunkWidthAt chunk))
              (readField i (chunkOffset chunk) (chunkWidthAt chunk))
          else 0) % 2) := by
  have hcontrol' : bitValue i
      ((borrowWiring chunk
        (if chunk = 0 then reductionWire else chunkCarryIn chunk)).getD 4 0) =
      if enabled = true then 1 else 0 := by
    simpa [borrowWiring, probeWiring] using hcontrol
  have hdisjoint : Wiring.Disjoint (probeLayout (chunkWidthAt chunk))
      (borrowWiring chunk
        (if chunk = 0 then reductionWire else chunkCarryIn chunk)) := by
    by_cases hzero : chunk = 0
    · subst chunk
      exact borrowWiring_disjoint (by omega) (Or.inl rfl)
    · exact borrowWiring_disjoint hchunk
        (Or.inr ⟨hzero, if_neg hzero⟩)
  simpa [borrowChunkGates, borrowWiring, probeWiring] using
    (placedBorrowProbeGates_act
      (value := if chunk = 0 then gap else 1)
      (width := chunkWidthAt chunk)
      (W := borrowWiring chunk
        (if chunk = 0 then reductionWire else chunkCarryIn chunk))
      (i := i) (enabled := enabled)
      (chunkWidthAt_positive hchunk) hdisjoint
      (borrowWiring_length chunk
        (if chunk = 0 then reductionWire else chunkCarryIn chunk))
      hsource hcarry houtput hcontrol' hscratch)

theorem borrowChunkGates_clear
    {chunk i x : Nat}
    (hchunk : chunk < 8)
    (hoverflow : carry7 x = 1)
    (hstable : CorrectionStable i)
    (htarget : readField i (chunkOffset chunk) (chunkWidthAt chunk) =
      chunkResult x chunk)
    (hcurrent : bitValue i (carryWire chunk) = 1)
    (hcontrol : bitValue i
      (if chunk = 0 then reductionWire else chunkCarryIn chunk) = 1) :
    actGates (borrowChunkGates chunk) i =
      writeField i (carryWire chunk) 1 0 := by
  rw [borrowChunkGates_act (enabled := true) (hchunk := hchunk)
    (hsource := hstable.constantChunk hchunk)
    (hcarry := hstable.zeroCarry) (houtput := hstable.output)
    (hcontrol := hcontrol) (hscratch := hstable.scratch)]
  rw [readField_borrowAddend hchunk, htarget, hcurrent,
    borrow_chunkResult_eq_one hchunk hoverflow]
  rfl

theorem borrowChunkGates_clear_general
    {chunk i x : Nat}
    (hchunk : chunk < 8)
    (hstable : CorrectionStable i)
    (htarget : readField i (chunkOffset chunk) (chunkWidthAt chunk) =
      chunkResult x chunk)
    (hcurrent : bitValue i (carryWire chunk) = chunkCarryValue x chunk)
    (hcontrol : bitValue i
      (if chunk = 0 then reductionWire else chunkCarryIn chunk) =
        if chunk = 0 then 1 else chunkIncomingCarryValue x chunk) :
    actGates (borrowChunkGates chunk) i =
      writeField i (carryWire chunk) 1 0 := by
  by_cases hzero : chunk = 0
  · subst chunk
    rw [borrowChunkGates_act (enabled := true) (hchunk := hchunk)
      (hsource := hstable.constantChunk hchunk)
      (hcarry := hstable.zeroCarry) (houtput := hstable.output)
      (hcontrol := by simpa using hcontrol) (hscratch := hstable.scratch)]
    rw [readField_borrowAddend hchunk, htarget, hcurrent]
    have hborrow : Adder.borrow gap (chunkResult x 0) =
        chunkCarryValue x 0 := by
      simpa using borrow_chunkResult_eq_carry (x := x) (chunk := 0) hchunk
    simp only [if_true]
    rw [hborrow]
    have hlt := chunkCarryValue_lt_two (x := x) hchunk
    interval_cases chunkCarryValue x 0 <;> rfl
  · have hincoming : chunkIncomingCarryValue x chunk < 2 := by
      simp only [chunkIncomingCarryValue, if_neg hzero]
      exact chunkCarryValue_lt_two (x := x) (chunk := chunk - 1) (by omega)
    interval_cases hvalue : chunkIncomingCarryValue x chunk
    · have hcurrentZero : chunkCarryValue x chunk = 0 := by
        have hborrow := borrow_chunkResult_eq_carry (x := x) hchunk
        simp [hzero, hvalue] at hborrow
        omega
      rw [borrowChunkGates_act (enabled := false) (hchunk := hchunk)
        (hsource := hstable.constantChunk hchunk)
        (hcarry := hstable.zeroCarry) (houtput := hstable.output)
        (hcontrol := by simpa [hzero, hvalue] using hcontrol)
        (hscratch := hstable.scratch)]
      simp [hcurrent, hcurrentZero]
    · have hborrow :
          Adder.borrow 1 (chunkResult x chunk) = chunkCarryValue x chunk := by
        have h := borrow_chunkResult_eq_carry (x := x) hchunk
        simpa [hzero, hvalue] using h
      rw [borrowChunkGates_act (enabled := true) (hchunk := hchunk)
        (hsource := hstable.constantChunk hchunk)
        (hcarry := hstable.zeroCarry) (houtput := hstable.output)
        (hcontrol := by simpa [hzero, hvalue] using hcontrol)
        (hscratch := hstable.scratch)]
      rw [readField_borrowAddend hchunk, htarget, hcurrent]
      simp only [if_true, if_neg hzero]
      rw [hborrow]
      have hlt := chunkCarryValue_lt_two (x := x) hchunk
      interval_cases chunkCarryValue x chunk <;> rfl

theorem additionChunkGates_addedPrefix
    {i x chunk : Nat}
    (hchunk : chunk < 8)
    (hx : readField i targetOffset wordWidth = x)
    (hstable : CorrectionStable i)
    (hcarries : ∀ j, j < 8 → bitValue i (carryWire j) = 0) :
    actGates (additionChunkGates chunk) (addedPrefix i x chunk) =
      addedPrefix i x (chunk + 1) := by
  have hprefixStable : CorrectionStable (addedPrefix i x chunk) :=
    addedPrefix_stable hstable (by omega)
  have htarget : readField (addedPrefix i x chunk)
      (chunkOffset chunk) (chunkWidthAt chunk) = chunkDigit x chunk := by
    rw [readField_addedPrefix_future (n := chunk) (chunk := chunk)
      (by omega) hchunk, readField_targetChunk hchunk hx]
    rfl
  have hcurrent : bitValue (addedPrefix i x chunk) (carryWire chunk) = 0 := by
    rw [bitValue_addedPrefix_future (n := chunk) (chunk := chunk)
      (by omega) hchunk, hcarries chunk hchunk]
  have hincoming : bitValue (addedPrefix i x chunk) (chunkCarryIn chunk) =
      chunkIncomingCarryValue x chunk := by
    by_cases hzero : chunk = 0
    · subst chunk
      simpa [chunkCarryIn, chunkIncomingCarryValue] using
        hprefixStable.zeroCarry
    · rw [chunkCarryIn, if_neg hzero,
        bitValue_addedPrefix_previous (n := chunk) (by omega) (by omega)]
      simp [chunkIncomingCarryValue, hzero]
  have haddend : readField (if chunk = 0 then gap else 0) 0
      (chunkWidthAt chunk) = chunkAddend chunk := by
    simpa [chunkAddend] using readField_chunkAddend hchunk
  rw [additionChunkGates_act (enabled := true) (hchunk := hchunk)
    (hsource := hprefixStable.constantChunk hchunk)
    (hcontrol := hprefixStable.reduction)
    (hscratch := hprefixStable.scratch)]
  simp only [if_true]
  rw [haddend, htarget, hincoming, hcurrent,
    Nat.zero_add, ← chunkCarryValue_eq_div hchunk,
    Nat.mod_eq_of_lt (chunkCarryValue_lt_two hchunk)]
  rfl

theorem additionChunks_act {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hreduction : bitValue i reductionWire = 1)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates additionChunks i = addedState i x := by
  have hstable : CorrectionStable i :=
    ⟨hconstant, houtput, hreduction, hscratch, hzeroCarry⟩
  have h0 := additionChunkGates_addedPrefix (chunk := 0) (by decide)
    hx hstable hcarries
  have h1 := additionChunkGates_addedPrefix (chunk := 1) (by decide)
    hx hstable hcarries
  have h2 := additionChunkGates_addedPrefix (chunk := 2) (by decide)
    hx hstable hcarries
  have h3 := additionChunkGates_addedPrefix (chunk := 3) (by decide)
    hx hstable hcarries
  have h4 := additionChunkGates_addedPrefix (chunk := 4) (by decide)
    hx hstable hcarries
  have h5 := additionChunkGates_addedPrefix (chunk := 5) (by decide)
    hx hstable hcarries
  have h6 := additionChunkGates_addedPrefix (chunk := 6) (by decide)
    hx hstable hcarries
  have h7 := additionChunkGates_addedPrefix (chunk := 7) (by decide)
    hx hstable hcarries
  have h0' : actGates (additionChunkGates 0) i =
      addedPrefix i x 1 := by simpa [addedPrefix] using h0
  have h1' : actGates (additionChunkGates 1) (addedPrefix i x 1) =
      addedPrefix i x 2 := by simpa using h1
  have h2' : actGates (additionChunkGates 2) (addedPrefix i x 2) =
      addedPrefix i x 3 := by simpa using h2
  have h3' : actGates (additionChunkGates 3) (addedPrefix i x 3) =
      addedPrefix i x 4 := by simpa using h3
  have h4' : actGates (additionChunkGates 4) (addedPrefix i x 4) =
      addedPrefix i x 5 := by simpa using h4
  have h5' : actGates (additionChunkGates 5) (addedPrefix i x 5) =
      addedPrefix i x 6 := by simpa using h5
  have h6' : actGates (additionChunkGates 6) (addedPrefix i x 6) =
      addedPrefix i x 7 := by simpa using h6
  have h7' : actGates (additionChunkGates 7) (addedPrefix i x 7) =
      addedPrefix i x 8 := by simpa using h7
  rw [additionChunks, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append, actGates_append, actGates_append,
    h0', h1', h2', h3', h4', h5', h6', h7']
  rfl

theorem borrowChunks_act_general {i x : Nat}
    (hstable : CorrectionStable i) :
    actGates borrowChunks (addedState i x) = clearedState i x := by
  let s8 := addedState i x
  let s7 := writeField s8 (carryWire 7) 1 0
  let s6 := writeField s7 (carryWire 6) 1 0
  let s5 := writeField s6 (carryWire 5) 1 0
  let s4 := writeField s5 (carryWire 4) 1 0
  let s3 := writeField s4 (carryWire 3) 1 0
  let s2 := writeField s3 (carryWire 2) 1 0
  let s1 := writeField s2 (carryWire 1) 1 0
  let s0 := writeField s1 (carryWire 0) 1 0
  have hstable8 : CorrectionStable s8 := by
    simpa only [s8, addedState] using addedPrefix_stable hstable (by decide)
  have hstep7 : actGates (borrowChunkGates 7) s8 = s7 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable8
    · simpa only [s8] using
        (readField_addedState (i := i) (x := x) (chunk := 7) (by decide))
    · simpa only [s8] using
        (bitValue_addedState (i := i) (x := x) (chunk := 7) (by decide))
    · simpa [s8, chunkCarryIn, chunkIncomingCarryValue] using
        (bitValue_addedState (i := i) (x := x) (chunk := 6) (by decide))
  have hstable7 : CorrectionStable s7 := hstable8.writeCarry
  have hstep6 : actGates (borrowChunkGates 6) s7 = s6 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable7
    · dsimp only [s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 6) (by decide)
    · dsimp only [s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 6) (by decide)]
    · change bitValue s7 (carryWire 5) = chunkCarryValue x 5
      dsimp only [s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 5) (by decide)]
  have hstable6 : CorrectionStable s6 := hstable7.writeCarry
  have hstep5 : actGates (borrowChunkGates 5) s6 = s5 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable6
    · dsimp only [s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 5) (by decide)
    · dsimp only [s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 5) (by decide)]
    · change bitValue s6 (carryWire 4) = chunkCarryValue x 4
      dsimp only [s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 4) (by decide)]
  have hstable5 : CorrectionStable s5 := hstable6.writeCarry
  have hstep4 : actGates (borrowChunkGates 4) s5 = s4 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable5
    · dsimp only [s5, s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 4) (by decide)
    · dsimp only [s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 4) (by decide)]
    · change bitValue s5 (carryWire 3) = chunkCarryValue x 3
      dsimp only [s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 3) (by decide)]
  have hstable4 : CorrectionStable s4 := hstable5.writeCarry
  have hstep3 : actGates (borrowChunkGates 3) s4 = s3 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable4
    · dsimp only [s4, s5, s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 3) (by decide)
    · dsimp only [s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 3) (by decide)]
    · change bitValue s4 (carryWire 2) = chunkCarryValue x 2
      dsimp only [s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 2) (by decide)]
  have hstable3 : CorrectionStable s3 := hstable4.writeCarry
  have hstep2 : actGates (borrowChunkGates 2) s3 = s2 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable3
    · dsimp only [s3, s4, s5, s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 2) (by decide)
    · dsimp only [s3, s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 2) (by decide)]
    · change bitValue s3 (carryWire 1) = chunkCarryValue x 1
      dsimp only [s3, s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 1) (by decide)]
  have hstable2 : CorrectionStable s2 := hstable3.writeCarry
  have hstep1 : actGates (borrowChunkGates 1) s2 = s1 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable2
    · dsimp only [s2, s3, s4, s5, s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 1) (by decide)
    · dsimp only [s2, s3, s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 1) (by decide)]
    · change bitValue s2 (carryWire 0) = chunkCarryValue x 0
      dsimp only [s2, s3, s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 0) (by decide)]
  have hstable1 : CorrectionStable s1 := hstable2.writeCarry
  have hstep0 : actGates (borrowChunkGates 0) s1 = s0 := by
    apply borrowChunkGates_clear_general (hchunk := by decide) hstable1
    · dsimp only [s1, s2, s3, s4, s5, s6, s7, s8]
      rw [readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel),
        readField_writeField_of_disjoint (by decide +kernel)]
      exact readField_addedState (chunk := 0) (by decide)
    · dsimp only [s1, s2, s3, s4, s5, s6, s7, s8]
      rw [bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_write_ne (by decide +kernel),
        bitValue_addedState (chunk := 0) (by decide)]
    · change bitValue s1 reductionWire = 1
      exact hstable1.reduction
  change actGates borrowChunks s8 = clearedState i x
  rw [borrowChunks, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append, actGates_append, actGates_append,
    hstep7, hstep6, hstep5, hstep4, hstep3, hstep2, hstep1, hstep0]
  rfl

theorem additionChunkGates_disabled
    {i chunk : Nat}
    (hchunk : chunk < 8)
    (hsource : readField i constantOffset (chunkWidthAt chunk) = 0)
    (hcontrol : bitValue i reductionWire = 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates (additionChunkGates chunk) i = i := by
  simpa using additionChunkGates_act (enabled := false) hchunk hsource
    hcontrol hscratch

theorem borrowChunkGates_disabled
    {i chunk : Nat}
    (hchunk : chunk < 8)
    (hsource : readField i constantOffset (chunkWidthAt chunk) = 0)
    (hcarry : bitValue i zeroCarryWire = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i
      (if chunk = 0 then reductionWire else chunkCarryIn chunk) = 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates (borrowChunkGates chunk) i = i := by
  rw [borrowChunkGates_act (enabled := false) hchunk hsource hcarry houtput
    hcontrol hscratch]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt i (carryWire chunk)),
    ← readField_one, writeField_read]

theorem additionChunks_disabled
    {i : Nat}
    (hconstant : readField i constantOffset chunkWidth = 0)
    (hcontrol : bitValue i reductionWire = 0)
    (hscratch : i.testBit scratchWire = false) :
    actGates additionChunks i = i := by
  have hsource : ∀ chunk, chunk < 8 →
      readField i constantOffset (chunkWidthAt chunk) = 0 := by
    intro chunk hchunk
    by_cases hlast : chunk = 7
    · subst chunk
      exact readField_narrow (by decide) hconstant
    · have hlt : chunk < 7 := by omega
      simpa [chunkWidthAt, hlt, chunkWidth] using hconstant
  have h0 := additionChunkGates_disabled (chunk := 0) (by decide)
    (hsource 0 (by decide)) hcontrol hscratch
  have h1 := additionChunkGates_disabled (chunk := 1) (by decide)
    (hsource 1 (by decide)) hcontrol hscratch
  have h2 := additionChunkGates_disabled (chunk := 2) (by decide)
    (hsource 2 (by decide)) hcontrol hscratch
  have h3 := additionChunkGates_disabled (chunk := 3) (by decide)
    (hsource 3 (by decide)) hcontrol hscratch
  have h4 := additionChunkGates_disabled (chunk := 4) (by decide)
    (hsource 4 (by decide)) hcontrol hscratch
  have h5 := additionChunkGates_disabled (chunk := 5) (by decide)
    (hsource 5 (by decide)) hcontrol hscratch
  have h6 := additionChunkGates_disabled (chunk := 6) (by decide)
    (hsource 6 (by decide)) hcontrol hscratch
  have h7 := additionChunkGates_disabled (chunk := 7) (by decide)
    (hsource 7 (by decide)) hcontrol hscratch
  simp [additionChunks, actGates_append, h0, h1, h2, h3, h4, h5, h6, h7]

theorem borrowChunks_disabled
    {i : Nat}
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i reductionWire = 0)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates borrowChunks i = i := by
  have hsource : ∀ chunk, chunk < 8 →
      readField i constantOffset (chunkWidthAt chunk) = 0 := by
    intro chunk hchunk
    by_cases hlast : chunk = 7
    · subst chunk
      exact readField_narrow (by decide) hconstant
    · have hlt : chunk < 7 := by omega
      simpa [chunkWidthAt, hlt, chunkWidth] using hconstant
  have hchunkControl : ∀ chunk, chunk < 8 →
      bitValue i (if chunk = 0 then reductionWire else chunkCarryIn chunk) = 0 := by
    intro chunk hchunk
    by_cases hzero : chunk = 0
    · simpa [hzero] using hcontrol
    · rw [if_neg hzero, chunkCarryIn, if_neg hzero]
      exact hcarries (chunk - 1) (by omega)
  have h0 := borrowChunkGates_disabled (chunk := 0) (by decide)
    (hsource 0 (by decide)) hzeroCarry houtput
    (hchunkControl 0 (by decide)) hscratch
  have h1 := borrowChunkGates_disabled (chunk := 1) (by decide)
    (hsource 1 (by decide)) hzeroCarry houtput
    (hchunkControl 1 (by decide)) hscratch
  have h2 := borrowChunkGates_disabled (chunk := 2) (by decide)
    (hsource 2 (by decide)) hzeroCarry houtput
    (hchunkControl 2 (by decide)) hscratch
  have h3 := borrowChunkGates_disabled (chunk := 3) (by decide)
    (hsource 3 (by decide)) hzeroCarry houtput
    (hchunkControl 3 (by decide)) hscratch
  have h4 := borrowChunkGates_disabled (chunk := 4) (by decide)
    (hsource 4 (by decide)) hzeroCarry houtput
    (hchunkControl 4 (by decide)) hscratch
  have h5 := borrowChunkGates_disabled (chunk := 5) (by decide)
    (hsource 5 (by decide)) hzeroCarry houtput
    (hchunkControl 5 (by decide)) hscratch
  have h6 := borrowChunkGates_disabled (chunk := 6) (by decide)
    (hsource 6 (by decide)) hzeroCarry houtput
    (hchunkControl 6 (by decide)) hscratch
  have h7 := borrowChunkGates_disabled (chunk := 7) (by decide)
    (hsource 7 (by decide)) hzeroCarry houtput
    (hchunkControl 7 (by decide)) hscratch
  simp [borrowChunks, actGates_append, h0, h1, h2, h3, h4, h5, h6, h7]

theorem correctionGates_disabled
    {i : Nat}
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i reductionWire = 0)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates correctionGates i = i := by
  rw [correctionGates, actGates_append,
    additionChunks_disabled hconstant hcontrol hscratch,
    borrowChunks_disabled hconstant houtput hcontrol hscratch hzeroCarry hcarries]

theorem correctionGates_enabled
    {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i reductionWire = 1)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates correctionGates i =
      writeField i targetOffset wordWidth (gap + x) := by
  have hstable : CorrectionStable i :=
    ⟨hconstant, houtput, hcontrol, hscratch, hzeroCarry⟩
  rw [correctionGates, actGates_append,
    additionChunks_act hx hconstant houtput hcontrol hscratch hzeroCarry hcarries,
    borrowChunks_act_general hstable,
    clearedState_eq_writeField hcarries]

theorem correctionGates_act
    {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hcontrol : bitValue i reductionWire = carry7 x)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates correctionGates i =
      if carry7 x = 1 then writeField i targetOffset wordWidth (gap + x) else i := by
  have hlt := carry7_lt_two x
  interval_cases hcarry : carry7 x
  · simp only [hcarry, zero_ne_one, if_false]
    exact correctionGates_disabled hconstant houtput (by simpa [hcarry] using hcontrol)
      hscratch hzeroCarry hcarries
  · simp only [hcarry, if_true]
    exact correctionGates_enabled hx hconstant houtput
      (by simpa [hcarry] using hcontrol) hscratch hzeroCarry hcarries

theorem detectionChunks_act {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hone : bitValue i oneWire = 1)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates detectionChunks i = detectedState i x := by
  let s0 := writeField i (carryWire 0) 1 (carry0 x)
  let s1 := writeField s0 (carryWire 1) 1 (carry1 x)
  let s2 := writeField s1 (carryWire 2) 1 (carry2 x)
  let s3 := writeField s2 (carryWire 3) 1 (carry3 x)
  let s4 := writeField s3 (carryWire 4) 1 (carry4 x)
  let s5 := writeField s4 (carryWire 5) 1 (carry5 x)
  let s6 := writeField s5 (carryWire 6) 1 (carry6 x)
  let s7 := writeField s6 (carryWire 7) 1 (carry7 x)
  have hstable0 : DetectionStable i x :=
    ⟨hx, hconstant, houtput, hone, hscratch⟩
  have hstep0 : actGates (detectionChunkGates 0) i = s0 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hconstant) (houtput := houtput)
      (hcontrol := hone) (hscratch := hscratch)]
    rw [readField_targetChunk (chunk := 0) (by decide) hx]
    have hgap33 : gap < 2 ^ 33 := by
      simpa [chunkWidth] using gap_lt
    have h07 : 0 < 7 := by decide
    simp only [chunkWidthAt, chunkOffset, chunkCarryIn,
      h07, if_true, hcarries 0 (by decide), hzeroCarry, Nat.zero_add,
      Nat.mul_zero, Nat.pow_zero, Nat.div_one, readField_zero]
    have hgapMod : gap % 8589934592 = gap :=
      Nat.mod_eq_of_lt (by simpa using hgap33)
    rw [hgapMod]
    change writeField i (carryWire 0) 1 (carry0 x % 2) = s0
    rw [Nat.mod_eq_of_lt (carry0_lt_two x)]
  have hstable1 : DetectionStable s0 x := by
    exact hstable0.writeCarry
  have hs0carry0 : bitValue s0 (carryWire 0) = carry0 x := by
    dsimp only [s0]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry0_lt_two x)]
  have hs0carry1 : bitValue s0 (carryWire 1) = 0 := by
    dsimp only [s0]
    rw [bitValue_write_ne (by decide +kernel), hcarries 1 (by decide)]
  have hstep1 : actGates (detectionChunkGates 1) s0 = s1 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable1.constant) (houtput := hstable1.output)
      (hcontrol := hstable1.one) (hscratch := hstable1.scratch)]
    rw [readField_targetChunk (chunk := 1) (by decide) hstable1.target]
    have h10 : 1 ≠ 0 := by decide
    have h17 : 1 < 7 := by decide
    simp only [chunkWidthAt, h17, if_true, chunkOffset, Nat.mul_one,
      chunkCarryIn, h10, if_false, Nat.sub_self, hs0carry1, hs0carry0,
      readField_zero, Nat.zero_mod, Nat.zero_add]
    change writeField s0 (carryWire 1) 1 (carry1 x % 2) = s1
    rw [Nat.mod_eq_of_lt (carry1_lt_two x)]
  have hstable2 : DetectionStable s1 x := by
    exact hstable1.writeCarry
  have hs1carry1 : bitValue s1 (carryWire 1) = carry1 x := by
    dsimp only [s1]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry1_lt_two x)]
  have hs1carry2 : bitValue s1 (carryWire 2) = 0 := by
    dsimp only [s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 2 (by decide)]
  have hstep2 : actGates (detectionChunkGates 2) s1 = s2 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable2.constant) (houtput := hstable2.output)
      (hcontrol := hstable2.one) (hscratch := hstable2.scratch)]
    rw [readField_targetChunk (chunk := 2) (by decide) hstable2.target]
    have h20 : 2 ≠ 0 := by decide
    have h27 : 2 < 7 := by decide
    simp only [chunkWidthAt, h27, if_true, chunkOffset, chunkCarryIn,
      h20, if_false, hs1carry2, hs1carry1, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s1 (carryWire 2) 1 (carry2 x % 2) = s2
    rw [Nat.mod_eq_of_lt (carry2_lt_two x)]
  have hstable3 : DetectionStable s2 x := by
    exact hstable2.writeCarry
  have hs2carry2 : bitValue s2 (carryWire 2) = carry2 x := by
    dsimp only [s2]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry2_lt_two x)]
  have hs2carry3 : bitValue s2 (carryWire 3) = 0 := by
    dsimp only [s2, s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 3 (by decide)]
  have hstep3 : actGates (detectionChunkGates 3) s2 = s3 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable3.constant) (houtput := hstable3.output)
      (hcontrol := hstable3.one) (hscratch := hstable3.scratch)]
    rw [readField_targetChunk (chunk := 3) (by decide) hstable3.target]
    have h30 : 3 ≠ 0 := by decide
    have h37 : 3 < 7 := by decide
    simp only [chunkWidthAt, h37, if_true, chunkOffset, chunkCarryIn,
      h30, if_false, hs2carry3, hs2carry2, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s2 (carryWire 3) 1 (carry3 x % 2) = s3
    rw [Nat.mod_eq_of_lt (carry3_lt_two x)]
  have hstable4 : DetectionStable s3 x := by
    exact hstable3.writeCarry
  have hs3carry3 : bitValue s3 (carryWire 3) = carry3 x := by
    dsimp only [s3]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry3_lt_two x)]
  have hs3carry4 : bitValue s3 (carryWire 4) = 0 := by
    dsimp only [s3, s2, s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 4 (by decide)]
  have hstep4 : actGates (detectionChunkGates 4) s3 = s4 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable4.constant) (houtput := hstable4.output)
      (hcontrol := hstable4.one) (hscratch := hstable4.scratch)]
    rw [readField_targetChunk (chunk := 4) (by decide) hstable4.target]
    have h40 : 4 ≠ 0 := by decide
    have h47 : 4 < 7 := by decide
    simp only [chunkWidthAt, h47, if_true, chunkOffset, chunkCarryIn,
      h40, if_false, hs3carry4, hs3carry3, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s3 (carryWire 4) 1 (carry4 x % 2) = s4
    rw [Nat.mod_eq_of_lt (carry4_lt_two x)]
  have hstable5 : DetectionStable s4 x := by
    exact hstable4.writeCarry
  have hs4carry4 : bitValue s4 (carryWire 4) = carry4 x := by
    dsimp only [s4]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry4_lt_two x)]
  have hs4carry5 : bitValue s4 (carryWire 5) = 0 := by
    dsimp only [s4, s3, s2, s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 5 (by decide)]
  have hstep5 : actGates (detectionChunkGates 5) s4 = s5 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable5.constant) (houtput := hstable5.output)
      (hcontrol := hstable5.one) (hscratch := hstable5.scratch)]
    rw [readField_targetChunk (chunk := 5) (by decide) hstable5.target]
    have h50 : 5 ≠ 0 := by decide
    have h57 : 5 < 7 := by decide
    simp only [chunkWidthAt, h57, if_true, chunkOffset, chunkCarryIn,
      h50, if_false, hs4carry5, hs4carry4, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s4 (carryWire 5) 1 (carry5 x % 2) = s5
    rw [Nat.mod_eq_of_lt (carry5_lt_two x)]
  have hstable6 : DetectionStable s5 x := by
    exact hstable5.writeCarry
  have hs5carry5 : bitValue s5 (carryWire 5) = carry5 x := by
    dsimp only [s5]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry5_lt_two x)]
  have hs5carry6 : bitValue s5 (carryWire 6) = 0 := by
    dsimp only [s5, s4, s3, s2, s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 6 (by decide)]
  have hstep6 : actGates (detectionChunkGates 6) s5 = s6 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := hstable6.constant) (houtput := hstable6.output)
      (hcontrol := hstable6.one) (hscratch := hstable6.scratch)]
    rw [readField_targetChunk (chunk := 6) (by decide) hstable6.target]
    have h60 : 6 ≠ 0 := by decide
    have h67 : 6 < 7 := by decide
    simp only [chunkWidthAt, h67, if_true, chunkOffset, chunkCarryIn,
      h60, if_false, hs5carry6, hs5carry5, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s5 (carryWire 6) 1 (carry6 x % 2) = s6
    rw [Nat.mod_eq_of_lt (carry6_lt_two x)]
  have hstable7 : DetectionStable s6 x := by
    exact hstable6.writeCarry
  have hs6carry6 : bitValue s6 (carryWire 6) = carry6 x := by
    dsimp only [s6]
    rw [bitValue_write_self, Nat.mod_eq_of_lt (carry6_lt_two x)]
  have hs6carry7 : bitValue s6 (carryWire 7) = 0 := by
    dsimp only [s6, s5, s4, s3, s2, s1, s0]
    rw [bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel),
      bitValue_write_ne (by decide +kernel), hcarries 7 (by decide)]
  have hstep7 : actGates (detectionChunkGates 7) s6 = s7 := by
    rw [detectionChunkGates_act (enabled := true) (hchunk := by decide)
      (hsource := readField_narrow (by decide) hstable7.constant)
      (houtput := hstable7.output) (hcontrol := hstable7.one)
      (hscratch := hstable7.scratch)]
    rw [readField_targetChunk (chunk := 7) (by decide) hstable7.target]
    have h70 : 7 ≠ 0 := by decide
    have h77 : ¬ 7 < 7 := by decide
    simp only [chunkWidthAt, h77, if_false, chunkOffset, chunkCarryIn,
      h70, hs6carry7, hs6carry6, readField_zero, Nat.zero_mod,
      Nat.zero_add]
    change writeField s6 (carryWire 7) 1 (carry7 x % 2) = s7
    rw [Nat.mod_eq_of_lt (carry7_lt_two x)]
  rw [detectionChunks, actGates_append, actGates_append, actGates_append,
    actGates_append, actGates_append, actGates_append, actGates_append,
    hstep0, hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hstep7]
  rfl

theorem detectionComputeGates_act {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hone : bitValue i oneWire = 0)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates detectionComputeGates i =
      detectedState (writeField i oneWire 1 1) x := by
  let j := writeField i oneWire 1 1
  have hxgate : actGates [.x oneWire] i = j := by
    simp only [actGates_cons, actGates_nil, act_x_write, hone,
      Nat.zero_add]
    rfl
  have hjx : readField j targetOffset wordWidth = x := by
    dsimp only [j]
    rw [readField_writeField_of_disjoint (by decide +kernel), hx]
  have hjconstant : readField j constantOffset chunkWidth = 0 := by
    dsimp only [j]
    rw [readField_writeField_of_disjoint (by decide +kernel), hconstant]
  have hjoutput : bitValue j probeOutputWire = 0 := by
    dsimp only [j]
    rw [bitValue_write_ne (by decide +kernel), houtput]
  have hjone : bitValue j oneWire = 1 := by
    dsimp only [j]
    rw [bitValue_write_self]
  have hjscratch : j.testBit scratchWire = false := by
    dsimp only [j]
    rw [testBit_writeField_outside (by decide +kernel), hscratch]
  have hjzeroCarry : bitValue j zeroCarryWire = 0 := by
    dsimp only [j]
    rw [bitValue_write_ne (by decide +kernel), hzeroCarry]
  have hjcarries : ∀ chunk, chunk < 8 →
      bitValue j (carryWire chunk) = 0 := by
    intro chunk hchunk
    dsimp only [j]
    rw [bitValue_write_ne (by
      unfold carryWire oneWire
      omega), hcarries chunk hchunk]
  rw [detectionComputeGates, actGates_append, hxgate]
  exact detectionChunks_act hjx hjconstant hjoutput hjone hjscratch
    hjzeroCarry hjcarries

theorem detectionChunkGates_avoids_reduction {chunk : Nat}
    (hchunk : chunk < 8) :
    ∀ gate ∈ detectionChunkGates chunk, ∀ q ∈ gate.wires,
      q < reductionWire ∨ reductionWire + 1 ≤ q := by
  apply placeGates_avoids (chunkWiring_length chunk oneWire)
  · intro gate hgate
    exact List.all_eq_true.mp
      (carryProbeGates_wellFormed (chunkWidthAt_positive hchunk)) gate hgate
  · intro j hj
    interval_cases chunk <;>
      simp [probeLayout] at hj <;> interval_cases j <;> decide +kernel

theorem detectionComputeGates_avoids_reduction :
    ∀ gate ∈ detectionComputeGates, ∀ q ∈ gate.wires,
      q < reductionWire ∨ reductionWire + 1 ≤ q := by
  intro gate hgate q hq
  have htop : gate ∈ [.x oneWire] ∨ gate ∈ detectionChunks := by
    exact List.mem_append.mp (by simpa [detectionComputeGates] using hgate)
  rcases htop with hx | hchunks
  · simp only [List.mem_singleton] at hx
    subst gate
    simp [RGate.wires] at hq
    subst q
    decide +kernel
  · simp only [detectionChunks, List.mem_append] at hchunks
    rcases hchunks with h0123456 | h7
    · rcases h0123456 with h012345 | h6
      · rcases h012345 with h01234 | h5
        · rcases h01234 with h0123 | h4
          · rcases h0123 with h012 | h3
            · rcases h012 with h01 | h2
              · rcases h01 with h0 | h1
                · exact detectionChunkGates_avoids_reduction
                    (by decide) gate h0 q hq
                · exact detectionChunkGates_avoids_reduction
                    (by decide) gate h1 q hq
              · exact detectionChunkGates_avoids_reduction
                  (by decide) gate h2 q hq
            · exact detectionChunkGates_avoids_reduction
                (by decide) gate h3 q hq
          · exact detectionChunkGates_avoids_reduction
              (by decide) gate h4 q hq
        · exact detectionChunkGates_avoids_reduction
            (by decide) gate h5 q hq
      · exact detectionChunkGates_avoids_reduction
          (by decide) gate h6 q hq
    · exact detectionChunkGates_avoids_reduction (by decide) gate h7 q hq

theorem detectionComputeGates_wellFormed :
    detectionComputeGates.all (RGate.wellFormed width) = true := by
  have h0 := detectionChunkGates_wellFormed (chunk := 0) (by decide)
  have h1 := detectionChunkGates_wellFormed (chunk := 1) (by decide)
  have h2 := detectionChunkGates_wellFormed (chunk := 2) (by decide)
  have h3 := detectionChunkGates_wellFormed (chunk := 3) (by decide)
  have h4 := detectionChunkGates_wellFormed (chunk := 4) (by decide)
  have h5 := detectionChunkGates_wellFormed (chunk := 5) (by decide)
  have h6 := detectionChunkGates_wellFormed (chunk := 6) (by decide)
  have h7 := detectionChunkGates_wellFormed (chunk := 7) (by decide)
  simp only [detectionComputeGates, detectionChunks, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  decide +kernel

theorem detectionGates_wellFormed :
    detectionGates.all (RGate.wellFormed width) = true := by
  have hcompute := detectionComputeGates_wellFormed
  simp only [detectionGates, List.all_append, List.all_cons, List.all_nil,
    List.all_reverse, Bool.and_true]
  rw [hcompute]
  decide +kernel

theorem bitValue_detectedState_carry7 (i x : Nat) :
    bitValue (detectedState i x) (carryWire 7) = carry7 x := by
  unfold detectedState
  rw [bitValue_write_self, Nat.mod_eq_of_lt (carry7_lt_two x)]

theorem detectionGates_act {i x : Nat}
    (hx : readField i targetOffset wordWidth = x)
    (hconstant : readField i constantOffset chunkWidth = 0)
    (houtput : bitValue i probeOutputWire = 0)
    (hone : bitValue i oneWire = 0)
    (hscratch : i.testBit scratchWire = false)
    (hzeroCarry : bitValue i zeroCarryWire = 0)
    (hcarries : ∀ chunk, chunk < 8 → bitValue i (carryWire chunk) = 0) :
    actGates detectionGates i =
      writeField i reductionWire 1
        ((bitValue i reductionWire + (gap + x) / 2 ^ wordWidth) % 2) := by
  let compute := detectionComputeGates
  have hcopy : ∀ j,
      actGates [.cx (carryWire 7) reductionWire] j =
        writeField j reductionWire 1
          ((bitValue j reductionWire + bitValue j (carryWire 7)) % 2) := by
    intro j
    simp only [actGates_cons, actGates_nil, act_cx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute) (cp := [.cx (carryWire 7) reductionWire])
    (w := width) (off := reductionWire) (len := 1)
    (f := fun j =>
      (bitValue j reductionWire + bitValue j (carryWire 7)) % 2)
    (by simpa [compute] using detectionComputeGates_wellFormed)
    (by simpa [compute] using detectionComputeGates_avoids_reduction)
    hcopy i
  have hcompute := detectionComputeGates_act hx hconstant houtput hone
    hscratch hzeroCarry hcarries
  have hreduction : bitValue (actGates compute i) reductionWire =
      bitValue i reductionWire := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside
      (by simpa [compute] using detectionComputeGates_avoids_reduction) i
  have hcarry : bitValue (actGates compute i) (carryWire 7) = carry7 x := by
    rw [show compute = detectionComputeGates from rfl, hcompute,
      bitValue_detectedState_carry7]
  have hxlt : x < 2 ^ wordWidth := by
    rw [← hx]
    exact readField_lt i targetOffset wordWidth
  rw [detectionGates, hsandwich, hreduction, hcarry,
    carry7_eq_overflow hxlt]

theorem correctionGates_wellFormed :
    correctionGates.all (RGate.wellFormed width) = true := by
  have ha0 := additionChunkGates_wellFormed (chunk := 0) (by decide)
  have ha1 := additionChunkGates_wellFormed (chunk := 1) (by decide)
  have ha2 := additionChunkGates_wellFormed (chunk := 2) (by decide)
  have ha3 := additionChunkGates_wellFormed (chunk := 3) (by decide)
  have ha4 := additionChunkGates_wellFormed (chunk := 4) (by decide)
  have ha5 := additionChunkGates_wellFormed (chunk := 5) (by decide)
  have ha6 := additionChunkGates_wellFormed (chunk := 6) (by decide)
  have ha7 := additionChunkGates_wellFormed (chunk := 7) (by decide)
  have hb0 := borrowChunkGates_wellFormed (chunk := 0) (by decide)
  have hb1 := borrowChunkGates_wellFormed (chunk := 1) (by decide)
  have hb2 := borrowChunkGates_wellFormed (chunk := 2) (by decide)
  have hb3 := borrowChunkGates_wellFormed (chunk := 3) (by decide)
  have hb4 := borrowChunkGates_wellFormed (chunk := 4) (by decide)
  have hb5 := borrowChunkGates_wellFormed (chunk := 5) (by decide)
  have hb6 := borrowChunkGates_wellFormed (chunk := 6) (by decide)
  have hb7 := borrowChunkGates_wellFormed (chunk := 7) (by decide)
  simp only [correctionGates, additionChunks, borrowChunks, List.all_append]
  rw [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
    hb7, hb6, hb5, hb4, hb3, hb2, hb1, hb0]
  decide

end VQ.Curve.PackedReversibleSecp256k1
