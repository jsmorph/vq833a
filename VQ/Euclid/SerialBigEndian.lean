/-
Ripple addition on two physically big-endian words.
-/
import VQ.Euclid.Serial
import VQ.Euclid.State
import VQ.Reversible.Relabel

namespace VQ
namespace Euclid
namespace SerialBigEndian

open Reversible

def layout (width : Nat) : Layout := [width, width, 1, 1]

def reverseWire (width q : Nat) : Nat :=
  if q < width then width - 1 - q
  else if q < 2 * width then width + (2 * width - 1 - q)
  else q

theorem layout_width (width : Nat) :
    (layout width).width = 2 * width + 2 := by
  simp [layout, Layout.width]
  omega

theorem reverseWire_lt {width q : Nat} (hq : q < 2 * width + 2) :
    reverseWire width q < 2 * width + 2 := by
  unfold reverseWire
  by_cases ht : q < width
  · rw [if_pos ht]
    omega
  · rw [if_neg ht]
    by_cases hs : q < 2 * width
    · rw [if_pos hs]
      omega
    · rw [if_neg hs]
      exact hq

theorem reverseWire_lt_body {width q : Nat} (hq : q < 2 * width + 1) :
    reverseWire width q < 2 * width + 1 := by
  unfold reverseWire
  by_cases ht : q < width
  · rw [if_pos ht]
    omega
  · rw [if_neg ht]
    by_cases hs : q < 2 * width
    · rw [if_pos hs]
      omega
    · rw [if_neg hs]
      exact hq

theorem reverseWire_involutive {width q : Nat} (_hq : q < 2 * width + 2) :
    reverseWire width (reverseWire width q) = q := by
  unfold reverseWire
  by_cases ht : q < width
  · rw [if_pos ht]
    have hr : width - 1 - q < width := by omega
    rw [if_pos hr]
    omega
  · rw [if_neg ht]
    by_cases hs : q < 2 * width
    · rw [if_pos hs]
      have hlo : width ≤ width + (2 * width - 1 - q) := by omega
      have hhi : width + (2 * width - 1 - q) < 2 * width := by omega
      rw [if_neg (by omega), if_pos hhi]
      omega
    · rw [if_neg hs]
      rw [if_neg (by omega)]
      by_cases hq' : q < 2 * width
      · exact absurd hq' hs
      · rw [if_neg hq']

theorem reverseWire_injective (width : Nat) :
    ∀ x y, x < 2 * width + 2 → y < 2 * width + 2 →
      reverseWire width x = reverseWire width y → x = y := by
  intro x y hx hy hxy
  rw [← reverseWire_involutive hx, ← reverseWire_involutive hy, hxy]

theorem reverseWire_target {width b : Nat} (hb : b < width) :
    reverseWire width (width - 1 - b) = b := by
  unfold reverseWire
  rw [if_pos (by omega)]
  omega

theorem reverseWire_source {width b : Nat} (hb : b < width) :
    reverseWire width (width + (width - 1 - b)) = width + b := by
  unfold reverseWire
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem reverseWire_target_index {width b : Nat} (hb : b < width) :
    reverseWire width b = width - 1 - b := by
  unfold reverseWire
  rw [if_pos hb]

theorem reverseWire_source_index {width b : Nat} (hb : b < width) :
    reverseWire width (width + b) = width + (width - 1 - b) := by
  unfold reverseWire
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem reverseWire_carry (width : Nat) :
    reverseWire width (2 * width) = 2 * width := by
  unfold reverseWire
  rw [if_neg (by omega), if_neg (by omega)]

theorem reverseWire_sign (width : Nat) :
    reverseWire width (2 * width + 1) = 2 * width + 1 := by
  unfold reverseWire
  rw [if_neg (by omega), if_neg (by omega)]

def reverseIndex (width i : Nat) : Nat :=
  permuteBits (reverseWire width) (2 * width + 2) i

def bodyReverseIndex (width i : Nat) : Nat :=
  permuteBits (reverseWire width) (2 * width + 1) i

theorem read_target_reverseIndex (width i : Nat) :
    readField (reverseIndex width i) 0 width =
      reverseBits width (readField i 0 width) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_reverseBits, testBit_readField]
  by_cases hb : b < width
  · have hmirror : width - 1 - b < 2 * width + 2 := by omega
    have hmirrorWidth : width - 1 - b < width := by omega
    have hp := testBit_permuteBits (reverseWire_injective width)
      hmirror i
    rw [reverseWire_target hb] at hp
    simp [reverseIndex, hb, hmirrorWidth, hp]
  · simp [hb]

theorem read_source_reverseIndex (width i : Nat) :
    readField (reverseIndex width i) width width =
      reverseBits width (readField i width width) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_reverseBits, testBit_readField]
  by_cases hb : b < width
  · have hmirror : width + (width - 1 - b) < 2 * width + 2 := by omega
    have hmirrorWidth : width - 1 - b < width := by omega
    have hp := testBit_permuteBits (reverseWire_injective width)
      hmirror i
    rw [reverseWire_source hb] at hp
    simp [reverseIndex, hb, hmirrorWidth, hp]
  · simp [hb]

theorem bitValue_carry_reverseIndex (width i : Nat) :
    bitValue (reverseIndex width i) (2 * width) =
      bitValue i (2 * width) := by
  unfold bitValue
  have hp := testBit_permuteBits (reverseWire_injective width)
    (show 2 * width < 2 * width + 2 by omega) i
  rw [reverseWire_carry] at hp
  exact congrArg (fun b => if b then 1 else 0) hp

theorem bitValue_sign_reverseIndex (width i : Nat) :
    bitValue (reverseIndex width i) (2 * width + 1) =
      bitValue i (2 * width + 1) := by
  unfold bitValue
  have hp := testBit_permuteBits (reverseWire_injective width)
    (show 2 * width + 1 < 2 * width + 2 by omega) i
  rw [reverseWire_sign] at hp
  exact congrArg (fun b => if b then 1 else 0) hp

theorem read_target_bodyReverseIndex (width i : Nat) :
    readField (bodyReverseIndex width i) 0 width =
      reverseBits width (readField i 0 width) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_reverseBits, testBit_readField]
  by_cases hb : b < width
  · have hmirror : width - 1 - b < 2 * width + 1 := by omega
    have hmirrorWidth : width - 1 - b < width := by omega
    have hp := testBit_permuteBits
      (fun x y hx hy hxy => reverseWire_injective width x y
        (by omega) (by omega) hxy) hmirror i
    rw [reverseWire_target hb] at hp
    simp [bodyReverseIndex, hb, hmirrorWidth, hp]
  · simp [hb]

theorem read_source_bodyReverseIndex (width i : Nat) :
    readField (bodyReverseIndex width i) width width =
      reverseBits width (readField i width width) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_reverseBits, testBit_readField]
  by_cases hb : b < width
  · have hmirror : width + (width - 1 - b) < 2 * width + 1 := by omega
    have hmirrorWidth : width - 1 - b < width := by omega
    have hp := testBit_permuteBits
      (fun x y hx hy hxy => reverseWire_injective width x y
        (by omega) (by omega) hxy) hmirror i
    rw [reverseWire_source hb] at hp
    simp [bodyReverseIndex, hb, hmirrorWidth, hp]
  · simp [hb]

theorem bitValue_carry_bodyReverseIndex (width i : Nat) :
    bitValue (bodyReverseIndex width i) (2 * width) =
      bitValue i (2 * width) := by
  unfold bitValue
  have hp := testBit_permuteBits
    (fun x y hx hy hxy => reverseWire_injective width x y
      (by omega) (by omega) hxy)
    (show 2 * width < 2 * width + 1 by omega) i
  rw [reverseWire_carry] at hp
  exact congrArg (fun b => if b then 1 else 0) hp

def gates (width : Nat) : List RGate :=
  (Serial.carryGates width).map (RGate.map (reverseWire width))

def bodyGates (width : Nat) : List RGate :=
  (Serial.body width 0 width).map (RGate.map (reverseWire width))

def majBackward (width : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Adder.maj (top - 1) (width + top - 1) (2 * width) ++
        majBackward width (top - 1) m

def umaForward (width : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Adder.uma (width + j) j (2 * width) ++
        umaForward width (j + 1) m

theorem map_maj {width k : Nat} (hk : k < width) :
    (Adder.maj k (width + k) (2 * width)).map
        (RGate.map (reverseWire width)) =
      Adder.maj (width - 1 - k) (width + (width - 1 - k))
        (2 * width) := by
  simp only [Adder.maj, List.map_cons, List.map_nil, RGate.map]
  rw [reverseWire_target_index hk, reverseWire_source_index hk,
    reverseWire_carry]

theorem map_uma {width k : Nat} (hk : k < width) :
    (Adder.uma (width + k) k (2 * width)).map
        (RGate.map (reverseWire width)) =
      Adder.uma (width + (width - 1 - k)) (width - 1 - k)
        (2 * width) := by
  simp only [Adder.uma, List.map_cons, List.map_nil, RGate.map]
  rw [reverseWire_target_index hk, reverseWire_source_index hk,
    reverseWire_carry]

theorem map_majChain (width : Nat) : ∀ m st,
    st + m ≤ width →
    (Serial.majChain width st m).map (RGate.map (reverseWire width)) =
      majBackward width (width - st) m := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hbound
      simp only [Serial.majChain, List.map_append, majBackward]
      rw [map_maj (by omega), ih (st + 1) (by omega)]
      have hbit : width - 1 - st = width - st - 1 := by omega
      have hsource : width + (width - st - 1) =
          width + (width - st) - 1 := by omega
      have hnext : width - (st + 1) = width - st - 1 := by omega
      rw [hbit, hsource, hnext]

theorem umaForward_snoc (width : Nat) : ∀ m j,
    umaForward width j (m + 1) =
      umaForward width j m ++
        Adder.uma (width + (j + m)) (j + m) (2 * width) := by
  intro m
  induction m with
  | zero => intro j; simp [umaForward]
  | succ m ih =>
      intro j
      change
        Adder.uma (width + j) j (2 * width) ++
            umaForward width (j + 1) (m + 1) =
          (Adder.uma (width + j) j (2 * width) ++
            umaForward width (j + 1) m) ++
          Adder.uma (width + (j + (m + 1))) (j + (m + 1))
            (2 * width)
      rw [ih (j + 1), List.append_assoc]
      rw [show j + 1 + m = j + (m + 1) by omega]

theorem map_umaChain (width : Nat) : ∀ m st,
    st + m ≤ width →
    (Serial.umaChain width st m).map (RGate.map (reverseWire width)) =
      umaForward width (width - (st + m)) m := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hbound
      simp only [Serial.umaChain, List.map_append]
      rw [ih (st + 1) (by omega), map_uma (by omega)]
      rw [umaForward_snoc]
      have hstart : width - (st + 1 + m) =
          width - (st + (m + 1)) := by omega
      have hbit : width - 1 - st =
          width - (st + (m + 1)) + m := by omega
      rw [hstart, hbit]

theorem gates_eq_chains (width : Nat) :
    gates width =
      majBackward width width width ++
        [.cx (2 * width) (2 * width + 1)] ++
      umaForward width 0 width := by
  simp only [gates, Serial.carryGates, List.map_append, List.map_cons,
    List.map_nil, RGate.map]
  rw [map_majChain width width 0 (by omega),
    map_umaChain width width 0 (by omega), reverseWire_carry]
  simp [Serial.signWire, reverseWire_sign]

theorem bodyGates_eq_chains (width : Nat) :
    bodyGates width =
      majBackward width width width ++ umaForward width 0 width := by
  rw [bodyGates, Serial.body_eq_chains]
  simp only [List.map_append]
  rw [map_majChain width width 0 (by omega),
    map_umaChain width width 0 (by omega)]
  simp

def circuit (width : Nat) : RCircuit :=
  { width := 2 * width + 2, gates := gates width }

def bodyCircuit (width : Nat) : RCircuit :=
  { width := 2 * width + 1, gates := bodyGates width }

theorem circuit_wellFormed (width : Nat) :
    (circuit width).wellFormed = true := by
  exact RCircuit.wellFormed_relabel
    (fun q hq => reverseWire_lt hq)
    (reverseWire_injective width)
    (Serial.carryCircuit_wellFormed width)

theorem bodyCircuit_wellFormed (width : Nat) :
    (bodyCircuit width).wellFormed = true := by
  change (RCircuit.relabel (reverseWire width) (2 * width + 1)
    (Serial.circuit width)).wellFormed = true
  apply RCircuit.wellFormed_relabel
  · intro q hq
    have hq' : q < 2 * width + 1 := by
      simpa [Serial.circuit] using hq
    exact reverseWire_lt_body hq'
  · intro x y hx hy hxy
    have hx' : x < 2 * width + 1 := by
      simpa [Serial.circuit] using hx
    have hy' : y < 2 * width + 1 := by
      simpa [Serial.circuit] using hy
    exact reverseWire_injective width x y (by omega) (by omega) hxy
  · exact Serial.circuit_wellFormed width

theorem reverseIndex_lt (width i : Nat) :
    reverseIndex width i < 2 ^ (2 * width + 2) := by
  exact permuteBits_lt (fun q hq => reverseWire_lt hq) i

theorem bodyReverseIndex_lt (width i : Nat) :
    bodyReverseIndex width i < 2 ^ (2 * width + 1) := by
  exact permuteBits_lt
    (f := reverseWire width) (w := 2 * width + 1)
    (w' := 2 * width + 1)
    (fun q hq => reverseWire_lt_body (width := width) (q := q) hq) i

theorem gates_act {width i : Nat} (hwidth : 0 < width)
    (hi : i < 2 ^ (2 * width + 2)) :
    actGates (gates width) i =
      writeField
        (writeField i 0 width
          (reverseBits width
            ((reverseBits width (readField i 0 width) +
              reverseBits width (readField i width width) +
              bitValue i (2 * width)) % 2 ^ width)))
        (2 * width + 1) 1
          ((bitValue i (2 * width + 1) +
            (reverseBits width (readField i 0 width) +
              reverseBits width (readField i width width) +
              bitValue i (2 * width)) / 2 ^ width) % 2) := by
  let localWidth := 2 * width + 2
  let p := reverseIndex width i
  let j := actGates (Serial.carryGates width) p
  let out := reverseIndex width j
  let targetValue := reverseBits width
    ((reverseBits width (readField i 0 width) +
      reverseBits width (readField i width width) +
      bitValue i (2 * width)) % 2 ^ width)
  let signValue := (bitValue i (2 * width + 1) +
    (reverseBits width (readField i 0 width) +
      reverseBits width (readField i width width) +
      bitValue i (2 * width)) / 2 ^ width) % 2
  have hconj := act_relabel_conj
    (r := Serial.carryCircuit width)
    (f := reverseWire width) (g := reverseWire width)
    (w' := localWidth)
    (fun q hq => reverseWire_lt hq)
    (fun q hq => reverseWire_lt hq)
    (fun q hq => reverseWire_involutive hq)
    (fun q hq => reverseWire_involutive hq)
    (Serial.carryCircuit_wellFormed width) hi
  change actGates (gates width) i = out at hconj
  rw [hconj]
  change out = writeField (writeField i 0 width targetValue)
    (2 * width + 1) 1 signValue
  let L := layout width
  have htargetValue : targetValue < 2 ^ width := by
    exact reverseBits_lt width _
  apply Layout.ext (l := L)
  · simpa [out, L, layout_width] using reverseIndex_lt width j
  · have ht : writeField i 0 width targetValue <
        2 ^ (2 * width + 2) :=
      writeField_lt (w := 2 * width + 2) (by omega) hi
    have hs : writeField (writeField i 0 width targetValue)
        (2 * width + 1) 1 signValue < 2 ^ (2 * width + 2) :=
      writeField_lt (w := 2 * width + 2) (by omega) ht
    simpa [L, layout_width] using hs
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    simp [L, layout] at hk
    omega
  rcases hk' with rfl | rfl | rfl | rfl
  · simp only [L, layout, Layout.read, Layout.offset, Layout.size]
    rw [read_target_reverseIndex]
    rw [readField_writeField_of_disjoint (Or.inr (by omega)),
      readField_writeField, Nat.mod_eq_of_lt htargetValue,
      show j = actGates (Serial.carryGates width) p from rfl,
      Serial.carryGates_act hwidth,
      readField_writeField_of_disjoint (Or.inr (by
        simp [Serial.signWire]
        omega)),
      readField_writeField,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos width))]
    simp [p, targetValue, read_target_reverseIndex,
      read_source_reverseIndex, bitValue_carry_reverseIndex]
  · simp only [L, layout, Layout.read, Layout.offset, Layout.size]
    change readField out width width = _
    rw [read_source_reverseIndex]
    rw [show j = actGates (Serial.carryGates width) p from rfl,
      Serial.carryGates_act hwidth,
      readField_writeField_of_disjoint (Or.inr (by
        simp [Serial.signWire]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      readField_writeField_of_disjoint (Or.inr (by omega)),
      readField_writeField_of_disjoint (Or.inl (by omega))]
    rw [read_source_reverseIndex,
      reverseBits_involutive (readField_lt i width width)]
    simp
  · simp only [L, layout, Layout.read, Layout.offset, Layout.size]
    rw [show width + (width + 0) = 2 * width by omega]
    change readField out (2 * width) 1 = _
    rw [readField_one, readField_one,
      bitValue_carry_reverseIndex]
    rw [show j = actGates (Serial.carryGates width) p from rfl,
      Serial.carryGates_act hwidth]
    rw [bitValue_write_ne (by simp [Serial.signWire]),
      bitValue_write_out (Or.inr (by omega)),
      bitValue_carry_reverseIndex]
    calc
      bitValue i (2 * width) =
          bitValue (writeField i 0 width targetValue) (2 * width) :=
        (bitValue_write_out
          (i := i) (off := 0) (len := width) (v := targetValue)
          (r := 2 * width) (Or.inr (by omega))).symm
      _ = bitValue (writeField (writeField i 0 width targetValue)
          (2 * width + 1) 1 signValue) (2 * width) :=
        (bitValue_write_ne
          (i := writeField i 0 width targetValue)
          (q := 2 * width + 1) (r := 2 * width) (v := signValue)
          (by omega)).symm
  · simp only [L, layout, Layout.read, Layout.offset, Layout.size]
    rw [show width + (width + (1 + 0)) = 2 * width + 1 by omega]
    change readField out (2 * width + 1) 1 = _
    rw [readField_one, bitValue_sign_reverseIndex]
    rw [show j = actGates (Serial.carryGates width) p from rfl,
      Serial.carryGates_act hwidth]
    rw [show Serial.signWire width = 2 * width + 1 by rfl,
      bitValue_write_self, readField_writeField, Nat.pow_one]
    simp [p, signValue, bitValue_sign_reverseIndex,
      read_target_reverseIndex, read_source_reverseIndex,
      bitValue_carry_reverseIndex]

theorem bodyGates_act {width i : Nat}
    (hi : i < 2 ^ (2 * width + 1)) :
    actGates (bodyGates width) i =
      writeField i 0 width
        (reverseBits width
          ((reverseBits width (readField i 0 width) +
            reverseBits width (readField i width width) +
            bitValue i (2 * width)) % 2 ^ width)) := by
  let localWidth := 2 * width + 1
  let p := bodyReverseIndex width i
  let j := actGates (Serial.body width 0 width) p
  let out := bodyReverseIndex width j
  let targetValue := reverseBits width
    ((reverseBits width (readField i 0 width) +
      reverseBits width (readField i width width) +
      bitValue i (2 * width)) % 2 ^ width)
  have hconj := act_relabel_conj
    (r := Serial.circuit width)
    (f := reverseWire width) (g := reverseWire width)
    (w' := localWidth)
    (fun q hq => by
      have hq' : q < 2 * width + 1 := by
        simpa [Serial.circuit] using hq
      simpa [Serial.circuit] using
        reverseWire_lt_body (width := width) (q := q) hq')
    (fun q hq => by
      have hq' : q < 2 * width + 1 := by
        simpa [Serial.circuit] using hq
      simpa [Serial.circuit] using
        reverseWire_lt_body (width := width) (q := q) hq')
    (fun q hq => reverseWire_involutive (width := width) (q := q) (by
      have hq' : q < 2 * width + 1 := by
        simpa [Serial.circuit] using hq
      omega))
    (fun q hq => reverseWire_involutive (width := width) (q := q) (by
      have hq' : q < 2 * width + 1 := by
        simpa [Serial.circuit] using hq
      omega))
    (Serial.circuit_wellFormed width) hi
  change actGates (bodyGates width) i = out at hconj
  rw [hconj]
  change out = writeField i 0 width targetValue
  let L : Layout := [width, width, 1]
  have htargetValue : targetValue < 2 ^ width := reverseBits_lt width _
  apply Layout.ext (l := L)
  · simpa [out, L, Layout.width,
      show width + (width + 1) = 2 * width + 1 by omega] using
      bodyReverseIndex_lt width j
  · have ht : writeField i 0 width targetValue <
        2 ^ (2 * width + 1) :=
      writeField_lt (w := 2 * width + 1) (by omega) hi
    simpa [L, Layout.width,
      show width + (width + 1) = 2 * width + 1 by omega] using ht
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
    simp [L] at hk
    omega
  rcases hk' with rfl | rfl | rfl
  · simp only [L, Layout.read, Layout.offset, Layout.size]
    rw [read_target_bodyReverseIndex, readField_writeField,
      Nat.mod_eq_of_lt htargetValue,
      show j = actGates (Serial.body width 0 width) p from rfl,
      Serial.body_act width width 0 p (by omega),
      readField_writeField,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos width))]
    simp [p, targetValue, read_target_bodyReverseIndex,
      read_source_bodyReverseIndex, bitValue_carry_bodyReverseIndex]
  · simp only [L, Layout.read, Layout.offset, Layout.size]
    change readField out width width = _
    rw [read_source_bodyReverseIndex,
      show j = actGates (Serial.body width 0 width) p from rfl,
      Serial.body_act width width 0 p (by omega),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      read_source_bodyReverseIndex,
      reverseBits_involutive (readField_lt i width width)]
    simp
  · simp only [L, Layout.read, Layout.offset, Layout.size]
    rw [show width + (width + 0) = 2 * width by omega]
    change readField out (2 * width) 1 = _
    rw [readField_one, readField_one,
      bitValue_carry_bodyReverseIndex,
      show j = actGates (Serial.body width 0 width) p from rfl,
      Serial.body_act width width 0 p (by omega),
      bitValue_write_out (Or.inr (by omega)),
      bitValue_carry_bodyReverseIndex]
    exact (bitValue_write_out
      (i := i) (off := 0) (len := width) (v := targetValue)
      (r := 2 * width) (Or.inr (by omega))).symm

theorem gates_length (width : Nat) :
    (gates width).length = (Serial.carryGates width).length := by
  simp [gates]

theorem gates_ccx (width : Nat) :
    (gates width).countP RGate.isCcx =
      (Serial.carryGates width).countP RGate.isCcx := by
  exact countP_map_gates (fun g => RGate.isCcx_map _ g) _

theorem gates_cx (width : Nat) :
    (gates width).countP RGate.isCx =
      (Serial.carryGates width).countP RGate.isCx := by
  exact countP_map_gates (fun g => RGate.isCx_map _ g) _

end SerialBigEndian
end Euclid
end VQ
