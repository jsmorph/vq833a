/-
Ripple addition with one dedicated carry wire.

The location-controlled cells in Figure 11 of Luo et al. use this arithmetic
core.  The first pass visits low bits before high bits, the recursive call
handles the remaining suffix, and the second pass restores the source and carry
while writing the sum into the target.
-/
import VQ.Euclid.Cell

namespace VQ
namespace Euclid
namespace Serial

open Reversible

def body (width : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      Adder.maj st (width + st) (2 * width) ++
        body width (st + 1) m ++
      Adder.uma (width + st) st (2 * width)

def circuit (width : Nat) : RCircuit :=
  { width := 2 * width + 1, gates := body width 0 width }

theorem majState_comm {i carry x y C X Y : Nat}
    (hxy : x + 1 ≤ y ∨ y + 1 ≤ x) :
    Adder.majState i carry x y C X Y =
      Adder.majState i carry y x C Y X := by
  unfold Adder.majState
  rw [show (C + X + Y) / 2 = (C + Y + X) / 2 by omega]
  congr 1
  exact writeField_comm hxy

theorem uma_collapse {i target source carry A B C X m : Nat}
    (hts : target + 1 + m ≤ source)
    (hsc : source + 1 ≤ carry)
    (_hA : bitValue i target = A) (_hA2 : A < 2)
    (hB : bitValue i source = B) (hB2 : B < 2)
    (hC : bitValue i carry = C) (hC2 : C < 2) :
    writeField
        (writeField
          (writeField
            (writeField
              (Adder.majState i carry target source C A B)
              (target + 1) m X)
            carry 1 C)
          source 1 B)
        target 1 ((C + A + B) % 2) =
      writeField (writeField i target 1 ((A + B + C) % 2))
        (target + 1) m X := by
  rw [writeField_comm
      (i := Adder.majState i carry target source C A B)
      (o₁ := target + 1) (n₁ := m) (v := X)
      (o₂ := carry) (n₂ := 1) (u := C) (Or.inl (by omega)),
    Adder.majState_restore_a (by omega) (by omega) hC hC2,
    writeField_comm
      (i := writeField (writeField i target 1 ((A + C) % 2))
        source 1 ((B + C) % 2))
      (o₁ := target + 1) (n₁ := m) (v := X)
      (o₂ := source) (n₂ := 1) (u := B) (Or.inl hts),
    Adder.majState_restore_c (by omega) hB hB2,
    writeField_comm
      (i := writeField i target 1 ((A + C) % 2))
      (o₁ := target + 1) (n₁ := m) (v := X)
      (o₂ := target) (n₂ := 1) (u := (C + A + B) % 2)
      (Or.inr (by omega)),
    writeField_writeField]
  congr 2
  omega

theorem adder_step {target source carry m : Nat}
    (gs : List RGate) (i : Nat)
    (hts : target + 1 + m ≤ source)
    (hsc : source + 1 + m ≤ carry)
    (hinner : ∀ j, actGates gs j =
      writeField j (target + 1) m
        ((readField j (target + 1) m +
          readField j (source + 1) m + bitValue j carry) % 2 ^ m)) :
    actGates
        (Adder.maj target source carry ++ gs ++
          Adder.uma source target carry) i =
      writeField i target (m + 1)
        ((readField i target (m + 1) +
          readField i source (m + 1) + bitValue i carry) % 2 ^ (m + 1)) := by
  obtain ⟨A, hA⟩ : ∃ x, bitValue i target = x := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, bitValue i source = x := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x, bitValue i carry = x := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ x, readField i (target + 1) m = x := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ x, readField i (source + 1) m = x := ⟨_, rfl⟩
  have hA2 : A < 2 := hA ▸ bitValue_lt i target
  have hB2 : B < 2 := hB ▸ bitValue_lt i source
  have hC2 : C < 2 := hC ▸ bitValue_lt i carry
  rw [readField_succ i target m, readField_succ i source m,
    hA, hB, hC, hA', hB']
  rw [actGates_append, actGates_append,
    Adder.act_maj' (by omega) (by omega) (by omega) hC hB hA,
    hinner (Adder.majState i carry source target C B A),
    Adder.readField_majState (o := target + 1) (len := m)
      (by omega) (by omega) (by omega),
    Adder.readField_majState (o := source + 1) (len := m)
      (by omega) (by omega) (by omega),
    Adder.bitValue_majState_a hC2 hB2 hA2, hA', hB']
  obtain ⟨X, hX⟩ : ∃ x,
      (A' + B' + (C + B + A) / 2) % 2 ^ m = x := ⟨_, rfl⟩
  rw [hX]
  have hswap : Adder.majState i carry source target C B A =
      Adder.majState i carry target source C A B :=
    majState_comm (by omega)
  rw [hswap]
  have hja : bitValue
      (writeField (Adder.majState i carry target source C A B)
        (target + 1) m X) carry = (C + A + B) / 2 := by
    rw [bitValue_write_out (Or.inr (by omega)),
      Adder.bitValue_majState_a hC2 hA2 hB2]
  have hjb : bitValue
      (writeField (Adder.majState i carry target source C A B)
        (target + 1) m X) target = (A + C) % 2 := by
    rw [bitValue_write_out (Or.inl (by omega)),
      Adder.bitValue_majState_b (by omega) (by omega)]
  have hjc : bitValue
      (writeField (Adder.majState i carry target source C A B)
        (target + 1) m X) source = (B + C) % 2 := by
    rw [bitValue_write_out (Or.inr hts),
      Adder.bitValue_majState_c (by omega)]
  have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
    rw [Nat.pow_succ]
    omega
  have hV :
      (A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1) =
        (C + A + B) % 2 + 2 * X := by
    rw [hpow, Nat.mod_mul]
    have h1 :
        (A + 2 * A' + (B + 2 * B') + C) % 2 =
          (C + A + B) % 2 := by omega
    have h2 :
        (A + 2 * A' + (B + 2 * B') + C) / 2 =
          (C + A + B) / 2 + A' + B' := by omega
    have h3 :
        (C + A + B) / 2 + A' + B' =
          A' + B' + (C + B + A) / 2 := by omega
    rw [h1, h2, h3, hX]
  rw [Adder.act_uma (by omega) (by omega) (by omega)
      hC2 hA2 hB2 hja hjb hjc,
    uma_collapse hts (by omega) hA hA2 hB hB2 hC hC2,
    writeField_succ i target m
      ((A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1)),
    hV,
    show ((C + A + B) % 2 + 2 * X) % 2 =
      (A + B + C) % 2 by omega,
    show ((C + A + B) % 2 + 2 * X) / 2 = X by omega]

theorem body_act (width : Nat) : ∀ m st i, st + m ≤ width →
    actGates (body width st m) i =
      writeField i st m
        ((readField i st m + readField i (width + st) m +
          bitValue i (2 * width)) % 2 ^ m) := by
  intro m
  induction m with
  | zero =>
      intro st i _
      rw [show body width st 0 = [] from rfl, actGates_nil, writeField_zero]
  | succ m ih =>
      intro st i hst
      exact adder_step
        (target := st) (source := width + st) (carry := 2 * width)
        (gs := body width (st + 1) m) i (by omega) (by omega)
        (fun j => ih (st + 1) j (by omega))

theorem circuit_act (width i : Nat) :
    act (circuit width) i =
      writeField i 0 width
        ((readField i 0 width + readField i width width +
          bitValue i (2 * width)) % 2 ^ width) := by
  exact body_act width width 0 i (by omega)

theorem body_wellFormed (width : Nat) : ∀ m st, st + m ≤ width →
    (body width st m).all (RGate.wellFormed (2 * width + 1)) = true := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hst
      have ht : st < 2 * width + 1 := by omega
      have hs : width + st < 2 * width + 1 := by omega
      have hc : 2 * width < 2 * width + 1 := by omega
      simp only [body, List.all_append, Bool.and_eq_true]
      exact ⟨⟨Adder.maj_wellFormed hc hs ht (by omega) (by omega) (by omega),
        ih (st + 1) (by omega)⟩,
        Adder.uma_wellFormed hc ht hs (by omega) (by omega) (by omega)⟩

theorem circuit_wellFormed (width : Nat) :
    (circuit width).wellFormed = true := by
  exact body_wellFormed width width 0 (by omega)

theorem length_body (width : Nat) : ∀ m st,
    (body width st m).length = 6 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [body, Adder.maj, Adder.uma, ih (st + 1)]
      omega

theorem ccx_body (width : Nat) : ∀ m st,
    (body width st m).countP RGate.isCcx = 2 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [body, Adder.maj, Adder.uma, List.countP_cons, ih (st + 1), RGate.isCcx]
      omega

theorem cx_body (width : Nat) : ∀ m st,
    (body width st m).countP RGate.isCx = 4 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [body, Adder.maj, Adder.uma, List.countP_cons, ih (st + 1), RGate.isCx]
      omega

def majChain (width : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      Adder.maj st (width + st) (2 * width) ++
        majChain width (st + 1) m

def umaChain (width : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      umaChain width (st + 1) m ++
        Adder.uma (width + st) st (2 * width)

theorem body_eq_chains (width : Nat) : ∀ m st,
    body width st m = majChain width st m ++ umaChain width st m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [body, majChain, umaChain, ih (st + 1), List.append_assoc]

theorem majChain_carry (width : Nat) : ∀ m st i,
    0 < m → st + m ≤ width →
    bitValue (actGates (majChain width st m) i) (2 * width) =
      (readField i st m + readField i (width + st) m +
        bitValue i (2 * width)) / 2 ^ m := by
  intro m
  induction m with
  | zero => intro st i h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
      intro st i _ hbound
      rw [show majChain width st (m + 1) =
        Adder.maj st (width + st) (2 * width) ++
          majChain width (st + 1) m from rfl,
        actGates_append,
        Adder.act_maj' (by omega) (by omega) (by omega) rfl rfl rfl]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [show majChain width (st + 1) 0 = [] from rfl, actGates_nil,
          Adder.bitValue_majState_a
            (bitValue_lt i (2 * width))
            (bitValue_lt i (width + st))
            (bitValue_lt i st),
          readField_one, readField_one, Nat.pow_one]
        congr 1
        omega
      · have hstep := ih (st + 1)
          (Adder.majState i (2 * width) (width + st) st
            (bitValue i (2 * width)) (bitValue i (width + st))
            (bitValue i st)) hm (by omega)
        rw [hstep,
          Adder.readField_majState (o := st + 1) (len := m)
            (by omega) (by omega) (by omega),
          Adder.readField_majState (o := width + (st + 1)) (len := m)
            (by omega) (by omega) (by omega),
          Adder.bitValue_majState_a
            (bitValue_lt i (2 * width))
            (bitValue_lt i (width + st))
            (bitValue_lt i st)]
        have hA := readField_succ i st m
        have hB := readField_succ i (width + st) m
        have hp : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
          rw [Nat.pow_succ]
          omega
        rw [show width + st + 1 = width + (st + 1) by omega] at hB
        rw [hA, hB, hp, ← Nat.div_div_eq_div_mul]
        refine congrArg (fun q => q / 2 ^ m) ?_
        have h1 := bitValue_lt i st
        have h2 := bitValue_lt i (width + st)
        have h3 := bitValue_lt i (2 * width)
        omega

theorem circuit_length (width : Nat) :
    (circuit width).gates.length = 6 * width :=
  length_body width width 0

theorem circuit_ccx (width : Nat) :
    (circuit width).gates.countP RGate.isCcx = 2 * width :=
  ccx_body width width 0

theorem circuit_cx (width : Nat) :
    (circuit width).gates.countP RGate.isCx = 4 * width :=
  cx_body width width 0

def signWire (width : Nat) : Nat := 2 * width + 1

def carryGates (width : Nat) : List RGate :=
  majChain width 0 width ++
    [.cx (2 * width) (signWire width)] ++
  umaChain width 0 width

def carryCircuit (width : Nat) : RCircuit :=
  { width := 2 * width + 2, gates := carryGates width }

theorem chain_wellFormed (width : Nat) :
    (majChain width 0 width ++ umaChain width 0 width).all
      (RGate.wellFormed (2 * width + 1)) = true := by
  have h := body_wellFormed width width 0 (by omega)
  rwa [body_eq_chains] at h

theorem majChain_wellFormed (width : Nat) :
    (majChain width 0 width).all
      (RGate.wellFormed (2 * width + 1)) = true := by
  have h := chain_wellFormed width
  have h' :
      (majChain width 0 width).all
          (RGate.wellFormed (2 * width + 1)) = true ∧
        (umaChain width 0 width).all
          (RGate.wellFormed (2 * width + 1)) = true := by
    simpa only [List.all_append, Bool.and_eq_true] using h
  exact h'.1

theorem umaChain_wellFormed (width : Nat) :
    (umaChain width 0 width).all
      (RGate.wellFormed (2 * width + 1)) = true := by
  have h := chain_wellFormed width
  have h' :
      (majChain width 0 width).all
          (RGate.wellFormed (2 * width + 1)) = true ∧
        (umaChain width 0 width).all
          (RGate.wellFormed (2 * width + 1)) = true := by
    simpa only [List.all_append, Bool.and_eq_true] using h
  exact h'.2

theorem carryCircuit_wellFormed (width : Nat) :
    (carryCircuit width).wellFormed = true := by
  apply List.all_eq_true.mpr
  intro g hg
  simp only [carryCircuit, carryGates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · change g.wellFormed (2 * width + 2) = true
    exact RGate.wellFormed_mono (by omega)
      (List.all_eq_true.mp (majChain_wellFormed width) g hg)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    change (RGate.cx (2 * width) (signWire width)).wellFormed
      (2 * width + 2) = true
    simp [RGate.wellFormed, signWire]
  · change g.wellFormed (2 * width + 2) = true
    exact RGate.wellFormed_mono (by omega)
      (List.all_eq_true.mp (umaChain_wellFormed width) g hg)

theorem carryGates_act {width i : Nat} (hwidth : 0 < width) :
    actGates (carryGates width) i =
      writeField
        (writeField i 0 width
          ((readField i 0 width + readField i width width +
            bitValue i (2 * width)) % 2 ^ width))
        (signWire width) 1
          ((bitValue i (signWire width) +
            (readField i 0 width + readField i width width +
              bitValue i (2 * width)) / 2 ^ width) % 2) := by
  let pre := actGates (majChain width 0 width) i
  have hcarry : bitValue pre (2 * width) =
      (readField i 0 width + readField i width width +
        bitValue i (2 * width)) / 2 ^ width := by
    simpa [pre] using majChain_carry width width 0 i hwidth (by omega)
  have hsign : bitValue pre (signWire width) =
      bitValue i (signWire width) := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside
      (fun g hg q hq => Or.inl (by
        have hw := List.all_eq_true.mp (majChain_wellFormed width) g hg
        have := wire_lt_of_wellFormed hw hq
        simp [signWire]
        omega)) i
  have hsuffix : ∀ g ∈ umaChain width 0 width, ∀ q ∈ g.wires,
      q < signWire width ∨ signWire width + 1 ≤ q := by
    intro g hg q hq
    left
    have hw := List.all_eq_true.mp (umaChain_wellFormed width) g hg
    have := wire_lt_of_wellFormed hw hq
    simp [signWire]
    omega
  have hbody := body_act width width 0 i (by omega)
  rw [body_eq_chains] at hbody
  change actGates
    (majChain width 0 width ++ [.cx (2 * width) (signWire width)] ++
      umaChain width 0 width) i = _
  rw [actGates_append, actGates_append]
  change actGates (umaChain width 0 width)
    (RGate.act (.cx (2 * width) (signWire width)) pre) = _
  rw [act_cx_write, hcarry, hsign,
    actGates_write_of_outside hsuffix]
  rw [← actGates_append, hbody]
  simp

theorem carryCircuit_act {width i : Nat} (hwidth : 0 < width) :
    act (carryCircuit width) i =
      writeField
        (writeField i 0 width
          ((readField i 0 width + readField i width width +
            bitValue i (2 * width)) % 2 ^ width))
        (signWire width) 1
          ((bitValue i (signWire width) +
            (readField i 0 width + readField i width width +
              bitValue i (2 * width)) / 2 ^ width) % 2) :=
  carryGates_act hwidth

theorem carryGates_reverse_act {width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (2 * width) = 0) :
    actGates (carryGates width).reverse i =
      writeField
        (writeField i 0 width
          (Adder.difference width (readField i width width)
            (readField i 0 width)))
        (signWire width) 1
          ((bitValue i (signWire width) +
            Adder.borrow (readField i width width)
              (readField i 0 width)) % 2) := by
  let a := readField i width width
  let b := readField i 0 width
  let s := bitValue i (signWire width)
  let x := Adder.difference width a b
  let br := Adder.borrow a b
  let j := writeField (writeField i 0 width x)
    (signWire width) 1 ((s + br) % 2)
  have ha : a < 2 ^ width := readField_lt i width width
  have hb : b < 2 ^ width := readField_lt i 0 width
  have hs : s < 2 := bitValue_lt i (signWire width)
  have hspec : (a + x) % 2 ^ width = b ∧
      (a + x) / 2 ^ width = Adder.borrow a b := by
    simpa [x, Adder.difference] using
      Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb
  have hx : x < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)
  have hjTarget : readField j 0 width = x := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by simp [signWire]; omega),
      readField_writeField_self hx]
  have hjSource : readField j width width = a := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by simp [signWire]; omega),
      readField_writeField_of_disjoint (by omega)]
  have hjCarry : bitValue j (2 * width) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by simp [signWire]),
      bitValue_write_out (by omega), hcarry]
  have hjSign : bitValue j (signWire width) = (s + br) % 2 := by
    simp only [j]
    rw [bitValue_write_self]
    omega
  have hsign : (((s + br) % 2 + br) % 2) = s := by
    unfold br Adder.borrow
    by_cases hlt : b < a <;> simp [hlt] <;> omega
  have hfwd := carryGates_act (width := width) (i := j) hwidth
  rw [hjTarget, hjSource, hjCarry, Nat.add_zero,
    show x + a = a + x by omega,
    hspec.1, hjSign, hspec.2, hsign] at hfwd
  have hrestore : writeField (writeField j 0 width b)
      (signWire width) 1 s = i := by
    simp only [j]
    rw [writeField_comm
        (i := writeField i 0 width x)
        (o₁ := signWire width) (n₁ := 1) (v := (s + br) % 2)
        (o₂ := 0) (n₂ := width) (u := b)
        (Or.inr (by simp [signWire]; omega)),
      writeField_writeField]
    change writeField (writeField (writeField i 0 width x) 0 width b)
      (signWire width) 1 s = i
    rw [writeField_writeField, show b = readField i 0 width from rfl,
      writeField_read]
    change writeField i (signWire width) 1
      (bitValue i (signWire width)) = i
    rw [← readField_one, writeField_read]
  rw [hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (carryCircuit width).width)
    (carryCircuit_wellFormed width) j
  change actGates (carryGates width).reverse
    (actGates (carryGates width) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, x, br, a, b, s] using hinv

theorem carryCircuit_reverse_act {width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (2 * width) = 0) :
    act (carryCircuit width).reverse i =
      writeField
        (writeField i 0 width
          (Adder.difference width (readField i width width)
            (readField i 0 width)))
        (signWire width) 1
          ((bitValue i (signWire width) +
            Adder.borrow (readField i width width)
              (readField i 0 width)) % 2) :=
  carryGates_reverse_act hwidth hcarry

theorem carryCircuit_length (width : Nat) :
    (carryCircuit width).gates.length = 6 * width + 1 := by
  have h := congrArg List.length (body_eq_chains width width 0)
  simp only [List.length_append] at h
  change (carryGates width).length = 6 * width + 1
  simp only [carryGates, List.length_append, List.length_cons, List.length_nil]
  have hb := length_body width width 0
  omega

theorem carryCircuit_ccx (width : Nat) :
    (carryCircuit width).gates.countP RGate.isCcx = 2 * width := by
  have h := congrArg (List.countP RGate.isCcx)
    (body_eq_chains width width 0)
  simp only [List.countP_append] at h
  change (carryGates width).countP RGate.isCcx = 2 * width
  simp only [carryGates, List.countP_append]
  simp only [List.countP_cons, List.countP_nil, RGate.isCcx, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero]
  have hb := ccx_body width width 0
  omega

theorem carryCircuit_cx (width : Nat) :
    (carryCircuit width).gates.countP RGate.isCx = 4 * width + 1 := by
  have h := congrArg (List.countP RGate.isCx)
    (body_eq_chains width width 0)
  simp only [List.countP_append] at h
  change (carryGates width).countP RGate.isCx = 4 * width + 1
  simp only [carryGates, List.countP_append]
  simp [RGate.isCx]
  have hb := cx_body width width 0
  omega

end Serial
end Euclid
end VQ
