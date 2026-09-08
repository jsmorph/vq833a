/-
Cuccaro ripple-carry addition with an observable final carry.

The ordinary MAJ/UMA circuit restores its carry wire and writes the wrapped
sum.  The carry variant copies the final carry into a separate bit between the
two ripple passes, so its reverse places the subtraction borrow on that bit.
-/
import VQ.Reversible.Bit
import VQ.Reversible.Place
import VQ.Reversible.ArithmeticSpec

namespace VQ
namespace Reversible
namespace Adder

def carryWire (n : Nat) : Nat → Nat
  | 0 => 2 * n
  | k + 1 => k

@[simp] theorem carryWire_zero (n : Nat) : carryWire n 0 = 2 * n := rfl

@[simp] theorem carryWire_succ (n k : Nat) : carryWire n (k + 1) = k := rfl

def maj (c b a : Nat) : List RGate :=
  [.cx a b, .cx a c, .ccx c b a]

def uma (c b a : Nat) : List RGate :=
  [.ccx c b a, .cx a c, .cx c b]

def body (n : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      maj (carryWire n st) (n + st) st ++
        body n (st + 1) m ++
        uma (carryWire n st) (n + st) st

def circuit (n : Nat) : RCircuit :=
  { width := 2 * n + 1, gates := body n 0 n }

theorem carry_lt {n st : Nat} (h : st < n) :
    carryWire n st < 2 * n + 1 := by
  cases st with
  | zero => simp
  | succ k => simp; omega

theorem carry_ne_a {n st : Nat} (h : st < n) : carryWire n st ≠ st := by
  cases st with
  | zero => simp; omega
  | succ k => simp

theorem carry_ne_b {n st : Nat} (h : st < n) :
    carryWire n st ≠ n + st := by
  cases st with
  | zero => simp; omega
  | succ k => simp; omega

theorem maj_wellFormed {w c b a : Nat}
    (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (maj c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hbc : b ≠ c := Ne.symm hcb
  simp [maj, RGate.wellFormed, ha, hb, hc, hab, hac, hcb, hba, hca]

theorem uma_wellFormed {w c b a : Nat}
    (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (uma c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hbc : b ≠ c := Ne.symm hcb
  simp [uma, RGate.wellFormed, ha, hb, hc, hac, hcb, hba, hca]

theorem body_wellFormed (n : Nat) : ∀ m st, st + m ≤ n →
    (body n st m).all (RGate.wellFormed (2 * n + 1)) = true := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hst
      have hlt : st < n := by omega
      have ha : st < 2 * n + 1 := by omega
      have hb : n + st < 2 * n + 1 := by omega
      have hc := carry_lt hlt
      have hab : st ≠ n + st := by omega
      have hac : st ≠ carryWire n st := fun e => carry_ne_a hlt e.symm
      have hcb := carry_ne_b hlt
      simp only [body, List.all_append, Bool.and_eq_true]
      exact ⟨⟨maj_wellFormed ha hb hc hab hac hcb,
        ih (st + 1) (by omega)⟩,
        uma_wellFormed ha hb hc hab hac hcb⟩

theorem circuit_wellFormed (n : Nat) : (circuit n).wellFormed = true := by
  exact body_wellFormed n n 0 (by omega)

theorem length_body (n : Nat) : ∀ m st, (body n st m).length = 6 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp only [body, List.length_append, ih (st + 1), maj, uma,
        List.length_cons, List.length_nil]
      omega

theorem ccx_body (n : Nat) : ∀ m st,
    (body n st m).countP RGate.isCcx = 2 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      have hm : (maj (carryWire n st) (n + st) st).countP RGate.isCcx = 1 := rfl
      have hu : (uma (carryWire n st) (n + st) st).countP RGate.isCcx = 1 := rfl
      simp only [body, List.countP_append, ih (st + 1), hm, hu]
      omega

theorem cx_body (n : Nat) : ∀ m st,
    (body n st m).countP RGate.isCx = 4 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      have hm : (maj (carryWire n st) (n + st) st).countP RGate.isCx = 2 := rfl
      have hu : (uma (carryWire n st) (n + st) st).countP RGate.isCx = 2 := rfl
      simp only [body, List.countP_append, ih (st + 1), hm, hu]
      omega

theorem majority_value {A B C : Nat}
    (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    (A + (C + A) % 2 * ((B + A) % 2)) % 2 = (A + B + C) / 2 := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hb : B = 0 ∨ B = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rfl

theorem unmajority_value {A B C : Nat}
    (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    ((A + B + C) / 2 + (C + A) % 2 * ((B + A) % 2)) % 2 = A := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hb : B = 0 ∨ B = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rfl

theorem act_maj {c b a : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (i : Nat) :
    actGates (maj c b a) i =
      writeField
        (writeField
          (writeField i b 1 ((bitValue i b + bitValue i a) % 2))
          c 1 ((bitValue i c + bitValue i a) % 2))
        a 1 ((bitValue i a + bitValue i b + bitValue i c) / 2) := by
  show RGate.act (.ccx c b a)
      (RGate.act (.cx a c) (RGate.act (.cx a b) i)) = _
  rw [act_cx_write, act_cx_write, act_ccx_write,
    bitValue_write_ne hcb, bitValue_write_ne hab,
    bitValue_write_ne hac, bitValue_write_ne hab,
    bitValue_write_self, bitValue_write_ne (Ne.symm hcb),
    bitValue_write_self]
  refine write_congr ?_
  rw [← majority_value (bitValue_lt i a) (bitValue_lt i b) (bitValue_lt i c)]
  have h1 : (bitValue i c + bitValue i a) % 2 % 2 =
      (bitValue i c + bitValue i a) % 2 := by omega
  have h2 : (bitValue i b + bitValue i a) % 2 % 2 =
      (bitValue i b + bitValue i a) % 2 := by omega
  rw [h1, h2]

theorem act_uma {c b a : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {i A B C : Nat} (hA : A < 2) (hB : B < 2) (hC : C < 2)
    (ha : bitValue i a = (A + B + C) / 2)
    (hb : bitValue i b = (B + A) % 2)
    (hc : bitValue i c = (C + A) % 2) :
    actGates (uma c b a) i =
      writeField (writeField (writeField i a 1 A) c 1 C)
        b 1 ((A + B + C) % 2) := by
  have h1 : RGate.act (.ccx c b a) i = writeField i a 1 A := by
    rw [act_ccx_write, ha, hb, hc, unmajority_value hA hB hC]
  have ha1 : bitValue (writeField i a 1 A) a = A := by
    rw [bitValue_write_self]
    omega
  have hb1 : bitValue (writeField i a 1 A) b = (B + A) % 2 := by
    rw [bitValue_write_ne (Ne.symm hab), hb]
  have hc1 : bitValue (writeField i a 1 A) c = (C + A) % 2 := by
    rw [bitValue_write_ne (Ne.symm hac), hc]
  have h2 : RGate.act (.cx a c) (writeField i a 1 A) =
      writeField (writeField i a 1 A) c 1 C := by
    rw [act_cx_write, hc1, ha1]
    exact write_congr (by omega)
  have hb2 : bitValue (writeField (writeField i a 1 A) c 1 C) b =
      (B + A) % 2 := by
    rw [bitValue_write_ne (Ne.symm hcb), hb1]
  have hc2 : bitValue (writeField (writeField i a 1 A) c 1 C) c = C := by
    rw [bitValue_write_self]
    omega
  have h3 : RGate.act (.cx c b) (writeField (writeField i a 1 A) c 1 C) =
      writeField (writeField (writeField i a 1 A) c 1 C)
        b 1 ((A + B + C) % 2) := by
    rw [act_cx_write, hb2, hc2]
    exact write_congr (by omega)
  show RGate.act (.cx c b)
      (RGate.act (.cx a c) (RGate.act (.ccx c b a) i)) = _
  rw [h1, h2, h3]

def majState (i a b c A B C : Nat) : Nat :=
  writeField
    (writeField (writeField i b 1 ((B + A) % 2))
      c 1 ((C + A) % 2))
    a 1 ((A + B + C) / 2)

theorem act_maj' {c b a : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {i A B C : Nat}
    (hA : bitValue i a = A) (hB : bitValue i b = B)
    (hC : bitValue i c = C) :
    actGates (maj c b a) i = majState i a b c A B C := by
  unfold majState
  rw [act_maj hab hac hcb, hA, hB, hC]

theorem bitValue_majState_a {i a b c A B C : Nat}
    (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    bitValue (majState i a b c A B C) a = (A + B + C) / 2 := by
  unfold majState
  rw [bitValue_write_self]
  omega

theorem bitValue_majState_b {i a b c A B C : Nat}
    (hab : a ≠ b) (hcb : c ≠ b) :
    bitValue (majState i a b c A B C) b = (B + A) % 2 := by
  unfold majState
  rw [bitValue_write_ne (Ne.symm hab),
    bitValue_write_ne (Ne.symm hcb), bitValue_write_self]
  omega

theorem bitValue_majState_c {i a b c A B C : Nat} (hac : a ≠ c) :
    bitValue (majState i a b c A B C) c = (C + A) % 2 := by
  unfold majState
  rw [bitValue_write_ne (Ne.symm hac), bitValue_write_self]
  omega

theorem readField_majState {i a b c A B C o len : Nat}
    (h1 : b + 1 ≤ o ∨ o + len ≤ b)
    (h2 : c + 1 ≤ o ∨ o + len ≤ c)
    (h3 : a + 1 ≤ o ∨ o + len ≤ a) :
    readField (majState i a b c A B C) o len = readField i o len := by
  unfold majState
  rw [readField_writeField_of_disjoint h3,
    readField_writeField_of_disjoint h2,
    readField_writeField_of_disjoint h1]

theorem majState_restore_a {i a b c A B C : Nat}
    (hab : a ≠ b) (hac : a ≠ c)
    (hA : bitValue i a = A) (hA2 : A < 2) :
    writeField (majState i a b c A B C) a 1 A =
      writeField (writeField i b 1 ((B + A) % 2))
        c 1 ((C + A) % 2) := by
  unfold majState
  rw [writeField_writeField]
  refine write_of_bitValue ?_
  rw [bitValue_write_ne hac, bitValue_write_ne hab, hA]
  omega

theorem majState_restore_c {i b c A B C : Nat}
    (hcb : c ≠ b) (hC : bitValue i c = C) (hC2 : C < 2) :
    writeField
        (writeField (writeField i b 1 ((B + A) % 2))
          c 1 ((C + A) % 2))
        c 1 C =
      writeField i b 1 ((B + A) % 2) := by
  rw [writeField_writeField]
  refine write_of_bitValue ?_
  rw [bitValue_write_ne hcb, hC]
  omega

theorem uma_collapse {i a b c A B C X m : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hm : a + 1 + m ≤ b)
    (hc : c + 1 ≤ a ∨ b + 1 + m ≤ c)
    (hA : bitValue i a = A) (hA2 : A < 2)
    (hC : bitValue i c = C) (hC2 : C < 2) :
    writeField
        (writeField
          (writeField
            (writeField (majState i a b c A B C) (b + 1) m X)
            a 1 A)
          c 1 C)
        b 1 ((A + B + C) % 2) =
      writeField (writeField i b 1 ((A + B + C) % 2))
        (b + 1) m X := by
  rw [writeField_comm
      (i := majState i a b c A B C)
      (o₁ := b + 1) (n₁ := m) (v := X)
      (o₂ := a) (n₂ := 1) (u := A) (Or.inr (by omega)),
    majState_restore_a hab hac hA hA2,
    writeField_comm
      (i := writeField (writeField i b 1 ((B + A) % 2))
        c 1 ((C + A) % 2))
      (o₁ := b + 1) (n₁ := m) (v := X)
      (o₂ := c) (n₂ := 1) (u := C) (by omega),
    majState_restore_c hcb hC hC2,
    writeField_comm
      (i := writeField i b 1 ((B + A) % 2))
      (o₁ := b + 1) (n₁ := m) (v := X)
      (o₂ := b) (n₂ := 1) (u := (A + B + C) % 2)
      (Or.inr (by omega)),
    writeField_writeField]

theorem adder_step {a b c m : Nat} (gs : List RGate) (i : Nat)
    (hm : a + 1 + m ≤ b)
    (hc : c + 1 ≤ a ∨ b + 1 + m ≤ c)
    (hinner : ∀ j, actGates gs j =
      writeField j (b + 1) m
        ((readField j (a + 1) m + readField j (b + 1) m +
          bitValue j a) % 2 ^ m)) :
    actGates (maj c b a ++ gs ++ uma c b a) i =
      writeField i b (m + 1)
        ((readField i a (m + 1) + readField i b (m + 1) +
          bitValue i c) % 2 ^ (m + 1)) := by
  have hab : a ≠ b := by omega
  have hac : a ≠ c := by omega
  have hcb : c ≠ b := by omega
  obtain ⟨A, hA⟩ : ∃ x, bitValue i a = x := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, bitValue i b = x := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x, bitValue i c = x := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ x, readField i (a + 1) m = x := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ x, readField i (b + 1) m = x := ⟨_, rfl⟩
  have hA2 : A < 2 := hA ▸ bitValue_lt i a
  have hB2 : B < 2 := hB ▸ bitValue_lt i b
  have hC2 : C < 2 := hC ▸ bitValue_lt i c
  rw [readField_succ i a m, readField_succ i b m,
    hA, hB, hC, hA', hB']
  rw [actGates_append, actGates_append,
    act_maj' hab hac hcb hA hB hC,
    hinner (majState i a b c A B C),
    readField_majState (o := a + 1) (len := m)
      (by omega) (by omega) (by omega),
    readField_majState (o := b + 1) (len := m)
      (by omega) (by omega) (by omega),
    bitValue_majState_a hA2 hB2 hC2, hA', hB']
  obtain ⟨X, hX⟩ : ∃ x,
      (A' + B' + (A + B + C) / 2) % 2 ^ m = x := ⟨_, rfl⟩
  rw [hX]
  have hja : bitValue
      (writeField (majState i a b c A B C) (b + 1) m X) a =
      (A + B + C) / 2 := by
    rw [bitValue_write_out (Or.inl (by omega)),
      bitValue_majState_a hA2 hB2 hC2]
  have hjb : bitValue
      (writeField (majState i a b c A B C) (b + 1) m X) b =
      (B + A) % 2 := by
    rw [bitValue_write_out (Or.inl (by omega)),
      bitValue_majState_b hab hcb]
  have hjc : bitValue
      (writeField (majState i a b c A B C) (b + 1) m X) c =
      (C + A) % 2 := by
    rw [bitValue_write_out (by omega), bitValue_majState_c hac]
  have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
    rw [Nat.pow_succ]
    omega
  have hV :
      (A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1) =
        (A + B + C) % 2 + 2 * X := by
    rw [hpow, Nat.mod_mul]
    have h1 :
        (A + 2 * A' + (B + 2 * B') + C) % 2 =
          (A + B + C) % 2 := by omega
    have h2 :
        (A + 2 * A' + (B + 2 * B') + C) / 2 =
          (A + B + C) / 2 + A' + B' := by omega
    have h3 :
        (A + B + C) / 2 + A' + B' =
          A' + B' + (A + B + C) / 2 := by omega
    rw [h1, h2, h3, hX]
  rw [act_uma hab hac hcb hA2 hB2 hC2 hja hjb hjc,
    uma_collapse hab hac hcb hm hc hA hA2 hC hC2,
    writeField_succ i b m
      ((A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1)),
    hV,
    show ((A + B + C) % 2 + 2 * X) % 2 =
      (A + B + C) % 2 by omega,
    show ((A + B + C) % 2 + 2 * X) / 2 = X by omega]

theorem body_act (n : Nat) : ∀ m st i, st + m ≤ n →
    actGates (body n st m) i =
      writeField i (n + st) m
        ((readField i st m + readField i (n + st) m +
          bitValue i (carryWire n st)) % 2 ^ m) := by
  intro m
  induction m with
  | zero =>
      intro st i _
      rw [show body n st 0 = [] from rfl, actGates_nil, writeField_zero]
  | succ m ih =>
      intro st i hst
      have hc :
          carryWire n st + 1 ≤ st ∨
            n + st + 1 + m ≤ carryWire n st := by
        cases st with
        | zero =>
            right
            rw [carryWire_zero]
            omega
        | succ k =>
            left
            simp
      exact adder_step
        (a := st) (b := n + st) (c := carryWire n st) (m := m)
        (body n (st + 1) m) i (by omega) hc
        (fun j => ih (st + 1) j (by omega))

theorem circuit_addsWrap (n : Nat) : AddsWrap 1 n (circuit n) := by
  intro a b i _ hsource htarget hwork
  have hsource' : readField i 0 n = a := by
    simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using hsource
  have htarget' : readField i n n = b := by
    simpa [adderLayout, Layout.read, Layout.offset, Layout.size] using htarget
  have hcarry : bitValue i (carryWire n 0) = 0 := by
    rw [carryWire_zero, ← readField_one]
    simpa [adderLayout, Layout.read, Layout.offset, Layout.size, Nat.two_mul]
      using hwork
  have hact := body_act n n 0 i (by omega)
  simp only [Nat.add_zero] at hact
  rw [hsource', htarget', hcarry, Nat.add_zero] at hact
  simpa [act, circuit, adderLayout, Layout.write, Layout.offset,
    Layout.size] using hact

def majChain (n : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      maj (carryWire n st) (n + st) st ++ majChain n (st + 1) m

def umaChain (n : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
      umaChain n (st + 1) m ++ uma (carryWire n st) (n + st) st

theorem body_eq_chains (n : Nat) : ∀ m st,
    body n st m = majChain n st m ++ umaChain n st m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [body, majChain, umaChain, ih (st + 1), List.append_assoc]

theorem majChain_carry (n : Nat) : ∀ m st i,
    0 < m → st + m ≤ n →
    bitValue (actGates (majChain n st m) i) (st + m - 1) =
      (readField i st m + readField i (n + st) m +
        bitValue i (carryWire n st)) / 2 ^ m := by
  intro m
  induction m with
  | zero => intro st i h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
      intro st i _ hbound
      have hab : st ≠ n + st := by omega
      have hac : st ≠ carryWire n st := by
        exact fun e => carry_ne_a (show st < n by omega) e.symm
      have hcb : carryWire n st ≠ n + st :=
        carry_ne_b (show st < n by omega)
      rw [show majChain n st (m + 1) =
        maj (carryWire n st) (n + st) st ++
          majChain n (st + 1) m from rfl,
        actGates_append,
        act_maj' hab hac hcb rfl rfl rfl]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [show majChain n (st + 1) 0 = [] from rfl, actGates_nil,
          show st + (0 + 1) - 1 = st from by omega,
          bitValue_majState_a
            (bitValue_lt i st)
            (bitValue_lt i (n + st))
            (bitValue_lt i (carryWire n st)),
          readField_one, readField_one, Nat.pow_one]
      · have hstep := ih (st + 1)
          (majState i st (n + st) (carryWire n st)
            (bitValue i st) (bitValue i (n + st))
            (bitValue i (carryWire n st)))
          hm (by omega)
        simp only [carryWire_succ] at hstep
        rw [show st + (m + 1) - 1 = st + 1 + m - 1 from by omega,
          hstep,
          readField_majState (o := st + 1) (len := m)
            (by omega) (by cases st <;> simp <;> omega) (by omega),
          readField_majState (o := n + (st + 1)) (len := m)
            (by omega) (by cases st <;> simp <;> omega) (by omega),
          bitValue_majState_a
            (bitValue_lt i st)
            (bitValue_lt i (n + st))
            (bitValue_lt i (carryWire n st))]
        have hA := readField_succ i st m
        have hB := readField_succ i (n + st) m
        have hp : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
          rw [Nat.pow_succ]
          omega
        rw [show st + 1 = st + 1 from rfl] at hA
        rw [show n + st + 1 = n + (st + 1) from by omega] at hB
        rw [hA, hB, hp, ← Nat.div_div_eq_div_mul]
        refine congrArg (fun q => q / 2 ^ m) ?_
        have h1 := bitValue_lt i st
        have h2 := bitValue_lt i (n + st)
        have h3 := bitValue_lt i (carryWire n st)
        omega

theorem majChain_wires_lt (n : Nat) : ∀ m st g,
    st + m ≤ n → g ∈ majChain n st m →
    ∀ q ∈ g.wires, q < 2 * n + 1 := by
  intro m
  induction m with
  | zero => intro st g _ hg; simp [majChain] at hg
  | succ m ih =>
      intro st g hbound hg q hq
      rw [show majChain n st (m + 1) =
        maj (carryWire n st) (n + st) st ++
          majChain n (st + 1) m from rfl,
        List.mem_append] at hg
      rcases hg with hg | hg
      · simp only [maj, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;>
          simp only [RGate.wires, List.mem_cons, List.not_mem_nil,
            or_false] at hq <;>
          have hc := carry_lt (show st < n by omega) <;> omega
      · exact ih (st + 1) g (by omega) hg q hq

theorem umaChain_wires_lt (n : Nat) : ∀ m st g,
    st + m ≤ n → g ∈ umaChain n st m →
    ∀ q ∈ g.wires, q < 2 * n + 1 := by
  intro m
  induction m with
  | zero => intro st g _ hg; simp [umaChain] at hg
  | succ m ih =>
      intro st g hbound hg q hq
      rw [show umaChain n st (m + 1) =
        umaChain n (st + 1) m ++
          uma (carryWire n st) (n + st) st from rfl,
        List.mem_append] at hg
      rcases hg with hg | hg
      · exact ih (st + 1) g (by omega) hg q hq
      · simp only [uma, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;>
          simp only [RGate.wires, List.mem_cons, List.not_mem_nil,
            or_false] at hq <;>
          have hc := carry_lt (show st < n by omega) <;> omega

def carryGates (n : Nat) : List RGate :=
  majChain n 0 n ++ [.cx (n - 1) (2 * n + 1)] ++ umaChain n 0 n

def carryCircuit (n : Nat) : RCircuit :=
  { width := 2 * n + 2, gates := carryGates n }

theorem carryCircuit_wellFormed {n : Nat} (hn : 0 < n) :
    (carryCircuit n).wellFormed = true := by
  apply List.all_eq_true.mpr
  intro g hg
  simp only [carryCircuit, carryGates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · have hbase := body_wellFormed n n 0 (by omega)
    rw [body_eq_chains] at hbase
    have h := (List.all_eq_true.mp hbase) g
      (List.mem_append_left _ hg)
    change g.wellFormed (2 * n + 2) = true
    exact RGate.wellFormed_mono (by omega) h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    change (RGate.cx (n - 1) (2 * n + 1)).wellFormed (2 * n + 2) = true
    simp only [carryCircuit, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · have hbase := body_wellFormed n n 0 (by omega)
    rw [body_eq_chains] at hbase
    have h := (List.all_eq_true.mp hbase) g
      (List.mem_append_right _ hg)
    change g.wellFormed (2 * n + 2) = true
    exact RGate.wellFormed_mono (by omega) h

theorem carryGates_act {n i : Nat} (hn : 0 < n) :
    actGates (carryGates n) i =
      writeField
        (writeField i n n
          ((readField i 0 n + readField i n n + bitValue i (2 * n)) %
            2 ^ n))
        (2 * n + 1) 1
          ((bitValue i (2 * n + 1) +
            (readField i 0 n + readField i n n + bitValue i (2 * n)) /
              2 ^ n) % 2) := by
  let pre := actGates (majChain n 0 n) i
  have hcarry : bitValue pre (n - 1) =
      (readField i 0 n + readField i n n + bitValue i (2 * n)) /
        2 ^ n := by
    simpa [pre] using majChain_carry n n 0 i hn (by omega)
  have hsign : bitValue pre (2 * n + 1) = bitValue i (2 * n + 1) := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside
      (fun g hg q hq => Or.inl (by
        have := majChain_wires_lt n n 0 g (by omega) hg q hq
        omega)) i
  have hsuffix : ∀ g ∈ umaChain n 0 n, ∀ q ∈ g.wires,
      q < 2 * n + 1 ∨ 2 * n + 2 ≤ q := by
    intro g hg q hq
    exact Or.inl (umaChain_wires_lt n n 0 g (by omega) hg q hq)
  have hbody := body_act n n 0 i (by omega)
  rw [body_eq_chains] at hbody
  change actGates
    (majChain n 0 n ++ [.cx (n - 1) (2 * n + 1)] ++
      umaChain n 0 n) i = _
  rw [actGates_append, actGates_append]
  change actGates (umaChain n 0 n)
    (RGate.act (.cx (n - 1) (2 * n + 1)) pre) = _
  rw [act_cx_write, hcarry, hsign,
    actGates_write_of_outside hsuffix]
  rw [← actGates_append, hbody]
  simp only [Nat.add_zero, carryWire_zero]

theorem carryCircuit_act {n i : Nat} (hn : 0 < n) :
    act (carryCircuit n) i =
      writeField
        (writeField i n n
          ((readField i 0 n + readField i n n + bitValue i (2 * n)) %
            2 ^ n))
        (2 * n + 1) 1
          ((bitValue i (2 * n + 1) +
            (readField i 0 n + readField i n n + bitValue i (2 * n)) /
              2 ^ n) % 2) :=
  carryGates_act hn

def difference (width a b : Nat) : Nat :=
  (b + (2 ^ width - a)) % 2 ^ width

theorem difference_eq_if {width a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) :
    difference width a b =
      if a ≤ b then b - a else b + (2 ^ width - a) := by
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    unfold difference
    have heq : b + (2 ^ width - a) = 2 ^ width + (b - a) := by
      omega
    have hsub : b - a < 2 ^ width := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hsub]
  · rw [if_neg hab]
    unfold difference
    exact Nat.mod_eq_of_lt (by omega)

theorem difference_eq_sub_of_le {width a b : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hab : a ≤ b) :
    difference width a b = b - a := by
  rw [difference_eq_if ha hb, if_pos hab]

def borrow (a b : Nat) : Nat := if b < a then 1 else 0

theorem difference_add {modulus a b : Nat}
    (_hm : 0 < modulus) (ha : a < modulus) (hb : b < modulus) :
    let x := (b + (modulus - a)) % modulus
    (a + x) % modulus = b ∧
      (a + x) / modulus = borrow a b := by
  dsimp only
  by_cases hlt : b < a
  · have hx : b + (modulus - a) < modulus := by omega
    rw [Nat.mod_eq_of_lt hx]
    constructor
    · have heq : a + (b + (modulus - a)) = modulus + b := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hb]
    · rw [borrow, if_pos hlt]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · have heq : b + (modulus - a) = modulus + (b - a) := by omega
    have hdiff : b - a < modulus := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hdiff]
    constructor
    · rw [show a + (b - a) = b by omega, Nat.mod_eq_of_lt hb]
    · rw [borrow, if_neg hlt, show a + (b - a) = b by omega]
      exact Nat.div_eq_of_lt hb

theorem body_reverse_act {n i : Nat}
    (hcarry : bitValue i (2 * n) = 0) :
    actGates (body n 0 n).reverse i =
      writeField i n n
        (difference n (readField i 0 n) (readField i n n)) := by
  let a := readField i 0 n
  let b := readField i n n
  let x := difference n a b
  let j := writeField i n n x
  have ha : a < 2 ^ n := readField_lt i 0 n
  have hb : b < 2 ^ n := readField_lt i n n
  have hspec : (a + x) % 2 ^ n = b := by
    exact (difference_add (a := a) (b := b)
      (Nat.two_pow_pos n) ha hb).1
  have hx : x < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hjA : readField j 0 n = a := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by omega)]
  have hjB : readField j n n = x := by
    simp only [j]
    rw [readField_writeField_self hx]
  have hjCarry : bitValue j (2 * n) = 0 := by
    simp only [j]
    rw [bitValue_write_out (by omega), hcarry]
  have hfwd := body_act n n 0 j (by omega)
  simp only [Nat.add_zero, carryWire_zero] at hfwd
  rw [hjA, hjB, hjCarry, Nat.add_zero, hspec] at hfwd
  have hrestore : writeField j n n b = i := by
    simp only [j]
    rw [writeField_writeField, show b = readField i n n from rfl,
      writeField_read]
  rw [hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (circuit n).width) (circuit_wellFormed n) j
  change actGates (body n 0 n).reverse (actGates (body n 0 n) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, x, a, b] using hinv

theorem carryGates_reverse_act {n i : Nat} (hn : 0 < n)
    (hcarry : bitValue i (2 * n) = 0) :
    actGates (carryGates n).reverse i =
      writeField
        (writeField i n n
          (difference n (readField i 0 n) (readField i n n)))
        (2 * n + 1) 1
          ((bitValue i (2 * n + 1) +
            borrow (readField i 0 n) (readField i n n)) % 2) := by
  let a := readField i 0 n
  let b := readField i n n
  let s := bitValue i (2 * n + 1)
  let x := difference n a b
  let br := borrow a b
  let j := writeField (writeField i n n x) (2 * n + 1) 1 ((s + br) % 2)
  have ha : a < 2 ^ n := by
    exact readField_lt i 0 n
  have hb : b < 2 ^ n := by
    exact readField_lt i n n
  have hs : s < 2 := bitValue_lt i (2 * n + 1)
  have hspec : (a + x) % 2 ^ n = b ∧
      (a + x) / 2 ^ n = borrow a b := by
    simpa [x, difference] using difference_add (a := a) (b := b)
      (Nat.two_pow_pos n) ha hb
  have hx : x < 2 ^ n := by
    exact Nat.mod_lt _ (Nat.two_pow_pos n)
  have hjA : readField j 0 n = a := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by omega),
      readField_writeField_of_disjoint (by omega)]
  have hjB : readField j n n = x := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by omega),
      readField_writeField_self hx]
  have hjCarry : bitValue j (2 * n) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by omega), bitValue_write_out (by omega), hcarry]
  have hjSign : bitValue j (2 * n + 1) = (s + br) % 2 := by
    simp only [j]
    rw [bitValue_write_self]
    omega
  have hsum : (a + x) % 2 ^ n = b := hspec.1
  have hover : (a + x) / 2 ^ n = br := hspec.2
  have hsign : (((s + br) % 2 + br) % 2) = s := by
    unfold br borrow
    by_cases hlt : b < a <;> simp [hlt] <;> omega
  have hfwd := carryGates_act (n := n) (i := j) hn
  rw [hjA, hjB, hjCarry, Nat.add_zero, hsum, hjSign, hover, hsign] at hfwd
  have hrestore :
      writeField (writeField j n n b) (2 * n + 1) 1 s = i := by
    simp only [j]
    rw [writeField_comm
        (i := writeField i n n x)
        (o₁ := 2 * n + 1) (n₁ := 1) (v := (s + br) % 2)
        (o₂ := n) (n₂ := n) (u := b) (by omega),
      writeField_writeField]
    change writeField (writeField (writeField i n n x) n n b)
      (2 * n + 1) 1 s = i
    rw [writeField_writeField, show b = readField i n n from rfl,
      writeField_read]
    change writeField i (2 * n + 1) 1 (bitValue i (2 * n + 1)) = i
    rw [← readField_one, writeField_read]
  rw [hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (carryCircuit n).width)
    (carryCircuit_wellFormed hn) j
  change actGates (carryGates n).reverse (actGates (carryGates n) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, x, br, a, b, s] using hinv

theorem carryCircuit_reverse_act {n i : Nat} (hn : 0 < n)
    (hcarry : bitValue i (2 * n) = 0) :
    act (carryCircuit n).reverse i =
      writeField
        (writeField i n n
          (difference n (readField i 0 n) (readField i n n)))
        (2 * n + 1) 1
          ((bitValue i (2 * n + 1) +
            borrow (readField i 0 n) (readField i n n)) % 2) :=
  carryGates_reverse_act hn hcarry

theorem length_majChain (n : Nat) : ∀ m st,
    (majChain n st m).length = 3 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [majChain, maj, ih (st + 1)]
      omega

theorem length_umaChain (n : Nat) : ∀ m st,
    (umaChain n st m).length = 3 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
      intro st
      simp [umaChain, uma, ih (st + 1)]
      omega

theorem carryGates_length (n : Nat) :
    (carryGates n).length = 6 * n + 1 := by
  simp [carryGates, length_majChain, length_umaChain]
  omega

theorem carryGates_ccx (n : Nat) :
    (carryGates n).countP RGate.isCcx = 2 * n := by
  rw [carryGates, List.countP_append, List.countP_append]
  have hbody := ccx_body n n 0
  rw [body_eq_chains, List.countP_append] at hbody
  simp [RGate.isCcx]
  omega

theorem carryGates_cx (n : Nat) :
    (carryGates n).countP RGate.isCx = 4 * n + 1 := by
  rw [carryGates, List.countP_append, List.countP_append]
  have hbody := cx_body n n 0
  rw [body_eq_chains, List.countP_append] at hbody
  simp [RGate.isCx]
  omega

end Adder
end Reversible
end VQ
