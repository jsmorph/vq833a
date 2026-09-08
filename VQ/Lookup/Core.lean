/-
Finite three-bit-address quantum read-only memory.
-/
import VQ.Program.Input
import VQ.Program.Realise
import VQ.Reversible.Place
import VQ.Lookup.Spec

namespace VQ
namespace Lookup3

open Algebra Reversible Semantics

def addressWidth : Nat := 3

def outputOffset : Nat := addressWidth

def workWire (m : Nat) : Nat := outputOffset + m

def flagWire (m : Nat) : Nat := outputOffset + m + 1

def width (m : Nat) : Nat := outputOffset + m + 2

def value (table : List Nat) (m address : Nat) : Nat :=
  table.getD address 0 % 2 ^ m

def address (i : Nat) : Nat := readField i 0 addressWidth

def output (m i : Nat) : Nat := readField i outputOffset m

def workspaceClear (m i : Nat) : Prop :=
  i.testBit (workWire m) = false ∧ i.testBit (flagWire m) = false

def maskBit (row q : Nat) : List RGate :=
  if row.testBit q then [] else [.x q]

def masks (row : Nat) : List RGate :=
  maskBit row 0 ++ maskBit row 1 ++ maskBit row 2

def compute (m row : Nat) : List RGate :=
  masks row ++ [.ccx 0 1 (workWire m), .ccx (workWire m) 2 (flagWire m)]

def wordXorsAux (m word : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | q, len + 1 =>
      (if word.testBit q then [.cx (flagWire m) (outputOffset + q)] else []) ++
        wordXorsAux m word (q + 1) len

def wordXors (m word : Nat) : List RGate := wordXorsAux m word 0 m

def rowLookup (m row word : Nat) : List RGate :=
  compute m row ++ wordXors m word ++ (compute m row).reverse

def lookupRows (table : List Nat) (m : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | row, count + 1 =>
      rowLookup m row (value table m row) ++ lookupRows table m (row + 1) count

def lookupGates (table : List Nat) (m : Nat) : List RGate :=
  lookupRows table m 0 (2 ^ addressWidth)

def lookupCircuit (table : List Nat) (m : Nat) : RCircuit :=
  { width := width m, gates := lookupGates table m }

def xorOutput (table : List Nat) (m i : Nat) : Nat :=
  writeField i outputOffset m (output m i ^^^ value table m (address i))

theorem value_lt (table : List Nat) (m address : Nat) : value table m address < 2 ^ m := by
  exact Nat.mod_lt _ (Nat.two_pow_pos m)

theorem address_lt (i : Nat) : address i < 2 ^ addressWidth :=
  readField_lt i 0 addressWidth

theorem output_lt (m i : Nat) : output m i < 2 ^ m :=
  readField_lt i outputOffset m

theorem compute_wellFormed (m row : Nat) :
    (compute m row).all (RGate.wellFormed (width m)) = true := by
  simp [compute, masks, maskBit, RGate.wellFormed, workWire, flagWire, width,
    outputOffset, addressWidth]
  omega

theorem rowLookup_wellFormed (m row word : Nat) :
    (rowLookup m row word).all (RGate.wellFormed (width m)) = true := by
  simp only [rowLookup, List.all_append, compute_wellFormed, List.all_reverse,
    Bool.true_and]
  have haux : ∀ q len, q + len ≤ m →
      (wordXorsAux m word q len).all (RGate.wellFormed (width m)) = true := by
    intro q len hlen
    induction len generalizing q with
    | zero => rfl
    | succ len ih =>
      simp only [wordXorsAux, List.all_append]
      split
      · simp only [List.all_cons, List.all_nil, Bool.and_true, RGate.wellFormed,
          Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · constructor <;> simp [flagWire, width, outputOffset] <;> omega
        · exact ih (q + 1) (by omega)
      · exact ih (q + 1) (by omega)
  simpa [wordXors] using haux 0 m (by omega)

theorem lookup_wellFormed (table : List Nat) (m : Nat) :
    (lookupCircuit table m).wellFormed = true := by
  have hrows : ∀ row count,
      (lookupRows table m row count).all (RGate.wellFormed (width m)) = true := by
    intro row count
    induction count generalizing row with
    | zero => rfl
    | succ count ih =>
      simp only [lookupRows, List.all_append, rowLookup_wellFormed, ih, Bool.and_self]
  exact hrows 0 (2 ^ addressWidth)

theorem act_wordXorsAux (m word : Nat) : ∀ q len i, q + len ≤ m →
    actGates (wordXorsAux m word q len) i =
      if i.testBit (flagWire m) then
        Program.inputXorIndex word q (outputOffset + q) len i
      else i := by
  intro q len
  induction len generalizing q with
  | zero => intro i _; simp [wordXorsAux, Program.inputXorIndex, actGates_nil]
  | succ len ih =>
    intro i hlen
    rw [wordXorsAux]
    by_cases hb : word.testBit q = true
    · rw [if_pos hb, actGates_append, ih (q + 1) _ (by omega)]
      dsimp +instances only [actGates, RGate.act]
      by_cases hf : i.testBit (flagWire m) = true
      · have hne : flagWire m ≠ outputOffset + q := by
          simp [flagWire, outputOffset]
          omega
        rw [if_pos hf, RGate.testBit_xor_of_ne hne,
          Program.inputXorIndex, if_pos hb]
        simp [hf, Nat.add_assoc]
      · rw [if_neg hf, if_neg hf, Program.inputXorIndex, if_pos hb]
        simp [hf]
    · rw [if_neg hb, List.nil_append, ih (q + 1) i (by omega),
        Program.inputXorIndex, if_neg hb]
      simp [Nat.add_assoc]

theorem act_wordXors (m word i : Nat) :
    actGates (wordXors m word) i =
      if i.testBit (flagWire m) then
        Program.inputXorIndex word 0 outputOffset m i
      else i := by
  exact act_wordXorsAux m word 0 m i (by omega)

theorem xor_shifted_eq_write_xor {i v off len : Nat} (hv : v < 2 ^ len) :
    i ^^^ (v <<< off) = writeField i off len (readField i off len ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge q off with hlo | hlo
  · rw [testBit_writeField_outside (Or.inl hlo)]
    simp [Nat.not_le.mpr hlo]
  · rcases Nat.lt_or_ge q (off + len) with hhi | hhi
    · rw [testBit_writeField_inside hlo hhi, Nat.testBit_xor, testBit_readField]
      simp [hlo, show q - off < len by omega, show off + (q - off) = q by omega]
    · rw [testBit_writeField_outside (Or.inr hhi)]
      have hvq : v.testBit (q - off) = false := by
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hlo, hvq]

theorem act_wordXors_eq (m word i : Nat) :
    actGates (wordXors m word) i =
      if i.testBit (flagWire m) then
        writeField i outputOffset m (output m i ^^^ readField word 0 m)
      else i := by
  rw [act_wordXors]
  split
  · rw [Program.inputXorIndex_eq_shiftedField,
      xor_shifted_eq_write_xor (readField_lt word 0 m)]
    rfl
  · rfl

theorem address_eq_row_iff (i row : Nat) :
    address i = row % 2 ^ addressWidth ↔
      ∀ q, q < addressWidth → i.testBit q = row.testBit q := by
  constructor
  · intro h q hq
    have hb := congrArg (fun x : Nat => x.testBit q) h
    simpa [address, testBit_readField, Nat.testBit_mod_two_pow, hq] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [address, testBit_readField, Nat.testBit_mod_two_pow]
    by_cases hq : q < addressWidth
    · simp [hq, h q hq]
    · simp [hq]

theorem maskBit_same (i row q : Nat) :
    (actGates (maskBit row q) i).testBit q = (i.testBit q == row.testBit q) := by
  cases hr : row.testBit q <;> cases hi : i.testBit q <;>
    simp [maskBit, hr, hi, actGates_cons, actGates_nil, RGate.act]

theorem maskBit_other {i row q r : Nat} (h : r ≠ q) :
    (actGates (maskBit row q) i).testBit r = i.testBit r := by
  cases hr : row.testBit q <;>
    simp [maskBit, hr, actGates_cons, actGates_nil, RGate.act,
      RGate.testBit_xor_of_ne h]

theorem maskBit_mem {row q : Nat} {g : RGate} (h : g ∈ maskBit row q) :
    g = .x q := by
  unfold maskBit at h
  split at h
  · simp at h
  · simpa using h

theorem masks_wires {row : Nat} {g : RGate} (hg : g ∈ masks row)
    {q : Nat} (hq : q ∈ g.wires) : q = 0 ∨ q = 1 ∨ q = 2 := by
  simp only [masks, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · have heq := maskBit_mem hg
    clear hg
    subst g
    left
    simpa [RGate.wires] using hq
  · have heq := maskBit_mem hg
    clear hg
    subst g
    right; left
    simpa [RGate.wires] using hq
  · have heq := maskBit_mem hg
    clear hg
    subst g
    right; right
    simpa [RGate.wires] using hq

theorem masks_bits (i row : Nat) :
    let j := actGates (masks row) i
    j.testBit 0 = (i.testBit 0 == row.testBit 0) ∧
      j.testBit 1 = (i.testBit 1 == row.testBit 1) ∧
      j.testBit 2 = (i.testBit 2 == row.testBit 2) := by
  simp only [masks, actGates_append]
  constructor
  · rw [maskBit_other (show 0 ≠ 2 by omega),
      maskBit_other (show 0 ≠ 1 by omega), maskBit_same]
  constructor
  · rw [maskBit_other (show 1 ≠ 2 by omega), maskBit_same,
      maskBit_other (show 1 ≠ 0 by omega)]
  · rw [maskBit_same, maskBit_other (show 2 ≠ 1 by omega),
      maskBit_other (show 2 ≠ 0 by omega)]

theorem compute_flag {m row i : Nat} (hclear : workspaceClear m i) :
    (actGates (compute m row) i).testBit (flagWire m) =
      decide (address i = row % 2 ^ addressWidth) := by
  let j := actGates (masks row) i
  have hj := masks_bits i row
  have hw : j.testBit (workWire m) = false := by
    show (actGates (masks row) i).testBit (workWire m) = false
    rw [testBit_actGates_of_outside]
    · exact hclear.1
    · intro g hg hmem
      rcases masks_wires hg hmem with h | h | h <;>
        simp [workWire, outputOffset, addressWidth] at h <;> omega
  have hf : j.testBit (flagWire m) = false := by
    show (actGates (masks row) i).testBit (flagWire m) = false
    rw [testBit_actGates_of_outside]
    · exact hclear.2
    · intro g hg hmem
      rcases masks_wires hg hmem with h | h | h <;>
        simp [flagWire, outputOffset, addressWidth] at h <;> omega
  let k := RGate.act (.ccx 0 1 (workWire m)) j
  have hkw : k.testBit (workWire m) = (j.testBit 0 && j.testBit 1) := by
    unfold k
    cases h0 : j.testBit 0 <;> cases h1 : j.testBit 1 <;>
      simp [RGate.act, h0, h1, hw]
  have hk2 : k.testBit 2 = j.testBit 2 := by
    unfold k
    apply RGate.testBit_act_of_not_mem
    simp [RGate.wires, workWire, outputOffset, addressWidth]
    omega
  have hkf : k.testBit (flagWire m) = false := by
    unfold k
    rw [RGate.testBit_act_of_not_mem (by
      simp [RGate.wires, workWire, flagWire, outputOffset, addressWidth])]
    exact hf
  have hcore : (RGate.act (.ccx (workWire m) 2 (flagWire m)) k).testBit
      (flagWire m) = (j.testBit 0 && j.testBit 1 && j.testBit 2) := by
    simp only [RGate.act]
    rw [hkw, hk2]
    cases h0 : j.testBit 0 <;> cases h1 : j.testBit 1 <;> cases h2 : j.testBit 2 <;>
      simp [hkf]
  rw [compute, actGates_append]
  change (RGate.act (.ccx (workWire m) 2 (flagWire m)) k).testBit (flagWire m) = _
  rw [hcore, hj.1, hj.2.1, hj.2.2]
  have haddr : address i = row % 2 ^ addressWidth ↔
      i.testBit 0 = row.testBit 0 ∧ i.testBit 1 = row.testBit 1 ∧
        i.testBit 2 = row.testBit 2 := by
    rw [address_eq_row_iff]
    constructor
    · intro h
      exact ⟨h 0 (by simp [addressWidth]), h 1 (by simp [addressWidth]),
        h 2 (by simp [addressWidth])⟩
    · intro h q hq
      have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by
        simp [addressWidth] at hq
        omega
      rcases hq' with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, haddr]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem compute_outside_output (m row : Nat) :
    ∀ g ∈ compute m row, ∀ q ∈ g.wires,
      q < outputOffset ∨ outputOffset + m ≤ q := by
  intro g hg q hq
  simp only [compute, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  · rcases masks_wires hg hq with rfl | rfl | rfl <;>
      simp [outputOffset, addressWidth]
  · simp [RGate.wires, workWire, outputOffset, addressWidth] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl (by simp [outputOffset, addressWidth])
    · exact Or.inl (by simp [outputOffset, addressWidth])
    · exact Or.inr (by simp [outputOffset, addressWidth])
  · simp [RGate.wires, workWire, flagWire, outputOffset, addressWidth] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inr (by simp [outputOffset, addressWidth])
    · exact Or.inl (by simp [outputOffset, addressWidth])
    · exact Or.inr (by simp [outputOffset, addressWidth])

theorem compute_preserves_output (m row i : Nat) :
    output m (actGates (compute m row) i) = output m i := by
  exact readField_actGates_of_outside (compute_outside_output m row) i

theorem rowLookup_act {m row word i : Nat} (hclear : workspaceClear m i) :
    actGates (rowLookup m row word) i =
      if address i = row % 2 ^ addressWidth then
        writeField i outputOffset m (output m i ^^^ readField word 0 m)
      else i := by
  have hwf := compute_wellFormed m row
  have hout := compute_outside_output m row
  have hcopy : ∀ j, actGates (wordXors m word) j =
      writeField j outputOffset m
        (if j.testBit (flagWire m) then output m j ^^^ readField word 0 m else output m j) := by
    intro j
    rw [act_wordXors_eq]
    split
    · rfl
    · exact (writeField_read j outputOffset m).symm
  have h := actGates_compute_use_uncompute hwf hout hcopy i
  rw [rowLookup, h, compute_preserves_output, compute_flag hclear]
  by_cases hp : address i = row % 2 ^ addressWidth <;>
    simp [hp, output, writeField_read]

theorem address_write_output (m i v : Nat) :
    address (writeField i outputOffset m v) = address i := by
  unfold address
  exact readField_writeField_of_disjoint (Or.inr (by
    simp [outputOffset, addressWidth]))

theorem workspaceClear_write_output {m i v : Nat} (h : workspaceClear m i) :
    workspaceClear m (writeField i outputOffset m v) := by
  constructor
  · rw [testBit_writeField_outside (Or.inr (by simp [workWire, outputOffset]))]
    exact h.1
  · rw [testBit_writeField_outside (Or.inr (by simp [flagWire, outputOffset]))]
    exact h.2

theorem rowLookup_value_act {table : List Nat} {m row i : Nat}
    (hrow : row < 2 ^ addressWidth) (hclear : workspaceClear m i) :
    actGates (rowLookup m row (value table m row)) i =
      if address i = row then xorOutput table m i else i := by
  rw [rowLookup_act hclear, Nat.mod_eq_of_lt hrow, readField_zero,
    Nat.mod_eq_of_lt (value_lt table m row)]
  by_cases h : address i = row <;> simp [h, xorOutput]

theorem lookupRows_act {table : List Nat} {m start count i : Nat}
    (hbound : start + count ≤ 2 ^ addressWidth) (hclear : workspaceClear m i) :
    actGates (lookupRows table m start count) i =
      if start ≤ address i ∧ address i < start + count then xorOutput table m i else i := by
  induction count generalizing start i with
  | zero =>
    rw [lookupRows, actGates_nil, if_neg]
    omega
  | succ count ih =>
    rw [lookupRows, actGates_append,
      rowLookup_value_act (show start < 2 ^ addressWidth by omega) hclear]
    by_cases heq : address i = start
    · rw [if_pos heq]
      have haddr : address (xorOutput table m i) = address i :=
        address_write_output m i _
      have hwork : workspaceClear m (xorOutput table m i) :=
        workspaceClear_write_output hclear
      rw [ih (start := start + 1) (i := xorOutput table m i) (by omega) hwork]
      rw [if_neg (by rw [haddr, heq]; omega), if_pos (by omega)]
    · rw [if_neg heq, ih (start := start + 1) (i := i) (by omega) hclear]
      by_cases hrange : start + 1 ≤ address i ∧ address i < start + 1 + count
      · rw [if_pos hrange, if_pos (by omega)]
      · rw [if_neg hrange, if_neg (by
          intro h
          apply hrange
          constructor <;> omega)]

theorem lookup_act {table : List Nat} {m i : Nat} (hclear : workspaceClear m i) :
    act (lookupCircuit table m) i = xorOutput table m i := by
  rw [lookupCircuit, lookupGates]
  change actGates (lookupRows table m 0 (2 ^ addressWidth)) i = _
  rw [lookupRows_act (by omega) hclear, if_pos]
  exact ⟨Nat.zero_le _, address_lt i⟩

def CoherentXorLookup (table : List Nat) (m : Nat) (r : RCircuit) : Prop :=
  r.width = width m ∧ r.wellFormed = true ∧
    ∀ i, workspaceClear m i → act r i = xorOutput table m i

theorem lookup_correct (table : List Nat) (m : Nat) :
    CoherentXorLookup table m (lookupCircuit table m) := by
  exact ⟨rfl, lookup_wellFormed table m, fun _ => lookup_act⟩

theorem generic_workspaceClear_iff (m i : Nat) :
    Lookup.workspace addressWidth m 2 i = 0 ↔ workspaceClear m i := by
  change readField i (addressWidth + m) 2 = 0 ↔ _
  rw [show 2 = 1 + 1 by omega, readField_split]
  simp [workspaceClear, workWire, flagWire, outputOffset,
    readField_one_eq_if]

theorem lookup_correct_generic (table : List Nat) (m : Nat) :
    Lookup.CoherentXorLookup table addressWidth m 2 (lookupCircuit table m) := by
  refine ⟨?_, lookup_wellFormed table m, ?_⟩
  · simp [lookupCircuit, Lookup.layout, width, outputOffset, addressWidth,
      Layout.width]
    omega
  · intro i hworkspace
    have hact := lookup_act (table := table) (m := m) (i := i)
      ((generic_workspaceClear_iff m i).mp hworkspace)
    simpa [Lookup.xorOutput, Lookup.output, Lookup.address, Lookup.value,
      Lookup.layout, Layout.write, Layout.read, Layout.offset, Layout.size,
      xorOutput, output, address, value, outputOffset, addressWidth] using hact

theorem run_lookup_basis {level : Nat} (hl : 3 ≤ level) {table : List Nat} {m i : Nat}
    (hclear : workspaceClear m i) :
    Semantics.run level (compile (lookupCircuit table m)) (basis i) =
      basis (xorOutput table m i) := by
  rw [run_compile_basis hl (lookup_wellFormed table m), lookup_act hclear]

theorem run_lookup_superpose {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (m : Nat) (L : List Nat) (a : Nat → Dy (deg level))
    (hclear : ∀ i ∈ L, workspaceClear m i) :
    Semantics.run level (compile (lookupCircuit table m)) (superpose id a L) =
      superpose (xorOutput table m) a L := by
  induction L with
  | nil => simp [superpose, Semantics.run_zero]
  | cons i L ih =>
    simp only [superpose, id_eq]
    rw [Semantics.run_add, Semantics.run_smul,
      run_lookup_basis hl (hclear i (List.mem_cons_self ..)),
      ih (fun j hj => hclear j (List.mem_cons_of_mem i hj))]

end Lookup3
end VQ
