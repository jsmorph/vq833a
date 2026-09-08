import VQ.Semantics.Expand
import VQ.Circuit.Compose
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 8000

namespace VQ
namespace Tests
namespace QFT

open Algebra Semantics

def qftLevel : Nat → Nat
  | 0 => 0
  | n + 1 => max 3 (n + 2)

def qftCircuit (n : Nat) : Circuit :=
  Circuit.ofGates n (Circuit.qft (List.range n).reverse)

def FourierColumn (level n x : Nat) : Vec (deg level) := fun y =>
  if y < 2 ^ n then
    (Dy.invSqrt2 (deg level) ^ n) *
      (Semantics.phase level n ^ (x * y))
  else Dy.zero (deg level)

theorem FourierColumn_support (level n x : Nat) :
    WFVec (2 ^ n) (FourierColumn level n x) := by
  intro y hy
  simp [FourierColumn, show ¬y < 2 ^ n by omega]

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n

theorem run_phase_basis {level width k q j : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) :
    runGates level width (Circuit.phase k q) (basis j : Vec (deg level)) =
      if j.testBit q then Semantics.phase level k • basis j else basis j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero =>
      simpa [Circuit.phase, runGates_cons, runGates_nil] using
        (apply_t (level := level) (w := width) hq (by omega) j)
  | succ k =>
      have hbound : k + 4 ≤ level := by omega
      have heq : 3 + (k + 1) = k + 4 := by omega
      rw [heq]
      simpa [Circuit.phase, runGates_cons, runGates_nil, Nat.add_assoc] using
        (apply_p (level := level) (w := width) (k := k + 4) hq (by omega) hbound j)

theorem run_phaseInv_basis {level width k q j : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) :
    runGates level width (Circuit.phaseInv k q) (basis j : Vec (deg level)) =
      if j.testBit q then Semantics.phaseInv level k • basis j else basis j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero =>
      simpa [Circuit.phaseInv, runGates_cons, runGates_nil] using
        (apply_tdg (level := level) (w := width) hq (by omega) j)
  | succ k =>
      have hbound : k + 4 ≤ level := by omega
      have heq : 3 + (k + 1) = k + 4 := by omega
      rw [heq]
      simpa [Circuit.phaseInv, runGates_cons, runGates_nil, Nat.add_assoc] using
        (apply_pdg (level := level) (w := width) (k := k + 4) hq (by omega) hbound j)

theorem phase_wellFormedAt {level width k q : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) :
    (Circuit.phase k q).all (Gate.wellFormedAt level width) = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => simp [Circuit.phase, Gate.wellFormedAt, hq, show 3 ≤ level by omega]
  | succ k =>
      have heq : 3 + (k + 1) = k + 4 := by omega
      have hbound : k + 4 ≤ level := by omega
      rw [heq]
      simp [Circuit.phase, Gate.wellFormedAt, hq, hbound]

theorem phaseInv_wellFormedAt {level width k q : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) :
    (Circuit.phaseInv k q).all (Gate.wellFormedAt level width) = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => simp [Circuit.phaseInv, Gate.wellFormedAt, hq, show 3 ≤ level by omega]
  | succ k =>
      have heq : 3 + (k + 1) = k + 4 := by omega
      have hbound : k + 4 ≤ level := by omega
      rw [heq]
      simp [Circuit.phaseInv, Gate.wellFormedAt, hq, hbound]

theorem cphase_wellFormedAt {level width k a b : Nat} (hk : 2 ≤ k)
    (hkl : k + 1 ≤ level) (ha : a < width) (hb : b < width) (hab : a ≠ b) :
    (Circuit.cphase k a b).all (Gate.wellFormedAt level width) = true := by
  simp [Circuit.cphase, phase_wellFormedAt (by omega) hkl,
    phaseInv_wellFormedAt (by omega) hkl, Gate.wellFormedAt, ha, hb, hab]

theorem cphase_length {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).length = 5 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => simp [Circuit.cphase, Circuit.phase, Circuit.phaseInv]
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv]

theorem cphase_cnot {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isTwoQubit = 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => simp [Circuit.cphase, Circuit.phase, Circuit.phaseInv, List.countP_cons,
      Gate.isTwoQubit]
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv, List.countP_cons, Gate.isTwoQubit]

theorem cphase_t_two (a b : Nat) :
    (Circuit.cphase 2 a b).countP Gate.isT = 3 := by
  rfl

theorem cphase_t_of_three {k a b : Nat} (hk : 3 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isT = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  have heq : 3 + k + 1 = k + 4 := by omega
  simp only [Circuit.cphase]
  rw [heq]
  simp [Circuit.phase, Circuit.phaseInv, Gate.isT]

theorem cphase_phase_two (a b : Nat) :
    (Circuit.cphase 2 a b).countP Gate.isPhase = 0 := by
  rfl

theorem cphase_phase_of_three {k a b : Nat} (hk : 3 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isPhase = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  have heq : 3 + k + 1 = k + 4 := by omega
  simp only [Circuit.cphase]
  rw [heq]
  simp [Circuit.phase, Circuit.phaseInv, List.countP_cons, Gate.isPhase]

theorem cphase_nonClifford {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isNonClifford = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => rfl
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv, List.countP_cons, Gate.isNonClifford]

theorem cphase_clifford {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP (fun g => !g.isNonClifford) = 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => rfl
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv, Gate.isNonClifford]

theorem cphase_toffoli {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isCcz = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => rfl
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv, Gate.isCcz]

theorem cphase_hadamard {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP (fun g => g.kind == Circuit.GateKind.h) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => rfl
  | succ k =>
      have heq : 2 + (k + 1) + 1 = k + 4 := by omega
      simp only [Circuit.cphase]
      rw [heq]
      simp [Circuit.phase, Circuit.phaseInv, Gate.kind]

theorem phaseRows_length (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).length = 5 * rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.length_append,
        cphase_length (by omega), ih]
      simp
      omega

theorem phaseRows_cnot (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isTwoQubit =
      2 * rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_cnot (by omega), ih]
      simp
      omega

theorem phaseRows_t_of_pos (rest : List Nat) (start q : Nat) (hstart : 0 < start) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isT = 0 := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_t_of_three (by omega), ih (start + 1) (by omega)]

theorem phaseRows_t (rest : List Nat) (q : Nat) :
    (rest.zipIdx.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isT =
      if rest.isEmpty then 0 else 3 := by
  cases rest with
  | nil => rfl
  | cons r rest =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_t_two, phaseRows_t_of_pos rest 1 q (by omega)]
      simp

theorem phaseRows_phase_of_pos (rest : List Nat) (start q : Nat)
    (hstart : 0 < start) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isPhase =
      3 * rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_phase_of_three (by omega), ih (start + 1) (by omega)]
      simp
      omega

theorem phaseRows_phase (rest : List Nat) (q : Nat) :
    (rest.zipIdx.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isPhase =
      3 * (rest.length - 1) := by
  cases rest with
  | nil => rfl
  | cons r rest =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_phase_two, phaseRows_phase_of_pos rest 1 q (by omega)]
      simp

theorem phaseRows_nonClifford (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isNonClifford =
      3 * rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_nonClifford (by omega), ih]
      simp
      omega

theorem phaseRows_clifford (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP
        (fun g => !g.isNonClifford) = 2 * rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_clifford (by omega), ih]
      simp
      omega

theorem phaseRows_toffoli (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP Gate.isCcz = 0 := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_toffoli (by omega), ih]

theorem phaseRows_hadamard (rest : List Nat) (start q : Nat) :
    (rest.zipIdx start |>.flatMap fun ri =>
      Circuit.cphase (ri.2 + 2) ri.1 q).countP
        (fun g => g.kind == Circuit.GateKind.h) = 0 := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append,
        cphase_hadamard (by omega), ih]

theorem qftNoSwap_length (wires : List Nat) :
    (Circuit.qftNoSwap wires).length =
      wires.length + 5 * triangle wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).length = _
      simp only [List.length_append, List.length_cons]
      rw [phaseRows_length rest 0 q, ih]
      simp [triangle]
      omega

theorem qftNoSwap_cnot (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP Gate.isTwoQubit =
      2 * triangle wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).countP
          Gate.isTwoQubit = _
      simp only [List.countP_append, List.countP_cons, Gate.isTwoQubit, Bool.false_eq_true,
        if_false, Nat.add_zero]
      rw [phaseRows_cnot rest 0 q, ih]
      simp [triangle]
      omega

theorem qftNoSwap_t (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP Gate.isT =
      3 * (wires.length - 1) := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).countP
          Gate.isT = _
      simp only [List.countP_append, List.countP_cons, Gate.isT, Bool.false_eq_true,
        if_false, Nat.add_zero]
      rw [phaseRows_t rest q, ih]
      cases rest <;> simp
      omega

theorem qftNoSwap_phase (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP Gate.isPhase =
      3 * triangle (wires.length - 1) := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).countP
          Gate.isPhase = _
      simp only [List.countP_append, List.countP_cons, Gate.isPhase, Bool.false_eq_true,
        if_false, Nat.add_zero]
      rw [phaseRows_phase rest q, ih]
      cases rest <;> simp [triangle]
      omega

theorem qftNoSwap_nonClifford (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP Gate.isNonClifford =
      3 * triangle wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).countP
          Gate.isNonClifford = _
      simp only [List.countP_append, List.countP_cons, Gate.isNonClifford,
        Bool.false_eq_true, if_false, Nat.add_zero]
      rw [phaseRows_nonClifford rest 0 q, ih]
      simp [triangle]
      omega

theorem qftNoSwap_clifford (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP (fun g => !g.isNonClifford) =
      wires.length * wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (([Gate.h q] ++ (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q)) ++ Circuit.qftNoSwap rest).countP
          (fun g => !g.isNonClifford) = _
      rw [List.countP_append, List.countP_append,
        phaseRows_clifford rest 0 q, ih]
      simp [Gate.isNonClifford]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega

theorem qftNoSwap_toffoli (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP Gate.isCcz = 0 := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).countP
          Gate.isCcz = _
      simp only [List.countP_append, List.countP_cons, Gate.isCcz,
        Bool.false_eq_true, if_false, Nat.add_zero]
      rw [phaseRows_toffoli rest 0 q, ih]

theorem qftNoSwap_hadamard (wires : List Nat) :
    (Circuit.qftNoSwap wires).countP
        (fun g => g.kind == Circuit.GateKind.h) = wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      change (([Gate.h q] ++ (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q)) ++ Circuit.qftNoSwap rest).countP
          (fun g => g.kind == Circuit.GateKind.h) = _
      rw [List.countP_append, List.countP_append,
        phaseRows_hadamard rest 0 q, ih]
      simp [Gate.kind]
      omega

theorem hadamard_mem_qftNoSwap {q : Nat} : ∀ wires : List Nat,
    q ∈ wires → Gate.h q ∈ Circuit.qftNoSwap wires := by
  intro wires
  induction wires with
  | nil => simp
  | cons a rest ih =>
      intro hq
      change Gate.h q ∈ Gate.h a ::
        ((rest.zipIdx.flatMap fun ri => Circuit.cphase (ri.2 + 2) ri.1 a) ++
          Circuit.qftNoSwap rest)
      rcases List.mem_cons.mp hq with h | h
      · subst a
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih h))

theorem qftNoSwap_wellFormedAt {level width : Nat} (wires : List Nat)
    (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup)
    (hl3 : 3 ≤ level) (hlevel : wires.length + 1 ≤ level) :
    (Circuit.qftNoSwap wires).all (Gate.wellFormedAt level width) = true := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      simp only [List.length_cons] at hlevel
      have hq : q < width := hw q (by simp)
      have hrest : ∀ r ∈ rest, r < width := by
        intro r hr
        exact hw r (by simp [hr])
      have hsplit : q ∉ rest ∧ rest.Nodup := by simpa using hnodup
      have hqrest : q ∉ rest := hsplit.1
      have hnrest : rest.Nodup := hsplit.2
      have hphase : (rest.zipIdx.flatMap fun ri =>
          Circuit.cphase (ri.2 + 2) ri.1 q).all
          (Gate.wellFormedAt level width) = true := by
        rw [List.all_flatMap, List.all_eq_true]
        intro ri hri
        rcases ri with ⟨r, i⟩
        have hi : i < rest.length := (List.mem_zipIdx' hri).1
        have hr : r ∈ rest := List.fst_mem_of_mem_zipIdx hri
        have hrq : r ≠ q := by
          intro h
          apply hqrest
          simpa [h] using hr
        exact cphase_wellFormedAt (by omega) (by omega) (hrest r hr) hq hrq
      have htail := ih hrest hnrest (by omega)
      change (Gate.h q :: (rest.zipIdx.flatMap fun ri =>
        Circuit.cphase (ri.2 + 2) ri.1 q) ++ Circuit.qftNoSwap rest).all
          (Gate.wellFormedAt level width) = true
      simp [Gate.wellFormedAt, hq, hl3, hphase, htail]

def qftSwaps (wires : List Nat) : List Gate :=
  (List.range (wires.length / 2)).flatMap fun i =>
    match wires[i]?, wires[wires.length - 1 - i]? with
    | some a, some b => Circuit.swap a b
    | _, _ => []

theorem qftSwaps_wellFormedAt {level width : Nat} (wires : List Nat)
    (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup) :
    (qftSwaps wires).all (Gate.wellFormedAt level width) = true := by
  rw [qftSwaps, List.all_flatMap, List.all_eq_true]
  intro i hi
  have hi' : i < wires.length / 2 := List.mem_range.mp hi
  split
  next a b ha hb =>
    have hia := List.getElem?_eq_some_iff.mp ha
    have hib := List.getElem?_eq_some_iff.mp hb
    rcases hia with ⟨hia, haeq⟩
    rcases hib with ⟨hib, hbeq⟩
    have hwa : a < width := hw a (List.mem_of_getElem? ha)
    have hwb : b < width := hw b (List.mem_of_getElem? hb)
    have hab : a ≠ b := by
      intro h
      have hindex : i = wires.length - 1 - i :=
        hnodup.getElem_inj_iff.mp (by
          calc
            wires[i] = a := haeq
            _ = b := h
            _ = wires[wires.length - 1 - i] := hbeq.symm)
      omega
    simp [Circuit.swap, Gate.wellFormedAt, hwa, hwb, hab, hab.symm]
  next => rfl

theorem qftSwaps_length (wires : List Nat) :
    (qftSwaps wires).length = 3 * (wires.length / 2) := by
  rw [qftSwaps, List.length_flatMap]
  have hmap :
      (List.range (wires.length / 2)).map (fun i =>
        (match wires[i]?, wires[wires.length - 1 - i]? with
        | some a, some b => Circuit.swap a b
        | _, _ => []).length) =
      (List.range (wires.length / 2)).map (fun _ => 3) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < wires.length / 2 := List.mem_range.mp hi
    have hleft : i < wires.length := by omega
    have hright : wires.length - 1 - i < wires.length := by omega
    rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright]
    rfl
  rw [hmap, List.map_const', List.sum_replicate_nat, List.length_range]
  omega

theorem qftSwaps_cnot (wires : List Nat) :
    (qftSwaps wires).countP Gate.isTwoQubit = (qftSwaps wires).length := by
  rw [List.countP_eq_length]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  next => simp at hg

theorem qftSwaps_t (wires : List Nat) :
    (qftSwaps wires).countP Gate.isT = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> simp [Gate.isT]
  next => simp at hg

theorem qftSwaps_phase (wires : List Nat) :
    (qftSwaps wires).countP Gate.isPhase = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> simp [Gate.isPhase]
  next => simp at hg

theorem qftSwaps_nonClifford (wires : List Nat) :
    (qftSwaps wires).countP Gate.isNonClifford = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> simp [Gate.isNonClifford]
  next => simp at hg

theorem qftSwaps_clifford (wires : List Nat) :
    (qftSwaps wires).countP (fun g => !g.isNonClifford) =
      (qftSwaps wires).length := by
  rw [List.countP_eq_length]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  next => simp at hg

theorem qftSwaps_toffoli (wires : List Nat) :
    (qftSwaps wires).countP Gate.isCcz = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> simp [Gate.isCcz]
  next => simp at hg

theorem qftSwaps_hadamard (wires : List Nat) :
    (qftSwaps wires).countP (fun g => g.kind == Circuit.GateKind.h) = 0 := by
  rw [List.countP_eq_zero]
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  split at hg
  next a b ha hb =>
    simp [Circuit.swap] at hg
    rcases hg with rfl | rfl | rfl <;> simp [Gate.kind]
  next => simp at hg

theorem qftCircuit_gateCount (n : Nat) :
    Circuit.gateCount (qftCircuit n) =
      n + 5 * triangle n + 3 * (n / 2) := by
  change (Circuit.qft (List.range n).reverse).length = _
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).length = _
  rw [List.length_append, qftNoSwap_length, qftSwaps_length]
  simp

theorem qftCircuit_cnotCount (n : Nat) :
    Circuit.cnotCount (qftCircuit n) =
      2 * triangle n + 3 * (n / 2) := by
  change (Circuit.qft (List.range n).reverse).countP Gate.isTwoQubit = _
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP Gate.isTwoQubit = _
  rw [List.countP_append, qftNoSwap_cnot, qftSwaps_cnot, qftSwaps_length]
  simp

theorem qftCircuit_tCount (n : Nat) :
    Circuit.tCount (qftCircuit n) = 3 * (n - 1) := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP Gate.isT = _
  rw [List.countP_append, qftNoSwap_t, qftSwaps_t]
  simp

theorem qftCircuit_phaseCount (n : Nat) :
    Circuit.phaseCount (qftCircuit n) = 3 * triangle (n - 1) := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP Gate.isPhase = _
  rw [List.countP_append, qftNoSwap_phase, qftSwaps_phase]
  simp

theorem qftCircuit_nonCliffordCount (n : Nat) :
    Circuit.nonCliffordCount (qftCircuit n) = 3 * triangle n := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP Gate.isNonClifford = _
  rw [List.countP_append, qftNoSwap_nonClifford, qftSwaps_nonClifford]
  simp

theorem qftCircuit_cliffordCount (n : Nat) :
    Circuit.cliffordCount (qftCircuit n) = n * n + 3 * (n / 2) := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP (fun g => !g.isNonClifford) = _
  rw [List.countP_append, qftNoSwap_clifford, qftSwaps_clifford,
    qftSwaps_length]
  simp

theorem qftCircuit_toffoliCount (n : Nat) :
    Circuit.toffoliCount (qftCircuit n) = 0 := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP Gate.isCcz = _
  rw [List.countP_append, qftNoSwap_toffoli, qftSwaps_toffoli]

theorem qftCircuit_hadamardCount (n : Nat) :
    Circuit.countKind Circuit.GateKind.h (qftCircuit n) = n := by
  change (Circuit.qftNoSwap (List.range n).reverse ++
    qftSwaps (List.range n).reverse).countP
      (fun g => g.kind == Circuit.GateKind.h) = _
  rw [List.countP_append, qftNoSwap_hadamard, qftSwaps_hadamard]
  simp

theorem qftCircuit_depth_le (n : Nat) :
    (qftCircuit n).depth ≤
      n + 5 * triangle n + 3 * (n / 2) := by
  rw [Circuit.depth_eq_depthOf]
  calc
    Circuit.depthOf (fun _ => true) (qftCircuit n) ≤
        (qftCircuit n).gates.countP (fun _ => true) :=
      Circuit.depthOf_le_countP _ _
    _ = (qftCircuit n).gateCount := by
      simp [Circuit.gateCount]
    _ = n + 5 * triangle n + 3 * (n / 2) :=
      qftCircuit_gateCount n

theorem qftCircuit_tDepth_le (n : Nat) :
    (qftCircuit n).tDepth ≤ 3 * (n - 1) := by
  calc
    (qftCircuit n).tDepth ≤ (qftCircuit n).tCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * (n - 1) := qftCircuit_tCount n

theorem qftCircuit_nonCliffordDepth_le (n : Nat) :
    (qftCircuit n).nonCliffordDepth ≤ 3 * triangle n := by
  calc
    (qftCircuit n).nonCliffordDepth ≤
        (qftCircuit n).nonCliffordCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * triangle n := qftCircuit_nonCliffordCount n

theorem qftCircuit_wellFormedAt {n level : Nat} (hl : qftLevel n ≤ level) :
    (qftCircuit n).wellFormedAt level = true := by
  cases n with
  | zero => rfl
  | succ n =>
      have hl3 : 3 ≤ level := by
        simp [qftLevel] at hl
        omega
      have hlevel : (List.range (n + 1)).reverse.length + 1 ≤ level := by
        simp [qftLevel] at hl ⊢
        omega
      have hw : ∀ q ∈ (List.range (n + 1)).reverse, q < n + 1 := by
        simp
      have hnodup : (List.range (n + 1)).reverse.Nodup := by
        exact List.nodup_reverse.mpr List.nodup_range
      have hnoSwap := qftNoSwap_wellFormedAt
        (level := level) (width := n + 1) (List.range (n + 1)).reverse
        hw hnodup hl3 hlevel
      have hswaps := qftSwaps_wellFormedAt
        (level := level) (width := n + 1) (List.range (n + 1)).reverse
        hw hnodup
      change (Circuit.qftNoSwap (List.range (n + 1)).reverse ++
          qftSwaps (List.range (n + 1)).reverse).all
        (Gate.wellFormedAt level (n + 1)) = true
      simp [List.all_append, hnoSwap, hswaps]

theorem qftCircuit_usedWires (n : Nat) :
    Circuit.usedWires (qftCircuit n) = n := by
  have hwf := qftCircuit_wellFormedAt
    (n := n) (level := qftLevel n) (Nat.le_refl _)
  have hgate : ∀ g ∈ (qftCircuit n).gates, ∀ q ∈ g.wires, q < n := by
    intro g hg q hq
    have hgw : g.wellFormedAt (qftLevel n) n = true :=
      List.all_eq_true.mp hwf g hg
    cases g <;> simp [Gate.wellFormedAt, Gate.wires] at hgw hq <;> omega
  have upper : Circuit.usedWires (qftCircuit n) ≤ n :=
    Circuit.usedWires_le_of_lt hgate
  have hsub : ∀ q ∈ List.range n, q ∈ (qftCircuit n).wiresUsed := by
    intro q hq
    rw [Circuit.wiresUsed, List.mem_eraseDups]
    apply List.mem_flatMap.mpr
    refine ⟨Gate.h q, ?_, by simp [Gate.wires]⟩
    change Gate.h q ∈ Circuit.qftNoSwap (List.range n).reverse ++
      qftSwaps (List.range n).reverse
    exact List.mem_append_left _
      (hadamard_mem_qftNoSwap _ (by simpa using hq))
  have lower : n ≤ Circuit.usedWires (qftCircuit n) := by
    have h := Circuit.eraseDups_length_le n (qftCircuit n).wiresUsed
      (List.range n) upper hsub
    have hrange : ∀ m : Nat, (List.range m).eraseDups = List.range m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          rw [List.range_succ, List.eraseDups_append, ih]
          simp [List.removeAll, List.eraseDups_cons]
    rw [hrange] at h
    simpa [Circuit.usedWires] using h
  exact Nat.le_antisymm upper lower

theorem phase_sq {level k : Nat} (hkl : k + 1 ≤ level) :
    Semantics.phase level (k + 1) * Semantics.phase level (k + 1) =
      Semantics.phase level k := by
  unfold Semantics.phase
  rw [← Dy.pow_add]
  congr 1
  have hs : level - k = (level - (k + 1)) + 1 := by omega
  rw [hs, Nat.pow_succ]
  omega

theorem phase_mul_phaseInv {level k : Nat} (hk : 3 ≤ k) (hkl : k ≤ level) :
    Semantics.phase level k * Semantics.phaseInv level k = Dy.one (deg level) := by
  unfold Semantics.phase Semantics.phaseInv
  rw [← Dy.pow_add]
  have he : 2 ^ (level - k) ≤ 2 ^ level :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le level k)
  rw [Nat.add_sub_of_le he]
  have hd : 2 ^ level = deg level + deg level := by
    show 2 ^ level = 2 ^ (level - 1) + 2 ^ (level - 1)
    have hl : 1 ≤ level := by omega
    have hs : level = (level - 1) + 1 := by omega
    calc
      2 ^ level = 2 ^ ((level - 1) + 1) := congrArg (fun n => 2 ^ n) hs
      _ = 2 ^ (level - 1) * 2 := Nat.pow_succ 2 (level - 1)
      _ = 2 ^ (level - 1) + 2 ^ (level - 1) := by omega
  rw [hd, zeta_pow_two_deg]

theorem run_phase_smul_basis {level width k q j : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) (s : Dy (deg level)) :
    runGates level width (Circuit.phase k q) (s • (basis j : Vec (deg level))) =
      if j.testBit q then
        (s * Semantics.phase level k) • (basis j : Vec (deg level))
      else s • basis j := by
  rw [runGates_smul, run_phase_basis hk hkl hq]
  by_cases hb : j.testBit q = true
  · rw [if_pos hb, if_pos hb, Vec.smul_smul]
  · rw [if_neg hb, if_neg hb]

theorem run_phaseInv_smul_basis {level width k q j : Nat} (hk : 3 ≤ k)
    (hkl : k ≤ level) (hq : q < width) (s : Dy (deg level)) :
    runGates level width (Circuit.phaseInv k q) (s • (basis j : Vec (deg level))) =
      if j.testBit q then
        (s * Semantics.phaseInv level k) • (basis j : Vec (deg level))
      else s • basis j := by
  rw [runGates_smul, run_phaseInv_basis hk hkl hq]
  by_cases hb : j.testBit q = true
  · rw [if_pos hb, if_pos hb, Vec.smul_smul]
  · rw [if_neg hb, if_neg hb]

theorem run_cphase_basis {level width k a b j : Nat} (hk : 2 ≤ k)
    (hkl : k + 1 ≤ level) (ha : a < width) (hb : b < width) (hab : a ≠ b) :
    runGates level width (Circuit.cphase k a b) (basis j : Vec (deg level)) =
      if j.testBit a && j.testBit b then
        Semantics.phase level k • (basis j : Vec (deg level))
      else basis j := by
  simp only [Circuit.cphase, runGates_append]
  rw [run_phase_basis (by omega) hkl ha]
  cases hja : j.testBit a <;> cases hjb : j.testBit b <;>
    simp only [hja, hjb, Bool.and_false, Bool.and_true, if_false, if_true,
      run_phase_smul_basis (by omega) hkl hb,
      run_phase_basis (by omega) hkl hb,
      smul_basis_cx ha hb hab, apply_cx ha hb hab, cxIndex, testBit_xor_self,
      testBit_xor_of_ne hab, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      run_phaseInv_smul_basis (by omega) hkl hb,
      run_phaseInv_basis (by omega) hkl hb,
      runGates_cons, runGates_nil, xor_cancel] <;>
    first
      | rw [phase_sq hkl]
      | rw [phase_mul_phaseInv (by omega) hkl, Vec.one_smul]

theorem qft0_basis :
    run 0 (qftCircuit 0) (basis 0 : Vec (deg 0)) = FourierColumn 0 0 0 := by
  apply eq_of_vecEq (wfVec_run 0 0 [] (wfVec_basis (by omega)))
    (FourierColumn_support 0 0 0)
  decide

theorem qft1_basis {x : Nat} (hx : x < 2) :
    run 3 (qftCircuit 1) (basis x : Vec (deg 3)) = FourierColumn 3 1 x := by
  apply eq_of_vecEq (wfVec_run 3 1 (qftCircuit 1).gates (wfVec_basis hx))
    (FourierColumn_support 3 1 x)
  interval_cases x <;> decide

theorem qft2_basis {x : Nat} (hx : x < 4) :
    run 3 (qftCircuit 2) (basis x : Vec (deg 3)) = FourierColumn 3 2 x := by
  apply eq_of_vecEq (wfVec_run 3 2 (qftCircuit 2).gates (wfVec_basis hx))
    (FourierColumn_support 3 2 x)
  interval_cases x <;> decide

theorem qft3_basis {x : Nat} (hx : x < 8) :
    run 4 (qftCircuit 3) (basis x : Vec (deg 4)) = FourierColumn 4 3 x := by
  apply eq_of_vecEq (wfVec_run 4 3 (qftCircuit 3).gates (wfVec_basis hx))
    (FourierColumn_support 4 3 x)
  interval_cases x <;> decide

example :
    runGates 4 2 (Circuit.cphase 3 0 1) (basis 3 : Vec (deg 4)) =
      Semantics.phase 4 3 • (basis 3 : Vec (deg 4)) :=
  run_cphase_basis (by omega) (by omega) (by omega) (by omega) (by omega)

example :
    runGates 4 2 (Circuit.cphase 3 0 1) (basis 2 : Vec (deg 4)) =
      (basis 2 : Vec (deg 4)) := by
  simpa using
    (run_cphase_basis (level := 4) (width := 2) (k := 3) (a := 0) (b := 1) (j := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega))

/-- info: 'VQ.Tests.QFT.run_cphase_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_cphase_basis

/-- info: 'VQ.Tests.QFT.qftCircuit_wellFormedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_wellFormedAt

/-- info: 'VQ.Tests.QFT.qft3_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qft3_basis

/-- info: 'VQ.Tests.QFT.qftCircuit_gateCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_gateCount

/-- info: 'VQ.Tests.QFT.qftCircuit_cnotCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_cnotCount

/-- info: 'VQ.Tests.QFT.qftCircuit_tCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_tCount

/-- info: 'VQ.Tests.QFT.qftCircuit_phaseCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_phaseCount

/-- info: 'VQ.Tests.QFT.qftCircuit_nonCliffordCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_nonCliffordCount

/-- info: 'VQ.Tests.QFT.qftCircuit_cliffordCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_cliffordCount

/-- info: 'VQ.Tests.QFT.qftCircuit_toffoliCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_toffoliCount

/-- info: 'VQ.Tests.QFT.qftCircuit_hadamardCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_hadamardCount

/-- info: 'VQ.Tests.QFT.qftCircuit_usedWires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_usedWires

/-- info: 'VQ.Tests.QFT.qftCircuit_depth_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_depth_le

/-- info: 'VQ.Tests.QFT.qftCircuit_tDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_tDepth_le

/-- info: 'VQ.Tests.QFT.qftCircuit_nonCliffordDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qftCircuit_nonCliffordDepth_le

end QFT
end Tests
end VQ
