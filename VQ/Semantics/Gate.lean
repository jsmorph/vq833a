/-
The action of one primitive gate on a state.

The semantics implements gate action through basis-index arithmetic.  Wire `q`
is bit `q` of the basis index, so a one-wire gate reads and writes the pair of
indices that differ in that bit.  Each gate takes one pass over the state,
matching SQIR's `f_to_vec` layer and avoiding dense matrix multiplication.

An ill-formed gate denotes the zero map.  This convention makes nonzero
denotation imply well-formedness.  A circuit indexing a wire outside its width
therefore cannot satisfy a unitary target.

The phase level uniquely determines the ring degree through `deg`.
-/
import VQ.Semantics.Vec
import VQ.Circuit.Syntax

namespace VQ
namespace Semantics

open Algebra

variable {d : Nat}

/-! ## The amplitude ring at a level -/

/--
The degree of the amplitude ring at a phase level.

`Cyc d` is `ℤ[x]/(x ^ d + 1)`, so `Dy.zeta d` satisfies `ζ ^ d = -1` and has
order `2 * d`.  The gate phases are powers of `exp (2 * pi * I / 2 ^ level)`, so
the root of unity has to have order `2 ^ level`, which forces `2 * d = 2 ^ level`
and hence this definition.  At level three and above `4 ∣ deg level`, which is
enough for the ring to contain `1 / √2` and represent the Hadamard gate
exactly.  Computing the degree from the level fixes the amplitude ring for every
semantic operation.
-/
abbrev deg (level : Nat) : Nat := 2 ^ (level - 1)

/-! ## Index arithmetic

Flipping wire `q` of an index is `^^^ (1 <<< q)`.  These three lemmas are
everything the basis-action proofs need about it. -/

theorem xor_cancel (i q : Nat) : (i ^^^ (1 <<< q)) ^^^ (1 <<< q) = i := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_xor_self (i q : Nat) : (i ^^^ (1 <<< q)).testBit q = !i.testBit q := by
  rw [Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true]

theorem testBit_xor_of_ne {q r : Nat} (h : r ≠ q) (i : Nat) :
    (i ^^^ (1 <<< q)).testBit r = i.testBit r := by
  rw [Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm h), Bool.xor_false]

/-- Flipping wire `q` in the index equals flipping the same wire in the basis
label.  One-wire gates therefore permute basis states and attach amplitudes. -/
theorem basis_xor_apply (q j i : Nat) :
    (basis j : Vec d) (i ^^^ (1 <<< q)) = (basis (j ^^^ (1 <<< q)) : Vec d) i := by
  by_cases h : i = j ^^^ (1 <<< q)
  · subst h
    rw [xor_cancel, basis_self, basis_self]
  · rw [basis_of_ne (fun he => h (by rw [← he, xor_cancel])), basis_of_ne h]

/-- The index a CNOT sends `i` to: flip wire `tgt` when wire `ctrl` is set. -/
def cxIndex (ctrl tgt i : Nat) : Nat :=
  if i.testBit ctrl then i ^^^ (1 <<< tgt) else i

theorem cxIndex_involutive {a b : Nat} (hab : a ≠ b) (i : Nat) :
    cxIndex a b (cxIndex a b i) = i := by
  by_cases h : i.testBit a = true
  · have h1 : cxIndex a b i = i ^^^ (1 <<< b) := if_pos h
    rw [h1, cxIndex, testBit_xor_of_ne hab i, if_pos h, xor_cancel]
  · have h1 : cxIndex a b i = i := if_neg h
    rw [h1, h1]

/-! ## Primitive gate actions -/

/-- Flip wire `q`: the action of `x`. -/
def flipVec (q : Nat) (u : Vec d) : Vec d := fun i => u (i ^^^ (1 <<< q))

/-- Multiply by `a` at every index whose wire `q` is set: the action of every
diagonal gate. -/
def diagVec (q : Nat) (a : Dy d) (u : Vec d) : Vec d :=
  fun i => if i.testBit q then a * u i else u i

/-- The action of `y`, whose matrix is `[[0, -a], [a, 0]]` with `a` the fourth
root of unity. -/
def yVec (q : Nat) (a : Dy d) (u : Vec d) : Vec d :=
  fun i => (if i.testBit q then a else -a) * u (i ^^^ (1 <<< q))

/-- The action of `h`.  Row `i` of the Hadamard on wire `q` reads the two
indices that agree off wire `q`, with a minus sign on the second when wire `q`
of `i` is set. -/
def hVec (q : Nat) (u : Vec d) : Vec d := fun i =>
  Dy.invSqrt2 d * (if i.testBit q then u (i ^^^ (1 <<< q)) - u i else u i + u (i ^^^ (1 <<< q)))

/-- The action of `cx`.  `cxIndex` is an involution, so the row index reads
through the same map the column index writes through. -/
def cxVec (a b : Nat) (u : Vec d) : Vec d := fun i => u (cxIndex a b i)

/-- The action of `ccz`: negate the one index whose three wires are all set.
Diagonal, so it permutes nothing and is symmetric in `a`, `b`, and `c`. -/
def cczVec (a b c : Nat) (u : Vec d) : Vec d :=
  fun i => if i.testBit a && i.testBit b && i.testBit c then -u i else u i

/-! ## Phases

`Dy.zeta (deg level)` is `exp (2 * pi * I / 2 ^ level)`, so the phase
`exp (2 * pi * I / 2 ^ k)` is its `2 ^ (level - k)`-th power and the inverse
phase is the complementary power.  `Gate.wellFormedAt` requires `k ≤ level`,
which keeps the exponent within the selected ring level. -/

/-- The phase `exp (2 * pi * I / 2 ^ k)`. -/
def phase (level k : Nat) : Dy (deg level) := Dy.zeta (deg level) ^ (2 ^ (level - k))

/-- The phase `exp (-2 * pi * I / 2 ^ k)`. -/
def phaseInv (level k : Nat) : Dy (deg level) :=
  Dy.zeta (deg level) ^ (2 ^ level - 2 ^ (level - k))

/-! ## The gate action -/

/-- The action of a gate, before the well-formedness test. -/
def gateAction (level : Nat) : Gate → Vec (deg level) → Vec (deg level)
  | .h q => hVec q
  | .x q => flipVec q
  | .y q => yVec q (phase level 2)
  | .z q => diagVec q (-Dy.one (deg level))
  | .s q => diagVec q (phase level 2)
  | .sdg q => diagVec q (phaseInv level 2)
  | .t q => diagVec q (phase level 3)
  | .tdg q => diagVec q (phaseInv level 3)
  | .p k q => diagVec q (phase level k)
  | .pdg k q => diagVec q (phaseInv level k)
  | .cx a b => cxVec a b
  | .ccz a b c => cczVec a b c

/-- The action of one gate on a state.  A gate outside the declared width, or a
phase gate at a level the amplitude ring cannot carry, denotes the zero map. -/
def gateVec (level w : Nat) (g : Gate) (u : Vec (deg level)) : Vec (deg level) :=
  if g.wellFormedAt level w then gateAction level g u else Vec.zero (deg level)

theorem gateVec_of_wf {level w : Nat} {g : Gate} (h : g.wellFormedAt level w = true)
    (u : Vec (deg level)) : gateVec level w g u = gateAction level g u := if_pos h

theorem gateVec_of_not_wf {level w : Nat} {g : Gate} (h : g.wellFormedAt level w = false)
    (u : Vec (deg level)) : gateVec level w g u = Vec.zero (deg level) :=
  if_neg (by rw [h]; exact Bool.noConfusion)

/-- Every action sends the zero state to itself, so a single ill-formed gate
takes the rest of the circuit with it. -/
theorem gateVec_zero (level w : Nat) (g : Gate) :
    gateVec level w g (Vec.zero (deg level)) = Vec.zero (deg level) := by
  by_cases hw : g.wellFormedAt level w = true
  · rw [gateVec_of_wf hw]
    refine Vec.ext (fun i => ?_)
    cases g with
    | h q =>
      show Dy.invSqrt2 (deg level) * _ = Dy.zero (deg level)
      by_cases hb : i.testBit q = true
      · rw [if_pos hb]
        show Dy.invSqrt2 (deg level) * (Dy.zero (deg level) - Dy.zero (deg level))
            = Dy.zero (deg level)
        rw [sub_zero, Dy.mul_zero]
      · rw [if_neg hb]
        show Dy.invSqrt2 (deg level) * (Dy.zero (deg level) + Dy.zero (deg level))
            = Dy.zero (deg level)
        rw [Dy.add_zero, Dy.mul_zero]
    | x q => rfl
    | cx a b => rfl
    | ccz a b c =>
      show (if _ then -(Vec.zero (deg level) i) else Vec.zero (deg level) i)
          = Dy.zero (deg level)
      rw [Vec.zero_apply, neg_zero, ite_self]
    | y q =>
      show (if i.testBit q then _ else _) * Vec.zero (deg level) _ = Dy.zero (deg level)
      rw [Vec.zero_apply, Dy.mul_zero]
    | z q | s q | sdg q | t q | tdg q | p k q | pdg k q =>
      show (if i.testBit q then _ * Vec.zero (deg level) i else Vec.zero (deg level) i)
          = Dy.zero (deg level)
      by_cases hb : i.testBit q = true
      · rw [if_pos hb, Vec.zero_apply, Dy.mul_zero]
      · rw [if_neg hb, Vec.zero_apply]
  · rw [gateVec_of_not_wf (Bool.eq_false_iff.mpr hw)]

/-! ## Action on a basis state

Each primitive maps `|j⟩` to one weighted basis state.  A Hadamard maps it to
two weighted basis states.  Later semantic proofs use these basis-action
forms. -/

theorem flipVec_basis (q j : Nat) :
    flipVec q (basis j : Vec d) = basis (j ^^^ (1 <<< q)) :=
  Vec.ext (fun i => basis_xor_apply q j i)

theorem cxVec_basis {a b : Nat} (hab : a ≠ b) (j : Nat) :
    cxVec a b (basis j : Vec d) = basis (cxIndex a b j) := by
  refine Vec.ext (fun i => ?_)
  show (basis j : Vec d) (cxIndex a b i) = (basis (cxIndex a b j) : Vec d) i
  by_cases h : i = cxIndex a b j
  · subst h
    rw [cxIndex_involutive hab, basis_self, basis_self]
  · rw [basis_of_ne (fun he => h (by rw [← he, cxIndex_involutive hab])), basis_of_ne h]

theorem diagVec_basis (q : Nat) (a : Dy d) (j : Nat) :
    diagVec q a (basis j : Vec d) = if j.testBit q then a • (basis j : Vec d) else basis j := by
  have key : ∀ i : Nat, diagVec q a (basis j : Vec d) i
      = if j.testBit q then a * (basis j : Vec d) i else (basis j : Vec d) i := by
    intro i
    by_cases hi : i = j
    · subst hi; rfl
    · show (if i.testBit q then a * (basis j : Vec d) i else (basis j : Vec d) i) = _
      rw [basis_of_ne hi, Dy.mul_zero, ite_self, ite_self]
  by_cases hb : j.testBit q = true
  · rw [if_pos hb]
    exact Vec.ext (fun i => by rw [Vec.smul_apply, key i, if_pos hb])
  · rw [if_neg hb]
    exact Vec.ext (fun i => by rw [key i, if_neg hb])

theorem cczVec_basis (a b c j : Nat) :
    cczVec a b c (basis j : Vec d)
      = if j.testBit a && j.testBit b && j.testBit c then (-Dy.one d) • (basis j : Vec d)
        else basis j := by
  have key : ∀ i : Nat, cczVec a b c (basis j : Vec d) i
      = if j.testBit a && j.testBit b && j.testBit c then (-Dy.one d) * (basis j : Vec d) i
        else (basis j : Vec d) i := by
    intro i
    by_cases hi : i = j
    · subst hi
      show (if _ then -(basis i : Vec d) i else (basis i : Vec d) i) = _
      by_cases hb : i.testBit a && i.testBit b && i.testBit c
      · rw [if_pos hb, if_pos hb, neg_eq_neg_one_mul]
      · rw [if_neg hb, if_neg hb]
    · show (if _ then -(basis j : Vec d) i else (basis j : Vec d) i) = _
      rw [basis_of_ne hi, neg_zero, ite_self, Dy.mul_zero, ite_self]
  by_cases hb : j.testBit a && j.testBit b && j.testBit c
  · rw [if_pos hb]
    exact Vec.ext (fun i => by rw [Vec.smul_apply, key i, if_pos hb])
  · rw [if_neg hb]
    exact Vec.ext (fun i => by rw [key i, if_neg hb])

theorem yVec_basis (q : Nat) (a : Dy d) (j : Nat) :
    yVec q a (basis j : Vec d)
      = (if j.testBit q then -a else a) • (basis (j ^^^ (1 <<< q)) : Vec d) := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then a else -a) * (basis j : Vec d) (i ^^^ (1 <<< q))
      = (if j.testBit q then -a else a) * (basis (j ^^^ (1 <<< q)) : Vec d) i
  rw [basis_xor_apply]
  by_cases hi : i = j ^^^ (1 <<< q)
  · subst hi
    rw [testBit_xor_self]
    cases hbq : j.testBit q <;> rfl
  · rw [basis_of_ne hi, Dy.mul_zero, Dy.mul_zero]

theorem hVec_basis_of_false {q j : Nat} (hb : j.testBit q = false) :
    hVec q (basis j : Vec d)
      = Dy.invSqrt2 d • ((basis j : Vec d) + basis (j ^^^ (1 <<< q))) := by
  refine Vec.ext (fun i => ?_)
  have key : (if i.testBit q then (basis j : Vec d) (i ^^^ (1 <<< q)) - (basis j : Vec d) i
        else (basis j : Vec d) i + (basis j : Vec d) (i ^^^ (1 <<< q)))
      = (basis j : Vec d) i + (basis (j ^^^ (1 <<< q)) : Vec d) i := by
    by_cases hi : i.testBit q = true
    · have hij : i ≠ j := fun he => by rw [he, hb] at hi; exact Bool.noConfusion hi
      rw [if_pos hi, basis_of_ne hij, sub_zero, Dy.zero_add, basis_xor_apply]
    · rw [if_neg hi, basis_xor_apply]
  show Dy.invSqrt2 d * _ = Dy.invSqrt2 d * _
  rw [key]
  rfl

theorem hVec_basis_of_true {q j : Nat} (hb : j.testBit q = true) :
    hVec q (basis j : Vec d)
      = Dy.invSqrt2 d • ((basis (j ^^^ (1 <<< q)) : Vec d) - basis j) := by
  refine Vec.ext (fun i => ?_)
  have key : (if i.testBit q then (basis j : Vec d) (i ^^^ (1 <<< q)) - (basis j : Vec d) i
        else (basis j : Vec d) i + (basis j : Vec d) (i ^^^ (1 <<< q)))
      = (basis (j ^^^ (1 <<< q)) : Vec d) i - (basis j : Vec d) i := by
    by_cases hi : i.testBit q = true
    · rw [if_pos hi, basis_xor_apply]
    · have hij : i ≠ j := fun he => by rw [he, hb] at hi; exact hi rfl
      rw [if_neg hi, basis_of_ne hij, Dy.zero_add, sub_zero, basis_xor_apply]
  show Dy.invSqrt2 d * _ = Dy.invSqrt2 d * _
  rw [key]
  rfl

/-! ## Named primitive gates

Each of these is `gateVec` at one constructor with its well-formedness
hypothesis discharged.  Qubit zero is the least significant bit of the index. -/

variable {level w q : Nat}

theorem apply_x (hq : q < w) (j : Nat) :
    gateVec level w (Gate.x q) (basis j : Vec (deg level)) = basis (j ^^^ (1 <<< q)) := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq])]
  exact flipVec_basis q j

theorem apply_cx {a b : Nat} (ha : a < w) (hb : b < w) (hab : a ≠ b) (j : Nat) :
    gateVec level w (Gate.cx a b) (basis j : Vec (deg level))
      = basis (if j.testBit a then j ^^^ (1 <<< b) else j) := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hab])]
  exact cxVec_basis hab j

theorem apply_ccz {a b c : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hl : 1 ≤ level) (j : Nat) :
    gateVec level w (Gate.ccz a b c) (basis j : Vec (deg level))
      = if j.testBit a && j.testBit b && j.testBit c then
          (-Dy.one (deg level)) • (basis j : Vec (deg level))
        else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hc, hab, hbc, hac, hl])]
  exact cczVec_basis a b c j

theorem apply_z (hq : q < w) (hl : 1 ≤ level) (j : Nat) :
    gateVec level w (Gate.z q) (basis j : Vec (deg level))
      = if j.testBit q then (-Dy.one (deg level)) • (basis j : Vec (deg level))
        else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact diagVec_basis q (-Dy.one (deg level)) j

theorem apply_s (hq : q < w) (hl : 2 ≤ level) (j : Nat) :
    gateVec level w (Gate.s q) (basis j : Vec (deg level))
      = if j.testBit q then phase level 2 • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact diagVec_basis q (phase level 2) j

theorem apply_sdg (hq : q < w) (hl : 2 ≤ level) (j : Nat) :
    gateVec level w (Gate.sdg q) (basis j : Vec (deg level))
      = if j.testBit q then phaseInv level 2 • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact diagVec_basis q (phaseInv level 2) j

theorem apply_t (hq : q < w) (hl : 3 ≤ level) (j : Nat) :
    gateVec level w (Gate.t q) (basis j : Vec (deg level))
      = if j.testBit q then phase level 3 • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact diagVec_basis q (phase level 3) j

theorem apply_tdg (hq : q < w) (hl : 3 ≤ level) (j : Nat) :
    gateVec level w (Gate.tdg q) (basis j : Vec (deg level))
      = if j.testBit q then phaseInv level 3 • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact diagVec_basis q (phaseInv level 3) j

theorem apply_p {k : Nat} (hq : q < w) (h4 : 4 ≤ k) (hk : k ≤ level) (j : Nat) :
    gateVec level w (Gate.p k q) (basis j : Vec (deg level))
      = if j.testBit q then phase level k • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, h4, hk])]
  exact diagVec_basis q (phase level k) j

theorem apply_pdg {k : Nat} (hq : q < w) (h4 : 4 ≤ k) (hk : k ≤ level) (j : Nat) :
    gateVec level w (Gate.pdg k q) (basis j : Vec (deg level))
      = if j.testBit q then phaseInv level k • (basis j : Vec (deg level)) else basis j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, h4, hk])]
  exact diagVec_basis q (phaseInv level k) j

theorem apply_y (hq : q < w) (hl : 2 ≤ level) (j : Nat) :
    gateVec level w (Gate.y q) (basis j : Vec (deg level))
      = (if j.testBit q then -phase level 2 else phase level 2)
          • (basis (j ^^^ (1 <<< q)) : Vec (deg level)) := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact yVec_basis q (phase level 2) j

theorem apply_h (hq : q < w) (hl : 3 ≤ level) (j : Nat) :
    gateVec level w (Gate.h q) (basis j : Vec (deg level))
      = if j.testBit q
        then Dy.invSqrt2 (deg level) • ((basis (j ^^^ (1 <<< q)) : Vec (deg level)) - basis j)
        else Dy.invSqrt2 (deg level) • ((basis j : Vec (deg level)) + basis (j ^^^ (1 <<< q))) := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  by_cases hb : j.testBit q = true
  · rw [if_pos hb]; exact hVec_basis_of_true hb
  · rw [if_neg hb]; exact hVec_basis_of_false (Bool.eq_false_iff.mpr hb)

/-- The ill-formed case, stated for the two ways a gate can fail. -/
theorem apply_of_not_wf {g : Gate} (h : g.wellFormedAt level w = false) (u : Vec (deg level)) :
    gateVec level w g u = Vec.zero (deg level) := gateVec_of_not_wf h u

/-! ## Linearity

Every action is additive and commutes with scaling.  These properties extend
the column semantics to a matrix product. -/

theorem flipVec_add (q : Nat) (u v : Vec d) : flipVec q (u + v) = flipVec q u + flipVec q v := rfl

theorem flipVec_smul (q : Nat) (a : Dy d) (u : Vec d) :
    flipVec q (a • u) = a • flipVec q u := rfl

theorem cxVec_add (a b : Nat) (u v : Vec d) : cxVec a b (u + v) = cxVec a b u + cxVec a b v := rfl

theorem cxVec_smul (a b : Nat) (c : Dy d) (u : Vec d) :
    cxVec a b (c • u) = c • cxVec a b u := rfl

theorem cczVec_add (a b c : Nat) (u v : Vec d) :
    cczVec a b c (u + v) = cczVec a b c u + cczVec a b c v := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit a && i.testBit b && i.testBit c then -(u i + v i) else u i + v i)
      = (if i.testBit a && i.testBit b && i.testBit c then -u i else u i)
        + (if i.testBit a && i.testBit b && i.testBit c then -v i else v i)
  by_cases hb : i.testBit a && i.testBit b && i.testBit c
  · rw [if_pos hb, if_pos hb, if_pos hb, neg_add]
  · rw [if_neg hb, if_neg hb, if_neg hb]

theorem cczVec_smul (a b c : Nat) (e : Dy d) (u : Vec d) :
    cczVec a b c (e • u) = e • cczVec a b c u := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit a && i.testBit b && i.testBit c then -(e * u i) else e * u i)
      = e * (if i.testBit a && i.testBit b && i.testBit c then -u i else u i)
  by_cases hb : i.testBit a && i.testBit b && i.testBit c
  · rw [if_pos hb, if_pos hb, Dy.mul_neg]
  · rw [if_neg hb, if_neg hb]

theorem diagVec_add (q : Nat) (a : Dy d) (u v : Vec d) :
    diagVec q a (u + v) = diagVec q a u + diagVec q a v := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then a * (u i + v i) else u i + v i)
      = (if i.testBit q then a * u i else u i) + (if i.testBit q then a * v i else v i)
  by_cases hb : i.testBit q = true
  · rw [if_pos hb, if_pos hb, if_pos hb, Dy.left_distrib]
  · rw [if_neg hb, if_neg hb, if_neg hb]

theorem diagVec_smul (q : Nat) (a c : Dy d) (u : Vec d) :
    diagVec q a (c • u) = c • diagVec q a u := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then a * (c * u i) else c * u i)
      = c * (if i.testBit q then a * u i else u i)
  by_cases hb : i.testBit q = true
  · rw [if_pos hb, if_pos hb, mul_left_comm]
  · rw [if_neg hb, if_neg hb]

theorem yVec_add (q : Nat) (a : Dy d) (u v : Vec d) :
    yVec q a (u + v) = yVec q a u + yVec q a v := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then a else -a) * (u (i ^^^ (1 <<< q)) + v (i ^^^ (1 <<< q))) = _
  rw [Dy.left_distrib]
  rfl

theorem yVec_smul (q : Nat) (a c : Dy d) (u : Vec d) :
    yVec q a (c • u) = c • yVec q a u := by
  refine Vec.ext (fun i => ?_)
  show (if i.testBit q then a else -a) * (c * u (i ^^^ (1 <<< q)))
      = c * ((if i.testBit q then a else -a) * u (i ^^^ (1 <<< q)))
  rw [mul_left_comm]

theorem hVec_add (q : Nat) (u v : Vec d) : hVec q (u + v) = hVec q u + hVec q v := by
  refine Vec.ext (fun i => ?_)
  show Dy.invSqrt2 d * (if i.testBit q
        then (u (i ^^^ (1 <<< q)) + v (i ^^^ (1 <<< q))) - (u i + v i)
        else (u i + v i) + (u (i ^^^ (1 <<< q)) + v (i ^^^ (1 <<< q))))
      = Dy.invSqrt2 d * (if i.testBit q then u (i ^^^ (1 <<< q)) - u i
          else u i + u (i ^^^ (1 <<< q)))
        + Dy.invSqrt2 d * (if i.testBit q then v (i ^^^ (1 <<< q)) - v i
          else v i + v (i ^^^ (1 <<< q)))
  rw [← Dy.left_distrib]
  by_cases hb : i.testBit q = true
  · rw [if_pos hb, if_pos hb, if_pos hb, add_sub_add]
  · rw [if_neg hb, if_neg hb, if_neg hb, add_add_add]

theorem hVec_smul (q : Nat) (c : Dy d) (u : Vec d) : hVec q (c • u) = c • hVec q u := by
  refine Vec.ext (fun i => ?_)
  show Dy.invSqrt2 d * (if i.testBit q then c * u (i ^^^ (1 <<< q)) - c * u i
        else c * u i + c * u (i ^^^ (1 <<< q)))
      = c * (Dy.invSqrt2 d * (if i.testBit q then u (i ^^^ (1 <<< q)) - u i
          else u i + u (i ^^^ (1 <<< q))))
  rw [mul_left_comm]
  by_cases hb : i.testBit q = true
  · rw [if_pos hb, if_pos hb, mul_sub c]
  · rw [if_neg hb, if_neg hb, Dy.left_distrib c]

theorem gateAction_add (level : Nat) (g : Gate) (u v : Vec (deg level)) :
    gateAction level g (u + v) = gateAction level g u + gateAction level g v := by
  cases g with
  | h q => exact hVec_add q u v
  | x q => exact flipVec_add q u v
  | y q => exact yVec_add q (phase level 2) u v
  | z q => exact diagVec_add q (-Dy.one (deg level)) u v
  | s q => exact diagVec_add q (phase level 2) u v
  | sdg q => exact diagVec_add q (phaseInv level 2) u v
  | t q => exact diagVec_add q (phase level 3) u v
  | tdg q => exact diagVec_add q (phaseInv level 3) u v
  | p k q => exact diagVec_add q (phase level k) u v
  | pdg k q => exact diagVec_add q (phaseInv level k) u v
  | cx a b => exact cxVec_add a b u v
  | ccz a b c => exact cczVec_add a b c u v

theorem gateAction_smul (level : Nat) (g : Gate) (c : Dy (deg level)) (u : Vec (deg level)) :
    gateAction level g (c • u) = c • gateAction level g u := by
  cases g with
  | h q => exact hVec_smul q c u
  | x q => exact flipVec_smul q c u
  | y q => exact yVec_smul q (phase level 2) c u
  | z q => exact diagVec_smul q (-Dy.one (deg level)) c u
  | s q => exact diagVec_smul q (phase level 2) c u
  | sdg q => exact diagVec_smul q (phaseInv level 2) c u
  | t q => exact diagVec_smul q (phase level 3) c u
  | tdg q => exact diagVec_smul q (phaseInv level 3) c u
  | p k q => exact diagVec_smul q (phase level k) c u
  | pdg k q => exact diagVec_smul q (phaseInv level k) c u
  | cx a b => exact cxVec_smul a b c u
  | ccz a b e => exact cczVec_smul a b e c u

theorem gateVec_add (level w : Nat) (g : Gate) (u v : Vec (deg level)) :
    gateVec level w g (u + v) = gateVec level w g u + gateVec level w g v := by
  by_cases hw : g.wellFormedAt level w = true
  · rw [gateVec_of_wf hw, gateVec_of_wf hw, gateVec_of_wf hw, gateAction_add]
  · rw [gateVec_of_not_wf (Bool.eq_false_iff.mpr hw),
      gateVec_of_not_wf (Bool.eq_false_iff.mpr hw),
      gateVec_of_not_wf (Bool.eq_false_iff.mpr hw), Vec.zero_add_zero]

theorem gateVec_smul (level w : Nat) (g : Gate) (c : Dy (deg level)) (u : Vec (deg level)) :
    gateVec level w g (c • u) = c • gateVec level w g u := by
  by_cases hw : g.wellFormedAt level w = true
  · rw [gateVec_of_wf hw, gateVec_of_wf hw, gateAction_smul]
  · rw [gateVec_of_not_wf (Bool.eq_false_iff.mpr hw),
      gateVec_of_not_wf (Bool.eq_false_iff.mpr hw), Vec.smul_zero]

/-! ## Support

A state supported on the first `2 ^ w` indices stays there.  Flipping a wire
below `w` changes no bit at or above `w`, so it moves no index across the
boundary. -/

theorem two_pow_le_xor {w q i : Nat} (hq : q < w) (hi : 2 ^ w ≤ i) :
    2 ^ w ≤ i ^^^ (1 <<< q) := by
  refine Nat.le_of_not_lt (fun h => ?_)
  have hpow : (1 <<< q) < 2 ^ w := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_of_lt (by omega) hq
  have hlt := Nat.xor_lt_two_pow h hpow
  rw [xor_cancel] at hlt
  omega

theorem wfVec_gateVec (level w : Nat) (g : Gate) {u : Vec (deg level)} (hu : WFVec (2 ^ w) u) :
    WFVec (2 ^ w) (gateVec level w g u) := by
  by_cases hw : g.wellFormedAt level w = true
  · rw [gateVec_of_wf hw]
    intro i hi
    cases g with
    | x q =>
      have hq : q < w := by simp [Gate.wellFormedAt] at hw; omega
      exact hu _ (two_pow_le_xor hq hi)
    | y q =>
      have hq : q < w := by simp [Gate.wellFormedAt] at hw; omega
      show (if i.testBit q then _ else _) * u (i ^^^ (1 <<< q)) = Dy.zero (deg level)
      rw [hu _ (two_pow_le_xor hq hi), Dy.mul_zero]
    | h q =>
      have hq : q < w := by simp [Gate.wellFormedAt] at hw; omega
      show Dy.invSqrt2 (deg level) * _ = Dy.zero (deg level)
      rw [hu i hi, hu _ (two_pow_le_xor hq hi)]
      by_cases hb : i.testBit q = true
      · rw [if_pos hb, sub_zero, Dy.mul_zero]
      · rw [if_neg hb, Dy.add_zero, Dy.mul_zero]
    | cx a b =>
      have hb : b < w := by
        simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hw
        omega
      refine hu _ ?_
      by_cases hc : i.testBit a = true
      · rw [cxIndex, if_pos hc]
        exact two_pow_le_xor hb hi
      · rw [cxIndex, if_neg hc]
        exact hi
    | ccz p q r =>
      show (if i.testBit p && i.testBit q && i.testBit r then -u i else u i)
          = Dy.zero (deg level)
      rw [hu i hi, neg_zero, ite_self]
    | z q | s q | sdg q | t q | tdg q | p k q | pdg k q =>
      show (if i.testBit q then _ * u i else u i) = Dy.zero (deg level)
      rw [hu i hi]
      by_cases hb : i.testBit q = true
      · rw [if_pos hb, Dy.mul_zero]
      · rw [if_neg hb]
  · rw [gateVec_of_not_wf (Bool.eq_false_iff.mpr hw)]
    exact wfVec_zero (2 ^ w)

end Semantics
end VQ
