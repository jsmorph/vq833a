/-
Compilation preserves the classical basis-index action.

`act` maps basis indices, while `run` maps quantum states.
`run_compile_basis` connects them: at level three or above, a well-formed
reversible circuit compiled into the primitive set sends `|j⟩` to
`|act r j⟩` with unit amplitude.

The proof reduces to the compiled action of each gate.  `x` and `cx` are single
primitives whose basis action is proven in `VQ.Semantics.Gate`.  `ccx` compiles to `h c; ccz a b c; h c`
and needs the conjugation identity below, which is `h z h = x` restricted to the
two indices that differ in wire `c` and applied only when wires `a` and `b` are
both set.  Its pointwise form on an arbitrary state names the two-dimensional
subspace directly and avoids carrying the identity through a sum.  It needs
`2 * (1/√2)² = 1`, which is
where `3 ≤ level` enters: `1 / √2` lies in the amplitude ring exactly when four
divides its degree.

The matrix theorem uses `MatEq` on the `2 ^ width` block.  `denote` is defined
at every index and repeats its block on higher cosets of the index space, so it
does not satisfy `WFMat (2 ^ w) (2 ^ w)`.  The preceding state theorem applies
without that matrix-shape condition.
-/
import VQ.Reversible.Compile
import VQ.Semantics.Expand
import VQ.Algebra.GrindRing

namespace VQ
namespace Reversible

open VQ.Semantics VQ.Algebra

/-! ## Hadamard amplitudes

`Dy.invSqrt2 d` is `√2 / 2`, and `Dy.sqrt2` lies in the ring when four divides
the degree.  Squaring it and doubling gives one, which is the only fact about
the Hadamard's amplitude the conjugation identity uses. -/

theorem two_invSqrt2_sq {d e : Nat} (he : 4 * e = d) :
    Dy.invSqrt2 d * Dy.invSqrt2 d + Dy.invSqrt2 d * Dy.invSqrt2 d = 1 := by
  have h1 : Dy.half (Dy.sqrt2 d) * Dy.invSqrt2 d = Dy.half (Dy.one d) := by
    rw [Dy.half_mul, Dy.mul_comm, Dy.invSqrt2_mul_sqrt2 he]
  have h2 : Dy.invSqrt2 d * Dy.invSqrt2 d = Dy.half (Dy.one d) := h1
  rw [h2]
  exact Dy.half_add_half (Dy.one d)

/-! ## The Toffoli as a conjugated CCZ -/

/--
`h c; ccz a b c; h c` is the Toffoli, on an arbitrary state.

Read at one index, the identity is two-dimensional.  Wires `a` and `b` are
untouched by the Hadamards, so the pair of indices `i` and `i ^^^ (1 <<< c)`
carries the whole computation: when either control is clear the `ccz` is the
identity on both of them and the two Hadamards cancel, and when both are set the
`ccz` is a `z` on wire `c` and `h z h` is `x`.
-/
theorem hVec_cczVec_hVec {d e : Nat} (he : 4 * e = d) {a b c : Nat}
    (hac : a ≠ c) (hbc : b ≠ c) (u : Vec d) :
    hVec c (cczVec a b c (hVec c u))
      = fun i => u (if i.testBit a && i.testBit b then i ^^^ (1 <<< c) else i) := by
  have hs := two_invSqrt2_sq he
  refine Vec.ext (fun i => ?_)
  have hcancel : (i ^^^ (1 <<< c)) ^^^ (1 <<< c) = i := xor_cancel i c
  have hta : (i ^^^ (1 <<< c)).testBit a = i.testBit a := testBit_xor_of_ne hac i
  have htb : (i ^^^ (1 <<< c)).testBit b = i.testBit b := testBit_xor_of_ne hbc i
  have htc : (i ^^^ (1 <<< c)).testBit c = !i.testBit c := testBit_xor_self i c
  cases hA : i.testBit a <;> cases hB : i.testBit b <;> cases hC : i.testBit c <;>
    simp only [hVec, cczVec, hcancel, hta, htb, htc, hA, hB, hC, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
    grind

/-- A state permuted by an involution of the indices sends a basis state to a
basis state.  `cxVec_basis` is this at one permutation.  Every clause of
`RGate.act` is an involution when its gate is well formed. -/
theorem basis_comp_involutive {d : Nat} {f : Nat → Nat} (hf : ∀ i, f (f i) = i) (j : Nat) :
    (fun i => (basis j : Vec d) (f i)) = (basis (f j) : Vec d) := by
  refine Vec.ext (fun i => ?_)
  by_cases h : i = f j
  · subst h
    rw [hf, basis_self, basis_self]
  · rw [basis_of_ne (fun he => h (by rw [← he, hf])), basis_of_ne h]

/-! ## Gate and gate-list semantics -/

variable {level : Nat}

/-- The compilation of one well-formed reversible gate sends `|j⟩` to
`|g.act j⟩`. -/
theorem runGates_compileGate (hl : 3 ≤ level) {w : Nat} {g : RGate}
    (hg : g.wellFormed w = true) (j : Nat) :
    runGates level w (compileGate g) (basis j : Vec (deg level)) = basis (g.act j) := by
  cases g with
  | x q =>
    have hq : q < w := by simpa [RGate.wellFormed] using hg
    show gateVec level w (Gate.x q) (basis j) = _
    rw [apply_x hq j]
    rfl
  | cx a b =>
    have hab : a < w ∧ b < w ∧ a ≠ b := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1, hg.1.2, hg.2⟩
    show gateVec level w (Gate.cx a b) (basis j) = _
    rw [apply_cx hab.1 hab.2.1 hab.2.2 j]
    rfl
  | ccx a b c =>
    have hg0 := hg
    simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := hg
    have hh : (Gate.h c).wellFormedAt level w = true := by
      simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hz : (Gate.ccz a b c).wellFormedAt level w = true := by
      simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq]
      omega
    show gateVec level w (Gate.h c)
      (gateVec level w (Gate.ccz a b c) (gateVec level w (Gate.h c) (basis j))) = _
    rw [gateVec_of_wf hh, gateVec_of_wf hz, gateVec_of_wf hh]
    show hVec c (cczVec a b c (hVec c (basis j))) = _
    rw [hVec_cczVec_hVec (deg_eq_four_mul hl).symm hac hbc (basis j)]
    exact basis_comp_involutive (fun i => RGate.act_act hg0 i) j

/-- The compilation of a well-formed gate list sends `|j⟩` to `|actGates gs j⟩`.
The hypothesis is quantified inside the statement so that the induction on the
list carries it rather than the tactic having to generalise it. -/
theorem runGates_compile (hl : 3 ≤ level) {w : Nat} (gs : List RGate) :
    ∀ (j : Nat), (∀ g ∈ gs, g.wellFormed w = true) →
      runGates level w (gs.flatMap compileGate) (basis j : Vec (deg level))
        = basis (actGates gs j) := by
  induction gs with
  | nil => intro _ _; rfl
  | cons g gs ih =>
    intro j hgs
    rw [List.flatMap_cons, runGates_append,
      runGates_compileGate hl (hgs g List.mem_cons_self) j, actGates_cons]
    exact ih (g.act j) (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))

/--
At level three or above, the compilation of a
well-formed reversible circuit run on `|j⟩` is `|act r j⟩`.

`j` may be any basis index.  Every gate acts on wires below the width,
so the circuit permutes each coset of the index space the same way it permutes
the block, and the identity holds on every coset.  The matrix theorem below uses
the width-bounded block because `denote` repeats on higher cosets.
-/
theorem run_compile_basis (hl : 3 ≤ level) {r : RCircuit} (h : r.wellFormed = true) (j : Nat) :
    run level (compile r) (basis j : Vec (deg level)) = basis (act r j) :=
  runGates_compile hl r.gates j (fun _ hg => RCircuit.wellFormed_mem h hg)

/-! ## Compiled permutation matrix -/

/-- The matrix of a permutation of basis indices: a one in row `f j` of column
`j` and zeros elsewhere.  Column `j` is `basis (f j)`, by definition. -/
def permMat (d : Nat) (f : Nat → Nat) : Mat d :=
  fun i j => if i = f j then Dy.one d else Dy.zero d

theorem permMat_column (d : Nat) (f : Nat → Nat) (j : Nat) :
    (fun i => permMat d f i j) = (basis (f j) : Vec d) := rfl

/--
The compilation of a well-formed reversible circuit
denotes the permutation matrix of `act r`, as an equality of matrices at every
index.

Every other statement about a circuit's matrix in this library is a `MatEq` on
the block, because `denote` repeats its block on higher cosets of the index
space and `eq_of_matEq` requires `WFMat (2 ^ w) (2 ^ w)`.
`run_compile_basis` holds at every `j` without a range hypothesis, and
`permMat (act r)` repeats on the higher cosets in exactly the same way, because
a gate acting on a wire below the width permutes each coset as it permutes the
block.  Thus this theorem states matrix equality, while
`denote_append_mul` retains a block statement for its bounded matrix product.

`width_compile` says the block the width addresses is the reversible circuit's
own register.
-/
theorem denote_compile_eq (hl : 3 ≤ level) {r : RCircuit} (h : r.wellFormed = true) :
    denote level (compile r) = permMat (deg level) (act r) :=
  funext fun i => funext fun j => congrFun (run_compile_basis hl h j) i

/-- The block form, for chaining with the results that are stated that way. -/
theorem denote_compile (hl : 3 ≤ level) {r : RCircuit} (h : r.wellFormed = true) :
    MatEq (2 ^ r.width) (2 ^ r.width) (denote level (compile r))
      (permMat (deg level) (act r)) :=
  fun i _ j _ => congrFun (congrFun (denote_compile_eq hl h) i) j

end Reversible
end VQ
