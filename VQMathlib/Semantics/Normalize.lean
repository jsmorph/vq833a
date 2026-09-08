/-
The outcome probabilities of a well-formed circuit sum to one.

`VQ/Semantics/Probability.lean` defines each probability as the squared modulus
of an amplitude.  The normalization theorem proves that these values form a
distribution for a well-formed circuit.

The proof uses Mathlib outside the Mathlib-free `VQ` library.
`unitary_denote` gives `Mᴴ M = 1` over ℂ, whose diagonal
entry at column `j` is `Σᵢ ‖M i j‖²`.  The embedding `dtoC` carries `dsum` to
`Finset.sum` and `absSq` to `star z * z`, and it is injective at every degree the
semantics uses, so the identity transfers back to the amplitude ring.

`deg` is an `abbrev` for `2 ^ (level - 1)`, so `dtoC_injective (level - 1)`
applies to `Dy (deg level)` with no cast.

The theorem states normalization for `VQ` objects while its proof remains in
the Mathlib bridge, matching the placement of `unitary_iff_wellFormedAt`.
-/
import VQMathlib.Semantics.Unitary
import VQ.Semantics.Probability

namespace VQBridge

open VQ VQ.Algebra VQ.Semantics
open scoped Matrix

/-- A probability is the squared modulus of the matrix entry it comes from. -/
theorem dtoC_probAt (level : Nat) (c : Circuit) (inp out : Nat) :
    dtoC (probAt level c inp out)
      = star (dtoC (run level c (basis inp) out)) * dtoC (run level c (basis inp) out) := by
  rw [probAt, absSq, dtoC_mul (deg_pos level), dtoC_conj (deg_pos level), mul_comm]

/-- The matrix entry, spelled as the semantics spells it. -/
theorem cmat_apply (level : Nat) (c : Circuit) (i j : Fin (2 ^ c.width)) :
    cmat level c.width c.gates i j = dtoC (run level c (basis (j : Nat)) (i : Nat)) := rfl

/--
The probabilities of a well-formed circuit's outcomes sum to one.

`inp` names a basis state within the register.  Every probability claim carries
this range condition, which selects a column of the represented unitary.  The
entries in that column therefore have total probability one.
-/
theorem dsum_probAt {level : Nat} {c : Circuit} (h : c.wellFormedAt level = true)
    {inp : Nat} (hi : inp < 2 ^ c.width) :
    dsum (2 ^ c.width) (fun i => probAt level c inp i) = Dy.one (deg level) := by
  refine dtoC_injective (level - 1) ?_
  rw [dtoC_dsum, dtoC_one (deg_pos level)]
  set M := cmat level c.width c.gates with hM
  set j : Fin (2 ^ c.width) := ⟨inp, hi⟩ with hj
  have h1 : (Mᴴ * M) j j = (1 : Matrix (Fin (2 ^ c.width)) (Fin (2 ^ c.width)) ℂ) j j := by
    rw [hM, unitary_denote h]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [← Fin.sum_univ_eq_sum_range, ← h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dtoC_probAt, Matrix.conjTranspose_apply]
  rfl

end VQBridge
