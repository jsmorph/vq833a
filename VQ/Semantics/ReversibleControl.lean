/-
Amplitude semantics for coherently controlled reversible circuits.
-/
import VQ.Reversible.Control
import VQ.Program.Realise

namespace VQ
namespace Reversible

open VQ.Algebra

/-- The amplitude semantics has the same two arms with phase one.  Applied to
each term of a superposition, linearity preserves every relative amplitude
between the clear-control and set-control sectors.  The control is never read
through a classical branch. -/
theorem run_control_basis {level : Nat} (hl : 3 ≤ level) {r : RCircuit}
    (hr : r.wellFormed = true) {i : Nat} (hs : i.testBit (r.width + 1) = false) :
    Semantics.run level (compile (control r)) (Semantics.basis i) =
      Semantics.basis (if i.testBit r.width then act r i else i) := by
  rw [run_compile_basis hl (control_wellFormed hr), act_control hr hs]

/-- Coherent control acts termwise on every finite superposition supported on a
clear decomposition wire.  The same unitary gate list processes the clear and
set control sectors, so their relative amplitudes remain unchanged. -/
theorem run_control_superpose {level : Nat} (hl : 3 ≤ level) {r : RCircuit}
    (hr : r.wellFormed = true) (L : List Nat) (a : Nat → Dy (Semantics.deg level))
    (hs : ∀ i ∈ L, i.testBit (r.width + 1) = false) :
    Semantics.run level (compile (control r)) (Semantics.superpose id a L) =
      Semantics.superpose (fun i => if i.testBit r.width then act r i else i) a L := by
  induction L with
  | nil => simp [Semantics.superpose, Semantics.run_zero]
  | cons i L ih =>
      simp only [Semantics.superpose, id_eq]
      rw [Semantics.run_add, Semantics.run_smul,
        run_control_basis hl hr (hs i (List.mem_cons_self ..)),
        ih (fun j hj => hs j (List.mem_cons_of_mem i hj))]

end Reversible
end VQ
