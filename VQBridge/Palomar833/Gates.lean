import VQBridge.Palomar833.Translation
import VQMathlib.Semantics.Gate

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics VQBridge

noncomputable def state {d : Nat} (u : Vec d) : State := fun j => dtoC (u j)

theorem state_basis (level j : Nat) :
    state (basis j : Vec (deg level)) = basisState j := by
  funext i
  exact dtoC_basis (deg_pos level) j i

theorem state_projection {d : Nat} (a : Nat) (b : Bool) (u : Vec d) :
    state (projVec a b u) = projection a b (state u) := by
  funext j
  simp only [state, projVec, projection]
  split <;> simp_all [dtoC_zero]

theorem state_flip {d : Nat} (a : Nat) (u : Vec d) :
    state (flipVec a u) = Palomar833.gateAction (.x a) (state u) := rfl

theorem state_gate {level width : Nat} (g : VQ.Gate)
    (hg : g.wellFormedAt level width = true) (u : Vec (deg level)) :
    state (gateVec level width g u) = Palomar833.gateAction (gate g) (state u) := by
  rw [gateVec_of_wf hg]
  have hpos := deg_pos level
  have hsqrt (hl : 3 ≤ level) :
      dtoC (Dy.invSqrt2 (deg level)) = 1 / (Real.sqrt 2 : ℂ) := by
    rw [deg_eq_four_mul hl]
    exact dtoC_invSqrt2 (Nat.two_pow_pos _)
  funext j
  cases g with
  | x a => rfl
  | h a =>
      have hl : 3 ≤ level := (gate_valid (.h a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, hVec, dtoC_mul hpos, hsqrt hl,
        gate, Palomar833.gateAction, flipIndex]
      split <;> simp [dtoC_add, dtoC_sub, div_eq_mul_inv, mul_comm]
  | y a =>
      have hl : 2 ≤ level := (gate_valid (.y a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, yVec, dtoC_mul hpos,
        gate, Palomar833.gateAction, flipIndex]
      split <;> simp [dtoC_neg, (dtoC_phase (by omega) hl).trans phaseC_two]
  | z a =>
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos, dtoC_neg, dtoC_one hpos]
  | s a =>
      have hl : 2 ≤ level := (gate_valid (.s a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos, (dtoC_phase (by omega) hl).trans phaseC_two]
  | sdg a =>
      have hl : 2 ≤ level := (gate_valid (.sdg a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos,
        (dtoC_phaseInv (by omega) hl).trans phaseC_two_inv]
  | t a =>
      have hl : 3 ≤ level := (gate_valid (.t a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos, (dtoC_phase (by omega) hl).trans phaseC_three]
  | tdg a =>
      have hl : 3 ≤ level := (gate_valid (.tdg a) level width).mpr hg |>.2
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos,
        (dtoC_phaseInv (by omega) hl).trans phaseC_three_inv, neg_div]
  | p k a =>
      have hk := (gate_valid (.p k a) level width).mpr hg
      simp only [gate, gateValid] at hk
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos, dtoC_phase (by omega) hk.2.2]
  | pdg k a =>
      have hk := (gate_valid (.pdg k a) level width).mpr hg
      simp only [gate, gateValid] at hk
      simp only [state, VQ.Semantics.gateAction, diagVec, gate,
        Palomar833.gateAction, diagonal]
      split <;> simp [dtoC_mul hpos, dtoC_phaseInv (by omega) hk.2.2]
  | cx a b =>
      simp only [state, VQ.Semantics.gateAction, cxVec, cxIndex, gate,
        Palomar833.gateAction, flipIndex]
      split <;> rfl
  | ccz a b c =>
      simp only [state, VQ.Semantics.gateAction, cczVec, gate, Palomar833.gateAction]
      split <;> simp [dtoC_neg]

end Palomar833.Connection
