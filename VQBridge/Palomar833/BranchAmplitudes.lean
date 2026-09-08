import VQBridge.Palomar833.Fourier
import VQBridge.Palomar833.Fields

namespace Palomar833

open VQ.Algebra VQ.Semantics VQBridge
open VQ.Tests.PackedAffineECDLP
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition
open Connection

theorem branch_amplitudes
    {pointQ d level input storage : Nat} {history : List Bool}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {b : Palomar833.Branch}
    (hb : b ∈ Palomar833.runOps (algorithm pointQ).ops
      ⟨history, storage, input, basisState 0, 0⟩) :
    b.input = input ∧ ∀ j,
      b.state j = ((1 / (Real.sqrt 2 : ℂ)) ^ (512 * 512)) *
        fourierState d (outcome b) j := by
  have hpoint' := (validPoint_eq pointQ).mp hpoint
  have hQ' : ScalarLoop.decodePoint pointQ =
      d • VQ.Tests.Secp256k1Order.decodedGenerator := by
    rw [decodePoint_eq, generator_eq] at hQ
    exact hQ
  have hzero : pointState 0 false = 0 := by
    rw [pointState_coordinates]
    simp only [publicX, publicY, Nat.zero_mod, Nat.zero_div, mul_zero, zero_add]
  have hrel := runOps_preserved (ProgramResources.program pointQ).ops
    (ProgramResources.program_wellFormed hlevel)
    (VQ.Semantics.Branch.mk history storage
      (basis (pointState 0 false) : Vec (deg level)) input) 0
  have hinit : Connection.branch
      (VQ.Semantics.Branch.mk history storage
        (basis (pointState 0 false) : Vec (deg level)) input) 0 =
      (⟨history, storage, input, basisState 0, 0⟩ : Palomar833.Branch) := by
    simp only [Connection.branch, hzero, state_basis]
  rw [hinit] at hrel
  obtain ⟨source, hsource, count, rfl⟩ := source_branch hrel hb
  obtain ⟨first, second, hfirst, hsecond, hfirstBits, hsecondBits, hinput, hstate⟩ :=
    ops_run_scaled_normalizedPairState (by omega)
      (show TwoScalarLoop.scalarWidth ≤ level from by
        simpa only [TwoScalarLoop.scalarWidth] using (show 256 ≤ level by omega))
      hpoint' hdpos hd hQ' history storage hsource
  have hfirst' : (outcome (Connection.branch source count)).1.val = first :=
    outcome_first hfirst hfirstBits
  have hsecond' : (outcome (Connection.branch source count)).2.val = second :=
    outcome_second hsecond hsecondBits
  refine ⟨hinput, fun j => ?_⟩
  change state source.state j = _
  rw [hstate, normalizedPairState_eq_pairListState hpoint' hQ',
    state_smul (deg_pos level), ← hfirst', ← hsecond', pairListState_fourier hlevel]
  have hscale : dtoC (translationAmplitude level ^ (2 * TwoScalarLoop.scalarWidth)) =
      (1 / (Real.sqrt 2 : ℂ)) ^ (512 * 512) := by
    rw [dtoC_pow (deg_pos level), translationAmplitude, dtoC_pow (deg_pos level),
      dtoC_inverse_sqrt_two (by omega), ← pow_mul]
    rfl
  exact congrArg (fun z : ℂ => z * fourierState d
    (outcome (Connection.branch source count)) j) hscale

end Palomar833
