import VQBridge.Palomar833.BranchAmplitudes
import VQBridge.Palomar833.Support

namespace Palomar833

theorem workspace_clean
    {pointQ d level input storage : Nat} {history : List Bool}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {b : Branch}
    (hb : b ∈ runOps (algorithm pointQ).ops
      ⟨history, storage, input, basisState 0, 0⟩)
    {j : Nat} (hj : 2 ^ 256 ≤ j % 2 ^ 259 ∨ 2 ^ 515 ≤ j) :
    b.state j = 0 := by
  rw [(branch_amplitudes hlevel hpoint hdpos hd hQ hb).2 j,
    Connection.fourierState_support d (outcome b) hj, mul_zero]

end Palomar833
