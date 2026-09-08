import VQ.Curve.Field
import VQ.Reversible.Place

/-!
# Register geometry

The offsets place every register inside the claim's workspace field and support
one round of the circuit.

## Round controls

Algorithm 7b of Häner, Jaques, Naehrig, Roetteler, and Soeken reduces Kaliski's
four branches to one sequence:

    bswap := (u even and v odd) or (u odd and v odd and u > v)
    if bswap:  swap u v;  swap r s
    if u odd and v odd:  v := v - u;  s := r + s
    v := v / 2
    r := 2 r
    if bswap:  swap u v;  swap r s

Two control bits drive it.  `bswap` is one.  `both`, meaning `u` and `v` are both
odd, is the other, and it is invariant under the swap, so it is computed once.

The round overwrites the values used to compute both controls.  Its output
recovers `bswap`: exactly one of `r` and `s` is even, and the branches with
even `r` are precisely those with `bswap` false.  A CNOT from the new parity of
`r` clears `bswap`.  Roetteler, Naehrig, Svore, and Lauter use the same
property for their encoder's upper bit.  The circuit clears `both` from
`bswap` and the retained branch bit because `both` is their exclusive-nor.
One retained qubit per round remains, for `2 n` qubits in the published circuit.

## Inactive rounds

Once `v` reaches zero, subsequent rounds must preserve the state.  Without a
termination control, the branch for odd `u` and even `v` continues doubling `r`.
Halving zero preserves `v`, so only the two shifts require a control.

The existing comparison computes the control `v ≠ 0`: it loads one into a
scratch register, compares `v < 1`, and negates the result.  An or-ladder over
the bits of `v` would use fewer gates but would require a separate correctness
proof.  The comparison adds two adder passes to a round that already has four.

That bit cannot be cleared at the end of the round, because the round that
drives `v` to zero and a round that found `v` already zero end in the same state
and disagree about it.  It therefore requires a second retained qubit per
round: `4 n` retained qubits instead of the published construction's `2 n`.
The workspace comes to `12 n + 11` wires, about `3083` at `n = 256`, against
roughly `5 n` ancillas for the published inversion, and the whole circuit to
`14 n + 11`.  The last `2 n` are the correction's, one per halving, and one more
records that the input is nonzero.

## Register widths

`r` and `s` reach `2 p`, so they require the `n + 1` bits established by
`VQ.Curve.PointAddition.Arithmetic.Inv.rs_le_p` and `VQ.Curve.PointAddition.Arithmetic.Inv.Wide`.  The published circuit uses this width.
`u` and `v` remain below the modulus but also use `n + 1` bits for the
comparison.

## Comparison register widths

The round needs `v < u`, which is the carry out of a subtraction.  `AddsWrap`
states that the workspace returns to zero, so its theorem supplies no carry bit
after completion.  Widening the operands by one bit puts
that carry inside the sum field instead.  With `u` and `v` below `2 ^ n` in
registers of `n + 1` bits, complementing `u` and adding with a carry-in of one
gives `v - u` modulo `2 ^ (n + 1)`, whose top bit is one exactly when `v < u`.
The comparison applies the adder, copies the top bit, and reverses the adder.
It uses two adder passes and avoids a separate induction over the carry chain.

The Cuccaro adder's Toffolis already use two controls.  A conditional addition
therefore copies its addend into `tu` or `tr` under the extra control and then
adds without that control.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible

/-- The modulus this construction inverts at.

It sits here rather than beside the circuit because the correction names it: the
modulus is a classical constant of the construction, so the correction loads it
rather than copying it out of a register. -/
def modulus : Nat := VQ.Curve.p

/-! ## Field offsets

Absolute wire offsets in the whole circuit, whose layout is the claim's
`unaryLayout n ws = [n, n, ws]`.  The input occupies wires `0` to `n - 1`, the
output `n` to `2 n - 1`, and everything below starts at `2 n`.

`VQ.Reversible.place` takes absolute offsets, while `readField` takes an offset
and a length.  The register definitions therefore use absolute offsets
directly. -/

/-- The width of the six large registers.  `r` and `s` reach `2 p` and `u` and
`v` carry the comparison's overflow bit, so all six get `n + 1`. -/
def bw (n : Nat) : Nat := n + 1

/-- `u`, the Euclidean register that starts at the modulus. -/
def aU (n : Nat) : Nat := 2 * n
/-- `v`, which starts at the value being inverted. -/
def aV (n : Nat) : Nat := aU n + bw n
/-- `r`, which ends holding the almost inverse. -/
def aR (n : Nat) : Nat := aV n + bw n
/-- `s`, which ends at the modulus. -/
def aS (n : Nat) : Nat := aR n + bw n
/-- Scratch for the addend of the conditional subtraction. -/
def aTU (n : Nat) : Nat := aS n + bw n
/-- Scratch for the addend of the conditional addition. -/
def aTR (n : Nat) : Nat := aTU n + bw n
/-- `bswap`, cleared at the end of each round from the parity of `r`. -/
def aA (n : Nat) : Nat := aTR n + bw n
/-- `both`, meaning `u` and `v` are both odd. -/
def aT (n : Nat) : Nat := aA n + 1
/-- The comparison `v < u`, computed and uncomputed inside a round. -/
def aGt (n : Nat) : Nat := aT n + 1
/-- The adder's carry wire. -/
def aC (n : Nat) : Nat := aGt n + 1
/-- One wire recording that the input is nonzero.

At input zero the chain never runs, so `s` never leaves its initial one and the
correction negates against that rather than against the modulus.  The
specification sends zero to zero, so the copy-out is controlled on this wire and
a zero input copies nothing.  This control persists through the forward pass.
The rounds use every working register, so it receives a dedicated wire. -/
def aNZ (n : Nat) : Nat := aC n + 1

/-- The `2 n` kept branch bits, one per round. -/
def aM (n : Nat) : Nat := aNZ n + 1
/-- The `2 n` kept termination bits, one per round. -/
def aZ (n : Nat) : Nat := aM n + 2 * n
/-- The control of the correction's halving, one wire for all `2 n` of them.

Each active halving adds the modulus when its operand is odd.  With the modulus
`p` odd and the operand `x` below it, halving sends an even `x` to
`x / 2 < (p + 1) / 2` and an odd `x` to
`(x + p) / 2 ≥ (p + 1) / 2`.  Comparing the result against
`(p - 1) / 2` therefore recovers the parity control and clears the reusable
wire before the next halving.  `VQ.Curve.PointAddition.Arithmetic.Inv.halfMod` is that threshold. -/
def aH (n : Nat) : Nat := aZ n + 2 * n

/-- The bit the recovery's comparison lands on, cleared with it. -/
def aG (n : Nat) : Nat := aH n + 1

/-- The constant the recovery compares against: `(p - 1) / 2`. -/
def halfMod : Nat := (modulus - 1) / 2

/-- The workspace the claim declares: `10 n + 13` wires. -/
def wsWidth (n : Nat) : Nat := 10 * n + 13

/-- The whole circuit's width, input and output included. -/
def totalWidth (n : Nat) : Nat := 12 * n + 13

theorem aH_end (n : Nat) : aG n + 1 = totalWidth n := by
  unfold aG aH aZ aM aNZ aC aGt aT aA aTR aTU aS aR aV aU bw totalWidth
  omega

theorem total_eq (n : Nat) : 2 * n + wsWidth n = totalWidth n := by
  unfold wsWidth totalWidth; omega

/-! ### Ordered offsets

The offset equalities prove pairwise register disjointness and the required
placement conditions. -/

theorem aU_lt (n : Nat) : aU n + bw n = aV n := rfl
theorem aV_lt (n : Nat) : aV n + bw n = aR n := rfl
theorem aR_lt (n : Nat) : aR n + bw n = aS n := rfl
theorem aS_lt (n : Nat) : aS n + bw n = aTU n := rfl
theorem aTU_lt (n : Nat) : aTU n + bw n = aTR n := rfl
theorem aTR_lt (n : Nat) : aTR n + bw n = aA n := rfl
theorem aA_lt (n : Nat) : aA n + 1 = aT n := rfl
theorem aT_lt (n : Nat) : aT n + 1 = aGt n := rfl
theorem aGt_lt (n : Nat) : aGt n + 1 = aC n := rfl
theorem aC_lt (n : Nat) : aC n + 1 = aNZ n := rfl
theorem aNZ_lt (n : Nat) : aNZ n + 1 = aM n := rfl
theorem aM_lt (n : Nat) : aM n + 2 * n = aZ n := rfl
theorem aZ_lt (n : Nat) : aZ n + 2 * n = aH n := rfl
theorem aH_lt (n : Nat) : aH n + 1 = aG n := rfl

end VQ.Curve.PointAddition.Arithmetic.Inv
