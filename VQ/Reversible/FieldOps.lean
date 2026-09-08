/-
Placement of proved field components into a larger register.
-/
import VQ.Reversible.Control
import VQ.Reversible.Wiring
import VQ.Reversible.ArithmeticSpec
import VQ.Curve.ReversibleSpec

namespace VQ
namespace Reversible

def placeUnaryGates (n ws input output work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (unaryLayout n ws) [input, output, work]))

def placeAddGates (n ws source target work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (adderLayout n ws) [source, target, work]))

def placeControlledAddGates
    (n ws source target work controlWire scratchWire : Nat)
    (r : RCircuit) : List RGate :=
  (control r).gates.map (RGate.map
    (place (controlledAdderLayout n ws)
      [source, target, work, controlWire, scratchWire]))

def placeControlledSubGates (n ws source target work controlWire scratchWire : Nat)
    (r : RCircuit) : List RGate :=
  (control r).gates.map (RGate.map
    (place (controlledAdderLayout n ws)
      [source, target, work, controlWire, scratchWire]))

def placeSubGates (n ws left target work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (adderLayout n ws) [left, target, work]))

def placeMulGates (n ws left right output work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (mulLayout n ws) [left, right, output, work]))

def placeNegGates (n ws target work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (constLayout n ws) [target, work]))

def placeControlledNegGates (n ws target work controlWire scratchWire : Nat)
    (r : RCircuit) : List RGate :=
  (control r).gates.map (RGate.map
    (place (controlledConstLayout n ws)
      [target, work, controlWire, scratchWire]))

def placeConstGates (n ws target work : Nat) (r : RCircuit) : List RGate :=
  r.gates.map (RGate.map (place (constLayout n ws) [target, work]))

theorem act_placeAddConst {m n ws target work c a I : Nat} {r : RCircuit}
    (hcomp : AddsConstMod m ws n c r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws).width = true)
    (hdis : Wiring.Disjoint (constLayout n ws) [target, work])
    (htarget : readField I target n = a) (hwork : readField I work ws = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hc : c < m) :
    actGates (placeConstGates n ws target work r) I =
      writeField I target n ((a + c) % m) := by
  rw [placeConstGates]
  apply actGates_placed_write (k := 0) (v := (a + c) % m) (I := I)
    hdis (by simp [constLayout]) (by simp [constLayout]) hwf
  apply hcomp a
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (constLayout n ws) [target, work] 0 I (by simp)]
    simpa [constLayout, Layout.size] using htarget
  · rw [read_gatherBits (constLayout n ws) [target, work] 1 I (by simp)]
    simpa [constLayout, Layout.size] using hwork
  · exact hm
  · exact ha
  · exact hc

theorem act_placeInvert {n ws input output work a I : Nat} {r : RCircuit}
    (hcomp : InvertsField ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws).width = true)
    (hdis : Wiring.Disjoint (unaryLayout n ws) [input, output, work])
    (hin : readField I input n = a) (hout : readField I output n = 0)
    (hwork : readField I work ws = 0) (hp : Curve.p ≤ 2 ^ n) (ha : a < Curve.p) :
    actGates (placeUnaryGates n ws input output work r) I =
      writeField I output n (Curve.inv a) := by
  rw [placeUnaryGates]
  apply actGates_placed_write (k := 1) (v := Curve.inv a) (I := I)
    hdis (by simp [unaryLayout]) (by simp [unaryLayout]) hwf
  apply hcomp a
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 0 I (by simp)]
    simpa [unaryLayout, Layout.size] using hin
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 1 I (by simp)]
    simpa [unaryLayout, Layout.size] using hout
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 2 I (by simp)]
    simpa [unaryLayout, Layout.size] using hwork
  · exact hp
  · exact ha

theorem act_placeAdd {m n ws source target work a b I : Nat} {r : RCircuit}
    (hcomp : AddsMod m ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (adderLayout n ws).width = true)
    (hdis : Wiring.Disjoint (adderLayout n ws) [source, target, work])
    (hsource : readField I source n = a) (htarget : readField I target n = b)
    (hwork : readField I work ws = 0) (hm : m ≤ 2 ^ n)
    (ha : a < m) (hb : b < m) :
    actGates (placeAddGates n ws source target work r) I =
      writeField I target n ((a + b) % m) := by
  rw [placeAddGates]
  apply actGates_placed_write (k := 1) (v := (a + b) % m) (I := I)
    hdis (by simp [adderLayout]) (by simp [adderLayout]) hwf
  apply hcomp a b
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (adderLayout n ws) [source, target, work] 0 I (by simp)]
    simpa [adderLayout, Layout.size] using hsource
  · rw [read_gatherBits (adderLayout n ws) [source, target, work] 1 I (by simp)]
    simpa [adderLayout, Layout.size] using htarget
  · rw [read_gatherBits (adderLayout n ws) [source, target, work] 2 I (by simp)]
    simpa [adderLayout, Layout.size] using hwork
  · exact hm
  · exact ha
  · exact hb

theorem act_placeControlledAddWrap
    {n ws source target work controlWire scratchWire a b I : Nat}
    {enabled : Bool} {r : RCircuit}
    (hcomp : AddsWrap ws n r) (hr : r.wellFormed = true)
    (hwidth : r.width = (adderLayout n ws).width)
    (hdis : Wiring.Disjoint (controlledAdderLayout n ws)
      [source, target, work, controlWire, scratchWire])
    (hsource : readField I source n = a) (htarget : readField I target n = b)
    (hwork : readField I work ws = 0)
    (hcontrol : readField I controlWire 1 = if enabled = true then 1 else 0)
    (hscratch : readField I scratchWire 1 = 0) :
    actGates
        (placeControlledAddGates n ws source target work controlWire
          scratchWire r) I =
      if enabled = true then writeField I target n ((a + b) % 2 ^ n)
      else I := by
  have hcontrolled := control_addsWrap hwidth hr hcomp
  have hcontrolWf : (control r).wellFormed = true := control_wellFormed hr
  have hcontrolWidth : (control r).width =
      (controlledAdderLayout n ws).width := by
    change r.width + 2 = (controlledAdderLayout n ws).width
    rw [hwidth]
    simp [controlledAdderLayout, adderLayout, Layout.width]
    omega
  have hlocalWf : ∀ g ∈ (control r).gates,
      g.wellFormed (controlledAdderLayout n ws).width = true := by
    intro g hg
    rw [← hcontrolWidth]
    exact RCircuit.wellFormed_mem hcontrolWf hg
  let wiring : Wiring := [source, target, work, controlWire, scratchWire]
  let gathered := gatherBits (place (controlledAdderLayout n ws) wiring)
    (controlledAdderLayout n ws).width I
  have hlocal : actGates (control r).gates gathered =
      if enabled = true then
        (controlledAdderLayout n ws).write gathered 1 ((a + b) % 2 ^ n)
      else gathered := by
    apply hcontrolled enabled a b
    · exact gatherBits_lt _ _ _
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 0 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hsource
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 1 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using htarget
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 2 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hwork
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 3 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hcontrol
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 4 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hscratch
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hlocal ⊢
      have hplaced := actGates_placed_congr (hs := []) hdis
        (by simp [controlledAdderLayout]) hlocalWf
        (by intro g hg; simp at hg) I hlocal
      simpa [placeControlledAddGates, wiring, gathered, actGates_nil] using
        hplaced
  | true =>
      simp only [if_true] at hlocal ⊢
      have hplaced := actGates_placed_write
        (gs := (control r).gates) (L := controlledAdderLayout n ws)
        (W := wiring) (k := 1) (v := (a + b) % 2 ^ n) (I := I)
        hdis (by simp [controlledAdderLayout, wiring])
        (by simp [controlledAdderLayout]) hlocalWf hlocal
      simpa [placeControlledAddGates, wiring, controlledAdderLayout,
        Layout.size] using hplaced

theorem act_placeControlledSub
    {m n ws source target work controlWire scratchWire a b I : Nat}
    {enabled : Bool} {r : RCircuit}
    (hcomp : SubsMod m ws n r) (hr : r.wellFormed = true)
    (hwidth : r.width = (adderLayout n ws).width)
    (hdis : Wiring.Disjoint (controlledAdderLayout n ws)
      [source, target, work, controlWire, scratchWire])
    (hsource : readField I source n = a) (htarget : readField I target n = b)
    (hwork : readField I work ws = 0)
    (hcontrol : readField I controlWire 1 = if enabled = true then 1 else 0)
    (hscratch : readField I scratchWire 1 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    actGates
        (placeControlledSubGates n ws source target work controlWire
          scratchWire r) I =
      if enabled = true then writeField I target n ((b + (m - a)) % m)
      else I := by
  have hcontrolled := control_subsMod hwidth hr hcomp
  have hcontrolWf : (control r).wellFormed = true := control_wellFormed hr
  have hcontrolWidth : (control r).width =
      (controlledAdderLayout n ws).width := by
    change r.width + 2 = (controlledAdderLayout n ws).width
    rw [hwidth]
    simp [controlledAdderLayout, adderLayout, Layout.width]
    omega
  have hlocalWf : ∀ g ∈ (control r).gates,
      g.wellFormed (controlledAdderLayout n ws).width = true := by
    intro g hg
    rw [← hcontrolWidth]
    exact RCircuit.wellFormed_mem hcontrolWf hg
  let wiring : Wiring := [source, target, work, controlWire, scratchWire]
  let gathered := gatherBits (place (controlledAdderLayout n ws) wiring)
    (controlledAdderLayout n ws).width I
  have hlocal : actGates (control r).gates gathered =
      if enabled = true then
        (controlledAdderLayout n ws).write gathered 1 ((b + (m - a)) % m)
      else gathered := by
    apply hcontrolled enabled a b
    · exact gatherBits_lt _ _ _
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 0 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hsource
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 1 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using htarget
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 2 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hwork
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 3 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hcontrol
    · rw [read_gatherBits (controlledAdderLayout n ws) wiring 4 I
        (by simp [wiring])]
      simpa [controlledAdderLayout, Layout.size, wiring] using hscratch
    · exact hm
    · exact ha
    · exact hb
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hlocal ⊢
      have hplaced := actGates_placed_congr (hs := []) hdis
        (by simp [controlledAdderLayout]) hlocalWf
        (by intro g hg; simp at hg) I hlocal
      simpa [placeControlledSubGates, wiring, gathered, actGates_nil] using hplaced
  | true =>
      simp only [if_true] at hlocal ⊢
      have hplaced := actGates_placed_write
        (gs := (control r).gates) (L := controlledAdderLayout n ws)
        (W := wiring) (k := 1) (v := (b + (m - a)) % m) (I := I)
        hdis (by simp [controlledAdderLayout, wiring])
        (by simp [controlledAdderLayout]) hlocalWf hlocal
      simpa [placeControlledSubGates, wiring, controlledAdderLayout, Layout.size]
        using hplaced

theorem act_placeSquare {m n ws input output work a I : Nat} {r : RCircuit}
    (hcomp : SquaresMod m ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws).width = true)
    (hdis : Wiring.Disjoint (unaryLayout n ws) [input, output, work])
    (hin : readField I input n = a) (hout : readField I output n = 0)
    (hwork : readField I work ws = 0) (hm : m ≤ 2 ^ n) (ha : a < m) :
    actGates (placeUnaryGates n ws input output work r) I =
      writeField I output n (a * a % m) := by
  rw [placeUnaryGates]
  apply actGates_placed_write (k := 1) (v := a * a % m) (I := I)
    hdis (by simp [unaryLayout]) (by simp [unaryLayout]) hwf
  apply hcomp a
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 0 I (by simp)]
    simpa [unaryLayout, Layout.size] using hin
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 1 I (by simp)]
    simpa [unaryLayout, Layout.size] using hout
  · rw [read_gatherBits (unaryLayout n ws) [input, output, work] 2 I (by simp)]
    simpa [unaryLayout, Layout.size] using hwork
  · exact hm
  · exact ha

theorem act_placeSub {m n ws left target work a b I : Nat} {r : RCircuit}
    (hcomp : SubsMod m ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (adderLayout n ws).width = true)
    (hdis : Wiring.Disjoint (adderLayout n ws) [left, target, work])
    (hleft : readField I left n = a) (htarget : readField I target n = b)
    (hwork : readField I work ws = 0) (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    actGates (placeSubGates n ws left target work r) I =
      writeField I target n ((b + (m - a)) % m) := by
  rw [placeSubGates]
  apply actGates_placed_write (k := 1) (v := (b + (m - a)) % m) (I := I)
    hdis (by simp [adderLayout]) (by simp [adderLayout]) hwf
  apply hcomp a b
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (adderLayout n ws) [left, target, work] 0 I (by simp)]
    simpa [adderLayout, Layout.size] using hleft
  · rw [read_gatherBits (adderLayout n ws) [left, target, work] 1 I (by simp)]
    simpa [adderLayout, Layout.size] using htarget
  · rw [read_gatherBits (adderLayout n ws) [left, target, work] 2 I (by simp)]
    simpa [adderLayout, Layout.size] using hwork
  · exact hm
  · exact ha
  · exact hb

theorem act_placeMul {m n ws left right output work a b I : Nat} {r : RCircuit}
    (hcomp : MulsMod m ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws).width = true)
    (hdis : Wiring.Disjoint (mulLayout n ws) [left, right, output, work])
    (hleft : readField I left n = a) (hright : readField I right n = b)
    (hout : readField I output n = 0) (hwork : readField I work ws = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    actGates (placeMulGates n ws left right output work r) I =
      writeField I output n (a * b % m) := by
  rw [placeMulGates]
  apply actGates_placed_write (k := 2) (v := a * b % m) (I := I)
    hdis (by simp [mulLayout]) (by simp [mulLayout]) hwf
  apply hcomp a b
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (mulLayout n ws) [left, right, output, work] 0 I (by simp)]
    simpa [mulLayout, Layout.size] using hleft
  · rw [read_gatherBits (mulLayout n ws) [left, right, output, work] 1 I (by simp)]
    simpa [mulLayout, Layout.size] using hright
  · rw [read_gatherBits (mulLayout n ws) [left, right, output, work] 2 I (by simp)]
    simpa [mulLayout, Layout.size] using hout
  · rw [read_gatherBits (mulLayout n ws) [left, right, output, work] 3 I (by simp)]
    simpa [mulLayout, Layout.size] using hwork
  · exact hm
  · exact ha
  · exact hb

theorem act_placeNeg {m n ws target work a I : Nat} {r : RCircuit}
    (hcomp : NegatesMod m ws n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws).width = true)
    (hdis : Wiring.Disjoint (constLayout n ws) [target, work])
    (htarget : readField I target n = a) (hwork : readField I work ws = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    actGates (placeNegGates n ws target work r) I =
      writeField I target n ((m - a) % m) := by
  rw [placeNegGates]
  apply actGates_placed_write (k := 0) (v := (m - a) % m) (I := I)
    hdis (by simp [constLayout]) (by simp [constLayout]) hwf
  apply hcomp a
  · exact gatherBits_lt _ _ _
  · rw [read_gatherBits (constLayout n ws) [target, work] 0 I (by simp)]
    simpa [constLayout, Layout.size] using htarget
  · rw [read_gatherBits (constLayout n ws) [target, work] 1 I (by simp)]
    simpa [constLayout, Layout.size] using hwork
  · exact hm
  · exact ha

theorem act_placeControlledNeg
    {m n ws target work controlWire scratchWire a I : Nat}
    {enabled : Bool} {r : RCircuit}
    (hcomp : NegatesMod m ws n r) (hr : r.wellFormed = true)
    (hwidth : r.width = (constLayout n ws).width)
    (hdis : Wiring.Disjoint (controlledConstLayout n ws)
      [target, work, controlWire, scratchWire])
    (htarget : readField I target n = a) (hwork : readField I work ws = 0)
    (hcontrol : readField I controlWire 1 = if enabled = true then 1 else 0)
    (hscratch : readField I scratchWire 1 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    actGates
        (placeControlledNegGates n ws target work controlWire scratchWire r) I =
      if enabled = true then writeField I target n ((m - a) % m)
      else I := by
  have hcontrolled := control_negatesMod hwidth hr hcomp
  have hcontrolWf : (control r).wellFormed = true := control_wellFormed hr
  have hcontrolWidth : (control r).width =
      (controlledConstLayout n ws).width := by
    change r.width + 2 = (controlledConstLayout n ws).width
    rw [hwidth]
    simp [controlledConstLayout, constLayout, Layout.width]
    omega
  have hlocalWf : ∀ g ∈ (control r).gates,
      g.wellFormed (controlledConstLayout n ws).width = true := by
    intro g hg
    rw [← hcontrolWidth]
    exact RCircuit.wellFormed_mem hcontrolWf hg
  let wiring : Wiring := [target, work, controlWire, scratchWire]
  let gathered := gatherBits (place (controlledConstLayout n ws) wiring)
    (controlledConstLayout n ws).width I
  have hlocal : actGates (control r).gates gathered =
      if enabled = true then
        (controlledConstLayout n ws).write gathered 0 ((m - a) % m)
      else gathered := by
    apply hcontrolled enabled a
    · exact gatherBits_lt _ _ _
    · rw [read_gatherBits (controlledConstLayout n ws) wiring 0 I
        (by simp [wiring])]
      simpa [controlledConstLayout, Layout.size, wiring] using htarget
    · rw [read_gatherBits (controlledConstLayout n ws) wiring 1 I
        (by simp [wiring])]
      simpa [controlledConstLayout, Layout.size, wiring] using hwork
    · rw [read_gatherBits (controlledConstLayout n ws) wiring 2 I
        (by simp [wiring])]
      simpa [controlledConstLayout, Layout.size, wiring] using hcontrol
    · rw [read_gatherBits (controlledConstLayout n ws) wiring 3 I
        (by simp [wiring])]
      simpa [controlledConstLayout, Layout.size, wiring] using hscratch
    · exact hm
    · exact ha
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hlocal ⊢
      have hplaced := actGates_placed_congr (hs := []) hdis
        (by simp [controlledConstLayout]) hlocalWf
        (by intro g hg; simp at hg) I hlocal
      simpa [placeControlledNegGates, wiring, gathered, actGates_nil] using hplaced
  | true =>
      simp only [if_true] at hlocal ⊢
      have hplaced := actGates_placed_write
        (gs := (control r).gates) (L := controlledConstLayout n ws)
        (W := wiring) (k := 0) (v := (m - a) % m) (I := I)
        hdis (by simp [controlledConstLayout, wiring])
        (by simp [controlledConstLayout]) hlocalWf hlocal
      simpa [placeControlledNegGates, wiring, controlledConstLayout, Layout.size]
        using hplaced

end Reversible
end VQ
