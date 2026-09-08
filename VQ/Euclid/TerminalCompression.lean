/-
Controlled terminal-epoch compression from the Luo version 2 companion circuit.
-/
import VQ.Euclid.Selector
import VQ.Reversible.Bit
import VQ.Reversible.Reverse

namespace VQ.Euclid.TerminalCompression

open Reversible

def layout : Layout := [3, 1, 1]

def codeOffset : Nat := 0
def outerWire : Nat := 3
def scratchWire : Nat := 4

def otherCodeWires (targetBit : Nat) : List Nat :=
  (List.range 3).filter (fun q => q != targetBit)

def maskGates (state targetBit : Nat) : List RGate :=
  (otherCodeWires targetBit).flatMap (Selector.maskBit state)

def adjacentGates (state targetBit : Nat) : List RGate :=
  maskGates state targetBit ++
    Selector.conjunction
      (otherCodeWires targetBit ++ [outerWire]) scratchWire targetBit ++
    (maskGates state targetBit).reverse

def gates : List RGate :=
  adjacentGates 7 0 ++
    adjacentGates 6 1 ++
    adjacentGates 4 2 ++
    adjacentGates 6 1 ++
    adjacentGates 7 0

def circuit : RCircuit :=
  { width := layout.width, gates := gates }

def compressCode (code : Nat) : Nat :=
  if code = 7 then 0 else if code = 0 then 7 else code

def out (i : Nat) : Nat :=
  if bitValue i outerWire = 1 then
    writeField i codeOffset 3 (compressCode (readField i codeOffset 3))
  else
    i

theorem compressCode_involutive (code : Nat) :
    compressCode (compressCode code) = code := by
  by_cases hseven : code = 7
  · subst code
    simp [compressCode]
  · by_cases hzero : code = 0
    · subst code
      simp [compressCode]
    · simp [compressCode, hseven, hzero]

theorem gates_wellFormed :
    gates.all (RGate.wellFormed layout.width) = true := by
  decide +kernel

theorem circuit_wellFormed : circuit.wellFormed = true :=
  gates_wellFormed

theorem gates_act_fin :
    ∀ i : Fin (2 ^ layout.width), bitValue i.val scratchWire = 0 →
      actGates gates i.val = out i.val := by
  decide +kernel

theorem gates_act
    {i : Nat} (hbound : i < 2 ^ layout.width)
    (hscratch : bitValue i scratchWire = 0) :
    actGates gates i = out i := by
  exact gates_act_fin ⟨i, hbound⟩ hscratch

theorem reverse_gates_act (i : Nat) :
    actGates gates.reverse (actGates gates i) = i :=
  actGates_reverse (w := layout.width) gates_wellFormed i

theorem circuit_width : circuit.width = 5 := by
  decide +kernel

theorem gates_explicit : gates =
    [.ccx 1 2 4, .ccx 4 3 0, .ccx 1 2 4,
      .x 0, .ccx 0 2 4, .ccx 4 3 1, .ccx 0 2 4, .x 0,
      .x 0, .x 1, .ccx 0 1 4, .ccx 4 3 2, .ccx 0 1 4, .x 1, .x 0,
      .x 0, .ccx 0 2 4, .ccx 4 3 1, .ccx 0 2 4, .x 0,
      .ccx 1 2 4, .ccx 4 3 0, .ccx 1 2 4] := by
  decide +kernel

theorem gates_length : gates.length = 23 := by
  decide +kernel

theorem gates_ccx : gates.countP RGate.isCcx = 15 := by
  decide +kernel

theorem gates_cx : gates.countP RGate.isCx = 0 := by
  decide +kernel

theorem compiled_toffoliCount :
    VQ.Circuit.toffoliCount (compile circuit) = 15 := by
  rw [toffoliCount_compile]
  exact gates_ccx

theorem compiled_gateCount :
    VQ.Circuit.gateCount (compile circuit) = 53 := by
  rw [gateCount_compile]
  change gates.length + 2 * gates.countP RGate.isCcx = 53
  rw [gates_length, gates_ccx]

theorem compiled_cnotCount :
    VQ.Circuit.cnotCount (compile circuit) = 0 := by
  rw [cnotCount_compile]
  exact gates_cx

end VQ.Euclid.TerminalCompression
