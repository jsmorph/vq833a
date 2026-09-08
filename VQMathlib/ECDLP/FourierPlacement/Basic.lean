import VQMathlib.Algorithms.QFT.Family
import VQ.Semantics.RegisterState
import VQ.Reversible.Register

namespace VQ.Tests.ECDLPQFTPlacement

open Algebra Semantics
open VQ.Reversible

def shiftWire (offset q : Nat) : Nat := offset + q

def placedCircuit (offset width : Nat) (c : Circuit) : Circuit :=
  Circuit.relabel (shiftWire offset) width c

def placedQFT (offset n width : Nat) : Circuit :=
  placedCircuit offset width (QFT.qftCircuit n)

def placedIQFT (offset n width : Nat) : Circuit :=
  placedCircuit offset width (QFTFamily.iqftCircuit n)

def suffixWidth (offset n width : Nat) : Nat := width - (offset + n)

def prefixContext (context offset : Nat) : Nat :=
  readField context 0 offset

def suffixContext (context offset n width : Nat) : Nat :=
  readField context (offset + n) (suffixWidth offset n width)

def factorizedProduct (offset n width : Nat)
    (prefixState active suffixState : Vec d) : Vec d :=
  RegisterState.join offset (n + suffixWidth offset n width) 0
    prefixState
    (RegisterState.join n (suffixWidth offset n width) 0 active suffixState)

def factorizedState (offset n width context : Nat) (u : Vec d) : Vec d :=
  factorizedProduct offset n width
    (basis (prefixContext context offset)) u
    (basis (suffixContext context offset n width))

def adjacentSuffixWidth (offset leftWidth rightWidth width : Nat) : Nat :=
  width - (offset + leftWidth + rightWidth)

def adjacentProduct (offset leftWidth rightWidth width : Nat)
    (prefixState leftState rightState suffixState : Vec d) : Vec d :=
  RegisterState.join offset
    (leftWidth + (rightWidth +
      adjacentSuffixWidth offset leftWidth rightWidth width)) 0
    prefixState
    (RegisterState.join leftWidth
      (rightWidth + adjacentSuffixWidth offset leftWidth rightWidth width) 0
      leftState
      (RegisterState.join rightWidth
        (adjacentSuffixWidth offset leftWidth rightWidth width) 0
        rightState suffixState))

@[simp] theorem placedCircuit_width (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).width = width := rfl

@[simp] theorem placedCircuit_gates (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).gates =
      c.gates.map (Gate.map (shiftWire offset)) := rfl

@[simp] theorem placedQFT_width (offset n width : Nat) :
    (placedQFT offset n width).width = width := rfl

@[simp] theorem placedQFT_gates (offset n width : Nat) :
    (placedQFT offset n width).gates =
      (QFT.qftCircuit n).gates.map (Gate.map (shiftWire offset)) := rfl

@[simp] theorem placedIQFT_width (offset n width : Nat) :
    (placedIQFT offset n width).width = width := rfl

@[simp] theorem placedIQFT_gates (offset n width : Nat) :
    (placedIQFT offset n width).gates =
      (QFTFamily.iqftCircuit n).gates.map (Gate.map (shiftWire offset)) := rfl

theorem suffixWidth_eq {offset n width : Nat} (hfit : offset + n ≤ width) :
    offset + (n + suffixWidth offset n width) = width := by
  simp [suffixWidth]
  omega

theorem adjacentSuffixWidth_eq {offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width) :
    offset + (leftWidth + (rightWidth +
      adjacentSuffixWidth offset leftWidth rightWidth width)) = width := by
  simp [adjacentSuffixWidth]
  omega

theorem suffixWidth_left_eq {offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width) :
    suffixWidth offset leftWidth width =
      rightWidth + adjacentSuffixWidth offset leftWidth rightWidth width := by
  simp [suffixWidth, adjacentSuffixWidth]
  omega

theorem suffixWidth_right_eq (offset leftWidth rightWidth width : Nat) :
    suffixWidth (offset + leftWidth) rightWidth width =
      adjacentSuffixWidth offset leftWidth rightWidth width := by
  simp [suffixWidth, adjacentSuffixWidth]

theorem prefixContext_lt (context offset : Nat) :
    prefixContext context offset < 2 ^ offset :=
  readField_lt context 0 offset

theorem suffixContext_lt (context offset n width : Nat) :
    suffixContext context offset n width < 2 ^ suffixWidth offset n width :=
  readField_lt context (offset + n) (suffixWidth offset n width)

theorem factorizedProduct_support {offset n width : Nat}
    (hfit : offset + n ≤ width) (prefixState active suffixState : Vec d) :
    WFVec (2 ^ width)
      (factorizedProduct offset n width prefixState active suffixState) := by
  have h := RegisterState.join_support offset
    (n + suffixWidth offset n width) 0 prefixState
    (RegisterState.join n (suffixWidth offset n width) 0 active suffixState)
  simpa [factorizedProduct, suffixWidth_eq hfit] using h

theorem adjacentProduct_support {offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (prefixState leftState rightState suffixState : Vec d) :
    WFVec (2 ^ width)
      (adjacentProduct offset leftWidth rightWidth width
        prefixState leftState rightState suffixState) := by
  have h := RegisterState.join_support offset
    (leftWidth + (rightWidth +
      adjacentSuffixWidth offset leftWidth rightWidth width)) 0
    prefixState
    (RegisterState.join leftWidth
      (rightWidth + adjacentSuffixWidth offset leftWidth rightWidth width) 0
      leftState
      (RegisterState.join rightWidth
        (adjacentSuffixWidth offset leftWidth rightWidth width) 0
        rightState suffixState))
  simpa [adjacentProduct, adjacentSuffixWidth_eq hfit] using h

theorem factorizedState_support {offset n width context : Nat}
    (hfit : offset + n ≤ width) (u : Vec d) :
    WFVec (2 ^ width) (factorizedState offset n width context u) := by
  simpa [factorizedState] using factorizedProduct_support hfit
    (basis (prefixContext context offset) : Vec d) u
    (basis (suffixContext context offset n width))

theorem factorizedState_basis {offset n width context x : Nat}
    (hx : x < 2 ^ n) :
    factorizedState offset n width context (basis x : Vec d) =
      basis (RegisterState.joinIndex offset (prefixContext context offset)
        (RegisterState.joinIndex n x
          (suffixContext context offset n width))) := by
  rw [factorizedState, factorizedProduct,
    RegisterState.join_basis_basis hx
      (suffixContext_lt context offset n width)]
  exact RegisterState.join_basis_basis
    (prefixContext_lt context offset)
    (RegisterState.joinIndex_lt hx
      (suffixContext_lt context offset n width))

theorem gate_map_wellFormedAt {level sourceWidth targetWidth : Nat}
    {f : Nat → Nat} {g : Gate}
    (hbound : ∀ q, q < sourceWidth → f q < targetWidth)
    (hinj : ∀ a b, a < sourceWidth → b < sourceWidth → f a = f b → a = b)
    (hg : g.wellFormedAt level sourceWidth = true) :
    (g.map f).wellFormedAt level targetWidth = true := by
  cases g with
  | x q =>
      simp only [Gate.map, Gate.wellFormedAt, decide_eq_true_eq] at hg ⊢
      exact hbound q hg
  | z q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨hbound q hg.1, hg.2⟩
  | y q | s q | sdg q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨hbound q hg.1, hg.2⟩
  | h q | t q | tdg q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨hbound q hg.1, hg.2⟩
  | p k q | pdg k q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨⟨hbound q hg.1.1, hg.1.2⟩, hg.2⟩
  | cx a b =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨⟨hbound a hg.1.1, hbound b hg.1.2⟩,
        fun hab => hg.2 (hinj a b hg.1.1 hg.1.2 hab)⟩
  | ccz a b c =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at hg ⊢
      exact ⟨⟨⟨⟨⟨⟨hbound a hg.1.1.1.1.1.1,
        hbound b hg.1.1.1.1.1.2⟩,
        hbound c hg.1.1.1.1.2⟩,
        fun hab => hg.1.1.1.2
          (hinj a b hg.1.1.1.1.1.1 hg.1.1.1.1.1.2 hab)⟩,
        fun hbc => hg.1.1.2
          (hinj b c hg.1.1.1.1.1.2 hg.1.1.1.1.2 hbc)⟩,
        fun hac => hg.1.2
          (hinj a c hg.1.1.1.1.1.1 hg.1.1.1.1.2 hac)⟩,
        hg.2⟩

theorem placedCircuit_wellFormedAt {level offset width : Nat} {c : Circuit}
    (hfit : offset + c.width ≤ width)
    (hc : c.wellFormedAt level = true) :
    (placedCircuit offset width c).wellFormedAt level = true := by
  simp only [Circuit.wellFormedAt, placedCircuit_gates,
    List.all_eq_true, List.mem_map] at hc ⊢
  rintro mapped ⟨g, hg, rfl⟩
  apply gate_map_wellFormedAt
    (sourceWidth := c.width) (targetWidth := width)
    (f := shiftWire offset)
  · intro q hq
    simp [shiftWire]
    omega
  · intro a b ha hb hab
    simp [shiftWire] at hab
    omega
  · exact hc g hg

theorem placedQFT_wellFormedAt {level offset n width : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    (placedQFT offset n width).wellFormedAt level = true := by
  exact placedCircuit_wellFormedAt hfit
    (QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel)

theorem placedIQFT_wellFormedAt {level offset n width : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    (placedIQFT offset n width).wellFormedAt level = true := by
  apply placedCircuit_wellFormedAt hfit
  rw [QFTFamily.iqftCircuit,
    Adjoint.circuit_adjoint_wellFormedAt]
  exact QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel

end VQ.Tests.ECDLPQFTPlacement
