import VQ.Reversible.Register

namespace VQ.Lookup

open Reversible

def layout (addressWidth outputWidth workspaceWidth : Nat) : Layout :=
  [addressWidth, outputWidth, workspaceWidth]

def value (table : List Nat) (outputWidth address : Nat) : Nat :=
  table.getD address 0 % 2 ^ outputWidth

def address (addressWidth outputWidth workspaceWidth i : Nat) : Nat :=
  (layout addressWidth outputWidth workspaceWidth).read i 0

def output (addressWidth outputWidth workspaceWidth i : Nat) : Nat :=
  (layout addressWidth outputWidth workspaceWidth).read i 1

def workspace (addressWidth outputWidth workspaceWidth i : Nat) : Nat :=
  (layout addressWidth outputWidth workspaceWidth).read i 2

def xorOutput (table : List Nat)
    (addressWidth outputWidth workspaceWidth i : Nat) : Nat :=
  (layout addressWidth outputWidth workspaceWidth).write i 1
    (output addressWidth outputWidth workspaceWidth i ^^^
      value table outputWidth
        (address addressWidth outputWidth workspaceWidth i))

def CoherentXorLookup (table : List Nat)
    (addressWidth outputWidth workspaceWidth : Nat) (r : RCircuit) : Prop :=
  r.width = (layout addressWidth outputWidth workspaceWidth).width ∧
    r.wellFormed = true ∧
    ∀ i, workspace addressWidth outputWidth workspaceWidth i = 0 →
      act r i = xorOutput table addressWidth outputWidth workspaceWidth i

theorem value_lt (table : List Nat) (outputWidth address : Nat) :
    value table outputWidth address < 2 ^ outputWidth := by
  exact Nat.mod_lt _ (Nat.two_pow_pos outputWidth)

theorem address_write_output
    (addressWidth outputWidth workspaceWidth i v : Nat) :
    address addressWidth outputWidth workspaceWidth
        ((layout addressWidth outputWidth workspaceWidth).write i 1 v) =
      address addressWidth outputWidth workspaceWidth i := by
  exact Layout.read_write_ne (by decide)

theorem workspace_write_output
    (addressWidth outputWidth workspaceWidth i v : Nat) :
    workspace addressWidth outputWidth workspaceWidth
        ((layout addressWidth outputWidth workspaceWidth).write i 1 v) =
      workspace addressWidth outputWidth workspaceWidth i := by
  exact Layout.read_write_ne (by decide)

theorem address_xorOutput (table : List Nat)
    (addressWidth outputWidth workspaceWidth i : Nat) :
    address addressWidth outputWidth workspaceWidth
        (xorOutput table addressWidth outputWidth workspaceWidth i) =
      address addressWidth outputWidth workspaceWidth i := by
  exact address_write_output addressWidth outputWidth workspaceWidth i _

theorem workspace_xorOutput (table : List Nat)
    (addressWidth outputWidth workspaceWidth i : Nat) :
    workspace addressWidth outputWidth workspaceWidth
        (xorOutput table addressWidth outputWidth workspaceWidth i) =
      workspace addressWidth outputWidth workspaceWidth i := by
  exact workspace_write_output addressWidth outputWidth workspaceWidth i _

theorem coherentXorLookup_read
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (h : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {i : Nat}
    (hworkspace : workspace addressWidth outputWidth workspaceWidth i = 0) :
    address addressWidth outputWidth workspaceWidth (act r i) =
        address addressWidth outputWidth workspaceWidth i ∧
      output addressWidth outputWidth workspaceWidth (act r i) =
        output addressWidth outputWidth workspaceWidth i ^^^
          value table outputWidth
            (address addressWidth outputWidth workspaceWidth i) ∧
      workspace addressWidth outputWidth workspaceWidth (act r i) = 0 := by
  have hact := h.2.2 i hworkspace
  have hvalue := value_lt table outputWidth
    (address addressWidth outputWidth workspaceWidth i)
  have houtput : output addressWidth outputWidth workspaceWidth i <
      2 ^ outputWidth := by
    simpa [output, layout, Layout.size] using
      Layout.read_lt (layout addressWidth outputWidth workspaceWidth) i 1
  have hxor : output addressWidth outputWidth workspaceWidth i ^^^
      value table outputWidth
        (address addressWidth outputWidth workspaceWidth i) < 2 ^ outputWidth :=
    Nat.xor_lt_two_pow houtput hvalue
  rw [hact]
  refine ⟨?_, ?_, ?_⟩
  · simpa [address, xorOutput] using
      (Layout.read_write_ne
        (l := layout addressWidth outputWidth workspaceWidth)
        (i := i) (j := 0) (k := 1) (v := _) (by decide))
  · simpa [output, xorOutput, layout, Layout.size] using
      (Layout.read_write_self
        (l := layout addressWidth outputWidth workspaceWidth)
        (i := i) (k := 1) (v := _) hxor)
  · rw [workspace, xorOutput,
      Layout.read_write_ne (l := layout addressWidth outputWidth workspaceWidth)
        (i := i) (j := 2) (k := 1) (v := _) (by decide)]
    simpa [workspace] using hworkspace

end VQ.Lookup
