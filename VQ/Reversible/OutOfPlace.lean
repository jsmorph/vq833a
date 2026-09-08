/-
Out-of-place reversible functions.

A circuit satisfying `XorComputes` exchanges a destination field for its XOR
with a function of a disjoint source field.  Computing a bijection into a clear
destination, swapping the fields, and computing its inverse clears the original
input while leaving the image in its place.
-/
import VQ.Reversible.Blocks

namespace VQ
namespace Reversible

/-- A reversible gate list XORs `f` of the source field into the destination
field and changes no other bit. -/
def XorComputes (source destination len : Nat) (f : Nat → Nat)
    (gates : List RGate) : Prop :=
  ∀ I, actGates gates I =
    writeField I destination len
      (readField I destination len ^^^ f (readField I source len))

/-- A reversible gate list XORs a function of a source field and a preserved
context field into the destination. -/
def XorComputesWith (source destination len context contextLen : Nat)
    (f : Nat → Nat → Nat) (gates : List RGate) : Prop :=
  ∀ I, actGates gates I =
    writeField I destination len
      (readField I destination len ^^^
        f (readField I source len) (readField I context contextLen))

/-- A calculator specification on a stated input domain with a clear scratch
field.  The equality requires the calculator to restore the scratch field. -/
def XorComputesWithOn (source destination len context contextLen
    workspace workspaceLen : Nat) (valid : Nat → Nat → Prop)
    (f : Nat → Nat → Nat) (gates : List RGate) : Prop :=
  ∀ I, valid (readField I source len) (readField I context contextLen) →
    readField I workspace workspaceLen = 0 →
    actGates gates I =
      writeField I destination len
        (readField I destination len ^^^
          f (readField I source len) (readField I context contextLen))

/-- Compute a bijection into a second field, exchange the fields, and XOR the
inverse image out of the second field. -/
def outOfPlace (source destination len : Nat)
    (forward inverse : List RGate) : List RGate :=
  forward ++ swapFields source destination len ++ inverse

/-- The out-of-place construction leaves `f x` in the source field and clears
the destination.  The proof uses only XOR computation and the left-inverse law,
so a concrete arithmetic implementation can remain opaque. -/
theorem actGates_outOfPlace {source destination len : Nat}
    {f g : Nat → Nat} {forward inverse : List RGate}
    (hdis : source + len ≤ destination ∨ destination + len ≤ source)
    (hforward : XorComputes source destination len f forward)
    (hinverse : XorComputes source destination len g inverse)
    (hfit : ∀ x, x < 2 ^ len → f x < 2 ^ len)
    (hleft : ∀ x, x < 2 ^ len → g (f x) = x)
    {I : Nat} (hclear : readField I destination len = 0) :
    actGates (outOfPlace source destination len forward inverse) I =
      writeField (writeField I source len (f (readField I source len)))
        destination len 0 := by
  have hdis' : destination + len ≤ source ∨ source + len ≤ destination :=
    hdis.elim Or.inr Or.inl
  let x := readField I source len
  have hx : x < 2 ^ len := readField_lt I source len
  have hfx : f x < 2 ^ len := hfit x hx
  have hf := hforward I
  change actGates forward I =
    writeField I destination len (readField I destination len ^^^ f x) at hf
  rw [hclear, Nat.zero_xor] at hf
  let J := writeField (writeField I source len (f x)) destination len x
  have hswap : actGates (swapFields source destination len) (actGates forward I) = J := by
    rw [actGates_swapFields hdis, hf,
      readField_writeField_self hfx,
      readField_writeField_of_disjoint hdis',
      writeField_comm hdis', writeField_writeField]
  have hi := hinverse J
  change actGates inverse J =
    writeField J destination len
      (readField J destination len ^^^ g (readField J source len)) at hi
  have hreadDestination : readField J destination len = x := by
    exact readField_writeField_self hx
  have hreadSource : readField J source len = f x := by
    dsimp [J]
    rw [readField_writeField_of_disjoint hdis', readField_writeField_self hfx]
  rw [hreadDestination, hreadSource, hleft x hx, Nat.xor_self] at hi
  rw [outOfPlace, actGates_append, actGates_append, hswap, hi]
  dsimp [J, x]
  rw [writeField_writeField]

/-- The out-of-place construction with a preserved context field.  Forward and
inverse may both read the context, while their XOR specifications ensure that
neither changes it. -/
theorem actGates_outOfPlaceWith {source destination len context contextLen : Nat}
    {f g : Nat → Nat → Nat} {forward inverse : List RGate}
    (hdis : source + len ≤ destination ∨ destination + len ≤ source)
    (hctxs : context + contextLen ≤ source ∨ source + len ≤ context)
    (hctxd : context + contextLen ≤ destination ∨ destination + len ≤ context)
    (hforward : XorComputesWith source destination len context contextLen f forward)
    (hinverse : XorComputesWith source destination len context contextLen g inverse)
    (hfit : ∀ x c, x < 2 ^ len → c < 2 ^ contextLen → f x c < 2 ^ len)
    (hleft : ∀ x c, x < 2 ^ len → c < 2 ^ contextLen → g (f x c) c = x)
    {I : Nat} (hclear : readField I destination len = 0) :
    actGates (outOfPlace source destination len forward inverse) I =
      writeField (writeField I source len
        (f (readField I source len) (readField I context contextLen))) destination len 0 := by
  have hdis' : destination + len ≤ source ∨ source + len ≤ destination :=
    hdis.elim Or.inr Or.inl
  have hsc : source + len ≤ context ∨ context + contextLen ≤ source :=
    hctxs.elim Or.inr Or.inl
  have hdc : destination + len ≤ context ∨ context + contextLen ≤ destination :=
    hctxd.elim Or.inr Or.inl
  let x := readField I source len
  let c := readField I context contextLen
  have hx : x < 2 ^ len := readField_lt I source len
  have hc : c < 2 ^ contextLen := readField_lt I context contextLen
  have hfx : f x c < 2 ^ len := hfit x c hx hc
  have hf := hforward I
  change actGates forward I =
    writeField I destination len (readField I destination len ^^^ f x c) at hf
  rw [hclear, Nat.zero_xor] at hf
  let J := writeField (writeField I source len (f x c)) destination len x
  have hswap : actGates (swapFields source destination len) (actGates forward I) = J := by
    rw [actGates_swapFields hdis, hf,
      readField_writeField_self hfx,
      readField_writeField_of_disjoint hdis',
      writeField_comm hdis', writeField_writeField]
  have hi := hinverse J
  change actGates inverse J =
    writeField J destination len
      (readField J destination len ^^^
        g (readField J source len) (readField J context contextLen)) at hi
  have hreadDestination : readField J destination len = x :=
    readField_writeField_self hx
  have hreadSource : readField J source len = f x c := by
    dsimp [J]
    rw [readField_writeField_of_disjoint hdis', readField_writeField_self hfx]
  have hreadContext : readField J context contextLen = c := by
    dsimp [J]
    rw [readField_writeField_of_disjoint hdc, readField_writeField_of_disjoint hsc]
  rw [hreadDestination, hreadSource, hreadContext, hleft x c hx hc, Nat.xor_self] at hi
  rw [outOfPlace, actGates_append, actGates_append, hswap, hi]
  dsimp [J, x, c]
  rw [writeField_writeField]

/-- Out-of-place computation from arithmetic components whose specifications
require reduced operands and clear scratch. -/
theorem actGates_outOfPlaceWithOn
    {source destination len context contextLen workspace workspaceLen : Nat}
    {valid : Nat → Nat → Prop} {f g : Nat → Nat → Nat}
    {forward inverse : List RGate}
    (hdis : source + len ≤ destination ∨ destination + len ≤ source)
    (hctxs : context + contextLen ≤ source ∨ source + len ≤ context)
    (hctxd : context + contextLen ≤ destination ∨ destination + len ≤ context)
    (hwss : workspace + workspaceLen ≤ source ∨ source + len ≤ workspace)
    (hwsd : workspace + workspaceLen ≤ destination ∨ destination + len ≤ workspace)
    (hwsc : workspace + workspaceLen ≤ context ∨ context + contextLen ≤ workspace)
    (hforward : XorComputesWithOn source destination len context contextLen
      workspace workspaceLen valid f forward)
    (hinverse : XorComputesWithOn source destination len context contextLen
      workspace workspaceLen valid g inverse)
    (hfit : ∀ x c, valid x c → x < 2 ^ len → c < 2 ^ contextLen → f x c < 2 ^ len)
    (hvalid : ∀ x c, valid x c → valid (f x c) c)
    (hleft : ∀ x c, valid x c → x < 2 ^ len → c < 2 ^ contextLen → g (f x c) c = x)
    {I : Nat}
    (hinput : valid (readField I source len) (readField I context contextLen))
    (hclear : readField I destination len = 0)
    (hwork : readField I workspace workspaceLen = 0) :
    actGates (outOfPlace source destination len forward inverse) I =
      writeField (writeField I source len
        (f (readField I source len) (readField I context contextLen))) destination len 0 := by
  have hdis' : destination + len ≤ source ∨ source + len ≤ destination :=
    hdis.elim Or.inr Or.inl
  have hsc : source + len ≤ context ∨ context + contextLen ≤ source :=
    hctxs.elim Or.inr Or.inl
  have hdc : destination + len ≤ context ∨ context + contextLen ≤ destination :=
    hctxd.elim Or.inr Or.inl
  let x := readField I source len
  let c := readField I context contextLen
  have hx : x < 2 ^ len := readField_lt I source len
  have hc : c < 2 ^ contextLen := readField_lt I context contextLen
  have hfx : f x c < 2 ^ len := hfit x c hinput hx hc
  have hf := hforward I hinput hwork
  change actGates forward I =
    writeField I destination len (readField I destination len ^^^ f x c) at hf
  rw [hclear, Nat.zero_xor] at hf
  let J := writeField (writeField I source len (f x c)) destination len x
  have hswap : actGates (swapFields source destination len) (actGates forward I) = J := by
    rw [actGates_swapFields hdis, hf,
      readField_writeField_self hfx,
      readField_writeField_of_disjoint hdis',
      writeField_comm hdis', writeField_writeField]
  have hreadDestination : readField J destination len = x :=
    readField_writeField_self hx
  have hreadSource : readField J source len = f x c := by
    dsimp [J]
    rw [readField_writeField_of_disjoint hdis', readField_writeField_self hfx]
  have hreadContext : readField J context contextLen = c := by
    dsimp [J]
    rw [readField_writeField_of_disjoint hdc, readField_writeField_of_disjoint hsc]
  have hreadWorkspace : readField J workspace workspaceLen = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by omega),
      readField_writeField_of_disjoint (by omega), hwork]
  have hi := hinverse J (by rw [hreadSource, hreadContext]; exact hvalid x c hinput)
    hreadWorkspace
  change actGates inverse J =
    writeField J destination len
      (readField J destination len ^^^
        g (readField J source len) (readField J context contextLen)) at hi
  rw [hreadDestination, hreadSource, hreadContext, hleft x c hinput hx hc,
    Nat.xor_self] at hi
  rw [outOfPlace, actGates_append, actGates_append, hswap, hi]
  dsimp [J, x, c]
  rw [writeField_writeField]

theorem outOfPlace_length (source destination len : Nat) (forward inverse : List RGate) :
    (outOfPlace source destination len forward inverse).length =
      forward.length + 3 * len + inverse.length := by
  simp [outOfPlace, swapFields_length]
  omega

theorem outOfPlace_ccx (source destination len : Nat) (forward inverse : List RGate) :
    (outOfPlace source destination len forward inverse).countP RGate.isCcx =
      forward.countP RGate.isCcx + inverse.countP RGate.isCcx := by
  simp [outOfPlace, swapFields_no_ccx]

theorem outOfPlace_cx (source destination len : Nat) (forward inverse : List RGate) :
    (outOfPlace source destination len forward inverse).countP RGate.isCx =
      forward.countP RGate.isCx + 3 * len + inverse.countP RGate.isCx := by
  simp [outOfPlace, swapFields_cx]
  omega

end Reversible
end VQ
