import VQ.Curve.PointAddition.Runtime.Double

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def selector (equalFlag negFlag : Nat) : List RGate :=
  T 0 1 5 ++ T 2 negFlag 6 ++ T 5 6 7 ++ X 9 ++ F 6 9 ++ T 5 9 10 ++
  T 2 equalFlag 8 ++ T 10 8 11 ++ X 12 ++ F 8 12 ++ T 10 12 13

def selectorFlags (equalFlag negFlag : Nat) (flags : Nat → Nat) : Nat → Nat :=
  let f1 := setAt flags 5 ((flags 5 + flags 0 * flags 1) % 2)
  let f2 := setAt f1 6 ((f1 6 + f1 2 * f1 negFlag) % 2)
  let f3 := setAt f2 7 ((f2 7 + f2 5 * f2 6) % 2)
  let f4 := setAt f3 9 ((f3 9 + 1) % 2)
  let f5 := setAt f4 9 ((f4 9 + f4 6) % 2)
  let f6 := setAt f5 10 ((f5 10 + f5 5 * f5 9) % 2)
  let f7 := setAt f6 8 ((f6 8 + f6 2 * f6 equalFlag) % 2)
  let f8 := setAt f7 11 ((f7 11 + f7 10 * f7 8) % 2)
  let f9 := setAt f8 12 ((f8 12 + 1) % 2)
  let f10 := setAt f9 12 ((f9 12 + f9 8) % 2)
  setAt f10 13 ((f10 13 + f10 10 * f10 12) % 2)

theorem State.stepSelector {I equalFlag negFlag : Nat} {v flags : Nat → Nat}
    (s : State I v flags)
    (hindices : (equalFlag = 3 ∧ negFlag = 4) ∨ (equalFlag = 4 ∧ negFlag = 3)) :
    State (actGates (selector equalFlag negFlag) I) v
      (selectorFlags equalFlag negFlag flags) := by
  have heq : equalFlag < flagCount := by rcases hindices with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hneg : negFlag < flagCount := by rcases hindices with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have s1 := s.stepT (by decide : 0 < flagCount) (by decide : 1 < flagCount)
    (by decide : 5 < flagCount)
  have s2 := s1.stepT (by decide : 2 < flagCount) hneg (by decide : 6 < flagCount)
  have s3 := s2.stepT (by decide : 5 < flagCount) (by decide : 6 < flagCount)
    (by decide : 7 < flagCount)
  have s4 := s3.stepX (by decide : 9 < flagCount)
  have s5 := s4.stepF (by decide : 6 < flagCount) (by decide : 9 < flagCount)
  have s6 := s5.stepT (by decide : 5 < flagCount) (by decide : 9 < flagCount)
    (by decide : 10 < flagCount)
  have s7 := s6.stepT (by decide : 2 < flagCount) heq (by decide : 8 < flagCount)
  have s8 := s7.stepT (by decide : 10 < flagCount) (by decide : 8 < flagCount)
    (by decide : 11 < flagCount)
  have s9 := s8.stepX (by decide : 12 < flagCount)
  have s10 := s9.stepF (by decide : 8 < flagCount) (by decide : 12 < flagCount)
  have s11 := s10.stepT (by decide : 10 < flagCount) (by decide : 12 < flagCount)
    (by decide : 13 < flagCount)
  simpa [selector, selectorFlags, actGates_append] using s11

theorem selectorFlags_active {equalFlag negFlag : Nat} {flags : Nat → Nat}
    {targetOn offsetOn xEqual yEqual yNegEqual : Bool}
    (hindices : (equalFlag = 3 ∧ negFlag = 4) ∨ (equalFlag = 4 ∧ negFlag = 3))
    (h0 : flags 0 = boolNat targetOn) (h1 : flags 1 = boolNat offsetOn)
    (h2 : flags 2 = boolNat xEqual) (heq : flags equalFlag = boolNat yEqual)
    (hneg : flags negFlag = boolNat yNegEqual)
    (h5 : flags 5 = 0) (h6 : flags 6 = 0) (h7 : flags 7 = 0)
    (h8 : flags 8 = 0) (h9 : flags 9 = 0) (h10 : flags 10 = 0)
    (h11 : flags 11 = 0) (h12 : flags 12 = 0) (h13 : flags 13 = 0) :
    selectorFlags equalFlag negFlag flags 7 =
        boolNat (targetOn && offsetOn && (xEqual && yNegEqual)) ∧
      selectorFlags equalFlag negFlag flags 11 =
        boolNat (targetOn && offsetOn && !(xEqual && yNegEqual) &&
          (xEqual && yEqual)) ∧
      selectorFlags equalFlag negFlag flags 13 =
        boolNat (targetOn && offsetOn && !(xEqual && yNegEqual) &&
          !(xEqual && yEqual)) := by
  rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases targetOn <;> cases offsetOn <;> cases xEqual <;> cases yEqual <;>
    cases yNegEqual <;>
    simp_all [selectorFlags, boolNat, setAt]

end VQ.Curve.PointAddition.Runtime
