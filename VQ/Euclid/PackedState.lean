/-
Computational-basis encoding for the 571-wire Euclidean core.
-/
import VQ.Euclid.PackedStepLayout
import VQ.Euclid.StepDomain

namespace VQ
namespace Euclid
namespace PackedState

open Reversible

def encoded (s : State) : Nat :=
  PackedStepLayout.layout.pack
    [encodeWork1 256 s, encodeWork2 256 s,
      encodeLength 9 s.lenT, encodeLength 9 s.lenQ,
      encodeLength 8 s.lenRPrime, 0, encodeLength 9 s.shift,
      boolValue s.phase1, boolValue s.phase2, boolValue s.iter,
      boolValue s.sign, 0]

theorem encoded_lt (s : State) :
    encoded s < 2 ^ PackedStepLayout.width := by
  exact Layout.pack_lt _ _

theorem read_encoded (s : State) (k : Nat) :
    PackedStepLayout.layout.read (encoded s) k =
      ([encodeWork1 256 s, encodeWork2 256 s,
        encodeLength 9 s.lenT, encodeLength 9 s.lenQ,
        encodeLength 8 s.lenRPrime, 0, encodeLength 9 s.shift,
        boolValue s.phase1, boolValue s.phase2, boolValue s.iter,
        boolValue s.sign, 0].getD k 0) %
        2 ^ PackedStepLayout.layout.size k := by
  exact Layout.read_pack _ _ _

theorem read_workOne (s : State) :
    readField (encoded s) PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 s % 2 ^ 259 := by
  simpa [PackedStepLayout.layout, PackedStepLayout.workOneOffset,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] using read_encoded s 0

theorem read_workTwo (s : State) :
    readField (encoded s) PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 s := by
  have h := read_encoded s 1
  have hfit : encodeWork2 256 s < 2 ^ 259 := by
    simpa [workWidth, encodeWork2] using
      rotatePositionsLeft_lt 259 s.shift (encodeWork2Raw 256 s)
  simpa [PackedStepLayout.layout, PackedStepLayout.workTwoOffset,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size, Nat.mod_eq_of_lt hfit] using h

theorem read_lengthT (s : State) :
    readField (encoded s) PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
  have h := read_encoded s 2
  simp [PackedStepLayout.layout,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] at h
  have hfit : encodeLength 9 s.lenT < 512 := by
    simpa using encodeLength_lt 9 s.lenT
  rw [Nat.mod_eq_of_lt hfit] at h
  exact h

theorem read_lengthQ (s : State) :
    readField (encoded s) PackedStepLayout.lengthQOffset 9 =
      encodeLength 9 s.lenQ := by
  have h := read_encoded s 3
  simp [PackedStepLayout.layout,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] at h
  have hfit : encodeLength 9 s.lenQ < 512 := by
    simpa using encodeLength_lt 9 s.lenQ
  rw [Nat.mod_eq_of_lt hfit] at h
  exact h

theorem read_lengthRPrime (s : State) :
    readField (encoded s) PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime := by
  have h := read_encoded s 4
  simp [PackedStepLayout.layout,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] at h
  have hfit : encodeLength 8 s.lenRPrime < 256 := by
    simpa using encodeLength_lt 8 s.lenRPrime
  rw [Nat.mod_eq_of_lt hfit] at h
  exact h

theorem read_extension (s : State) :
    bitValue (encoded s) PackedStepLayout.extensionWire = 0 := by
  rw [← readField_one]
  simpa [PackedStepLayout.layout, PackedStepLayout.extensionWire,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] using read_encoded s 5

theorem read_shift (s : State) :
    readField (encoded s) PackedStepLayout.shiftOffset 9 =
      encodeLength 9 s.shift := by
  have h := read_encoded s 6
  simp [PackedStepLayout.layout,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] at h
  have hfit : encodeLength 9 s.shift < 512 := by
    simpa using encodeLength_lt 9 s.shift
  rw [Nat.mod_eq_of_lt hfit] at h
  exact h

private theorem boolValue_lt (b : Bool) : boolValue b < 2 := by
  cases b <;> simp [boolValue]

theorem read_phaseOne (s : State) :
    bitValue (encoded s) PackedStepLayout.phaseOneWire =
      boolValue s.phase1 := by
  rw [← readField_one]
  simpa [PackedStepLayout.layout, PackedStepLayout.phaseOneWire,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (boolValue_lt s.phase1)] using read_encoded s 7

theorem read_phaseTwo (s : State) :
    bitValue (encoded s) PackedStepLayout.phaseTwoWire =
      boolValue s.phase2 := by
  rw [← readField_one]
  simpa [PackedStepLayout.layout, PackedStepLayout.phaseTwoWire,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (boolValue_lt s.phase2)] using read_encoded s 8

theorem read_iteration (s : State) :
    bitValue (encoded s) PackedStepLayout.iterationWire =
      boolValue s.iter := by
  rw [← readField_one]
  simpa [PackedStepLayout.layout, PackedStepLayout.iterationWire,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (boolValue_lt s.iter)] using read_encoded s 9

theorem read_sign (s : State) :
    bitValue (encoded s) PackedStepLayout.signWire = boolValue s.sign := by
  rw [← readField_one]
  simpa [PackedStepLayout.layout, PackedStepLayout.signWire,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size,
    Nat.mod_eq_of_lt (boolValue_lt s.sign)] using read_encoded s 10

theorem read_pool (s : State) :
    readField (encoded s) PackedStepLayout.poolOffset 13 = 0 := by
  simpa [PackedStepLayout.layout, PackedStepLayout.poolOffset,
    PackedStepLayout.workWidth, PackedStepLayout.lengthWidth,
    PackedStepLayout.remainderLengthWidth, PackedStepLayout.poolWidth,
    Layout.read, Layout.offset, Layout.size] using read_encoded s 11

theorem read_pool_subfield {s : State} {offset width : Nat}
    (hlow : PackedStepLayout.poolOffset ≤ offset)
    (hhigh : offset + width ≤ PackedStepLayout.poolOffset + 13) :
    readField (encoded s) offset width = 0 :=
  readField_sub_zero hlow hhigh (read_pool s)

theorem encoded_write_shiftWorkTwo
    (newShift : Nat) (s : State)
    (hlengthQ : s.lenQ = 0) :
    writeField
        (writeField (encoded s) PackedStepLayout.shiftOffset 9
          (encodeLength 9 newShift))
        PackedStepLayout.workTwoOffset 259
        (rotatePositionsLeft 259 newShift (encodeWork2Raw 256 s)) =
      encoded { s with shift := newShift } := by
  let L := PackedStepLayout.layout
  let newWorkTwo :=
    rotatePositionsLeft 259 newShift (encodeWork2Raw 256 s)
  change L.write
      (L.write (encoded s) 6 (encodeLength 9 newShift))
      1 newWorkTwo = encoded { s with shift := newShift }
  have hshiftFit : encodeLength 9 newShift < 2 ^ L.size 6 := by
    have hsize : L.size 6 = 9 := by decide
    rw [hsize]
    exact encodeLength_lt 9 newShift
  have hworkTwoFit : newWorkTwo < 2 ^ L.size 1 := by
    have hsize : L.size 1 = 259 := by decide
    rw [hsize]
    exact rotatePositionsLeft_lt 259 newShift (encodeWork2Raw 256 s)
  have hreads := read_write_two (l := L)
    (i := encoded s)
    (k₁ := 6) (v₁ := encodeLength 9 newShift)
    (k₂ := 1) (v₂ := newWorkTwo) (by decide) hshiftFit hworkTwoFit
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt (encoded_lt s)))
    (encoded_lt { s with shift := newShift })
  intro k hk
  have hk' : k < 12 := by
    simpa [L, PackedStepLayout.layout] using hk
  interval_cases k
  · rw [hreads.2.2 0 (by decide) (by decide), read_encoded, read_encoded]
    simp [encodeWork1, hlengthQ, reverseBits]
  · rw [hreads.2.1, read_encoded]
    change newWorkTwo = newWorkTwo % 2 ^ 259
    have hsize : L.size 1 = 259 := by decide
    have hfit : newWorkTwo < 2 ^ 259 := by rwa [← hsize]
    rw [Nat.mod_eq_of_lt hfit]
  · rw [hreads.2.2 2 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 3 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 4 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 5 (by decide) (by decide), read_encoded, read_encoded]
    simp [PackedStepLayout.layout, Layout.size]
  · rw [hreads.1, read_encoded]
    change encodeLength 9 newShift = encodeLength 9 newShift % 2 ^ 9
    rw [Nat.mod_eq_of_lt (encodeLength_lt 9 newShift)]
  · rw [hreads.2.2 7 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 8 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 9 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 10 (by decide) (by decide), read_encoded, read_encoded]
    simp
  · rw [hreads.2.2 11 (by decide) (by decide), read_encoded, read_encoded]
    simp

theorem encoded_write_phaseSign
    (s : State) (phaseOne phaseTwo sign : Bool) :
    writeField
        (writeField
          (writeField (encoded s) PackedStepLayout.phaseOneWire 1
            (boolValue phaseOne))
          PackedStepLayout.phaseTwoWire 1 (boolValue phaseTwo))
        PackedStepLayout.signWire 1 (boolValue sign) =
      encoded { s with
        phase1 := phaseOne
        phase2 := phaseTwo
        sign := sign } := by
  let L := PackedStepLayout.layout
  have hleft :
      L.write
          (L.write
            (L.write (encoded s) 7 (boolValue phaseOne))
            8 (boolValue phaseTwo))
          10 (boolValue sign) =
        writeField
          (writeField
            (writeField (encoded s) PackedStepLayout.phaseOneWire 1
              (boolValue phaseOne))
            PackedStepLayout.phaseTwoWire 1 (boolValue phaseTwo))
          PackedStepLayout.signWire 1 (boolValue sign) := by
    rfl
  rw [← hleft]
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt (Layout.write_lt (encoded_lt s))))
    (encoded_lt _)
  intro k hk
  have hk' : k < 12 := by
    simpa [L, PackedStepLayout.layout] using hk
  have hphaseOneFit : boolValue phaseOne < 2 ^ L.size 7 := by
    simpa [L, PackedStepLayout.layout, Layout.size] using
      boolValue_lt phaseOne
  have hphaseTwoFit : boolValue phaseTwo < 2 ^ L.size 8 := by
    simpa [L, PackedStepLayout.layout, Layout.size] using
      boolValue_lt phaseTwo
  have hsignFit : boolValue sign < 2 ^ L.size 10 := by
    simpa [L, PackedStepLayout.layout, Layout.size] using boolValue_lt sign
  by_cases hkSign : k = 10
  · subst k
    rw [Layout.read_write_self hsignFit]
    rw [read_encoded]
    exact (Nat.mod_eq_of_lt (by simpa [L] using hsignFit)).symm
  by_cases hkPhaseTwo : k = 8
  · subst k
    rw [Layout.read_write_ne (by omega),
      Layout.read_write_self hphaseTwoFit]
    rw [read_encoded]
    exact (Nat.mod_eq_of_lt (by simpa [L] using hphaseTwoFit)).symm
  by_cases hkPhaseOne : k = 7
  · subst k
    rw [Layout.read_write_ne (by omega),
      Layout.read_write_ne (by omega),
      Layout.read_write_self hphaseOneFit]
    rw [read_encoded]
    exact (Nat.mod_eq_of_lt (by simpa [L] using hphaseOneFit)).symm
  rw [Layout.read_write_ne hkSign, Layout.read_write_ne hkPhaseTwo,
    Layout.read_write_ne hkPhaseOne]
  interval_cases k <;>
    first
    | omega
    | simp [read_encoded, encodeWork1, encodeWork2, encodeWork2Raw,
        boolValue]

end PackedState
end Euclid
end VQ
