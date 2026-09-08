import VQ.Euclid.LuoSelectionPermutation

namespace VQMathlib.Euclid.PackedRotationCounts

open VQ.Euclid

theorem findSource_list (want : Nat) (current : Array Nat) :
    LuoSelectionPermutation.findSource want current =
      (current.toList.findIdx? fun source => source = want).getD 0 := by
  cases current
  simp [LuoSelectionPermutation.findSource]

def listSwap (values : List Nat) (i j : Nat) : List Nat :=
  if i < values.length ∧ j < values.length then
    (values.set i values[j]!).set j values[i]!
  else values

theorem swap_list (current : Array Nat) (i j : Nat) :
    (current.swapIfInBounds i j).toList = listSwap current.toList i j := by
  unfold Array.swapIfInBounds listSwap
  split <;> rename_i hi
  · split <;> rename_i hj
    · simp [hi, hj, Array.toList_swap]
    · simp [hi, hj]
  · simp [hi]

def listStep (width distance : Nat) (state : List Nat × Nat) (position : Nat) :
    List Nat × Nat :=
  let want := LuoSelectionPermutation.desiredSource width distance position
  if state.1[position]! = want then state
  else
    let found := (state.1.findIdx? fun source => source = want).getD 0
    (listSwap state.1 position found, state.2 + 1)

def summary (state : LuoSelectionPermutation.SelectionState) : List Nat × Nat :=
  (state.current.toList, state.swapsRev.length)

theorem step_summary (width distance position : Nat)
    (state : LuoSelectionPermutation.SelectionState) :
    summary (LuoSelectionPermutation.selectionStep width distance state position) =
      listStep width distance (summary state) position := by
  simp only [LuoSelectionPermutation.selectionStep, listStep, summary,
    Array.getElem!_toList, findSource_list]
  split <;> simp [summary, swap_list]

theorem fold_summary (width distance : Nat) (positions : List Nat)
    (state : LuoSelectionPermutation.SelectionState) :
    summary (positions.foldl (LuoSelectionPermutation.selectionStep width distance) state) =
      positions.foldl (listStep width distance) (summary state) := by
  induction positions generalizing state with
  | nil => rfl
  | cons position positions ih =>
    simp only [List.foldl_cons, ih, step_summary]

def swapCount (width distance : Nat) : Nat :=
  ((List.range width).foldl (listStep width distance) (List.range width, 0)).2

theorem selectionSwaps_length (width distance : Nat) :
    (LuoSelectionPermutation.selectionSwaps width distance).length =
      swapCount width distance := by
  have h := congrArg Prod.snd (fold_summary width distance (List.range width)
    (LuoSelectionPermutation.selectionInitial width))
  simpa [summary, swapCount, LuoSelectionPermutation.selectionSwaps,
    LuoSelectionPermutation.selectionResult, LuoSelectionPermutation.selectionInitial] using h

set_option maxRecDepth 4096 in
theorem firstRotation :
    (LuoSelectionPermutation.selectionSwaps 259 1).length = 258 := by
  rw [selectionSwaps_length]
  decide +kernel

end VQMathlib.Euclid.PackedRotationCounts
