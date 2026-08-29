import OneChannelCNNUniversality.SharedBiasFiniteSelection

open OneChannelCNNUniversality

/-- A concrete one-request schedule exercises the dependent constructor: its
tail dimensions are computed from the first selector's expansion. -/
def oneRequestSchedule : SuccessorSelectionSchedule 1 1 :=
  .cons 1 0 ⟨0, by omega⟩ ⟨0, by omega⟩ 0 (by omega) (by omega)
    (.nil _ _)

example : oneRequestSchedule.length = 1 := rfl

example (rows cols : ℕ) :
    (SuccessorSelectionSchedule.nil rows cols).length = 0 := rfl

example (rows cols : ℕ) :
    (SuccessorSelectionSchedule.nil rows cols).finalRows = rows := rfl

example (rows cols : ℕ) :
    (SuccessorSelectionSchedule.nil rows cols).finalCols = cols := rfl

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} (F : X → Image inRows inCols)
    (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
    (schedule : SuccessorSelectionSchedule rows cols)
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule) :
    SharedBiasNetworkTo 2 2 inRows inCols
      schedule.finalRows schedule.finalCols :=
  compiled.finalNetwork

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {inRows inCols rows cols : ℕ}
    (F : X → Image inRows inCols) (hF : ContinuousFeatureOn K F)
    (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
    (hhead : 0 < head.net.depth)
    (schedule : SuccessorSelectionSchedule rows cols) :
    Nonempty (CompiledSuccessorSelectionSchedule K F head schedule) := by
  exact exists_compiledSuccessorSelectionSchedule hK F hF head hhead schedule

#check SuccessorSelectionSchedule
#check CompiledSuccessorSelectionSchedule.finalNetwork
#check exists_compiledSuccessorSelectionSchedule
