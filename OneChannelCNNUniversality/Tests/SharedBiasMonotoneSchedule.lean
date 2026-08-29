import OneChannelCNNUniversality.SharedBiasMonotoneSchedule

open OneChannelCNNUniversality

def twoNorthwestRequests : SuccessorSelectionSchedule 1 1 :=
  .cons 1 0 ⟨0, by omega⟩ ⟨0, by omega⟩ 0 (by omega) (by omega)
    (.cons
      (protectedSelectionSize (1 + 2 - 1) 1 0)
      (protectedSelectionSize (1 + 2 - 1) 1 0)
      ⟨0, by omega⟩ ⟨0, by omega⟩ 1 (by omega) (by omega)
      (.nil _ _))

example : twoNorthwestRequests.NorthwestTargeted := by
  simp [twoNorthwestRequests, SuccessorSelectionSchedule.NorthwestTargeted]

example (n rowSteps extraColSteps : ℕ) :
    2 ≤ protectedSelectionSize n rowSteps extraColSteps := by
  exact two_le_protectedSelectionSize n rowSteps extraColSteps

#check CompiledSuccessorSelectionSchedule.monotoneCode_and_injectiveOn
#check CompiledSuccessorSelectionSchedule.preserves_northwestMonotoneCode
#check CompiledSuccessorSelectionSchedule.finalNetwork_injectiveOn_of_northwestMonotoneCode
#check northwestMonotoneCodeOn_adjacentCopy
#check exists_injective_compiledNorthwestSchedule
