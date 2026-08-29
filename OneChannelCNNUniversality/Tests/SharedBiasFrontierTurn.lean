import OneChannelCNNUniversality.SharedBiasFrontierTurn

open OneChannelCNNUniversality

#check SouthRowsVacant
#check NorthwestTwoRegisterSeed
#check TwoDimensionalFrontierInvariant
#check iterateHorizontalAccumulation_southRowsVacant
#check iteratePascalGrid_frontierInvariant
#check twoDimensionalFrontierNetwork_depth
#check twoDimensionalFrontierNetwork_eval_of_nonnegative
#check twoDimensionalFrontierNetwork_injectiveOn_and_invariant

example {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (x : Image rows cols) (hseed : NorthwestTwoRegisterSeed x) :
    TwoDimensionalFrontierInvariant x rowSteps colSteps
      (iterateFullConv verticalAccumulationKernel rowSteps
        (iterateFullConv horizontalAccumulationKernel colSteps x)) := by
  exact iteratePascalGrid_frontierInvariant rowSteps colSteps x hseed
