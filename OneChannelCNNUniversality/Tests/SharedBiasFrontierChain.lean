import OneChannelCNNUniversality.SharedBiasFrontierChain

open OneChannelCNNUniversality

#check EastTailVacant
#check HorizontalFrontierInvariant
#check iterateHorizontalAccumulation_frontierInvariant
#check horizontalFrontierNetwork_eval_of_nonnegative
#check horizontalFrontierNetwork_injectiveOn_and_invariant

example {rows cols : ℕ} (steps : ℕ) (x : Image rows cols)
    (htail : EastTailVacant x) :
    HorizontalFrontierInvariant x steps
      (iterateFullConv horizontalAccumulationKernel steps x) := by
  exact iterateHorizontalAccumulation_frontierInvariant steps x htail
