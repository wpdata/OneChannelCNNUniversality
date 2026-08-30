import OneChannelCNNUniversality.SharedBiasFrontierRoute

open OneChannelCNNUniversality

#check FrontierDirection
#check FrontierDirection.kernel
#check eastStepCount
#check southStepCount
#check applyFrontierRoute
#check frontierRouteNetwork
#check fullConvImage_horizontal_vertical_commute
#check applyFrontierRoute_eq_pascalGrid
#check applyFrontierRoute_injective
#check frontierRouteNetwork_depth
#check frontierRouteNetwork_eval_of_nonnegative
#check frontierRouteNetwork_injectiveOn_and_invariant

example {rows cols : ℕ} (x : Image rows cols)
    (hseed : NorthwestTwoRegisterSeed x) :
    TwoDimensionalFrontierInvariant x 2 2
      (applyFrontierRoute
        [.east, .south, .east, .south] x) := by
  exact applyFrontierRoute_frontierInvariant
    [.east, .south, .east, .south] x hseed
