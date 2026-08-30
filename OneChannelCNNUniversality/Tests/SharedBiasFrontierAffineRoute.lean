import OneChannelCNNUniversality.SharedBiasFrontierAffineRoute

open OneChannelCNNUniversality

#check FrontierDirection.bias
#check affineFrontierStep
#check applyBiasedFrontierRoute
#check biasedFrontierRouteNetwork
#check sharedLayerEval_of_nonnegative_bias
#check affineFrontierStep_nonnegative
#check affineFrontierStep_injective
#check applyBiasedFrontierRoute_injective
#check biasedFrontierRouteNetwork_depth
#check biasedFrontierRouteNetwork_eval_of_nonnegative
#check biasedFrontierRouteNetwork_injectiveOn
#check eastSouthBiasedRoute_one_one
#check southEastBiasedRoute_one_one
#check eastSouth_sub_southEast
#check biasedFrontierRouteNetwork_order_sensitive

example {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (x : Image rows cols) (hx : ImageNonnegative x)
    (eastBias southBias : ℝ) (heast : 0 ≤ eastBias)
    (hsouth : 0 ≤ southBias) (hne : eastBias ≠ southBias) :
    (biasedFrontierRouteNetwork [.east, .south]
        eastBias southBias).eval x ≠
      (biasedFrontierRouteNetwork [.south, .east]
        eastBias southBias).eval x := by
  exact biasedFrontierRouteNetwork_order_sensitive
    hrows hcols x hx heast hsouth hne
