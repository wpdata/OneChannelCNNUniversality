import OneChannelCNNUniversality.SharedBiasDepthLowerBound

open OneChannelCNNUniversality

#check ReceptiveAgree
#check receptiveAgree_sharedLayerEval
#check sharedBiasNetwork_eval_eq_of_receptiveAgree
#check endpointSignImage
#check endpointProduct
#check continuous_endpointProduct
#check endpointCornerSet_finite
#check endpointCornerSet_compact
#check endpoint_eval_eq_of_same_left
#check endpoint_eval_eq_of_same_right
#check endpoint_mixedDifference_zero
#check endpoint_four_point_error_lower_bound
#check depth_ge_endpointDistance_of_error_lt_one

example (L : ℕ) (a b : ℝ) :
    endpointProduct L (endpointSignImage L a b) = a * b := by
  exact endpointProduct_endpointSignImage L a b
