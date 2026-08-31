import OneChannelCNNUniversality.SharedBiasGeneralRidgeOptimality

/-!
# Regression tests for the sharp endpoint-ridge depth bound
-/

namespace OneChannelCNNUniversality

#check endpointReluSum
#check endpointReluSum_endpointSignImage
#check continuous_endpointReluSum
#check endpointReluSumWeights
#check endpointReluSumWeights_dot
#check endpointReluSum_four_point_error_lower_bound
#check depth_ge_endpointDistance_of_endpointReluSum_error_lt_half
#check sharedBiasNetworkToPointReadoutWeight
#check sharedBiasNetworkTo_pointReadout
#check exists_exactDepth_endpointReluSum_on_corners

#print axioms endpointReluSum_four_point_error_lower_bound
#print axioms depth_ge_endpointDistance_of_endpointReluSum_error_lt_half
#print axioms exists_exactDepth_endpointReluSum_on_corners

/-- The endpoint ridge takes values `0,0,0,2` on the four sign corners. -/
example (L : ℕ) :
    endpointReluSum L (endpointSignImage L (-1) (-1)) = 0 ∧
      endpointReluSum L (endpointSignImage L (-1) 1) = 0 ∧
      endpointReluSum L (endpointSignImage L 1 (-1)) = 0 ∧
      endpointReluSum L (endpointSignImage L 1 1) = 2 := by
  norm_num [endpointReluSum_endpointSignImage, relu]

/-- Strict error below one half at distance three forces depth at least
three. -/
example (net : SharedBiasNetwork 2 2 1 4)
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (happrox : ∀ x ∈ endpointCornerSet 2,
      |net.realize weight constant x - endpointReluSum 2 x| < (1 : ℝ) / 2) :
    3 ≤ net.depth := by
  exact depth_ge_endpointDistance_of_endpointReluSum_error_lt_half
    2 net weight constant happrox

/-- At endpoint distance two, the certified upper construction has exactly
the matching depth two. -/
example :
    ∃ (net : SharedBiasNetworkTo 2 2 1 3 3 5)
      (weight : Image net.net.outRows net.net.outCols),
      net.net.depth = 2 ∧
        ∀ x ∈ endpointCornerSet 1,
          net.net.realize weight 0 x = endpointReluSum 1 x := by
  exact exists_exactDepth_endpointReluSum_on_corners (n := 0)

end OneChannelCNNUniversality
