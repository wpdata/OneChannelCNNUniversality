import OneChannelCNNUniversality.SpatialInteractionDepthLowerBound

/-!
# Regression tests for anisotropic spatial-interaction depth lower bounds
-/

namespace OneChannelCNNUniversality

#check RectReceptiveAgree
#check rectReceptiveAgree_layerEval
#check network_eval_eq_of_rectReceptiveAgree
#check twoSiteSignImage
#check twoSiteProduct
#check continuous_twoSiteProduct
#check spatialUnitCube
#check spatialUnitCube_compact
#check twoSite_mixedDifference_zero
#check twoSite_four_point_error_lower_bound
#check spatialInteraction_depth_requirements_of_error_lt_one
#check sharedBias_spatialInteraction_depth_requirements_of_error_lt_one

example (rowDistance colDistance : ℕ) (left right : ℝ)
    (hdistinct : 0 < rowDistance ∨ 0 < colDistance) :
    twoSiteProduct rowDistance colDistance
        (twoSiteSignImage rowDistance colDistance left right) = left * right := by
  exact twoSiteProduct_twoSiteSignImage
    rowDistance colDistance left right hdistinct

end OneChannelCNNUniversality
