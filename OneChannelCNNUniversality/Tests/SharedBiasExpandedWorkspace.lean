import OneChannelCNNUniversality

/-! # Regression tests for the expanded workspace interface -/

namespace OneChannelCNNUniversality

#check expandedWorkspaceRidgeKernel
#check nondestructiveBoundaryTransform_oneTwo_decode_zero
#check nondestructiveBoundaryTransform_oneTwo_decode_one
#check expandedWorkspaceRidgeKernel_preactivation
#check exists_depthThree_expandedWorkspace_ridge_on_compact
#check expandedWorkspacePackedWeights
#check expandedWorkspacePackedFullConv_target_zero
#check expandedWorkspacePackedFullConv_target_one

#print axioms nondestructiveBoundaryTransform_oneTwo_decode_zero
#print axioms nondestructiveBoundaryTransform_oneTwo_decode_one
#print axioms expandedWorkspaceRidgeKernel_preactivation
#print axioms exists_depthThree_expandedWorkspace_ridge_on_compact
#print axioms expandedWorkspacePackedFullConv_target_zero
#print axioms expandedWorkspacePackedFullConv_target_one

/-- The expanded interface specializes to an exact three-layer realization
of an arbitrary affine ridge on the compact square `[-1,1]^2`. -/
example (w : Fin 2 → ℝ) (theta : ℝ) :
    ∃ net : SharedBiasNetworkTo 2 2 1 2 4 5,
      net.net.depth = 3 ∧
        ∀ x ∈ twoPointSymmetricBox 1,
          net.eval x 1 1 =
            relu (w 0 * x 0 0 + w 1 * x 0 1 + theta) := by
  exact exists_depthThree_expandedWorkspace_ridge_on_compact
    (twoPointSymmetricBox_compact 1) w theta

end OneChannelCNNUniversality
