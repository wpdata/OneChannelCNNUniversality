import OneChannelCNNUniversality.SharedBiasCarrierDepthOptimality

/-! # Regression tests for sharp carrier-initialization depth -/

namespace OneChannelCNNUniversality

#check SpatiallyNonuniform
#check sharedLayerEval_zero
#check oneLayer_constant_on_zero_mem_eq_relu_bias
#check not_oneLayer_nonuniform_inputIndependent_on_zero_mem
#check twoLayerLeftBoundaryCarrierNetwork
#check twoLayerLeftBoundaryCarrierNetwork_depth
#check twoLayerLeftBoundaryCarrierNetwork_eval
#check twoLayerLeftBoundaryCarrier_nonuniform
#check nonuniform_inputIndependent_carrier_depth_two_sharp
#check nonuniform_inputIndependent_carrier_depth_two_sharp_on_symmetricBox

#print axioms not_oneLayer_nonuniform_inputIndependent_on_zero_mem
#print axioms nonuniform_inputIndependent_carrier_depth_two_sharp
#print axioms nonuniform_inputIndependent_carrier_depth_two_sharp_on_symmetricBox

/-- On the concrete compact box `[-1,1]^2`, two layers are sufficient and
one layer is insufficient for initializing a nonuniform carrier independent
of the input. -/
example :
    (∃ (net : SharedBiasNetworkTo 2 2 1 2
          ((1 + 2 - 1) + 2 - 1) ((2 + 2 - 1) + 2 - 1))
        (carrier : Image ((1 + 2 - 1) + 2 - 1) ((2 + 2 - 1) + 2 - 1)),
        net.net.depth = 2 ∧ SpatiallyNonuniform carrier ∧
          ∀ x ∈ twoPointSymmetricBox 1, net.eval x = carrier) ∧
      (∀ (w : Kernel 2 2) (b : ℝ),
        ¬ ∃ carrier : Image (1 + 2 - 1) (2 + 2 - 1),
          SpatiallyNonuniform carrier ∧
            ∀ x ∈ twoPointSymmetricBox 1,
              sharedLayerEval w b x = carrier) := by
  exact nonuniform_inputIndependent_carrier_depth_two_sharp_on_symmetricBox
    1 (by norm_num)

end OneChannelCNNUniversality
