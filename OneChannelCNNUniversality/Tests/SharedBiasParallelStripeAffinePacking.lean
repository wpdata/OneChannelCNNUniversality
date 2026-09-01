import OneChannelCNNUniversality.SharedBiasParallelStripeAffinePacking

namespace OneChannelCNNUniversality

#check parallelStripeAffineSeed
#check continuousFeatureOn_parallelStripeAffineSeed
#check parallelStripePackedFullConv_affine_target_zero
#check parallelStripePackedFullConv_affine_target_one
#check parallelStripePackedFinalVariable
#check parallelStripePackedFinalVariable_affine_target_zero
#check parallelStripePackedFinalVariable_affine_target_one

example (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w)
          (parallelStripeAffineSeed ε θ x)) 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) :=
  parallelStripePackedFullConv_affine_target_zero ε w θ x

example (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w)
          (parallelStripeAffineSeed ε θ x)) 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) :=
  parallelStripePackedFullConv_affine_target_one ε w θ x

end OneChannelCNNUniversality
