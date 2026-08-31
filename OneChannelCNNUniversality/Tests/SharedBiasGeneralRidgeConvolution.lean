import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution

/-!
# Regression tests for the arbitrary-width polynomial-to-convolution bridge
-/

namespace OneChannelCNNUniversality

#check bilinearKernel
#check fullConv_bilinearKernel_nat
#check linearPolynomial
#check bilinearKernelPolynomial
#check rowPolynomial
#check rowPolynomial_coeff
#check BilinearKernelFactor
#check BilinearKernelFactor.kernel
#check BilinearKernelFactor.polynomial
#check horizontalProduct
#check verticalOne
#check bivariateProduct
#check bivariateProduct_coeff_one
#check fullConvChain
#check rowPolynomial_fullConvChain_zero
#check rowPolynomial_fullConvChain_one
#check fullConvChain_row_one_reversed_dot
#check zeroBiasBilinearNetwork
#check LinearBranchAlong
#check zeroBiasBilinearNetwork_eval_eq_fullConvChain
#check zeroBiasBilinearNetwork_natural_target_reversed_dot
#check generalRidgeKernelFactor
#check generalRidgeFactorList
#check generalRidgeFactorList_length
#check generalRidgeFactorList_bivariateProduct
#check generalRidgeFullConv
#check generalRidgeFullConv_target
#check generalRidgeFullConv_north

example (w : Fin 1 → ℝ) (η : Fin 0 → ℝ) (x : Image 1 1) :
    zeroExtend (generalRidgeFullConv w η x) 1 0 = 0 := by
  have hlist : generalRidgeFactorList w η = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact generalRidgeFactorList_length w η
  rw [generalRidgeFullConv, hlist]
  simp [grownSize, zeroExtend]

end OneChannelCNNUniversality
