import OneChannelCNNUniversality.SharedBiasGeneralRidgePolynomial

/-!
# Regression tests for the arbitrary-width ridge polynomial factorization
-/

namespace OneChannelCNNUniversality

#check generalRidgeNode
#check generalRidgeNode_injective
#check generalRidgeNodalFactor
#check generalRidgeNodalProduct
#check generalRidgeNodalComplement
#check generalRidgeNodalProduct_monic
#check generalRidgeNodalProduct_natDegree
#check generalRidgeTargetPolynomial
#check generalRidgeTargetPolynomial_coeff
#check generalRidgeTargetPolynomial_reversed_dot
#check generalRidgeTargetPolynomial_zero
#check generalRidgeResidualPolynomial
#check generalRidgeResidualPolynomial_degree_lt
#check generalRidgeNormalization
#check generalRidgeBeta
#check generalRidgeTargetPolynomial_decomposition
#check generalRidgeLowerFactor
#check generalRidgeLowerFactor_decomposition
#check generalRidgeCoeffOne_product
#check generalRidgeBiFactor
#check generalRidgeBiProduct_vertical_one
#check exists_generalRidgeLeadingAllocation
#check exists_generalRidgeBiProduct_vertical_one

open Polynomial

example (w : Fin 2 → ℝ) :
    (generalRidgeTargetPolynomial w).coeff 0 = w 1 := by
  simpa using generalRidgeTargetPolynomial_coeff w (0 : Fin 2)

example (w : Fin 2 → ℝ) :
    (generalRidgeTargetPolynomial w).coeff 1 = w 0 := by
  simpa using generalRidgeTargetPolynomial_coeff w (1 : Fin 2)

example :
    generalRidgeNodalProduct 3 = (X + 1) * (X + 2) * (X + 3) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [generalRidgeNodalProduct, hu]
  simp [generalRidgeNodalFactor]
  ring

end OneChannelCNNUniversality
