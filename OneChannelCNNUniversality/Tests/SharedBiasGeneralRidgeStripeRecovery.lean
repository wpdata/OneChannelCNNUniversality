import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeRecovery

/-! # Regression tests for signed-stripe state recovery -/

namespace OneChannelCNNUniversality

open Set

#check generalRidgeStripeVariableNorthRow
#check generalRidgeStripeVariableSeed_row_zero_eq_input
#check generalRidgeStripeVariableNorthRow_injective
#check generalRidgeStripeVariableNorthLinearMap
#check generalRidgeStripeVariableNorthLinearMap_injective
#check generalRidgeStripeVariableNorthLeftInverse
#check generalRidgeStripeVariableNorthLeftInverse_apply
#check generalRidgeStripeNorthProjection
#check generalRidgeStripeNorthOffset
#check generalRidgeStripeAffineRecoveryLinearMap
#check generalRidgeStripeAffineReadoutWeight
#check generalRidgeStripeAffineReadoutConstant
#check generalRidgeStripeAffineReadout_spec
#check generalRidgeStripeNetwork_row_zero_eq_code_add_offset
#check exists_injective_generalRidgeStripeNetwork_on_compact
#check exists_generalRidgeStripeNetwork_with_affine_readout_on_compact

#print axioms generalRidgeStripeVariableNorthRow_injective
#print axioms generalRidgeStripeVariableNorthLeftInverse_apply
#print axioms generalRidgeStripeAffineReadout_spec
#print axioms generalRidgeStripeNetwork_row_zero_eq_code_add_offset
#print axioms exists_injective_generalRidgeStripeNetwork_on_compact
#print axioms exists_generalRidgeStripeNetwork_with_affine_readout_on_compact

/-- The smallest-width variable northern code is faithful for every nonzero
reciprocal scale. -/
example (w : Fin 2 → ℝ) (T : ℝ) (hT : T ≠ 0) :
    Function.Injective (generalRidgeStripeVariableNorthRow w T) :=
  generalRidgeStripeVariableNorthRow_injective w T hT

example (w : Fin 2 → ℝ) (T : ℝ) (hT : T ≠ 0)
    (x : Image 1 2) :
    generalRidgeStripeVariableNorthLeftInverse w T
        (generalRidgeStripeVariableNorthLinearMap w T x) = x := by
  exact generalRidgeStripeVariableNorthLeftInverse_apply w T hT x

end OneChannelCNNUniversality
