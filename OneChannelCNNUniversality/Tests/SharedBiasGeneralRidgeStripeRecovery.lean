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
#check exists_injective_generalRidgeStripeNetwork_on_compact

#print axioms generalRidgeStripeVariableNorthRow_injective
#print axioms generalRidgeStripeVariableNorthLeftInverse_apply
#print axioms exists_injective_generalRidgeStripeNetwork_on_compact

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
