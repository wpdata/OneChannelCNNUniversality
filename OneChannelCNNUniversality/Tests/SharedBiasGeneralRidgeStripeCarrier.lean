import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeCarrier

/-!
# Regression tests for the signed-stripe proper-prefix carrier
-/

namespace OneChannelCNNUniversality

open Polynomial

#check generalRidgeStripeOriginalPrefixVerticalOne
#check generalRidgeStripeProperPrefix_verticalOne
#check rowPolynomial_constantTwoStripe
#check generalRidgeStripeProperPrefix_carrier_row_zero
#check generalRidgeStripeProperPrefix_carrier_row_one
#check generalRidgeStripeProperPrefix_carrier_row_zero_coeff
#check generalRidgeStripeProperPrefix_carrier_row_one_coeff
#check generalRidgeStripePrefixErrorBound
#check generalRidgeStripePrefixErrorBound_nonneg
#check generalRidgeStripePrefixErrorBound_coeff_abs_le
#check generalRidgeStripeCarrierThreshold
#check generalRidgeStripeCarrierThreshold_one_le
#check northTwoUnitLowerAlong_of_take_fullConvChain_unitLower
#check generalRidgeStripeTwistedProperFactors_take_eq_properPrefix
#check generalRidgeStripeProperPrefix_carrier_unitLower
#check generalRidgeStripeTwistedProperFactors_unitLower_of_large
#check exists_generalRidgeStripeTwistedProperFactors_unitLower_threshold

/-- The public theorem includes the shortest nontrivial schedule and is
upward closed in the reciprocal scale. -/
example (w : Fin 2 → ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      NorthTwoUnitLowerAlong
        (generalRidgeStripeTwistedProperFactors (n := 0) w T)
        (constantImage 2 3 2) := by
  exact exists_generalRidgeStripeTwistedProperFactors_unitLower_threshold w

/-- The explicit threshold theorem itself covers the boundary column of the
shortest nonempty proper prefix. -/
example (w : Fin 2 → ℝ) (T : ℝ)
    (hT : generalRidgeStripeCarrierThreshold w ≤ T) :
    ∀ p : Fin (grownSize 2 2
        (generalRidgeStripeProperPrefix (n := 0) w T 1).length),
      (p : ℕ) ≤ 1 →
      ∀ q : Fin (grownSize 2 3
          (generalRidgeStripeProperPrefix (n := 0) w T 1).length),
        1 ≤ fullConvChain
          (generalRidgeStripeProperPrefix (n := 0) w T 1)
          (constantImage 2 3 2) p q := by
  exact generalRidgeStripeProperPrefix_carrier_unitLower
    w T hT (by omega)

#print axioms generalRidgeStripeProperPrefix_carrier_row_zero
#print axioms generalRidgeStripeProperPrefix_carrier_row_one
#print axioms generalRidgeStripePrefixErrorBound_coeff_abs_le
#print axioms northTwoUnitLowerAlong_of_take_fullConvChain_unitLower
#print axioms generalRidgeStripeProperPrefix_carrier_unitLower
#print axioms generalRidgeStripeTwistedProperFactors_unitLower_of_large
#print axioms exists_generalRidgeStripeTwistedProperFactors_unitLower_threshold

end OneChannelCNNUniversality
