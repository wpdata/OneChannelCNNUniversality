import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripePrefix

/-!
# Regression tests for proper prefixes of the signed stripe schedule
-/

namespace OneChannelCNNUniversality

open Polynomial

#check generalRidgeStripeProperPrefix
#check generalRidgeStripeTwistedProperFactors
#check generalRidgeStripeTwistedProperFactors_length
#check generalRidgeStripeTwistedProperFactors_eq_take
#check generalRidgeStripeProperPrefix_eq_take_twistedFactors
#check generalRidgeStripeProperPrefix_horizontalProduct
#check generalRidgeStripeTwistedFactors_take_horizontalProduct
#check generalRidgeStripeProperPrefix_coeff_nonneg
#check generalRidgeStripeProperPrefix_coeff_one_le
#check generalRidgeNodalProduct_eval_one
#check generalRidgeNodalProduct_mul_boxcar_coeff_one_le
#check generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_one_le
#check generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_pos
#check generalRidgeStripeProperPrefix_boxcar_coeff_eq_factorial
#check generalRidgeStripeProperPrefix_boxcar_coeff_one_le

/-- The empty proper prefix is the empty nodal product. -/
example (w : Fin 2 → ℝ) (T : ℝ) :
    horizontalProduct
        (generalRidgeStripeProperPrefix (n := 0) w T 0) = 1 := by
  simpa [generalRidgeNodalProduct] using
    (generalRidgeStripeProperPrefix_horizontalProduct
      (n := 0) w T (k := 0) (by omega))

/-- At the shortest stripe depth, the only nonempty proper prefix is
`X + 1`. -/
example (w : Fin 2 → ℝ) (T : ℝ) :
    horizontalProduct
        (generalRidgeStripeProperPrefix (n := 0) w T 1) = X + C 1 := by
  simpa [generalRidgeNodalProduct, generalRidgeNodalFactor] using
    (generalRidgeStripeProperPrefix_horizontalProduct
      (n := 0) w T (k := 1) (by omega))

/-- The public proper-prefix object agrees with an actual list prefix of the
complete twisted schedule. -/
example (w : Fin 3 → ℝ) (T : ℝ) :
    generalRidgeStripeProperPrefix (n := 1) w T 2 =
      (generalRidgeStripeTwistedFactors w T).take 2 := by
  exact generalRidgeStripeProperPrefix_eq_take_twistedFactors
    (n := 1) w T (k := 2) (by omega)

/-- A width-five boxcar sees the complete support of the first three
positive nodal factors on every coordinate from three through four. -/
example (w : Fin 4 → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 3 ≤ q) (hq1 : q ≤ 4) :
    ((horizontalProduct
          (generalRidgeStripeProperPrefix (n := 2) w T 3)) *
        generalRidgeBoxcar 4).coeff q = 24 := by
  rw [generalRidgeStripeProperPrefix_boxcar_coeff_eq_factorial
    (n := 2) w T (k := 3) (m := 4) (q := q)
    (by omega) hq0 hq1]
  norm_num

/-- Positivity also holds on both boundary ramps, not only on the central
full-window plateau. -/
example (w : Fin 4 → ℝ) (T : ℝ) (q : ℕ) (hq : q ≤ 7) :
    1 ≤ ((horizontalProduct
          (generalRidgeStripeProperPrefix (n := 2) w T 3)) *
        generalRidgeBoxcar 4).coeff q := by
  exact generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_one_le
    (n := 2) w T (k := 3) (m := 4) (q := q) (by omega) hq

#print axioms generalRidgeStripeProperPrefix_eq_take_twistedFactors
#print axioms generalRidgeStripeTwistedFactors_take_horizontalProduct
#print axioms generalRidgeNodalProduct_mul_boxcar_coeff_one_le
#print axioms generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_one_le

end OneChannelCNNUniversality
