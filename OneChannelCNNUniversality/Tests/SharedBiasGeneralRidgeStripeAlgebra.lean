import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAlgebra

/-!
# Regression tests for the signed stripe ridge factor algebra
-/

namespace OneChannelCNNUniversality

open Polynomial

#check generalRidgeExtendedWeights
#check generalRidgeExtendedWeights_castSucc
#check generalRidgeExtendedWeights_last
#check generalRidgeStripeSeparationScale
#check generalRidgeStripeSeparationScale_one_le
#check generalRidgeStripeAllocation
#check generalRidgeStripeAllocation_sum
#check BilinearKernelFactor.scaleLower
#check BilinearKernelFactor.scaleHorizontal
#check generalRidgeStripeTwistedFactors
#check generalRidgeStripeTwistedFactors_horizontalProduct
#check generalRidgeStripeTwistedFactors_verticalOne
#check generalRidgeStripeTwistedLastFactor_taps
#check generalRidgeStripeTwistedLastFactor_taps_le_neg_one

#print axioms generalRidgeStripeTwistedFactors_horizontalProduct
#print axioms generalRidgeStripeTwistedFactors_verticalOne
#print axioms generalRidgeStripeTwistedLastFactor_taps_le_neg_one

/-- The appended coordinate has zero target weight. -/
example (w : Fin 3 → ℝ) :
    generalRidgeExtendedWeights w (Fin.last 3) = 0 := by
  exact generalRidgeExtendedWeights_last w

/-- Original weights occupy the initial coordinates unchanged. -/
example (w : Fin 3 → ℝ) (i : Fin 3) :
    generalRidgeExtendedWeights w i.castSucc = w i := by
  exact generalRidgeExtendedWeights_castSucc w i

/-- The signed allocation still has the required total leading weight. -/
example (w : Fin 3 → ℝ) :
    ∑ i : Fin 3, generalRidgeStripeAllocation (n := 1) w i =
      generalRidgeExtendedWeights w 0 := by
  exact generalRidgeStripeAllocation_sum (n := 1) w

/-- Twisting the last horizontal factor changes the full horizontal product
by exactly the scalar `-T`. -/
example (w : Fin 3 → ℝ) (T : ℝ) :
    horizontalProduct (generalRidgeStripeTwistedFactors (n := 1) w T) =
      C (-T) * generalRidgeNodalProduct 3 := by
  exact generalRidgeStripeTwistedFactors_horizontalProduct (n := 1) w T

/-- For nonzero scale, the vertical coefficient remains the requested target
polynomial. -/
example (w : Fin 3 → ℝ) (T : ℝ) (hT : T ≠ 0) :
    verticalOne (generalRidgeStripeTwistedFactors (n := 1) w T) =
      generalRidgeTargetPolynomial (generalRidgeExtendedWeights w) := by
  exact generalRidgeStripeTwistedFactors_verticalOne (n := 1) w T hT

/-- At the first nontrivial depth, all four taps of the final twisted factor
are at most `-1` once `T ≥ 1`. -/
example (w : Fin 2 → ℝ) (T : ℝ) (hT : 1 ≤ T) :
    let f := generalRidgeStripeTwistedLastFactor (n := 0) w T
    f.a0 ≤ -1 ∧ f.a1 ≤ -1 ∧ f.b0 ≤ -1 ∧ f.b1 ≤ -1 := by
  exact generalRidgeStripeTwistedLastFactor_taps_le_neg_one
    (n := 0) w T hT

end OneChannelCNNUniversality
