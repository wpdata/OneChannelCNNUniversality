import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeNetwork

/-! # Regression tests for the genuine signed-stripe ridge network -/

namespace OneChannelCNNUniversality

open Set

#check generalRidgeStripeFinalBias
#check generalRidgeStripeNetwork
#check generalRidgeStripeNetwork_depth
#check zeroExtend_generalRidgeStripeNetwork_eval
#check generalRidgeStripeFormalFinal_preactivation
#check exists_generalRidgeStripeNetwork_on_compact

#print axioms generalRidgeStripeNetwork_depth
#print axioms generalRidgeStripeFormalFinal_preactivation
#print axioms exists_generalRidgeStripeNetwork_on_compact

/-- At the smallest width, the final network has two input coordinates,
four output rows, five output columns, and three genuine ReLU layers. -/
noncomputable example (w : Fin 2 → ℝ) (T c t theta : ℝ) :
    SharedBiasNetworkTo 2 2 1 2 4 5 :=
  generalRidgeStripeNetwork w T c t theta

example (w : Fin 2 → ℝ) (T c t theta : ℝ) :
    (generalRidgeStripeNetwork w T c t theta).net.depth = 3 := by
  exact generalRidgeStripeNetwork_depth w T c t theta

private def stripeNetworkRegressionFeature : Unit → Image 1 2 :=
  fun _ _ _ ↦ 0

private theorem stripeNetworkRegressionFeature_continuous :
    ContinuousFeatureOn (Set.univ : Set Unit)
      stripeNetworkRegressionFeature := by
  intro p q
  exact continuousOn_const

/-- The compact existence theorem is inhabited at the boundary case
`n=0`, including positivity and the exact depth certificate. -/
example (w : Fin 2 → ℝ) (theta : ℝ) :
    ∃ T c t : ℝ, 1 ≤ T ∧ 0 < c ∧ 0 < t ∧
      (generalRidgeStripeNetwork w T c t theta).net.depth = 3 := by
  obtain ⟨T, c, t, hT, hc, ht, hdepth, -⟩ :=
    exists_generalRidgeStripeNetwork_on_compact
      (K := (Set.univ : Set Unit)) isCompact_univ
      stripeNetworkRegressionFeature
      stripeNetworkRegressionFeature_continuous w theta
  exact ⟨T, c, t, hT, hc, ht, hdepth⟩

end OneChannelCNNUniversality
