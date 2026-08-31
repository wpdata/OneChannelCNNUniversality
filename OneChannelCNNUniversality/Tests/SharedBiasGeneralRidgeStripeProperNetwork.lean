import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeProperNetwork

/-! # Regression tests for the genuine proper signed-stripe network -/

namespace OneChannelCNNUniversality

open Set

#check generalRidgeStripeTwistedProperFactors_ne_nil
#check generalRidgeStripeProperRawNetwork
#check generalRidgeStripeProperNetwork
#check generalRidgeStripeProperNetwork_depth
#check generalRidgeStripeProperFormalState
#check zeroExtend_generalRidgeStripeProperFormalState
#check generalRidgeStripeProperNetwork_northTwoAgree_formalState
#check generalRidgeStripeJointScaleThreshold
#check generalRidgeStripeJointScaleThreshold_one_le
#check generalRidgeStripeJointScaleThreshold_spec
#check exists_generalRidgeStripeJointScale
#check exists_generalRidgeStripeProperNetwork_threshold_on_compact
#check exists_generalRidgeStripeProperNetwork_on_compact

#print axioms generalRidgeStripeProperNetwork_depth
#print axioms generalRidgeStripeJointScaleThreshold_spec
#print axioms generalRidgeStripeProperNetwork_northTwoAgree_formalState
#print axioms exists_generalRidgeStripeProperNetwork_on_compact

/-- At the smallest width (`n=0`, hence two input coordinates), the public
network has the exact promised input and output dimensions. -/
noncomputable example (w : Fin 2 → ℝ) (T c t : ℝ) :
    SharedBiasNetworkTo 2 2 1 2 3 4 :=
  generalRidgeStripeProperNetwork w T c t

/-- The same smallest-width network consists of the seed and one proper
factor layer. -/
example (w : Fin 2 → ℝ) (T c t : ℝ) :
    (generalRidgeStripeProperNetwork w T c t).net.depth = 2 := by
  exact generalRidgeStripeProperNetwork_depth w T c t

private def stripeProperRegressionFeature : Unit → Image 1 2 :=
  fun _ _ _ ↦ 0

private theorem stripeProperRegressionFeature_continuous :
    ContinuousFeatureOn (Set.univ : Set Unit)
      stripeProperRegressionFeature := by
  intro p q
  exact continuousOn_const

/-- The fully bundled compact theorem is inhabited at the `n=0` boundary,
not merely its dimension-only specialization. -/
example (w : Fin 2 → ℝ) :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C := by
  obtain ⟨T, C, hT, hC, -⟩ :=
    exists_generalRidgeStripeProperNetwork_on_compact
      (K := (Set.univ : Set Unit)) isCompact_univ
      stripeProperRegressionFeature
      stripeProperRegressionFeature_continuous w
  exact ⟨T, C, hT, hC⟩

end OneChannelCNNUniversality
