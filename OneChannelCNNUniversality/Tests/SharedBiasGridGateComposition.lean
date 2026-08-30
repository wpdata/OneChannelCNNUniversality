import OneChannelCNNUniversality.SharedBiasGridGateComposition

open OneChannelCNNUniversality

#check twoStageProtectedGridGateNetwork
#check twoStageProtectedGridGateNetwork_depth
#check twoStageProtectedGridGateNetwork_gate
#check twoStageProtectedGridGateNetwork_injectiveOn
#check exists_twoStageProtectedGridGateNetwork_on_compact

example {rows cols : ℕ} (x : Image rows cols)
    (a₁ c₁ M₁ a₂ c₂ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hbound₁ : ∀ i j, |x i j| ≤ M₁)
    (hM₂ : 0 ≤ M₂)
    (hbound₂ : ∀ i j,
      |(protectedGridGateNetwork a₁ c₁ M₁).eval x i j| ≤ M₂)
    (j : Fin cols) :
    zeroExtend
        ((twoStageProtectedGridGateNetwork
          a₁ c₁ M₁ a₂ c₂ M₂).eval x) 0 j =
      relu (a₂ * relu (a₁ * zeroExtend x 0 j + c₁) + c₂) := by
  exact twoStageProtectedGridGateNetwork_gate
    x a₁ c₁ M₁ a₂ c₂ M₂ hM₁ hbound₁ hM₂ hbound₂ j
