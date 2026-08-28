import OneChannelCNNUniversality.GridRouting

open OneChannelCNNUniversality

example {d₁ d₂ r c R C : ℕ} (hr : r < R) (hc : c < C)
    (coefficient : ℝ) (value : Site → ℝ) :
    executeRoute
        (routeGridToGridSteps d₁ d₂ r c R C coefficient)
        (staticState (gridSupport d₁ d₂) value) =
      staticState (gridSupport d₁ d₂)
        (updateAt value (gridSite d₁ d₂ R C)
          (value (gridSite d₁ d₂ R C) +
            coefficient * value (gridSite d₁ d₂ r c))) := by
  exact executeRoute_routeGridToGrid hr hc coefficient value
