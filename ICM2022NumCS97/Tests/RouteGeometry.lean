import ICM2022NumCS97.RouteGeometry

open ICM2022NumCS97

example {d₁ d₂ : ℕ} (i : Fin d₁) (j : Fin d₂) :
    registerSupport d₁ d₂ (masterSite d₁ d₂ i j) = true := by
  exact registerSupport_master i j

example (d₁ d₂ : ℕ) (direction : RouteDirection) (s : Site)
    (hs : registerSupport d₁ d₂ s = true) :
    registerSupport d₁ d₂ (advanceSite direction s) = false := by
  exact registerSupport_advance_eq_false d₁ d₂ direction s hs

example (d₁ d₂ : ℕ) (direction : RouteDirection) :
    IncomingClear direction (registerSupport d₁ d₂) := by
  exact registerSupport_incomingClear d₁ d₂ direction

example {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (i : Fin d₁) (j : Fin d₂) (coefficient : ℝ) (value : Site → ℝ) :
    executeRoute (routeMasterToWorkSteps d₁ d₂ i j coefficient)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (registerSupport d₁ d₂)
        (updateAt value (workSite d₁ d₂)
          (value (workSite d₁ d₂) + coefficient * value (masterSite d₁ d₂ i j))) := by
  exact executeRoute_routeMasterToWork hd₁ hd₂ i j coefficient value

example (d₁ d₂ : ℕ) (coefficient token : ℝ) (value : Site → ℝ) :
    executeRoute (routeWorkToSumSteps d₁ d₂ coefficient)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (ridgeSupport d₁ d₂)
        (updateAt value (sumSite d₁ d₂)
          (value (sumSite d₁ d₂) + coefficient * value (workSite d₁ d₂))) := by
  exact executeRoute_routeWorkToSum d₁ d₂ coefficient value

example {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (coefficient : Fin d₁ → Fin d₂ → ℝ) (value : Site → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) :
    executeRoute (routeMastersToWorkSteps d₁ d₂ coefficient entries)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (registerSupport d₁ d₂)
        (accumulateAt value (workSite d₁ d₂)
          (masterWeightedSum d₁ d₂ coefficient value entries)) := by
  exact executeRoute_routeMastersToWork hd₁ hd₂ coefficient value entries
