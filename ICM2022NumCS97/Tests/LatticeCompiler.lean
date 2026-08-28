import ICM2022NumCS97.LatticeCompiler

open ICM2022NumCS97

example {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂) (start : ℕ)
    (x : Image d₁ d₂) (value : Site → ℝ)
    (hmaster : ∀ i : Fin d₁, ∀ j : Fin d₂,
      value (gridSite d₁ d₂ i j) = sparseEncodedValue x i j)
    (hfresh : ∀ t, start ≤ t → value (circuitNodeSite d₁ d₂ t) = 0) :
    executeGridCommands (e.compileCommands start) value
        (circuitNodeSite d₁ d₂ (e.outputIndex start)) =
      e.evalEncoded x := by
  exact LatticeExpr.compileCommands_output e start x value hmaster hfresh
