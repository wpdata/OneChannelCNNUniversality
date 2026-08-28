import ICM2022NumCS97.Universal

open ICM2022NumCS97

example {d₁ d₂ : ℕ} {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : LatticeExpr d₁ d₂,
      ∀ x : K, |e.eval x.1 - f x| < ε := by
  exact latticeExpr_dense_on_compact hK f hε

example {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : LatticeExpr d₁ d₂,
      ∀ x : K, |e.evalEncoded x.1 - f x| < ε := by
  exact encodedLatticeExpr_dense_on_compact hd₁ hd₂ hK f hε
