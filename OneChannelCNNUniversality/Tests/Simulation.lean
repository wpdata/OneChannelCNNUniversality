import OneChannelCNNUniversality.Simulation

open OneChannelCNNUniversality

example {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (e : LatticeExpr d₁ d₂) :
    ∃ (net : NetworkTo kRows kCols d₁ d₂
          (latticeOutRows kRows d₁ d₂ e)
          (latticeOutCols kCols d₁ d₂ e))
      (weight : Image (latticeOutRows kRows d₁ d₂ e)
        (latticeOutCols kCols d₁ d₂ e))
      (constant : ℝ),
      ∀ x ∈ K, net.realize weight constant x = e.evalEncoded x := by
  exact exists_network_realizing_latticeExpr hkRows hkCols hd₁ hd₂ hK e
