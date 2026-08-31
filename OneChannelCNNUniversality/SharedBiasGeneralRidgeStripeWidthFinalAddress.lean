import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeFinalAddress

/-!
# Final signed-stripe address with independent predecessor width

The original local-address calculation fixed the predecessor width to
`2*(n+2)`.  The genuine independent-width proper network instead reaches a
state of size `(n+3) × (m+n+2)`.  This module repeats the exact final-factor
calculation at that general width.

Every row-one interior site sees the same sum of all four final taps.  When
`T ≥ 1`, every row-zero site and both row-one endpoints lie at least two above
that common interior baseline.  Consequently any finite collection of
interior packed targets is compatible with one shared final-layer carrier
baseline.
-/

namespace OneChannelCNNUniversality

/-- Address produced by the final twisted factor from a unit constant image
whose width is independent of the factor depth. -/
noncomputable def generalRidgeStripeWidthFinalLocalAddress {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (p q : ℕ) : ℝ :=
  fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
    (constantImage (n + 3) (m + n + 2) 1) p q

/-- Every row-one interior site sees all four final taps. -/
theorem generalRidgeStripeWidthFinalLocalAddress_interior_value
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < m + n + 2) :
    generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 q =
      let f := generalRidgeStripeTwistedLastFactor w T
      f.a0 + f.a1 + f.b0 + f.b1 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hpred : q - 1 < m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hq0, hq1, hpred]

private theorem generalRidgeStripeWidthFinalLocalAddress_row_zero_left
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeWidthFinalLocalAddress (m := m) w T 0 0 =
      (generalRidgeStripeTwistedLastFactor w T).a0 := by
  have hrows : 0 < n + 3 := by omega
  have hcols : 0 < m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hcols]

private theorem generalRidgeStripeWidthFinalLocalAddress_row_zero_right
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeWidthFinalLocalAddress
        (m := m) w T 0 (m + n + 2) =
      (generalRidgeStripeTwistedLastFactor w T).a1 := by
  have hrows : 0 < n + 3 := by omega
  have hone : 1 ≤ m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hone]

private theorem generalRidgeStripeWidthFinalLocalAddress_row_zero_interior
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < m + n + 2) :
    generalRidgeStripeWidthFinalLocalAddress (m := m) w T 0 q =
      (generalRidgeStripeTwistedLastFactor w T).a0 +
        (generalRidgeStripeTwistedLastFactor w T).a1 := by
  have hrows : 0 < n + 3 := by omega
  have hpred : q - 1 < m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hq0, hq1, hpred]

private theorem generalRidgeStripeWidthFinalLocalAddress_row_one_left
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 0 =
      (generalRidgeStripeTwistedLastFactor w T).a0 +
        (generalRidgeStripeTwistedLastFactor w T).b0 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hcols : 0 < m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hcols]

private theorem generalRidgeStripeWidthFinalLocalAddress_row_one_right
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeWidthFinalLocalAddress
        (m := m) w T 1 (m + n + 2) =
      (generalRidgeStripeTwistedLastFactor w T).a1 +
        (generalRidgeStripeTwistedLastFactor w T).b1 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hone : 1 ≤ m + n + 2 := by omega
  rw [generalRidgeStripeWidthFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hone]

/-- Relative to any chosen row-one interior target, every northern output
coordinate exceeds the common local baseline by at least two. -/
theorem generalRidgeStripeWidthFinalLocalAddress_row_zero_gap
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (target : ℕ) (htarget0 : 1 ≤ target)
    (htarget1 : target < m + n + 2)
    (q : ℕ) (hq : q ≤ m + n + 2) :
    2 ≤ generalRidgeStripeWidthFinalLocalAddress (m := m) w T 0 q -
      generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 target := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeWidthFinalLocalAddress_interior_value
    w T target htarget0 htarget1]
  by_cases hleft : q = 0
  · subst q
    rw [generalRidgeStripeWidthFinalLocalAddress_row_zero_left]
    linarith
  · by_cases hright : q = m + n + 2
    · subst q
      rw [generalRidgeStripeWidthFinalLocalAddress_row_zero_right]
      linarith
    · have hq0 : 1 ≤ q := by omega
      have hq1 : q < m + n + 2 := by omega
      rw [generalRidgeStripeWidthFinalLocalAddress_row_zero_interior
        w T q hq0 hq1]
      linarith

/-- The left row-one endpoint exceeds every interior target baseline by at
least two. -/
theorem generalRidgeStripeWidthFinalLocalAddress_row_one_left_gap
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (target : ℕ) (htarget0 : 1 ≤ target)
    (htarget1 : target < m + n + 2) :
    2 ≤ generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 0 -
      generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 target := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeWidthFinalLocalAddress_interior_value
      w T target htarget0 htarget1,
    generalRidgeStripeWidthFinalLocalAddress_row_one_left]
  linarith

/-- The right row-one endpoint exceeds every interior target baseline by at
least two. -/
theorem generalRidgeStripeWidthFinalLocalAddress_row_one_right_gap
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (target : ℕ) (htarget0 : 1 ≤ target)
    (htarget1 : target < m + n + 2) :
    2 ≤ generalRidgeStripeWidthFinalLocalAddress
        (m := m) w T 1 (m + n + 2) -
      generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 target := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeWidthFinalLocalAddress_interior_value
      w T target htarget0 htarget1,
    generalRidgeStripeWidthFinalLocalAddress_row_one_right]
  linarith

/-- All row-one interior coordinates have exactly the same local address.
This is the common baseline required by simultaneous target selection. -/
theorem generalRidgeStripeWidthFinalLocalAddress_row_one_interior
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (target q : ℕ)
    (htarget0 : 1 ≤ target) (htarget1 : target < m + n + 2)
    (hq0 : 1 ≤ q) (hq1 : q < m + n + 2) :
    generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 q =
      generalRidgeStripeWidthFinalLocalAddress (m := m) w T 1 target := by
  rw [generalRidgeStripeWidthFinalLocalAddress_interior_value
      w T q hq0 hq1,
    generalRidgeStripeWidthFinalLocalAddress_interior_value
      w T target htarget0 htarget1]

end OneChannelCNNUniversality
