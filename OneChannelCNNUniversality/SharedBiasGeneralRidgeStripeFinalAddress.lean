import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAlgebra

/-!
# Local address of the final signed-stripe factor

Immediately before the final twisted factor, the proposed stripe compiler
has spatial size `(n + 3) × (2 * (n + 2))`.  A nonnegative shared-bias
boost at that stage contributes a constant image.  This file computes the
address obtained by convolving that unit constant image with the final
twisted factor.

When `T ≥ 1`, all four taps of the final factor are at most `-1`.  Hence
every northern coordinate lies at least two above the target `(1,n+2)`.
The two horizontal endpoints of row one also lie at least two above the
target, while every interior coordinate of row one has exactly the target
address.  Thus this local direction supplies vertical separation but not
horizontal uniqueness; the latter must come from the full signed boxcar
address.
-/

namespace OneChannelCNNUniversality

/-- Address produced by the final twisted factor from a unit constant image
of the predecessor dimensions used by the stripe construction. -/
noncomputable def generalRidgeStripeFinalLocalAddress {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (p q : ℕ) : ℝ :=
  fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
    (constantImage (n + 3) (2 * (n + 2)) 1) p q

/-- The target is an interior site and therefore sees all four final taps. -/
theorem generalRidgeStripeFinalLocalAddress_target {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeFinalLocalAddress w T 1 (n + 2) =
      let f := generalRidgeStripeTwistedLastFactor w T
      f.a0 + f.a1 + f.b0 + f.b1 := by
  have hrow : 1 < n + 3 := by omega
  have hcol : n + 2 < 2 * (n + 2) := by omega
  have hone : 1 ≤ n + 2 := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow, hcol, hone]
  rw [if_pos (by omega), if_pos (by omega)]

private theorem generalRidgeStripeFinalLocalAddress_row_zero_left {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeFinalLocalAddress w T 0 0 =
      (generalRidgeStripeTwistedLastFactor w T).a0 := by
  have hrows : 0 < n + 3 := by omega
  have hcols : 0 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hcols]

private theorem generalRidgeStripeFinalLocalAddress_row_zero_right {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeFinalLocalAddress w T 0 (2 * (n + 2)) =
      (generalRidgeStripeTwistedLastFactor w T).a1 := by
  have hrows : 0 < n + 3 := by omega
  have hone : 1 ≤ 2 * (n + 2) := by omega
  have hpred : 2 * (n + 2) - 1 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hone, hpred]

private theorem generalRidgeStripeFinalLocalAddress_row_zero_interior
    {n : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < 2 * (n + 2)) :
    generalRidgeStripeFinalLocalAddress w T 0 q =
      (generalRidgeStripeTwistedLastFactor w T).a0 +
        (generalRidgeStripeTwistedLastFactor w T).a1 := by
  have hrows : 0 < n + 3 := by omega
  have hpred : q - 1 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrows, hq0, hq1, hpred]

private theorem generalRidgeStripeFinalLocalAddress_row_one_left {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeFinalLocalAddress w T 1 0 =
      (generalRidgeStripeTwistedLastFactor w T).a0 +
        (generalRidgeStripeTwistedLastFactor w T).b0 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hcols : 0 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hcols]

private theorem generalRidgeStripeFinalLocalAddress_row_one_right {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeFinalLocalAddress w T 1 (2 * (n + 2)) =
      (generalRidgeStripeTwistedLastFactor w T).a1 +
        (generalRidgeStripeTwistedLastFactor w T).b1 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hone : 1 ≤ 2 * (n + 2) := by omega
  have hpred : 2 * (n + 2) - 1 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hone, hpred]

private theorem generalRidgeStripeFinalLocalAddress_row_one_interior_eq_sum
    {n : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < 2 * (n + 2)) :
    generalRidgeStripeFinalLocalAddress w T 1 q =
      let f := generalRidgeStripeTwistedLastFactor w T
      f.a0 + f.a1 + f.b0 + f.b1 := by
  have hrow0 : 0 < n + 3 := by omega
  have hrow1 : 1 < n + 3 := by omega
  have hpred : q - 1 < 2 * (n + 2) := by omega
  rw [generalRidgeStripeFinalLocalAddress,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [zeroExtend, constantImage, hrow0, hrow1, hq0, hq1, hpred]

/-- Every northern output coordinate exceeds the local target address by at
least two. -/
theorem generalRidgeStripeFinalLocalAddress_row_zero_gap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (q : ℕ) (hq : q ≤ 2 * (n + 2)) :
    2 ≤ generalRidgeStripeFinalLocalAddress w T 0 q -
      generalRidgeStripeFinalLocalAddress w T 1 (n + 2) := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeFinalLocalAddress_target]
  by_cases hleft : q = 0
  · subst q
    rw [generalRidgeStripeFinalLocalAddress_row_zero_left]
    linarith
  · by_cases hright : q = 2 * (n + 2)
    · subst q
      rw [generalRidgeStripeFinalLocalAddress_row_zero_right]
      linarith
    · have hq0 : 1 ≤ q := by omega
      have hq1 : q < 2 * (n + 2) := by omega
      rw [generalRidgeStripeFinalLocalAddress_row_zero_interior
        w T q hq0 hq1]
      linarith

/-- The left endpoint of row one exceeds the local target address by at
least two. -/
theorem generalRidgeStripeFinalLocalAddress_row_one_left_gap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T) :
    2 ≤ generalRidgeStripeFinalLocalAddress w T 1 0 -
      generalRidgeStripeFinalLocalAddress w T 1 (n + 2) := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeFinalLocalAddress_target,
    generalRidgeStripeFinalLocalAddress_row_one_left]
  linarith

/-- The right endpoint of row one exceeds the local target address by at
least two. -/
theorem generalRidgeStripeFinalLocalAddress_row_one_right_gap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T) :
    2 ≤
      generalRidgeStripeFinalLocalAddress w T 1 (2 * (n + 2)) -
        generalRidgeStripeFinalLocalAddress w T 1 (n + 2) := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps_le_neg_one w T hT
  rw [generalRidgeStripeFinalLocalAddress_target,
    generalRidgeStripeFinalLocalAddress_row_one_right]
  linarith

/-- Every interior coordinate of row one has exactly the local target
address.  In particular, this local carrier direction alone cannot select a
unique horizontal site. -/
theorem generalRidgeStripeFinalLocalAddress_row_one_interior {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < 2 * (n + 2)) :
    generalRidgeStripeFinalLocalAddress w T 1 q =
      generalRidgeStripeFinalLocalAddress w T 1 (n + 2) := by
  rw [generalRidgeStripeFinalLocalAddress_row_one_interior_eq_sum
      w T q hq0 hq1,
    generalRidgeStripeFinalLocalAddress_target]

end OneChannelCNNUniversality
