import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeCarrier

/-!
# Signed-stripe prefix carriers with independent input width

The original carrier module specialized the seed width to the ridge-factor
depth.  Parallel ridge packing needs depth `d = r*m` while the actual input
width remains `m`.  The prefix argument only uses convolution of the positive
nodal product with a boxcar, so the two sizes can be separated.

For an arbitrary seed width `m+1`, one finite error bound again yields the
upward-closed threshold

\[
  T_0=2(B+1).
\]

Every larger reciprocal scale keeps every genuine proper-prefix
preactivation on the northern two rows at least one.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Either row of a constant two-row carrier of width `m+1` has generating
polynomial twice the width-`m+1` boxcar. -/
theorem rowPolynomial_constantTwoStripe_width (m p : ℕ) (hp : p < 2) :
    rowPolynomial (constantImage 2 (m + 1) 2) p =
      C 2 * generalRidgeBoxcar m := by
  ext q
  rw [rowPolynomial_coeff, coeff_C_mul, generalRidgeBoxcar_coeff]
  by_cases hq : q < m + 1
  · have hq' : q ≤ m := by omega
    simp [zeroExtend, constantImage, hp, hq, hq']
  · have hq' : ¬q ≤ m := by omega
    simp [zeroExtend, hp, hq, hq']

/-- Exact northern-row carrier polynomial for an arbitrary seed width. -/
theorem generalRidgeStripeProperPrefix_carrier_row_zero_width
    {n k m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (m + 1) 2)) 0 =
      C 2 * (generalRidgeNodalProduct k * generalRidgeBoxcar m) := by
  rw [rowPolynomial_fullConvChain_zero,
    generalRidgeStripeProperPrefix_horizontalProduct w T hk,
    rowPolynomial_constantTwoStripe_width m 0 (by omega)]
  ring

/-- Exact first-southern-row carrier polynomial for an arbitrary seed
width. -/
theorem generalRidgeStripeProperPrefix_carrier_row_one_width
    {n k m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (m + 1) 2)) 1 =
      C 2 * (generalRidgeNodalProduct k * generalRidgeBoxcar m) -
        C (2 * T⁻¹) *
          (generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar m) := by
  rw [rowPolynomial_fullConvChain_one,
    generalRidgeStripeProperPrefix_horizontalProduct w T hk,
    generalRidgeStripeProperPrefix_verticalOne,
    rowPolynomial_constantTwoStripe_width m 1 (by omega),
    rowPolynomial_constantTwoStripe_width m 0 (by omega)]
  simp only [map_neg, map_mul]
  ring

/-- Coefficient form of the independent-width northern carrier identity. -/
theorem generalRidgeStripeProperPrefix_carrier_row_zero_coeff_width
    {n k m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (q : ℕ) :
    zeroExtend
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (m + 1) 2)) 0 q =
      2 * (generalRidgeNodalProduct k *
        generalRidgeBoxcar m).coeff q := by
  rw [← rowPolynomial_coeff,
    generalRidgeStripeProperPrefix_carrier_row_zero_width w T hk,
    coeff_C_mul]

/-- Coefficient form of the independent-width southern carrier identity. -/
theorem generalRidgeStripeProperPrefix_carrier_row_one_coeff_width
    {n k m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (q : ℕ) :
    zeroExtend
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (m + 1) 2)) 1 q =
      2 * (generalRidgeNodalProduct k *
          generalRidgeBoxcar m).coeff q -
        2 * T⁻¹ *
          (generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar m).coeff q := by
  rw [← rowPolynomial_coeff,
    generalRidgeStripeProperPrefix_carrier_row_one_width w T hk,
    coeff_sub, coeff_C_mul, coeff_C_mul]

/-- One finite absolute bound over every proper-prefix error coefficient at
the independently specified seed width. -/
noncomputable def generalRidgeStripeWidthPrefixErrorBound {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 2),
    ∑ q ∈ Finset.range (m + 1 + k),
      |(generalRidgeStripeOriginalPrefixVerticalOne w k *
        generalRidgeBoxcar m).coeff q|

theorem generalRidgeStripeWidthPrefixErrorBound_nonneg {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) :
    0 ≤ generalRidgeStripeWidthPrefixErrorBound w m := by
  unfold generalRidgeStripeWidthPrefixErrorBound
  positivity

theorem generalRidgeStripeWidthPrefixErrorBound_coeff_abs_le
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ)
    (hk : k < n + 2) (hq : q < m + 1 + k) :
    |(generalRidgeStripeOriginalPrefixVerticalOne w k *
        generalRidgeBoxcar m).coeff q| ≤
      generalRidgeStripeWidthPrefixErrorBound w m := by
  classical
  unfold generalRidgeStripeWidthPrefixErrorBound
  calc
    |(generalRidgeStripeOriginalPrefixVerticalOne w k *
          generalRidgeBoxcar m).coeff q| ≤
        ∑ j ∈ Finset.range (m + 1 + k),
          |(generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar m).coeff j| := by
      exact Finset.single_le_sum
        (fun j _ ↦ abs_nonneg
          ((generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar m).coeff j))
        (Finset.mem_range.mpr hq)
    _ ≤ ∑ i ∈ Finset.range (n + 2),
          ∑ j ∈ Finset.range (m + 1 + i),
            |(generalRidgeStripeOriginalPrefixVerticalOne w i *
              generalRidgeBoxcar m).coeff j| := by
      exact Finset.single_le_sum
        (f := fun i ↦ ∑ j ∈ Finset.range (m + 1 + i),
          |(generalRidgeStripeOriginalPrefixVerticalOne w i *
            generalRidgeBoxcar m).coeff j|)
        (s := Finset.range (n + 2))
        (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ abs_nonneg
          ((generalRidgeStripeOriginalPrefixVerticalOne w i *
            generalRidgeBoxcar m).coeff j)))
        (Finset.mem_range.mpr hk)

/-- Explicit independent-width reciprocal-scale threshold. -/
noncomputable def generalRidgeStripeWidthCarrierThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) : ℝ :=
  2 * (generalRidgeStripeWidthPrefixErrorBound w m + 1)

theorem generalRidgeStripeWidthCarrierThreshold_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) :
    1 ≤ generalRidgeStripeWidthCarrierThreshold w m := by
  have hB := generalRidgeStripeWidthPrefixErrorBound_nonneg w m
  unfold generalRidgeStripeWidthCarrierThreshold
  linarith

private theorem generalRidgeStripeWidth_scaled_error_le_one
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeWidthCarrierThreshold w m ≤ T)
    (hk : k < n + 2) (hq : q < m + 1 + k) :
    2 * T⁻¹ *
        (generalRidgeStripeOriginalPrefixVerticalOne w k *
          generalRidgeBoxcar m).coeff q ≤ 1 := by
  let B := generalRidgeStripeWidthPrefixErrorBound w m
  let z := (generalRidgeStripeOriginalPrefixVerticalOne w k *
    generalRidgeBoxcar m).coeff q
  have hB : 0 ≤ B := generalRidgeStripeWidthPrefixErrorBound_nonneg w m
  have habs : |z| ≤ B :=
    generalRidgeStripeWidthPrefixErrorBound_coeff_abs_le w hk hq
  have hz : z ≤ B := (le_abs_self z).trans habs
  have hT' : 2 * (B + 1) ≤ T := by
    simpa [B, generalRidgeStripeWidthCarrierThreshold] using hT
  have hTpos : 0 < T := by linarith
  have hinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
  have htwoB : 2 * B ≤ T := by linarith
  calc
    2 * T⁻¹ * z ≤ 2 * T⁻¹ * B := by
      exact mul_le_mul_of_nonneg_left hz (by positivity)
    _ = (2 * B) * T⁻¹ := by ring
    _ ≤ T * T⁻¹ := mul_le_mul_of_nonneg_right htwoB hinv
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hTpos)

/-- Every proper prefix has a northern-two-row unit-lower carrier at the
independently specified seed width. -/
theorem generalRidgeStripeProperPrefix_carrier_unitLower_width
    {n k m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeWidthCarrierThreshold w m ≤ T)
    (hk : k < n + 2) :
    ∀ p : Fin (grownSize 2 2
        (generalRidgeStripeProperPrefix w T k).length),
      (p : ℕ) ≤ 1 →
      ∀ q : Fin (grownSize 2 (m + 1)
          (generalRidgeStripeProperPrefix w T k).length),
        1 ≤ fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (m + 1) 2) p q := by
  have hlength :
      (generalRidgeStripeProperPrefix w T k).length = k := by
    simp [generalRidgeStripeProperPrefix, generalRidgeFactorList_length,
      Nat.min_eq_left (by omega : k ≤ n + 2)]
  intro p hp q
  have hq : (q : ℕ) < m + 1 + k := by
    simpa [hlength, grownSize_two_eq_add] using q.isLt
  have hsupport : (q : ℕ) ≤ k + m := by omega
  have hbase :
      1 ≤ (generalRidgeNodalProduct k *
        generalRidgeBoxcar m).coeff (q : ℕ) :=
    generalRidgeNodalProduct_mul_boxcar_coeff_one_le
      k m q hsupport
  have hp_cases : (p : ℕ) = 0 ∨ (p : ℕ) = 1 := by omega
  rcases hp_cases with hp0 | hp1
  · have hp_eq : p = ⟨0, by
        simp [hlength, grownSize_two_eq_add]⟩ := Fin.ext hp0
    rw [hp_eq]
    have hrow :=
      generalRidgeStripeProperPrefix_carrier_row_zero_coeff_width
        (m := m) w T hk (q : ℕ)
    simp [zeroExtend, hlength, grownSize_two_eq_add, hq] at hrow
    rw [hrow]
    linarith
  · have hp_eq : p = ⟨1, by
        simpa [hlength, grownSize_two_eq_add] using
          (show 1 < 2 + k by omega)⟩ := Fin.ext hp1
    rw [hp_eq]
    have herror := generalRidgeStripeWidth_scaled_error_le_one
      w T hT hk hq
    have hrow :=
      generalRidgeStripeProperPrefix_carrier_row_one_coeff_width
        (m := m) w T hk (q : ℕ)
    have hrowIndex : 1 < 2 + k := by omega
    simp [zeroExtend, hlength, grownSize_two_eq_add, hq, hrowIndex]
      at hrow
    rw [hrow]
    linarith

/-- The complete proper signed-stripe block has a unit-lower carrier for an
arbitrary seed width once `T` exceeds the independent-width threshold. -/
theorem generalRidgeStripeTwistedProperFactors_unitLower_width_of_large
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeWidthCarrierThreshold w m ≤ T) :
    NorthTwoUnitLowerAlong
      (generalRidgeStripeTwistedProperFactors w T)
      (constantImage 2 (m + 1) 2) := by
  apply northTwoUnitLowerAlong_of_take_fullConvChain_unitLower
  intro k hkpos hklength p hp hprows q hpcols
  have hk : k ≤ n + 1 := by simpa using hklength
  have htake :=
    generalRidgeStripeTwistedProperFactors_take_eq_properPrefix w T hk
  rw [htake] at hprows hpcols ⊢
  have hprows' :
      p < 2 + (generalRidgeStripeProperPrefix w T k).length := by
    simpa [grownSize_two_eq_add] using hprows
  have hpcols' :
      q < m + 1 + (generalRidgeStripeProperPrefix w T k).length := by
    simpa [grownSize_two_eq_add] using hpcols
  have hunit := generalRidgeStripeProperPrefix_carrier_unitLower_width
    w T hT (by omega) ⟨p, hprows⟩ hp ⟨q, hpcols⟩
  simpa [zeroExtend, hprows', hpcols'] using hunit

/-- Upward-closed threshold interface for the independent-width carrier. -/
theorem exists_generalRidgeStripeTwistedProperFactors_unitLower_width_threshold
    {n : ℕ} (w : Fin (n + 2) → ℝ) (m : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      NorthTwoUnitLowerAlong
        (generalRidgeStripeTwistedProperFactors w T)
        (constantImage 2 (m + 1) 2) := by
  refine ⟨generalRidgeStripeWidthCarrierThreshold w m,
    generalRidgeStripeWidthCarrierThreshold_one_le w m, ?_⟩
  intro T hT
  exact generalRidgeStripeTwistedProperFactors_unitLower_width_of_large
    w T hT

end OneChannelCNNUniversality
