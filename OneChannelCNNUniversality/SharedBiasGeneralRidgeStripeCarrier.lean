import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripePrefix
import OneChannelCNNUniversality.SharedBiasNorthTwoCarrier
import OneChannelCNNUniversality.SharedBiasGeneralRidgeNetwork

/-!
# A uniform northern-two-row carrier for the signed stripe

For every proper prefix of the signed stripe, the horizontal response to the
constant two-row image of value two is twice the positive nodal product
convolved with a boxcar.  Its coefficients are at least two on the complete
output support.  The first southern row differs from this positive response
by a term of order `T⁻¹`.

The finitely many coefficients of all unscaled proper-prefix error
polynomials have one global absolute-value bound.  Choosing

\[
  T_0 = 2(B+1)
\]

makes every northern-two-row preactivation at least one, simultaneously for
all prefixes and all genuine output columns.  The conclusion is upward
closed: every `T ≥ T₀` has the same carrier property.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- The coefficient of vertical degree one before applying the reciprocal
lower scaling to the first `k` factors. -/
noncomputable def generalRidgeStripeOriginalPrefixVerticalOne {n : ℕ}
    (w : Fin (n + 2) → ℝ) (k : ℕ) : ℝ[X] :=
  verticalOne
    ((generalRidgeFactorList (generalRidgeExtendedWeights w)
      (generalRidgeStripeAllocation w)).take k)

/-- Reciprocal lower scaling multiplies the complete vertical-degree-one
prefix polynomial by the same scalar. -/
theorem generalRidgeStripeProperPrefix_verticalOne {n k : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    verticalOne (generalRidgeStripeProperPrefix w T k) =
      C (-T⁻¹) * generalRidgeStripeOriginalPrefixVerticalOne w k := by
  rw [generalRidgeStripeProperPrefix, verticalOne_map_scaleLower]
  rfl

/-- Either row of the constant two-row carrier has generating polynomial
twice the width-`n+3` boxcar. -/
theorem rowPolynomial_constantTwoStripe (n p : ℕ) (hp : p < 2) :
    rowPolynomial (constantImage 2 (n + 3) 2) p =
      C 2 * generalRidgeBoxcar (n + 2) := by
  ext q
  rw [rowPolynomial_coeff, coeff_C_mul, generalRidgeBoxcar_coeff]
  by_cases hq : q < n + 3
  · have hq' : q ≤ n + 2 := by omega
    simp [zeroExtend, constantImage, hp, hq, hq']
  · have hq' : ¬q ≤ n + 2 := by omega
    simp [zeroExtend, hp, hq, hq']

/-- Exact northern-row polynomial transported through any proper prefix. -/
theorem generalRidgeStripeProperPrefix_carrier_row_zero
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (n + 3) 2)) 0 =
      C 2 *
        (generalRidgeNodalProduct k * generalRidgeBoxcar (n + 2)) := by
  rw [rowPolynomial_fullConvChain_zero,
    generalRidgeStripeProperPrefix_horizontalProduct w T hk,
    rowPolynomial_constantTwoStripe n 0 (by omega)]
  ring

/-- Exact first-southern-row polynomial transported through any proper
prefix.  The second term is the sole reciprocal-scale error. -/
theorem generalRidgeStripeProperPrefix_carrier_row_one
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (n + 3) 2)) 1 =
      C 2 *
          (generalRidgeNodalProduct k * generalRidgeBoxcar (n + 2)) -
        C (2 * T⁻¹) *
          (generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar (n + 2)) := by
  rw [rowPolynomial_fullConvChain_one,
    generalRidgeStripeProperPrefix_horizontalProduct w T hk,
    generalRidgeStripeProperPrefix_verticalOne,
    rowPolynomial_constantTwoStripe n 1 (by omega),
    rowPolynomial_constantTwoStripe n 0 (by omega)]
  simp only [map_neg, map_mul]
  ring

/-- Coefficient form of the exact northern-row carrier identity. -/
theorem generalRidgeStripeProperPrefix_carrier_row_zero_coeff
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (q : ℕ) :
    zeroExtend
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (n + 3) 2)) 0 q =
      2 * (generalRidgeNodalProduct k *
        generalRidgeBoxcar (n + 2)).coeff q := by
  rw [← rowPolynomial_coeff,
    generalRidgeStripeProperPrefix_carrier_row_zero w T hk,
    coeff_C_mul]

/-- Coefficient form of the exact first-southern-row carrier identity. -/
theorem generalRidgeStripeProperPrefix_carrier_row_one_coeff
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (q : ℕ) :
    zeroExtend
        (fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (n + 3) 2)) 1 q =
      2 * (generalRidgeNodalProduct k *
          generalRidgeBoxcar (n + 2)).coeff q -
        2 * T⁻¹ *
          (generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar (n + 2)).coeff q := by
  rw [← rowPolynomial_coeff,
    generalRidgeStripeProperPrefix_carrier_row_one w T hk,
    coeff_sub, coeff_C_mul, coeff_C_mul]

/-- Sum of the absolute values of every first-southern-row error coefficient
that can occur in a proper prefix and a genuine output column. -/
noncomputable def generalRidgeStripePrefixErrorBound {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 2),
    ∑ q ∈ Finset.range (n + 3 + k),
      |(generalRidgeStripeOriginalPrefixVerticalOne w k *
        generalRidgeBoxcar (n + 2)).coeff q|

theorem generalRidgeStripePrefixErrorBound_nonneg {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    0 ≤ generalRidgeStripePrefixErrorBound w := by
  unfold generalRidgeStripePrefixErrorBound
  positivity

/-- Every error coefficient belonging to a proper prefix and an actual
output column is bounded by the single global finite sum. -/
theorem generalRidgeStripePrefixErrorBound_coeff_abs_le
    {n k q : ℕ} (w : Fin (n + 2) → ℝ)
    (hk : k < n + 2) (hq : q < n + 3 + k) :
    |(generalRidgeStripeOriginalPrefixVerticalOne w k *
        generalRidgeBoxcar (n + 2)).coeff q| ≤
      generalRidgeStripePrefixErrorBound w := by
  classical
  unfold generalRidgeStripePrefixErrorBound
  calc
    |(generalRidgeStripeOriginalPrefixVerticalOne w k *
          generalRidgeBoxcar (n + 2)).coeff q| ≤
        ∑ j ∈ Finset.range (n + 3 + k),
          |(generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar (n + 2)).coeff j| := by
      exact Finset.single_le_sum
        (fun j _ ↦ abs_nonneg
          ((generalRidgeStripeOriginalPrefixVerticalOne w k *
            generalRidgeBoxcar (n + 2)).coeff j))
        (Finset.mem_range.mpr hq)
    _ ≤ ∑ i ∈ Finset.range (n + 2),
          ∑ j ∈ Finset.range (n + 3 + i),
            |(generalRidgeStripeOriginalPrefixVerticalOne w i *
              generalRidgeBoxcar (n + 2)).coeff j| := by
      exact Finset.single_le_sum
        (f := fun i ↦ ∑ j ∈ Finset.range (n + 3 + i),
          |(generalRidgeStripeOriginalPrefixVerticalOne w i *
            generalRidgeBoxcar (n + 2)).coeff j|)
        (s := Finset.range (n + 2))
        (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ abs_nonneg
          ((generalRidgeStripeOriginalPrefixVerticalOne w i *
            generalRidgeBoxcar (n + 2)).coeff j)))
        (Finset.mem_range.mpr hk)

/-- One explicit scale threshold that controls all proper-prefix errors. -/
noncomputable def generalRidgeStripeCarrierThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  2 * (generalRidgeStripePrefixErrorBound w + 1)

theorem generalRidgeStripeCarrierThreshold_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    1 ≤ generalRidgeStripeCarrierThreshold w := by
  have hB := generalRidgeStripePrefixErrorBound_nonneg w
  unfold generalRidgeStripeCarrierThreshold
  linarith

private theorem generalRidgeStripe_scaled_error_le_one
    {n k q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeCarrierThreshold w ≤ T)
    (hk : k < n + 2) (hq : q < n + 3 + k) :
    2 * T⁻¹ *
        (generalRidgeStripeOriginalPrefixVerticalOne w k *
          generalRidgeBoxcar (n + 2)).coeff q ≤ 1 := by
  let B := generalRidgeStripePrefixErrorBound w
  let r := (generalRidgeStripeOriginalPrefixVerticalOne w k *
    generalRidgeBoxcar (n + 2)).coeff q
  have hB : 0 ≤ B := generalRidgeStripePrefixErrorBound_nonneg w
  have habs : |r| ≤ B :=
    generalRidgeStripePrefixErrorBound_coeff_abs_le w hk hq
  have hr : r ≤ B := (le_abs_self r).trans habs
  have hT' : 2 * (B + 1) ≤ T := by
    simpa [B, generalRidgeStripeCarrierThreshold] using hT
  have hTpos : 0 < T := by linarith
  have hinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
  have htwoB : 2 * B ≤ T := by linarith
  calc
    2 * T⁻¹ * r ≤ 2 * T⁻¹ * B := by
      exact mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (2 * B) * T⁻¹ := by ring
    _ ≤ T * T⁻¹ := mul_le_mul_of_nonneg_right htwoB hinv
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hTpos)

/-- A generic finite-chain bridge: if every nonempty list prefix transports
the carrier to values at least one on the northern two rows, then the
recursive carrier predicate holds for the complete list. -/
theorem northTwoUnitLowerAlong_of_take_fullConvChain_unitLower
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (carrier : Image rows cols)
    (hprefix : ∀ k : ℕ, 0 < k → k ≤ fs.length →
      ∀ p : ℕ, p ≤ 1 →
        p < grownSize 2 rows (fs.take k).length →
        ∀ q : ℕ, q < grownSize 2 cols (fs.take k).length →
          1 ≤ zeroExtend (fullConvChain (fs.take k) carrier) p q) :
    NorthTwoUnitLowerAlong fs carrier := by
  induction fs generalizing rows cols carrier with
  | nil => trivial
  | cons f fs ih =>
      constructor
      · intro p hp q
        have hp' : (p : ℕ) ≤ rows := by omega
        have hq' : (q : ℕ) ≤ cols := by omega
        simpa [fullConvChain, fullConvImage, zeroExtend, hp', hq']
          using (hprefix 1 (by omega) (by simp) p hp p.isLt q q.isLt)
      · apply ih (fullConvImage f.kernel carrier)
        intro k hkpos hklength p hp hprows q hpcols
        have h := hprefix (k + 1) (by omega) (by simp; omega)
          p hp hprows q hpcols
        change 1 ≤ zeroExtend
          (fullConvChain (fs.take k) (fullConvImage f.kernel carrier))
          p q at h
        exact h

/-- Taking a prefix of the public proper-factor block gives the corresponding
explicit proper prefix. -/
theorem generalRidgeStripeTwistedProperFactors_take_eq_properPrefix
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hk : k ≤ n + 1) :
    (generalRidgeStripeTwistedProperFactors w T).take k =
      generalRidgeStripeProperPrefix w T k := by
  rw [generalRidgeStripeTwistedProperFactors_eq_take, List.take_take,
    min_eq_left hk,
    ← generalRidgeStripeProperPrefix_eq_take_twistedFactors w T (by omega)]

/-- At every proper prefix, both northern rows of the constant carrier are
at least one on every genuine output column once `T` exceeds the global
threshold. -/
theorem generalRidgeStripeProperPrefix_carrier_unitLower
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeCarrierThreshold w ≤ T)
    (hk : k < n + 2) :
    ∀ p : Fin (grownSize 2 2
        (generalRidgeStripeProperPrefix w T k).length),
      (p : ℕ) ≤ 1 →
      ∀ q : Fin (grownSize 2 (n + 3)
          (generalRidgeStripeProperPrefix w T k).length),
        1 ≤ fullConvChain (generalRidgeStripeProperPrefix w T k)
          (constantImage 2 (n + 3) 2) p q := by
  have hlength :
      (generalRidgeStripeProperPrefix w T k).length = k := by
    simp [generalRidgeStripeProperPrefix, generalRidgeFactorList_length,
      Nat.min_eq_left (by omega : k ≤ n + 2)]
  intro p hp q
  have hq : (q : ℕ) < n + 3 + k := by
    simpa [hlength, grownSize_two_eq_add] using q.isLt
  have hsupport : (q : ℕ) ≤ k + (n + 2) := by omega
  have hbase :
      1 ≤ (generalRidgeNodalProduct k *
        generalRidgeBoxcar (n + 2)).coeff (q : ℕ) :=
    generalRidgeNodalProduct_mul_boxcar_coeff_one_le
      k (n + 2) q hsupport
  have hp_cases : (p : ℕ) = 0 ∨ (p : ℕ) = 1 := by omega
  rcases hp_cases with hp0 | hp1
  · have hp_eq : p = ⟨0, by
        simp [hlength, grownSize_two_eq_add]⟩ := Fin.ext hp0
    rw [hp_eq]
    have hrow := generalRidgeStripeProperPrefix_carrier_row_zero_coeff
      w T hk (q : ℕ)
    simp [zeroExtend, hlength, grownSize_two_eq_add, hq]
      at hrow
    rw [hrow]
    linarith
  · have hp_eq : p = ⟨1, by
        simpa [hlength, grownSize_two_eq_add] using
          (show 1 < 2 + k by omega)⟩ := Fin.ext hp1
    rw [hp_eq]
    have herror := generalRidgeStripe_scaled_error_le_one
      w T hT hk hq
    have hrow := generalRidgeStripeProperPrefix_carrier_row_one_coeff
      w T hk (q : ℕ)
    have hrowIndex : 1 < 2 + k := by omega
    simp [zeroExtend, hlength, grownSize_two_eq_add, hq, hrowIndex]
      at hrow
    rw [hrow]
    linarith

/-- Every reciprocal scale above the explicit threshold makes the complete
proper-factor block a unit-lower northern-two-row carrier. -/
theorem generalRidgeStripeTwistedProperFactors_unitLower_of_large
    {n : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeCarrierThreshold w ≤ T) :
    NorthTwoUnitLowerAlong
      (generalRidgeStripeTwistedProperFactors w T)
      (constantImage 2 (n + 3) 2) := by
  apply northTwoUnitLowerAlong_of_take_fullConvChain_unitLower
  intro k hkpos hklength p hp hprows q hpcols
  have hk : k ≤ n + 1 := by
    simpa using hklength
  have htake :=
    generalRidgeStripeTwistedProperFactors_take_eq_properPrefix w T hk
  rw [htake] at hprows hpcols ⊢
  have hprows' :
      p < 2 + (generalRidgeStripeProperPrefix w T k).length := by
    simpa [grownSize_two_eq_add] using hprows
  have hpcols' :
      q < n + 3 + (generalRidgeStripeProperPrefix w T k).length := by
    simpa [grownSize_two_eq_add] using hpcols
  have hunit := generalRidgeStripeProperPrefix_carrier_unitLower
    w T hT (by omega) ⟨p, hprows⟩ hp ⟨q, hpcols⟩
  simpa [zeroExtend, hprows', hpcols'] using hunit

/-- There is one upward-closed reciprocal-scale threshold for the signed
stripe's complete proper factor block. -/
theorem exists_generalRidgeStripeTwistedProperFactors_unitLower_threshold
    {n : ℕ} (w : Fin (n + 2) → ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      NorthTwoUnitLowerAlong
        (generalRidgeStripeTwistedProperFactors w T)
        (constantImage 2 (n + 3) 2) := by
  refine ⟨generalRidgeStripeCarrierThreshold w,
    generalRidgeStripeCarrierThreshold_one_le w, ?_⟩
  intro T hT
  exact generalRidgeStripeTwistedProperFactors_unitLower_of_large w T hT

end OneChannelCNNUniversality
