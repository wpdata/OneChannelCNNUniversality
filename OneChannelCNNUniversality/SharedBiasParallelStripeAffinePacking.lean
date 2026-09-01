import OneChannelCNNUniversality.SharedBiasParallelStripeProperNetwork

/-!
# Packing two independent affine ridge offsets

The packed vertical polynomial already transports two independent linear
forms from the northern input row.  A second input row supplies two further
degrees of freedom.  We solve the resulting two-by-two linear system and use
that row to insert independent affine offsets at the two target columns.

Thus the complete four-factor convolution produces

\[
  \varepsilon (w_{0,0}x_0+w_{0,1}x_1+\theta_0),\qquad
  \varepsilon (w_{1,0}x_0+w_{1,1}x_1+\theta_1)
\]

at positions `(1,2)` and `(1,4)`, respectively.  This is the algebraic step
that lets one final shared-bias ReLU layer activate two ridges with genuinely
independent affine offsets.
-/

namespace OneChannelCNNUniversality

open Polynomial
open scoped Polynomial

set_option maxHeartbeats 5000000

/-- Constant coefficient of the southern offset seed. -/
noncomputable def parallelStripeOffsetSeedZero (a b : ℝ) : ℝ :=
  (-38 * a - 6 * b) / 367

/-- Quadratic coefficient of the southern offset seed. -/
noncomputable def parallelStripeOffsetSeedTwo (a b : ℝ) : ℝ :=
  (4 * a - 38 * b) / 367

/-- A two-row, width-three seed.  The original width-two input occupies the
northern row.  The southern row encodes the two requested target offsets. -/
noncomputable def parallelStripeAffineSeed
    (ε : ℝ) (θ : Fin 2 → ℝ) (x : Image 1 2) : Image 2 3 :=
  ![![x 0 0, x 0 1, 0],
    ![parallelStripeOffsetSeedZero (ε * θ 0) (ε * θ 1), 0,
      parallelStripeOffsetSeedTwo (ε * θ 0) (ε * θ 1)]]

/-- The affine packing map is coordinatewise continuous on every input set. -/
theorem continuousFeatureOn_parallelStripeAffineSeed
    (K : Set (Image 1 2)) (ε : ℝ) (θ : Fin 2 → ℝ) :
    ContinuousFeatureOn K (parallelStripeAffineSeed ε θ) := by
  intro p q
  fin_cases p <;> fin_cases q
  · simpa [parallelStripeAffineSeed] using
      (continuousFeatureOn_identity K (0 : Fin 1) (0 : Fin 2))
  · simpa [parallelStripeAffineSeed] using
      (continuousFeatureOn_identity K (0 : Fin 1) (1 : Fin 2))
  · simpa [parallelStripeAffineSeed] using
      (continuousOn_const : ContinuousOn (fun _ : Image 1 2 ↦ (0 : ℝ)) K)
  · simpa [parallelStripeAffineSeed] using
      (continuousOn_const : ContinuousOn
        (fun _ : Image 1 2 ↦
          parallelStripeOffsetSeedZero (ε * θ 0) (ε * θ 1)) K)
  · simpa [parallelStripeAffineSeed] using
      (continuousOn_const : ContinuousOn (fun _ : Image 1 2 ↦ (0 : ℝ)) K)
  · simpa [parallelStripeAffineSeed] using
      (continuousOn_const : ContinuousOn
        (fun _ : Image 1 2 ↦
          parallelStripeOffsetSeedTwo (ε * θ 0) (ε * θ 1)) K)

private theorem parallelStripeAffineSeed_row_zero
    (ε : ℝ) (θ : Fin 2 → ℝ) (x : Image 1 2) :
    rowPolynomial (parallelStripeAffineSeed ε θ x) 0 =
      linearPolynomial (x 0 0) (x 0 1) := by
  simp [rowPolynomial, parallelStripeAffineSeed, linearPolynomial,
    Fin.sum_univ_succ, ← C_mul_X_pow_eq_monomial]

private theorem parallelStripeAffineSeed_row_one
    (ε : ℝ) (θ : Fin 2 → ℝ) (x : Image 1 2) :
    rowPolynomial (parallelStripeAffineSeed ε θ x) 1 =
      C (parallelStripeOffsetSeedZero (ε * θ 0) (ε * θ 1)) +
        C (parallelStripeOffsetSeedTwo (ε * θ 0) (ε * θ 1)) * X ^ 2 := by
  simp [rowPolynomial, parallelStripeAffineSeed, Fin.sum_univ_succ,
    ← C_mul_X_pow_eq_monomial]

private theorem parallelStripePackedHorizontal_offset_coeff_two
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    (horizontalProduct (parallelStripePackedFactorList ε w) *
        (C (parallelStripeOffsetSeedZero (ε * θ 0) (ε * θ 1)) +
          C (parallelStripeOffsetSeedTwo (ε * θ 0) (ε * θ 1)) * X ^ 2)).coeff 2 =
      ε * θ 0 := by
  norm_num [parallelStripePackedFactorList,
    parallelStripePackedFactorZero, parallelStripePackedFactorOne,
    parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
    horizontalProduct, BilinearKernelFactor.A, linearPolynomial,
    parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
  ring

private theorem parallelStripePackedHorizontal_offset_coeff_four
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    (horizontalProduct (parallelStripePackedFactorList ε w) *
        (C (parallelStripeOffsetSeedZero (ε * θ 0) (ε * θ 1)) +
          C (parallelStripeOffsetSeedTwo (ε * θ 0) (ε * θ 1)) * X ^ 2)).coeff 4 =
      ε * θ 1 := by
  norm_num [parallelStripePackedFactorList,
    parallelStripePackedFactorZero, parallelStripePackedFactorOne,
    parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
    horizontalProduct, BilinearKernelFactor.A, linearPolynomial,
    parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
  ring

private theorem parallelStripePackedVertical_input_coeff_two
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    (verticalOne (parallelStripePackedFactorList ε w) *
        linearPolynomial (x 0 0) (x 0 1)).coeff 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1) := by
  rw [coeff_mul]
  norm_num [linearPolynomial,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  rw [parallelStripePackedFactorList_verticalOne_coeff ε w 2 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε w 1 (by omega)]
  norm_num [parallelStripePackedPolynomial, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  ring

private theorem parallelStripePackedVertical_input_coeff_four
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    (verticalOne (parallelStripePackedFactorList ε w) *
        linearPolynomial (x 0 0) (x 0 1)).coeff 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1) := by
  rw [coeff_mul]
  norm_num [linearPolynomial,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  rw [parallelStripePackedFactorList_verticalOne_coeff ε w 4 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε w 3 (by omega)]
  norm_num [parallelStripePackedPolynomial, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  ring

/-- Exact first affine target of the complete packed convolution. -/
theorem parallelStripePackedFullConv_affine_target_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w)
          (parallelStripeAffineSeed ε θ x)) 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) := by
  rw [← rowPolynomial_coeff, rowPolynomial_fullConvChain_one,
    parallelStripeAffineSeed_row_zero, parallelStripeAffineSeed_row_one,
    coeff_add, parallelStripePackedHorizontal_offset_coeff_two,
    parallelStripePackedVertical_input_coeff_two]
  ring

/-- Exact second affine target of the complete packed convolution. -/
theorem parallelStripePackedFullConv_affine_target_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w)
          (parallelStripeAffineSeed ε θ x)) 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  rw [← rowPolynomial_coeff, rowPolynomial_fullConvChain_one,
    parallelStripeAffineSeed_row_zero, parallelStripeAffineSeed_row_one,
    coeff_add, parallelStripePackedHorizontal_offset_coeff_four,
    parallelStripePackedVertical_input_coeff_four]
  ring

/-- Append the fourth packed convolution to the pure variable component of
the three compensated proper layers. -/
noncomputable def parallelStripePackedFinalVariable
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (V : Image 2 3) : Image 6 7 :=
  fullConvImage (parallelStripePackedFactorThree ε w).kernel
    (compensatedVariableChain (parallelStripePackedProperSteps ε w) V)

/-- The proper-chain variable semantics followed by the fourth convolution
is definitionally the complete packed four-factor convolution. -/
theorem parallelStripePackedFinalVariable_eq_fullConvChain
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (V : Image 2 3) :
    parallelStripePackedFinalVariable ε w V =
      fullConvChain (parallelStripePackedFactorList ε w) V := by
  rfl

/-- First affine target after the three proper layers and final convolution. -/
theorem parallelStripePackedFinalVariable_affine_target_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    parallelStripePackedFinalVariable ε w
        (parallelStripeAffineSeed ε θ x) 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) := by
  rw [parallelStripePackedFinalVariable_eq_fullConvChain]
  exact parallelStripePackedFullConv_affine_target_zero ε w θ x

/-- Second affine target after the three proper layers and final convolution. -/
theorem parallelStripePackedFinalVariable_affine_target_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) :
    parallelStripePackedFinalVariable ε w
        (parallelStripeAffineSeed ε θ x) 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  rw [parallelStripePackedFinalVariable_eq_fullConvChain]
  exact parallelStripePackedFullConv_affine_target_one ε w θ x

end OneChannelCNNUniversality
