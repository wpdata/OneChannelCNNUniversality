import OneChannelCNNUniversality.SharedBiasParallelStripeFactorization

/-!
# Correcting the packed two-target carrier

The packed vertical taps perturb the second row of the compensated carrier.
For the doubled carrier, a single weight-dependent correction at the
southwest input site restores the exact common baseline at target columns
two and four.  This is an exact algebraic correction, not an asymptotic one.
-/

namespace OneChannelCNNUniversality

open Polynomial
open Filter
open scoped Topology

set_option maxHeartbeats 5000000

/-- The first three packed factors, with doubled compensated biases. -/
noncomputable def parallelStripePackedProperSteps
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : List CompensatedBilinearStep :=
  [{ factor := parallelStripePackedFactorZero ε w, bias := 0 },
    { factor := parallelStripePackedFactorOne ε w, bias := 10 },
    { factor := parallelStripePackedFactorTwo ε w, bias := 26 }]

/-- The scalar discrepancy forced by the packed target polynomial. -/
noncomputable def parallelStripePackedCarrierDiscrepancy
    (w : Fin 2 → Fin 2 → ℝ) : ℝ :=
  w 0 1 - w 1 1 - w 1 0

/-- Doubled width-three boxcar carrier, with one southwest correction.
The correction is chosen so that multiplication by the complete horizontal
product cancels the target-baseline discrepancy caused by the vertical taps. -/
noncomputable def parallelStripeCorrectedCarrier
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 2 3 :=
  fun p q ↦
    8 + if (p : ℕ) = 1 ∧ (q : ℕ) = 0 then
      (16 / 17 : ℝ) * ε * parallelStripePackedCarrierDiscrepancy w
    else 0

/-- Northern-row generating polynomial of the doubled input carrier. -/
noncomputable def parallelStripeCorrectedNorthZero : ℝ[X] :=
  C 8 * generalRidgeBoxcar 2

/-- First-southern-row generating polynomial of the corrected input carrier. -/
noncomputable def parallelStripeCorrectedSouthZero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  parallelStripeCorrectedNorthZero +
    C ((16 / 17 : ℝ) * ε * parallelStripePackedCarrierDiscrepancy w)

noncomputable def parallelStripeCorrectedNorthOne
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorZero ε w).A *
    parallelStripeCorrectedNorthZero

noncomputable def parallelStripeCorrectedSouthOne
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorZero ε w).A *
      parallelStripeCorrectedSouthZero ε w +
    (parallelStripePackedFactorZero ε w).B *
      parallelStripeCorrectedNorthZero

noncomputable def parallelStripeCorrectedNorthTwo
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorOne ε w).A *
      parallelStripeCorrectedNorthOne ε w +
    C 10 * generalRidgeBoxcar 4

noncomputable def parallelStripeCorrectedSouthTwo
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorOne ε w).A *
      parallelStripeCorrectedSouthOne ε w +
    (parallelStripePackedFactorOne ε w).B *
      parallelStripeCorrectedNorthOne ε w +
    C 10 * generalRidgeBoxcar 4

noncomputable def parallelStripeCorrectedNorthThree
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorTwo ε w).A *
      parallelStripeCorrectedNorthTwo ε w +
    C 26 * generalRidgeBoxcar 5

noncomputable def parallelStripeCorrectedSouthThree
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorTwo ε w).A *
      parallelStripeCorrectedSouthTwo ε w +
    (parallelStripePackedFactorTwo ε w).B *
      parallelStripeCorrectedNorthTwo ε w +
    C 26 * generalRidgeBoxcar 5

/-- First-southern-row carrier polynomial after the final packed factor. -/
noncomputable def parallelStripeCorrectedFinalCarrier
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  (parallelStripePackedFactorThree ε w).A *
      parallelStripeCorrectedSouthThree ε w +
    (parallelStripePackedFactorThree ε w).B *
      parallelStripeCorrectedNorthThree ε w

private theorem rowPolynomial_add_image {rows cols : ℕ}
    (x y : Image rows cols) (p : ℕ) :
    rowPolynomial (x + y) p = rowPolynomial x p + rowPolynomial y p := by
  ext q
  simp only [rowPolynomial_coeff, zeroExtend_add, coeff_add]

private theorem rowPolynomial_constantImage_boxcar
    (rows n : ℕ) (c : ℝ) (p : ℕ) (hp : p < rows) :
    rowPolynomial (constantImage rows (n + 1) c) p =
      C c * generalRidgeBoxcar n := by
  ext q
  rw [rowPolynomial_coeff, coeff_C_mul, generalRidgeBoxcar_coeff]
  by_cases hq : q < n + 1
  · have hqle : q ≤ n := by omega
    simp [zeroExtend, constantImage, hp, hq, hqle]
  · have hqle : ¬q ≤ n := by omega
    simp [zeroExtend, hp, hq, hqle]

private theorem rowPolynomial_fullConv_factor_zero
    {rows cols : ℕ} (f : BilinearKernelFactor) (x : Image rows cols) :
    rowPolynomial (fullConvImage f.kernel x) 0 =
      f.A * rowPolynomial x 0 := by
  exact rowPolynomial_fullConv_zero x f.a0 f.a1 f.b0 f.b1

private theorem rowPolynomial_fullConv_factor_one
    {rows cols : ℕ} (f : BilinearKernelFactor) (x : Image rows cols) :
    rowPolynomial (fullConvImage f.kernel x) 1 =
      f.A * rowPolynomial x 1 + f.B * rowPolynomial x 0 := by
  exact rowPolynomial_fullConv_one x f.a0 f.a1 f.b0 f.b1

private theorem parallelStripeCorrectedCarrier_row_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrier ε w) 0 =
      parallelStripeCorrectedNorthZero := by
  ext q
  rw [rowPolynomial_coeff]
  by_cases hq : q < 3
  · interval_cases q <;>
      norm_num [parallelStripeCorrectedCarrier,
        parallelStripeCorrectedNorthZero, generalRidgeBoxcar_coeff,
        zeroExtend, coeff_C_mul, coeff_C]
  · have hqle : ¬q ≤ 2 := by omega
    simp [parallelStripeCorrectedNorthZero, zeroExtend, hq, hqle,
      generalRidgeBoxcar_coeff, coeff_C_mul]

private theorem parallelStripeCorrectedCarrier_row_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrier ε w) 1 =
      parallelStripeCorrectedSouthZero ε w := by
  ext q
  rw [rowPolynomial_coeff]
  by_cases hq : q < 3
  · interval_cases q <;>
      norm_num [parallelStripeCorrectedCarrier,
        parallelStripeCorrectedSouthZero,
        parallelStripeCorrectedNorthZero, generalRidgeBoxcar_coeff,
        zeroExtend, coeff_add, coeff_C_mul, coeff_C]
  · have hqle : ¬q ≤ 2 := by omega
    have hq0 : q ≠ 0 := by omega
    simp [parallelStripeCorrectedSouthZero,
      parallelStripeCorrectedNorthZero, zeroExtend, hq, hqle, hq0,
      generalRidgeBoxcar_coeff, coeff_add, coeff_C_mul, coeff_C]

private noncomputable def parallelStripeCorrectedCarrierStageOne
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 3 4 :=
  fullConvImage (parallelStripePackedFactorZero ε w).kernel
      (parallelStripeCorrectedCarrier ε w) +
    constantImage 3 4 0

private noncomputable def parallelStripeCorrectedCarrierStageTwo
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 4 5 :=
  fullConvImage (parallelStripePackedFactorOne ε w).kernel
      (parallelStripeCorrectedCarrierStageOne ε w) +
    constantImage 4 5 10

private noncomputable def parallelStripeCorrectedCarrierStageThree
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 5 6 :=
  fullConvImage (parallelStripePackedFactorTwo ε w).kernel
      (parallelStripeCorrectedCarrierStageTwo ε w) +
    constantImage 5 6 26

private theorem parallelStripeCorrectedCarrierStageOne_row_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageOne ε w) 0 =
      parallelStripeCorrectedNorthOne ε w := by
  rw [parallelStripeCorrectedCarrierStageOne, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_zero,
    parallelStripeCorrectedCarrier_row_zero,
    rowPolynomial_constantImage_boxcar 3 3 0 0 (by omega)]
  simp [parallelStripeCorrectedNorthOne]

private theorem parallelStripeCorrectedCarrierStageOne_row_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageOne ε w) 1 =
      parallelStripeCorrectedSouthOne ε w := by
  rw [parallelStripeCorrectedCarrierStageOne, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_one,
    parallelStripeCorrectedCarrier_row_zero,
    parallelStripeCorrectedCarrier_row_one,
    rowPolynomial_constantImage_boxcar 3 3 0 1 (by omega)]
  simp [parallelStripeCorrectedSouthOne]

private theorem parallelStripeCorrectedCarrierStageTwo_row_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageTwo ε w) 0 =
      parallelStripeCorrectedNorthTwo ε w := by
  rw [parallelStripeCorrectedCarrierStageTwo, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_zero,
    parallelStripeCorrectedCarrierStageOne_row_zero,
    rowPolynomial_constantImage_boxcar 4 4 10 0 (by omega)]
  rfl

private theorem parallelStripeCorrectedCarrierStageTwo_row_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageTwo ε w) 1 =
      parallelStripeCorrectedSouthTwo ε w := by
  rw [parallelStripeCorrectedCarrierStageTwo, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_one,
    parallelStripeCorrectedCarrierStageOne_row_zero,
    parallelStripeCorrectedCarrierStageOne_row_one,
    rowPolynomial_constantImage_boxcar 4 4 10 1 (by omega)]
  rfl

private theorem parallelStripeCorrectedCarrierStageThree_row_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageThree ε w) 0 =
      parallelStripeCorrectedNorthThree ε w := by
  rw [parallelStripeCorrectedCarrierStageThree, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_zero,
    parallelStripeCorrectedCarrierStageTwo_row_zero,
    rowPolynomial_constantImage_boxcar 5 5 26 0 (by omega)]
  rfl

private theorem parallelStripeCorrectedCarrierStageThree_row_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial (parallelStripeCorrectedCarrierStageThree ε w) 1 =
      parallelStripeCorrectedSouthThree ε w := by
  rw [parallelStripeCorrectedCarrierStageThree, rowPolynomial_add_image,
    rowPolynomial_fullConv_factor_one,
    parallelStripeCorrectedCarrierStageTwo_row_zero,
    parallelStripeCorrectedCarrierStageTwo_row_one,
    rowPolynomial_constantImage_boxcar 5 5 26 1 (by omega)]
  rfl

private theorem parallelStripeCorrectedCarrierChain_eq_stageThree
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    compensatedCarrierChain (parallelStripePackedProperSteps ε w)
        (parallelStripeCorrectedCarrier ε w) =
      parallelStripeCorrectedCarrierStageThree ε w := by
  rfl

/-- The symbolic corrected recurrence is exactly the first-southern-row
polynomial of the genuine compensated carrier followed by the final factor. -/
theorem parallelStripeCorrectedFinalCarrier_rowPolynomial
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    rowPolynomial
        (fullConvImage (parallelStripePackedFactorThree ε w).kernel
          (compensatedCarrierChain
            (parallelStripePackedProperSteps ε w)
            (parallelStripeCorrectedCarrier ε w))) 1 =
      parallelStripeCorrectedFinalCarrier ε w := by
  change rowPolynomial
      (fullConvImage (parallelStripePackedFactorThree ε w).kernel
        (parallelStripeCorrectedCarrierStageThree ε w)) 1 = _
  rw [rowPolynomial_fullConv_factor_one,
    parallelStripeCorrectedCarrierStageThree_row_zero,
    parallelStripeCorrectedCarrierStageThree_row_one]
  rfl

private theorem continuous_parallelStripeCorrectedSouthOne_coeff
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 4) :
    Continuous fun ε : ℝ =>
      (parallelStripeCorrectedSouthOne ε w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedSouthOne,
      parallelStripeCorrectedSouthZero, parallelStripeCorrectedNorthZero,
      parallelStripePackedFactorZero, parallelStripePackedCarrierDiscrepancy,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
    fun_prop

private theorem continuous_parallelStripeCorrectedSouthTwo_coeff
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 5) :
    Continuous fun ε : ℝ =>
      (parallelStripeCorrectedSouthTwo ε w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedSouthTwo,
      parallelStripeCorrectedSouthOne, parallelStripeCorrectedSouthZero,
      parallelStripeCorrectedNorthOne, parallelStripeCorrectedNorthZero,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedCarrierDiscrepancy,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
    fun_prop

private theorem continuous_parallelStripeCorrectedSouthThree_coeff
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 6) :
    Continuous fun ε : ℝ =>
      (parallelStripeCorrectedSouthThree ε w).coeff q := by
  fin_cases q <;>
    norm_num (config := { maxSteps := 1000000 })
      [parallelStripeCorrectedSouthThree,
        parallelStripeCorrectedSouthTwo,
        parallelStripeCorrectedSouthOne,
        parallelStripeCorrectedSouthZero,
        parallelStripeCorrectedNorthTwo,
        parallelStripeCorrectedNorthOne,
        parallelStripeCorrectedNorthZero,
        parallelStripePackedFactorZero, parallelStripePackedFactorOne,
        parallelStripePackedFactorTwo,
        parallelStripePackedCarrierDiscrepancy,
        BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
        generalRidgeBoxcar_coeff, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
    fun_prop

private theorem continuous_parallelStripeCorrectedFinalCarrier_gap
    (w : Fin 2 → Fin 2 → ℝ) :
    Continuous fun ε : ℝ =>
      (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 := by
  norm_num (config := { maxSteps := 1000000 })
    [parallelStripeCorrectedFinalCarrier,
      parallelStripeCorrectedNorthZero, parallelStripeCorrectedSouthZero,
      parallelStripeCorrectedNorthOne, parallelStripeCorrectedSouthOne,
      parallelStripeCorrectedNorthTwo, parallelStripeCorrectedSouthTwo,
      parallelStripeCorrectedNorthThree, parallelStripeCorrectedSouthThree,
      parallelStripePackedCarrierDiscrepancy,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]
  fun_prop

private theorem parallelStripeCorrectedSouthOne_zero_ge_two
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 4) :
    2 ≤ (parallelStripeCorrectedSouthOne 0 w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedSouthOne,
      parallelStripeCorrectedSouthZero, parallelStripeCorrectedNorthZero,
      parallelStripePackedFactorZero, parallelStripePackedCarrierDiscrepancy,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedSouthTwo_zero_ge_two
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 5) :
    2 ≤ (parallelStripeCorrectedSouthTwo 0 w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedSouthTwo,
      parallelStripeCorrectedSouthOne, parallelStripeCorrectedSouthZero,
      parallelStripeCorrectedNorthOne, parallelStripeCorrectedNorthZero,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedCarrierDiscrepancy,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedSouthThree_zero_ge_two
    (w : Fin 2 → Fin 2 → ℝ) (q : Fin 6) :
    2 ≤ (parallelStripeCorrectedSouthThree 0 w).coeff q := by
  fin_cases q <;>
    norm_num (config := { maxSteps := 1000000 })
      [parallelStripeCorrectedSouthThree,
        parallelStripeCorrectedSouthTwo,
        parallelStripeCorrectedSouthOne,
        parallelStripeCorrectedSouthZero,
        parallelStripeCorrectedNorthTwo,
        parallelStripeCorrectedNorthOne,
        parallelStripeCorrectedNorthZero,
        parallelStripePackedFactorZero, parallelStripePackedFactorOne,
        parallelStripePackedFactorTwo,
        parallelStripePackedCarrierDiscrepancy,
        BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
        generalRidgeBoxcar_coeff, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedFinalCarrier_gap_zero
    (w : Fin 2 → Fin 2 → ℝ) :
    (parallelStripeCorrectedFinalCarrier 0 w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier 0 w).coeff 2 = 34 := by
  norm_num (config := { maxSteps := 1000000 })
    [parallelStripeCorrectedFinalCarrier,
      parallelStripeCorrectedNorthZero, parallelStripeCorrectedSouthZero,
      parallelStripeCorrectedNorthOne, parallelStripeCorrectedSouthOne,
      parallelStripeCorrectedNorthTwo, parallelStripeCorrectedSouthTwo,
      parallelStripeCorrectedNorthThree, parallelStripeCorrectedSouthThree,
      parallelStripePackedCarrierDiscrepancy,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem continuous_parallelStripeCorrectedCarrier_apply
    (w : Fin 2 → Fin 2 → ℝ) (p : Fin 2) (q : Fin 3) :
    Continuous fun ε : ℝ ↦ parallelStripeCorrectedCarrier ε w p q := by
  fin_cases p <;> fin_cases q <;>
    simp [parallelStripeCorrectedCarrier] <;> fun_prop

/-- A small positive packed scale can additionally be chosen so that the
corrected carrier is already strictly above one at every input site. -/
private theorem exists_parallelStripeCorrected_positive_scale_with_input
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ p q, 1 < parallelStripeCorrectedCarrier ε w p q) ∧
      (∀ q : Fin 4, 1 < (parallelStripeCorrectedSouthOne ε w).coeff q) ∧
      (∀ q : Fin 5, 1 < (parallelStripeCorrectedSouthTwo ε w).coeff q) ∧
      (∀ q : Fin 6, 1 < (parallelStripeCorrectedSouthThree ε w).coeff q) ∧
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 := by
  have hinput : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ p q, 1 < parallelStripeCorrectedCarrier ε w p q :=
    Filter.eventually_all.2 fun p ↦ Filter.eventually_all.2 fun q ↦
      continuousAt_const.eventually_lt
        (continuous_parallelStripeCorrectedCarrier_apply w p q).continuousAt
        (by simp [parallelStripeCorrectedCarrier])
  have h₁ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ q : Fin 4, 1 < (parallelStripeCorrectedSouthOne ε w).coeff q :=
    Filter.eventually_all.2 fun q ↦
      continuousAt_const.eventually_lt
        (continuous_parallelStripeCorrectedSouthOne_coeff w q).continuousAt
        (lt_of_lt_of_le one_lt_two
          (parallelStripeCorrectedSouthOne_zero_ge_two w q))
  have h₂ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ q : Fin 5, 1 < (parallelStripeCorrectedSouthTwo ε w).coeff q :=
    Filter.eventually_all.2 fun q ↦
      continuousAt_const.eventually_lt
        (continuous_parallelStripeCorrectedSouthTwo_coeff w q).continuousAt
        (lt_of_lt_of_le one_lt_two
          (parallelStripeCorrectedSouthTwo_zero_ge_two w q))
  have h₃ : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ q : Fin 6, 1 < (parallelStripeCorrectedSouthThree ε w).coeff q :=
    Filter.eventually_all.2 fun q ↦
      continuousAt_const.eventually_lt
        (continuous_parallelStripeCorrectedSouthThree_coeff w q).continuousAt
        (lt_of_lt_of_le one_lt_two
          (parallelStripeCorrectedSouthThree_zero_ge_two w q))
  have hgap : ∀ᶠ ε in 𝓝 (0 : ℝ),
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 :=
    continuousAt_const.eventually_lt
      (continuous_parallelStripeCorrectedFinalCarrier_gap w).continuousAt
      (by rw [parallelStripeCorrectedFinalCarrier_gap_zero]; norm_num)
  have hall := hinput.and (h₁.and (h₂.and (h₃.and hgap)))
  rcases Metric.mem_nhds_iff.1 hall with ⟨r, hr, hball⟩
  refine ⟨r / 2, by linarith, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by linarith)]
  linarith

/-- A strictly positive packed scale simultaneously preserves all three
proper southern-row margins and the final middle-to-target gap. -/
theorem exists_parallelStripeCorrected_positive_scale
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ q : Fin 4, 1 < (parallelStripeCorrectedSouthOne ε w).coeff q) ∧
      (∀ q : Fin 5, 1 < (parallelStripeCorrectedSouthTwo ε w).coeff q) ∧
      (∀ q : Fin 6, 1 < (parallelStripeCorrectedSouthThree ε w).coeff q) ∧
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 := by
  rcases exists_parallelStripeCorrected_positive_scale_with_input w with
    ⟨ε, hε, _hinput, h₁, h₂, h₃, hgap⟩
  exact ⟨ε, hε, h₁, h₂, h₃, hgap⟩

private theorem parallelStripeCorrectedNorthOne_ge_two
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (q : Fin 4) :
    2 ≤ (parallelStripeCorrectedNorthOne ε w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedNorthOne,
      parallelStripeCorrectedNorthZero, parallelStripePackedFactorZero,
      BilinearKernelFactor.A, linearPolynomial, generalRidgeBoxcar_coeff,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedNorthTwo_ge_two
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (q : Fin 5) :
    2 ≤ (parallelStripeCorrectedNorthTwo ε w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedNorthTwo,
      parallelStripeCorrectedNorthOne,
      parallelStripeCorrectedNorthZero, parallelStripePackedFactorZero,
      parallelStripePackedFactorOne,
      BilinearKernelFactor.A, linearPolynomial, generalRidgeBoxcar_coeff,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedNorthThree_ge_two
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (q : Fin 6) :
    2 ≤ (parallelStripeCorrectedNorthThree ε w).coeff q := by
  fin_cases q <;>
    norm_num [parallelStripeCorrectedNorthThree,
      parallelStripeCorrectedNorthTwo,
      parallelStripeCorrectedNorthOne,
      parallelStripeCorrectedNorthZero, parallelStripePackedFactorZero,
      parallelStripePackedFactorOne, parallelStripePackedFactorTwo,
      BilinearKernelFactor.A, linearPolynomial, generalRidgeBoxcar_coeff,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]

private theorem parallelStripeCorrectedCarrierStageOne_unitLower
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (hsouth : ∀ q : Fin 4,
      1 < (parallelStripeCorrectedSouthOne ε w).coeff q) :
    ∀ p : Fin 3, (p : ℕ) ≤ 1 → ∀ q : Fin 4,
      1 ≤ parallelStripeCorrectedCarrierStageOne ε w p q := by
  intro p hp q
  fin_cases p
  · have h := parallelStripeCorrectedNorthOne_ge_two ε w q
    rw [← parallelStripeCorrectedCarrierStageOne_row_zero,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using one_lt_two.le.trans h
  · have h := (hsouth q).le
    rw [← parallelStripeCorrectedCarrierStageOne_row_one,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using h
  · norm_num at hp

private theorem parallelStripeCorrectedCarrierStageTwo_unitLower
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (hsouth : ∀ q : Fin 5,
      1 < (parallelStripeCorrectedSouthTwo ε w).coeff q) :
    ∀ p : Fin 4, (p : ℕ) ≤ 1 → ∀ q : Fin 5,
      1 ≤ parallelStripeCorrectedCarrierStageTwo ε w p q := by
  intro p hp q
  fin_cases p
  · have h := parallelStripeCorrectedNorthTwo_ge_two ε w q
    rw [← parallelStripeCorrectedCarrierStageTwo_row_zero,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using one_lt_two.le.trans h
  · have h := (hsouth q).le
    rw [← parallelStripeCorrectedCarrierStageTwo_row_one,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using h
  · norm_num at hp
  · norm_num at hp

private theorem parallelStripeCorrectedCarrierStageThree_unitLower
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (hsouth : ∀ q : Fin 6,
      1 < (parallelStripeCorrectedSouthThree ε w).coeff q) :
    ∀ p : Fin 5, (p : ℕ) ≤ 1 → ∀ q : Fin 6,
      1 ≤ parallelStripeCorrectedCarrierStageThree ε w p q := by
  intro p hp q
  fin_cases p
  · have h := parallelStripeCorrectedNorthThree_ge_two ε w q
    rw [← parallelStripeCorrectedCarrierStageThree_row_zero,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using one_lt_two.le.trans h
  · have h := (hsouth q).le
    rw [← parallelStripeCorrectedCarrierStageThree_row_one,
      rowPolynomial_coeff] at h
    simpa [zeroExtend] using h
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp

private theorem parallelStripeCorrected_unitLower_of_polynomial_margins
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (h₁ : ∀ q : Fin 4,
      1 < (parallelStripeCorrectedSouthOne ε w).coeff q)
    (h₂ : ∀ q : Fin 5,
      1 < (parallelStripeCorrectedSouthTwo ε w).coeff q)
    (h₃ : ∀ q : Fin 6,
      1 < (parallelStripeCorrectedSouthThree ε w).coeff q) :
    NorthTwoCompensatedUnitLowerAlong
      (parallelStripePackedProperSteps ε w)
      (parallelStripeCorrectedCarrier ε w) := by
  have hs₁ := parallelStripeCorrectedCarrierStageOne_unitLower ε w h₁
  have hs₂ := parallelStripeCorrectedCarrierStageTwo_unitLower ε w h₂
  have hs₃ := parallelStripeCorrectedCarrierStageThree_unitLower ε w h₃
  simp only [parallelStripePackedProperSteps,
    NorthTwoCompensatedUnitLowerAlong]
  refine ⟨?_, ?_⟩
  · intro p hp q
    simpa [parallelStripeCorrectedCarrierStageOne,
      fullConvImage, constantImage] using hs₁ p hp q
  refine ⟨?_, ?_⟩
  · intro p hp q
    simpa [parallelStripeCorrectedCarrierStageOne,
      parallelStripeCorrectedCarrierStageTwo,
      fullConvImage, constantImage] using hs₂ p hp q
  refine ⟨?_, ?_⟩
  · intro p hp q
    simpa [parallelStripeCorrectedCarrierStageOne,
      parallelStripeCorrectedCarrierStageTwo,
      parallelStripeCorrectedCarrierStageThree,
      fullConvImage, constantImage] using hs₃ p hp q
  trivial

/-- There is a positive packed scale whose corrected carrier satisfies the
complete three-step northern-two-row unit-lower hypothesis, while the final
two-target selector retains a strict unit gap. -/
theorem exists_parallelStripeCorrected_unitLower_and_gap
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      NorthTwoCompensatedUnitLowerAlong
        (parallelStripePackedProperSteps ε w)
        (parallelStripeCorrectedCarrier ε w) ∧
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 := by
  rcases exists_parallelStripeCorrected_positive_scale w with
    ⟨ε, hε, h₁, h₂, h₃, hgap⟩
  exact ⟨ε, hε,
    parallelStripeCorrected_unitLower_of_polynomial_margins ε w h₁ h₂ h₃,
    hgap⟩

/-- There is one positive packed scale satisfying the proper-prefix and final
gap conditions while the corrected input carrier is pointwise at least one. -/
theorem exists_parallelStripeCorrected_unitLower_gap_and_inputPositive
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ p q, 1 ≤ parallelStripeCorrectedCarrier ε w p q) ∧
      NorthTwoCompensatedUnitLowerAlong
        (parallelStripePackedProperSteps ε w)
        (parallelStripeCorrectedCarrier ε w) ∧
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 := by
  rcases exists_parallelStripeCorrected_positive_scale_with_input w with
    ⟨ε, hε, hinput, h₁, h₂, h₃, hgap⟩
  exact ⟨ε, hε, fun p q ↦ (hinput p q).le,
    parallelStripeCorrected_unitLower_of_polynomial_margins ε w h₁ h₂ h₃,
    hgap⟩

/-- The southwest correction restores the exact common carrier baseline at
the two packed target columns, for every scale `ε` and every pair of weights. -/
theorem parallelStripeCorrectedFinalCarrier_common_targets
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    (parallelStripeCorrectedFinalCarrier ε w).coeff 2 =
      (parallelStripeCorrectedFinalCarrier ε w).coeff 4 := by
  norm_num (config := { maxSteps := 1000000 }) [parallelStripeCorrectedFinalCarrier,
    parallelStripeCorrectedNorthZero, parallelStripeCorrectedSouthZero,
    parallelStripeCorrectedNorthOne, parallelStripeCorrectedSouthOne,
    parallelStripeCorrectedNorthTwo, parallelStripeCorrectedSouthTwo,
    parallelStripeCorrectedNorthThree, parallelStripeCorrectedSouthThree,
    parallelStripePackedCarrierDiscrepancy, compensatedCarrierChain,
    parallelStripePackedFactorZero, parallelStripePackedFactorOne,
    parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
    BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
    generalRidgeBoxcar_coeff, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]
  ring

/-- At zero perturbation the corrected doubled carrier retains the doubled
middle-to-target gap `34`. -/
theorem parallelStripeCorrectedFinalCarrier_middle_gap_at_zero
    (w : Fin 2 → Fin 2 → ℝ) :
    (parallelStripeCorrectedFinalCarrier 0 w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier 0 w).coeff 2 = 34 :=
  parallelStripeCorrectedFinalCarrier_gap_zero w

/-- Image-level common-baseline identity for the corrected compensated
carrier followed by the final packed convolution. -/
theorem parallelStripeCorrectedFinalImage_common_targets
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    zeroExtend
        (fullConvImage (parallelStripePackedFactorThree ε w).kernel
          (compensatedCarrierChain
            (parallelStripePackedProperSteps ε w)
            (parallelStripeCorrectedCarrier ε w))) 1 2 =
      zeroExtend
        (fullConvImage (parallelStripePackedFactorThree ε w).kernel
          (compensatedCarrierChain
            (parallelStripePackedProperSteps ε w)
            (parallelStripeCorrectedCarrier ε w))) 1 4 := by
  rw [← rowPolynomial_coeff, ← rowPolynomial_coeff,
    parallelStripeCorrectedFinalCarrier_rowPolynomial,
    parallelStripeCorrectedFinalCarrier_common_targets]

/-- At zero perturbation the genuine final carrier image has gap `34`. -/
theorem parallelStripeCorrectedFinalImage_middle_gap_at_zero
    (w : Fin 2 → Fin 2 → ℝ) :
    zeroExtend
        (fullConvImage (parallelStripePackedFactorThree 0 w).kernel
          (compensatedCarrierChain
            (parallelStripePackedProperSteps 0 w)
            (parallelStripeCorrectedCarrier 0 w))) 1 3 -
      zeroExtend
        (fullConvImage (parallelStripePackedFactorThree 0 w).kernel
          (compensatedCarrierChain
            (parallelStripePackedProperSteps 0 w)
            (parallelStripeCorrectedCarrier 0 w))) 1 2 = 34 := by
  rw [← rowPolynomial_coeff, ← rowPolynomial_coeff,
    parallelStripeCorrectedFinalCarrier_rowPolynomial,
    parallelStripeCorrectedFinalCarrier_middle_gap_at_zero]

end OneChannelCNNUniversality
