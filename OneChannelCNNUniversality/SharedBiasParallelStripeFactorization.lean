import OneChannelCNNUniversality.SharedBiasCompensatedCarrier
import OneChannelCNNUniversality.SharedBiasParallelStripeCompensation

/-!
# Two-ridge factorization for the compensated stripe

For two width-two weight vectors, store their four coefficients in the
collision-free polynomial

\[
  P(X)=w_{0,1}X+w_{0,0}X^2+w_{1,1}X^3+w_{1,0}X^4.
\]

This file gives explicit rational lower taps for the four compensated
horizontal factors.  Lean checks coefficientwise that the vertical-degree
one polynomial of their bilinear product is exactly `ε P`.  Consequently
the formal convolution chain reads the two scaled linear forms at columns
two and four.  The free nonzero scale `ε` will later be chosen small enough
that these lower taps do not destroy the positive compensated carrier.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

set_option maxHeartbeats 1000000

/-- Collision-free polynomial storing two width-two ridge weight vectors. -/
noncomputable def parallelStripePackedPolynomial
    (w : Fin 2 → Fin 2 → ℝ) : ℝ[X] :=
  C (w 0 1) * X + C (w 0 0) * X ^ 2 +
    C (w 1 1) * X ^ 3 + C (w 1 0) * X ^ 4

private noncomputable def parallelStripePackedFactorZero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : BilinearKernelFactor where
  a0 := 1 / 4
  a1 := 1
  b0 := ε *
    ((-16 * w 0 1 + 4 * w 0 0 - w 1 1 - 146 * w 1 0) / 585)
  b1 := ε * (-w 1 0)

private noncomputable def parallelStripePackedFactorOne
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : BilinearKernelFactor where
  a0 := 1
  a1 := -1
  b0 := ε * (2 * (w 0 1 + w 0 0 + w 1 1 + w 1 0) / 5)
  b1 := 0

private noncomputable def parallelStripePackedFactorTwo
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : BilinearKernelFactor where
  a0 := -2
  a1 := 1
  b0 := ε *
    ((8 * w 0 1 + 16 * w 0 0 + 32 * w 1 1 + 64 * w 1 0) / 9)
  b1 := 0

private noncomputable def parallelStripePackedFactorThree
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : BilinearKernelFactor where
  a0 := -3
  a1 := 1
  b0 := ε *
    (-(6 * w 0 1 + 18 * w 0 0 + 54 * w 1 1 + 162 * w 1 0) / 13)
  b1 := 0

/-- Ordered bilinear factors with horizontal parts
`X+1/4`, `1-X`, `X-2`, and `X-3`. -/
noncomputable def parallelStripePackedFactorList
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : List BilinearKernelFactor :=
  [parallelStripePackedFactorZero ε w,
    parallelStripePackedFactorOne ε w,
    parallelStripePackedFactorTwo ε w,
    parallelStripePackedFactorThree ε w]

@[simp] theorem parallelStripePackedFactorList_length
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    (parallelStripePackedFactorList ε w).length = 4 := by
  rfl

/-- Coefficientwise exact factorization through the complete degree budget. -/
theorem parallelStripePackedFactorList_verticalOne_coeff
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (q : ℕ) (hq : q ≤ 4) :
    (verticalOne (parallelStripePackedFactorList ε w)).coeff q =
      (C ε * parallelStripePackedPolynomial w).coeff q := by
  interval_cases q <;>
    norm_num [parallelStripePackedFactorList,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
      parallelStripePackedPolynomial, verticalOne, horizontalProduct,
      BilinearKernelFactor.A, BilinearKernelFactor.B, linearPolynomial,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;>
    ring

/-- The first packed target column reads the first scaled linear form. -/
theorem parallelStripePackedFullConv_target_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w) x) 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1) := by
  rw [fullConvChain_row_one_reversed_dot, bivariateProduct_coeff_one]
  simp only [Fin.sum_univ_two]
  norm_num
  rw [parallelStripePackedFactorList_verticalOne_coeff ε w 2 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε w 1 (by omega)]
  norm_num [parallelStripePackedPolynomial, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  ring

/-- The second packed target column reads the second scaled linear form. -/
theorem parallelStripePackedFullConv_target_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    zeroExtend
        (fullConvChain (parallelStripePackedFactorList ε w) x) 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1) := by
  rw [fullConvChain_row_one_reversed_dot, bivariateProduct_coeff_one]
  simp only [Fin.sum_univ_two]
  norm_num
  rw [parallelStripePackedFactorList_verticalOne_coeff ε w 4 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε w 3 (by omega)]
  norm_num [parallelStripePackedPolynomial, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C]
  ring

end OneChannelCNNUniversality
