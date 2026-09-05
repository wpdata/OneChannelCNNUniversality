import OneChannelCNNUniversality.SharedBiasNondestructiveCarrier
import OneChannelCNNUniversality.SharedBiasParallelStripeFactorization

/-!
# A usable expanded workspace interface

The lossless depth-two carrier initializer has a stronger local property on a
width-two input.  Its northwest `2 × 2` block is an affine difference code:
subtracting the second row from the first recovers `x₀` and the increment
`x₁ - x₀`.  Hence one further shared-bias `2 × 2` layer can compute an
arbitrary affine ReLU ridge at a fixed output site.  The carrier cancels
exactly in this local readout, so no external crop or affine preprocessing is
used.
-/

namespace OneChannelCNNUniversality

open Set
open Polynomial

/-- The vertical-difference readout kernel for the affine functional
`w₀ x₀ + w₁ x₁` on the expanded workspace code. -/
def expandedWorkspaceRidgeKernel (w : Fin 2 → ℝ) : Kernel 2 2 :=
  ![![-w 1, -(w 0 + w 1)],
    ![w 1, w 0 + w 1]]

/-- The first input coordinate is the first vertical difference in the
nondestructive expanded state. -/
theorem nondestructiveBoundaryTransform_oneTwo_decode_zero
    (x : Image 1 2) :
    nondestructiveBoundaryTransform x 0 0 -
        nondestructiveBoundaryTransform x 1 0 = x 0 0 := by
  norm_num [nondestructiveBoundaryTransform, fullConvImage,
    horizontalBoundaryKernel, expansiveIdentityKernel, twoTapKernel,
    deltaKernel, fullConv, zeroExtend]

/-- Adding the two first vertical differences recovers the second input
coordinate. -/
theorem nondestructiveBoundaryTransform_oneTwo_decode_one
    (x : Image 1 2) :
    (nondestructiveBoundaryTransform x 0 0 -
          nondestructiveBoundaryTransform x 1 0) +
        (nondestructiveBoundaryTransform x 0 1 -
          nondestructiveBoundaryTransform x 1 1) = x 0 1 := by
  norm_num [nondestructiveBoundaryTransform, fullConvImage,
    horizontalBoundaryKernel, expansiveIdentityKernel, twoTapKernel,
    deltaKernel, fullConv, zeroExtend]

/-- The local readout cancels the fixed carrier and evaluates the requested
linear functional exactly at output coordinate `(1,1)`. -/
theorem expandedWorkspaceRidgeKernel_preactivation
    (w : Fin 2 → ℝ) (x : Image 1 2) (c b : ℝ) :
    fullConv (expandedWorkspaceRidgeKernel w)
        (nondestructiveBoundaryTransform x +
          horizontalSharedCarrier 2 3 c b) 1 1 =
      w 0 * x 0 0 + w 1 * x 0 1 := by
  norm_num [expandedWorkspaceRidgeKernel, nondestructiveBoundaryTransform,
    horizontalSharedCarrier, horizontalBoundaryKernel,
    expansiveIdentityKernel, fullConvImage, fullConv, twoTapKernel,
    deltaKernel, constantImage, zeroExtend]
  ring

/-- Cumulative reparameterization of two width-two weights for the horizontal
difference code.  Successive coefficient differences recover the four
original ridge weights. -/
def expandedWorkspacePackedWeights
    (w : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![w 0 0 + w 0 1, w 0 1],
    ![w 0 0 + w 0 1 + w 1 0 + w 1 1,
      w 0 0 + w 0 1 + w 1 1]]

/-- The first target of the existing four-factor packing algebra remains an
arbitrary linear form when its input is the generated difference code. -/
theorem expandedWorkspacePackedFullConv_target_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    zeroExtend
        (fullConvChain
          (parallelStripePackedFactorList ε
            (expandedWorkspacePackedWeights w))
          (nondestructiveBoundaryTransform x)) 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1) := by
  rw [← rowPolynomial_coeff, rowPolynomial_fullConvChain_one, coeff_add,
    coeff_mul, coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  rw [parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 2 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 1 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 0 (by omega)]
  norm_num [parallelStripePackedPolynomial, expandedWorkspacePackedWeights,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, rowPolynomial_coeff,
    nondestructiveBoundaryTransform, fullConvImage, horizontalBoundaryKernel,
    expansiveIdentityKernel, twoTapKernel, deltaKernel, fullConv, zeroExtend]
  ring

/-- The second target likewise recovers the second arbitrary linear form.
Thus workspace expansion introduces no algebraic loss in the two-ridge signal
packing step. -/
theorem expandedWorkspacePackedFullConv_target_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) :
    zeroExtend
        (fullConvChain
          (parallelStripePackedFactorList ε
            (expandedWorkspacePackedWeights w))
          (nondestructiveBoundaryTransform x)) 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1) := by
  rw [← rowPolynomial_coeff, rowPolynomial_fullConvChain_one, coeff_add,
    coeff_mul, coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  rw [parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 4 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 3 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 2 (by omega),
    parallelStripePackedFactorList_verticalOne_coeff ε
      (expandedWorkspacePackedWeights w) 1 (by omega)]
  norm_num [parallelStripePackedPolynomial, expandedWorkspacePackedWeights,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, rowPolynomial_coeff,
    nondestructiveBoundaryTransform, fullConvImage, horizontalBoundaryKernel,
    expansiveIdentityKernel, twoTapKernel, deltaKernel, fullConv, zeroExtend]
  ring

/-- **Exact affine ridge through a network-generated expanded interface.**

On every compact family of width-two inputs, two genuine expansive
shared-bias ReLU layers first create a nonnegative `3 × 4` workspace with a
fixed spatially nonuniform carrier and an injective signal code.  A third
genuine layer reads that code locally and computes any prescribed affine
ReLU ridge exactly at `(1,1)`. -/
theorem exists_depthThree_expandedWorkspace_ridge_on_compact
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → ℝ) (theta : ℝ) :
    ∃ net : SharedBiasNetworkTo 2 2 1 2 4 5,
      net.net.depth = 3 ∧
        ∀ x ∈ K,
          net.eval x 1 1 =
            relu (w 0 * x 0 0 + w 1 * x 0 1 + theta) := by
  obtain ⟨initializer, c, b, carrier, hc, hb, hdepth, hcarrier,
      _hnonuniform, heval, _hinjective⟩ :=
    exists_depthTwo_nondestructive_nonuniform_carrier_on_compact
      K hK (by norm_num)
  let ridge : SharedBiasNetworkTo 2 2 3 4 4 5 :=
    SharedBiasNetworkTo.single (expandedWorkspaceRidgeKernel w) theta
  let net : SharedBiasNetworkTo 2 2 1 2 4 5 := initializer.append ridge
  refine ⟨net, ?_, ?_⟩
  · change (initializer.append ridge).net.depth = 3
    rw [SharedBiasNetworkTo.depth_append, hdepth]
    rfl
  · intro x hx
    change (initializer.append ridge).eval x 1 1 = _
    rw [SharedBiasNetworkTo.eval_append]
    change (SharedBiasNetworkTo.single
      (expandedWorkspaceRidgeKernel w) theta).eval
        (initializer.eval x) 1 1 = _
    rw [SharedBiasNetworkTo.eval_single]
    change relu
        (fullConv (expandedWorkspaceRidgeKernel w) (initializer.eval x) 1 1 +
          theta) = _
    rw [heval x hx, hcarrier,
      expandedWorkspaceRidgeKernel_preactivation]

end OneChannelCNNUniversality
