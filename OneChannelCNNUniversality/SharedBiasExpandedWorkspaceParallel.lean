import OneChannelCNNUniversality.SharedBiasAffineCompensatedCarrier
import OneChannelCNNUniversality.SharedBiasExpandedWorkspace

/-!
# Two affine ridges from an internally generated expanded workspace

The depth-two boundary initializer can be incorporated into the compensated
factor chain itself.  Its carrier biases are scaled, while one fixed bias in
the first packing layer records the difference of two requested affine
offsets.  The remaining carrier biases only enforce positivity and do not
change the difference between the two target sites.
-/

namespace OneChannelCNNUniversality

open Set
open Filter
open scoped Topology

set_option maxHeartbeats 2000000

/-- Bilinear form of the expansive identity kernel. -/
def expandedWorkspaceIdentityFactor : BilinearKernelFactor where
  a0 := 1
  a1 := 0
  b0 := 0
  b1 := 0

/-- Bilinear form of the horizontal first-difference kernel. -/
def expandedWorkspaceBoundaryFactor : BilinearKernelFactor where
  a0 := 1
  a1 := -1
  b0 := 0
  b1 := 0

@[simp] theorem expandedWorkspaceIdentityFactor_kernel :
    expandedWorkspaceIdentityFactor.kernel = expansiveIdentityKernel := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp [expandedWorkspaceIdentityFactor, BilinearKernelFactor.kernel,
      bilinearKernel, expansiveIdentityKernel, deltaKernel]

@[simp] theorem expandedWorkspaceBoundaryFactor_kernel :
    expandedWorkspaceBoundaryFactor.kernel = horizontalBoundaryKernel := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp [expandedWorkspaceBoundaryFactor, BilinearKernelFactor.kernel,
      bilinearKernel, horizontalBoundaryKernel, twoTapKernel, deltaKernel]

@[simp] theorem constantImage_zero_eq_zero (rows cols : ℕ) :
    constantImage rows cols 0 = (0 : Image rows cols) := by
  rfl

@[simp] theorem fullConvImage_zero_input
    {kRows kCols rows cols : ℕ} (kernel : Kernel kRows kCols) :
    fullConvImage kernel (0 : Image rows cols) = 0 := by
  funext p q
  simp [fullConvImage]

/-- Two carrier-only affine-compensated steps generate the lossless
`3 × 4` boundary workspace from the original `1 × 2` input. -/
def expandedWorkspaceInitializerSteps :
    List AffineCompensatedBilinearStep :=
  [{ factor := expandedWorkspaceIdentityFactor,
      signalBias := 0, carrierBias := 1 },
    { factor := expandedWorkspaceBoundaryFactor,
      signalBias := 0, carrierBias := 2 }]

/-- Unit-scale carrier produced by the two initializer steps. -/
def expandedWorkspaceUnitCarrier : Image 3 4 :=
  affineCompensatedCarrierChain expandedWorkspaceInitializerSteps
    (0 : Image 1 2)

/-- Closed form of the internally generated unit carrier. -/
theorem expandedWorkspaceUnitCarrier_eq_horizontal :
    expandedWorkspaceUnitCarrier = horizontalSharedCarrier 2 3 1 2 := by
  unfold expandedWorkspaceUnitCarrier
  simp only [expandedWorkspaceInitializerSteps,
    affineCompensatedCarrierChain]
  funext p q
  fin_cases p <;> fin_cases q <;>
    norm_num [expandedWorkspaceIdentityFactor,
      expandedWorkspaceBoundaryFactor, BilinearKernelFactor.kernel,
      bilinearKernel, horizontalSharedCarrier, horizontalBoundaryKernel,
      twoTapKernel, fullConvImage, fullConv, constantImage, zeroExtend,
      deltaKernel]

/-- Explicit first-layer carrier bias that balances the two final targets. -/
noncomputable def expandedWorkspaceRawCarrierDifference
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ :=
  47 / 4 + ε *
    (4 * w 0 0 + 3 * w 0 1 + 3 * w 1 0 + 5 * w 1 1)

/-- Closed form of the unbalanced target difference. -/
theorem expandedWorkspaceRawCarrierDifference_formula
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    expandedWorkspaceRawCarrierDifference ε w =
      47 / 4 + ε *
        (4 * w 0 0 + 3 * w 0 1 + 3 * w 1 0 + 5 * w 1 1) := by
  simp [expandedWorkspaceRawCarrierDifference]

/-- A fixed signal bias in the first packed layer stores the difference
between the requested affine offsets. -/
noncomputable def expandedWorkspaceOffsetSignalBias
    (ε : ℝ) (theta : Fin 2 → ℝ) : ℝ :=
  ε * (theta 0 - theta 1)

/-- Five proper steps: two generate the workspace and three transport the
two packed signals.  `d₁` and `d₂` are free carrier-only positivity biases. -/
noncomputable def expandedWorkspaceParallelProperSteps
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) : List AffineCompensatedBilinearStep :=
  expandedWorkspaceInitializerSteps ++
    [{ factor := parallelStripePackedFactorZero ε
          (expandedWorkspacePackedWeights w),
        signalBias := expandedWorkspaceOffsetSignalBias ε theta,
        carrierBias := expandedWorkspaceRawCarrierDifference ε w },
      { factor := parallelStripePackedFactorOne ε
          (expandedWorkspacePackedWeights w),
        signalBias := 0, carrierBias := d₁ },
      { factor := parallelStripePackedFactorTwo ε
          (expandedWorkspacePackedWeights w),
        signalBias := 0, carrierBias := d₂ }]

@[simp] theorem expandedWorkspaceParallelProperSteps_length
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) :
    (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂).length = 5 := by
  rfl

/-- Carrier-only view of the three packed proper steps. -/
noncomputable def expandedWorkspaceParallelCarrierSteps
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (d₁ d₂ : ℝ) :
    List AffineCompensatedBilinearStep :=
  [{ factor := parallelStripePackedFactorZero ε
        (expandedWorkspacePackedWeights w),
      signalBias := 0,
      carrierBias := expandedWorkspaceRawCarrierDifference ε w },
    { factor := parallelStripePackedFactorOne ε
        (expandedWorkspacePackedWeights w),
      signalBias := 0, carrierBias := d₁ },
    { factor := parallelStripePackedFactorTwo ε
        (expandedWorkspacePackedWeights w),
      signalBias := 0, carrierBias := d₂ }]

/-- Response of the last three packed factors to a broadcast bias inserted
after the first packed factor. -/
noncomputable def expandedWorkspaceOffsetResponse
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (r : ℝ) : Image 7 8 :=
  fullConvChain
    [parallelStripePackedFactorOne ε (expandedWorkspacePackedWeights w),
      parallelStripePackedFactorTwo ε (expandedWorkspacePackedWeights w),
      parallelStripePackedFactorThree ε (expandedWorkspacePackedWeights w)]
    (constantImage 4 5 r)

/-- The offset response differs by exactly the inserted scalar between the
two packed targets. -/
theorem expandedWorkspaceOffsetResponse_difference
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (r : ℝ) :
    expandedWorkspaceOffsetResponse ε w r 1 2 -
        expandedWorkspaceOffsetResponse ε w r 1 4 = r := by
  norm_num [expandedWorkspaceOffsetResponse, fullConvChain, fullConvImage,
    parallelStripePackedFactorOne, parallelStripePackedFactorTwo,
    parallelStripePackedFactorThree, expandedWorkspacePackedWeights,
    BilinearKernelFactor.kernel, bilinearKernel, fullConv,
    constantImage, zeroExtend, deltaKernel]

/-- Final carrier after the five proper steps and the fourth packed
convolution. -/
noncomputable def expandedWorkspaceParallelFinalCarrier
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (d₁ d₂ : ℝ) : Image 7 8 :=
  fullConvImage
    (parallelStripePackedFactorThree ε
      (expandedWorkspacePackedWeights w)).kernel
    (affineCompensatedCarrierChain
      (expandedWorkspaceParallelCarrierSteps ε w d₁ d₂)
      expandedWorkspaceUnitCarrier)

/-- The balancing carrier bias makes the two target carrier values equal;
the later two broadcast carrier biases do not alter that equality. -/
theorem expandedWorkspaceParallelFinalCarrier_common_targets
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (d₁ d₂ : ℝ) :
    expandedWorkspaceParallelFinalCarrier ε w d₁ d₂ 1 2 =
      expandedWorkspaceParallelFinalCarrier ε w d₁ d₂ 1 4 := by
  simp only [expandedWorkspaceParallelFinalCarrier,
    expandedWorkspaceParallelCarrierSteps,
    affineCompensatedCarrierChain]
  rw [expandedWorkspaceRawCarrierDifference_formula]
  rw [expandedWorkspaceUnitCarrier_eq_horizontal]
  norm_num (config := { maxSteps := 1000000 })
    [
      expandedWorkspaceRawCarrierDifference,
      expandedWorkspaceUnitCarrier, fullConvChain, fullConvImage,
      expandedWorkspaceIdentityFactor,
      expandedWorkspaceBoundaryFactor,
      parallelStripePackedFactorZero, parallelStripePackedFactorOne,
      parallelStripePackedFactorTwo, parallelStripePackedFactorThree,
      parallelStripePackedFactorList, expandedWorkspacePackedWeights,
      BilinearKernelFactor.kernel, bilinearKernel, horizontalSharedCarrier,
      horizontalBoundaryKernel, twoTapKernel, fullConv, constantImage,
      zeroExtend, deltaKernel, grownSize]
  ring

/-- Every finite convolution state admits a shared scalar bias that raises
all output coordinates above one. -/
theorem exists_unitLower_shared_bias
    {rows cols : ℕ} (factor : BilinearKernelFactor)
    (carrier : Image rows cols) :
    ∃ bias : ℝ, ∀ p : Fin (rows + 2 - 1),
      ∀ q : Fin (cols + 2 - 1),
        1 ≤ fullConv factor.kernel carrier p q + bias := by
  let bias : ℝ :=
    (∑ p : Fin (rows + 2 - 1),
      ∑ q : Fin (cols + 2 - 1),
        |fullConv factor.kernel carrier p q|) + 1
  refine ⟨bias, ?_⟩
  intro p q
  have hnonneg : ∀ p' : Fin (rows + 2 - 1),
      ∀ q' : Fin (cols + 2 - 1),
        0 ≤ |fullConv factor.kernel carrier p' q'| :=
    fun _ _ ↦ abs_nonneg _
  have hq : |fullConv factor.kernel carrier p q| ≤
      ∑ q' : Fin (cols + 2 - 1),
        |fullConv factor.kernel carrier p q'| := by
    exact Finset.single_le_sum (fun q' _ ↦ hnonneg p q')
      (Finset.mem_univ q)
  have hp : (∑ q' : Fin (cols + 2 - 1),
      |fullConv factor.kernel carrier p q'|) ≤
      ∑ p' : Fin (rows + 2 - 1),
        ∑ q' : Fin (cols + 2 - 1),
          |fullConv factor.kernel carrier p' q'| := by
    exact Finset.single_le_sum
      (fun p' _ ↦ Finset.sum_nonneg fun q' _ ↦ hnonneg p' q')
      (Finset.mem_univ p)
  have hneg : -|fullConv factor.kernel carrier p q| ≤
      fullConv factor.kernel carrier p q := neg_abs_le _
  have htotal : |fullConv factor.kernel carrier p q| ≤
      ∑ p' : Fin (rows + 2 - 1),
        ∑ q' : Fin (cols + 2 - 1),
          |fullConv factor.kernel carrier p' q'| := hq.trans hp
  have hz : 0 ≤ fullConv factor.kernel carrier p q +
      |fullConv factor.kernel carrier p q| := by
    linarith
  have hsum : fullConv factor.kernel carrier p q +
      |fullConv factor.kernel carrier p q| ≤
      fullConv factor.kernel carrier p q +
        ∑ p' : Fin (rows + 2 - 1),
          ∑ q' : Fin (cols + 2 - 1),
            |fullConv factor.kernel carrier p' q'| :=
    by simpa [add_comm] using
      (add_le_add_left htotal (fullConv factor.kernel carrier p q))
  dsimp [bias]
  calc
    1 = 0 + 1 := by ring
    _ ≤ (fullConv factor.kernel carrier p q +
          |fullConv factor.kernel carrier p q|) + 1 :=
      by simpa [add_comm] using add_le_add_right hz 1
    _ ≤ (fullConv factor.kernel carrier p q +
          ∑ p' : Fin (rows + 2 - 1),
            ∑ q' : Fin (cols + 2 - 1),
              |fullConv factor.kernel carrier p' q'|) + 1 :=
      by simpa [add_comm] using add_le_add_right hsum 1
    _ = fullConv factor.kernel carrier p q +
          ((∑ p' : Fin (rows + 2 - 1),
            ∑ q' : Fin (cols + 2 - 1),
              |fullConv factor.kernel carrier p' q'|) + 1) := by ring

/-- Carrier state after the first packed factor and its balancing bias. -/
noncomputable def expandedWorkspaceParallelCarrierStageOne
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 4 5 :=
  fullConvImage
      (parallelStripePackedFactorZero ε
        (expandedWorkspacePackedWeights w)).kernel
      expandedWorkspaceUnitCarrier +
    constantImage 4 5 (expandedWorkspaceRawCarrierDifference ε w)

private theorem expandedWorkspaceParallelCarrierStageOne_zero_gt_one
    (w : Fin 2 → Fin 2 → ℝ) (p : Fin 4) (q : Fin 5) :
    1 < expandedWorkspaceParallelCarrierStageOne 0 w p q := by
  rw [expandedWorkspaceParallelCarrierStageOne,
    expandedWorkspaceUnitCarrier_eq_horizontal]
  fin_cases p <;> fin_cases q <;>
    norm_num [
      expandedWorkspaceRawCarrierDifference,
      expandedWorkspacePackedWeights,
      parallelStripePackedFactorZero, BilinearKernelFactor.kernel,
      bilinearKernel, horizontalSharedCarrier, horizontalBoundaryKernel,
      twoTapKernel, fullConvImage, fullConv, constantImage, zeroExtend,
      deltaKernel]

private theorem continuous_expandedWorkspaceParallelCarrierStageOne_apply
    (w : Fin 2 → Fin 2 → ℝ) (p : Fin 4) (q : Fin 5) :
    Continuous fun ε : ℝ ↦
      expandedWorkspaceParallelCarrierStageOne ε w p q := by
  rw [show (fun ε : ℝ ↦
      expandedWorkspaceParallelCarrierStageOne ε w p q) =
      (fun ε : ℝ ↦
        (fullConvImage
          (parallelStripePackedFactorZero ε
            (expandedWorkspacePackedWeights w)).kernel
          (horizontalSharedCarrier 2 3 1 2) +
        constantImage 4 5
          (expandedWorkspaceRawCarrierDifference ε w)) p q) by
    funext ε
    rw [expandedWorkspaceParallelCarrierStageOne,
      expandedWorkspaceUnitCarrier_eq_horizontal]]
  fin_cases p <;> fin_cases q <;>
    norm_num [
      expandedWorkspaceRawCarrierDifference,
      expandedWorkspacePackedWeights,
      parallelStripePackedFactorZero, BilinearKernelFactor.kernel,
      bilinearKernel, horizontalSharedCarrier, horizontalBoundaryKernel,
      twoTapKernel, fullConvImage, fullConv, constantImage, zeroExtend,
      deltaKernel] <;> fun_prop

/-- A positive packing scale keeps the first packed carrier stage uniformly
above one. -/
theorem exists_expandedWorkspace_positive_packing_scale
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ p q, 1 < expandedWorkspaceParallelCarrierStageOne ε w p q := by
  have hall : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ p q, 1 < expandedWorkspaceParallelCarrierStageOne ε w p q :=
    Filter.eventually_all.2 fun p ↦ Filter.eventually_all.2 fun q ↦
      continuousAt_const.eventually_lt
        (continuous_expandedWorkspaceParallelCarrierStageOne_apply
          w p q).continuousAt
        (expandedWorkspaceParallelCarrierStageOne_zero_gt_one w p q)
  rcases Metric.mem_nhds_iff.1 hall with ⟨radius, hradius, hball⟩
  refine ⟨radius / 2, by linarith, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by linarith)]
  linarith

/-- The two initializer carrier steps turn the zero input carrier into the
unit expanded-workspace carrier. -/
theorem expandedWorkspaceInitializerCarrier_eq :
    affineCompensatedCarrierChain expandedWorkspaceInitializerSteps
        (0 : Image 1 2) = expandedWorkspaceUnitCarrier := by
  rfl

/-- The initializer itself satisfies the unit-lower carrier invariant. -/
theorem expandedWorkspaceInitializer_unitLower :
    AffineNorthTwoCompensatedUnitLowerAlong
      expandedWorkspaceInitializerSteps (0 : Image 1 2) := by
  simp only [expandedWorkspaceInitializerSteps,
    AffineNorthTwoCompensatedUnitLowerAlong]
  refine ⟨?_, ?_⟩
  · intro p hp q
    fin_cases p <;> fin_cases q <;>
      norm_num [expandedWorkspaceIdentityFactor,
        BilinearKernelFactor.kernel, bilinearKernel, fullConv, zeroExtend,
        deltaKernel]
  refine ⟨?_, trivial⟩
  intro p hp q
  fin_cases p <;> fin_cases q <;>
    norm_num [expandedWorkspaceIdentityFactor,
      expandedWorkspaceBoundaryFactor, BilinearKernelFactor.kernel,
      bilinearKernel, fullConvImage, fullConv, constantImage, zeroExtend,
      deltaKernel]

/-- There are two later carrier biases for which all five proper layers have
the northern-two-row unit-lower certificate. -/
theorem exists_expandedWorkspaceParallel_unitLower
    (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ) :
    ∃ ε d₁ d₂ : ℝ, 0 < ε ∧
      AffineNorthTwoCompensatedUnitLowerAlong
        (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂)
        (0 : Image 1 2) := by
  rcases exists_expandedWorkspace_positive_packing_scale w with
    ⟨ε, hε, hfirst⟩
  let factorOne := parallelStripePackedFactorOne ε
    (expandedWorkspacePackedWeights w)
  obtain ⟨d₁, hd₁⟩ := exists_unitLower_shared_bias factorOne
    (expandedWorkspaceParallelCarrierStageOne ε w)
  let carrierTwo : Image 5 6 :=
    fullConvImage factorOne.kernel
        (expandedWorkspaceParallelCarrierStageOne ε w) +
      constantImage 5 6 d₁
  let factorTwo := parallelStripePackedFactorTwo ε
    (expandedWorkspacePackedWeights w)
  obtain ⟨d₂, hd₂⟩ := exists_unitLower_shared_bias factorTwo carrierTwo
  refine ⟨ε, d₁, d₂, hε, ?_⟩
  rw [expandedWorkspaceParallelProperSteps,
    affineNorthTwoCompensatedUnitLowerAlong_append_iff]
  refine ⟨expandedWorkspaceInitializer_unitLower, ?_⟩
  simp only [AffineNorthTwoCompensatedUnitLowerAlong]
  refine ⟨?_, ?_⟩
  · intro p hp q
    exact (hfirst p q).le
  refine ⟨?_, ?_⟩
  · intro p hp q
    change Fin 5 at p
    change Fin 6 at q
    exact hd₁ p q
  refine ⟨?_, trivial⟩
  intro p hp q
  change Fin 6 at p
  change Fin 7 at q
  exact hd₂ p q

/-- Proper affine variable state with normalized dimensions. -/
noncomputable def expandedWorkspaceParallelProperVariable
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) (x : Image 1 2) : Image 6 7 :=
  affineCompensatedVariableChain
    (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂) x

/-- Proper carrier state with normalized dimensions. -/
noncomputable def expandedWorkspaceParallelProperCarrier
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) : Image 6 7 :=
  affineCompensatedCarrierChain
    (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂)
    (0 : Image 1 2)

/-- The affine variable part after all five proper layers and the final
packed convolution. -/
noncomputable def expandedWorkspaceParallelFinalVariable
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) (x : Image 1 2) : Image 7 8 :=
  fullConvImage
    (parallelStripePackedFactorThree ε
      (expandedWorkspacePackedWeights w)).kernel
    (expandedWorkspaceParallelProperVariable ε w theta d₁ d₂ x)

/-- The initializer's affine variable recursion is exactly the previously
defined nondestructive boundary transform. -/
theorem expandedWorkspaceInitializerVariable_eq (x : Image 1 2) :
    affineCompensatedVariableChain expandedWorkspaceInitializerSteps x =
      nondestructiveBoundaryTransform x := by
  simp only [expandedWorkspaceInitializerSteps,
    affineCompensatedVariableChain,
    expandedWorkspaceIdentityFactor_kernel,
    expandedWorkspaceBoundaryFactor_kernel]
  funext p q
  simp [nondestructiveBoundaryTransform, fullConvImage, fullConv]

/-- The pure four-factor packed signal, with dimensions normalized to the
expanded workspace. -/
noncomputable def expandedWorkspacePackedLinearSignal
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (x : Image 1 2) : Image 7 8 :=
  fullConvChain
    (parallelStripePackedFactorList ε (expandedWorkspacePackedWeights w))
    (nondestructiveBoundaryTransform x)

/-- The complete affine variable output is the packed linear signal plus
the response to the fixed offset-difference bias. -/
theorem expandedWorkspaceParallelFinalVariable_eq
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) (x : Image 1 2) :
    expandedWorkspaceParallelFinalVariable ε w theta d₁ d₂ x =
      expandedWorkspacePackedLinearSignal ε w x +
        expandedWorkspaceOffsetResponse ε w
          (expandedWorkspaceOffsetSignalBias ε theta) := by
  simp [expandedWorkspaceParallelFinalVariable,
    expandedWorkspaceParallelProperVariable,
    expandedWorkspaceParallelProperSteps,
    expandedWorkspaceInitializerSteps,
    affineCompensatedVariableChain,
    expandedWorkspacePackedLinearSignal,
    expandedWorkspaceOffsetResponse,
    parallelStripePackedFactorList, fullConvChain,
    expandedWorkspaceIdentityFactor_kernel,
    expandedWorkspaceBoundaryFactor_kernel,
    nondestructiveBoundaryTransform, fullConvImage_add]

/-- First affine variable target before the final shared bias. -/
theorem expandedWorkspaceParallelFinalVariable_target_zero
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) (x : Image 1 2) :
    expandedWorkspaceParallelFinalVariable ε w theta d₁ d₂ x 1 2 =
      ε * (w 0 0 * x 0 0 + w 0 1 * x 0 1) +
        expandedWorkspaceOffsetResponse ε w
          (expandedWorkspaceOffsetSignalBias ε theta) 1 2 := by
  rw [expandedWorkspaceParallelFinalVariable_eq]
  simp only [Pi.add_apply]
  have h := expandedWorkspacePackedFullConv_target_zero ε w x
  change zeroExtend (expandedWorkspacePackedLinearSignal ε w x) 1 2 = _ at h
  simpa [zeroExtend] using congrArg
    (fun z ↦ z + expandedWorkspaceOffsetResponse ε w
      (expandedWorkspaceOffsetSignalBias ε theta) 1 2) h

/-- Second affine variable target before the final shared bias. -/
theorem expandedWorkspaceParallelFinalVariable_target_one
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) (x : Image 1 2) :
    expandedWorkspaceParallelFinalVariable ε w theta d₁ d₂ x 1 4 =
      ε * (w 1 0 * x 0 0 + w 1 1 * x 0 1) +
        expandedWorkspaceOffsetResponse ε w
          (expandedWorkspaceOffsetSignalBias ε theta) 1 4 := by
  rw [expandedWorkspaceParallelFinalVariable_eq]
  simp only [Pi.add_apply]
  have h := expandedWorkspacePackedFullConv_target_one ε w x
  change zeroExtend (expandedWorkspacePackedLinearSignal ε w x) 1 4 = _ at h
  simpa [zeroExtend] using congrArg
    (fun z ↦ z + expandedWorkspaceOffsetResponse ε w
      (expandedWorkspaceOffsetSignalBias ε theta) 1 4) h

/-- Carrier recursion for the combined five-step chain is the packed carrier
recursion started from the internally generated unit workspace carrier. -/
theorem expandedWorkspaceParallelCarrierChain_eq
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ : ℝ) :
    expandedWorkspaceParallelProperCarrier ε w theta d₁ d₂ =
      affineCompensatedCarrierChain
        (expandedWorkspaceParallelCarrierSteps ε w d₁ d₂)
      expandedWorkspaceUnitCarrier := by
  rfl

/-- Final bias that removes the common scaled carrier baseline and aligns
the second affine offset. -/
noncomputable def expandedWorkspaceParallelFinalBias
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ scale : ℝ) : ℝ :=
  ε * theta 1 -
    expandedWorkspaceOffsetResponse ε w
      (expandedWorkspaceOffsetSignalBias ε theta) 1 4 -
    scale * expandedWorkspaceParallelFinalCarrier ε w d₁ d₂ 1 4

/-- The genuine six-layer network, including the two-layer internal
workspace initializer. -/
private def expandedWorkspaceParallelReindexNetworkTo
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols) :
    SharedBiasNetworkTo kRows kCols inRows inCols outRows' outCols' :=
  ⟨net.net, net.rows_eq.trans hrows, net.cols_eq.trans hcols⟩

private theorem zeroExtend_expandedWorkspaceParallelReindexNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) (p q : ℕ) :
    zeroExtend
        ((expandedWorkspaceParallelReindexNetworkTo hrows hcols net).eval x)
        p q =
      zeroExtend (net.eval x) p q := by
  subst outRows'
  subst outCols'
  rfl

noncomputable def expandedWorkspaceParallelNetwork
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ scale : ℝ) : SharedBiasNetworkTo 2 2 1 2 7 8 :=
  expandedWorkspaceParallelReindexNetworkTo
    (by simp [expandedWorkspaceParallelProperSteps_length, grownSize])
    (by simp [expandedWorkspaceParallelProperSteps_length, grownSize])
    ((affineCompensatedBilinearNetwork
        (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂) scale).append
      (SharedBiasNetworkTo.single
        (parallelStripePackedFactorThree ε
          (expandedWorkspacePackedWeights w)).kernel
        (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)))

@[simp] theorem expandedWorkspaceParallelNetwork_depth
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ scale : ℝ) :
    (expandedWorkspaceParallelNetwork ε w theta d₁ d₂ scale).net.depth = 6 := by
  simp [expandedWorkspaceParallelNetwork,
    expandedWorkspaceParallelReindexNetworkTo,
    expandedWorkspaceParallelProperSteps,
    expandedWorkspaceInitializerSteps, SharedBiasNetworkTo.single,
    SharedBiasNetworkTo.nil, SharedBiasNetworkTo.cons,
    SharedBiasNetwork.depth]

/-- Coordinatewise evaluation formula for the appended final layer.  The
zero extension hides the harmless dependent reindexing between the length-
five generated dimensions and their normalized `6 × 7` presentation. -/
theorem zeroExtend_expandedWorkspaceParallelNetwork_eval
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ scale : ℝ) (x : Image 1 2) (p q : ℕ) :
    zeroExtend
        ((expandedWorkspaceParallelNetwork ε w theta d₁ d₂ scale).eval x)
        p q =
      zeroExtend (sharedLayerEval
        (parallelStripePackedFactorThree ε
          (expandedWorkspacePackedWeights w)).kernel
        (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
        ((affineCompensatedBilinearNetwork
          (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂)
          scale).eval x)) p q := by
  rw [expandedWorkspaceParallelNetwork,
    zeroExtend_expandedWorkspaceParallelReindexNetworkTo_eval,
    SharedBiasNetworkTo.eval_append, SharedBiasNetworkTo.eval_single]

/-- Exact formal signal/carrier decomposition of the last shared layer. -/
theorem expandedWorkspaceParallelFormalFinal
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ)
    (d₁ d₂ scale bias : ℝ) (x : Image 1 2) (q : Fin 8) :
    zeroExtend (sharedLayerEval
        (parallelStripePackedFactorThree ε
          (expandedWorkspacePackedWeights w)).kernel bias
        (expandedWorkspaceParallelProperVariable ε w theta d₁ d₂ x +
          scale • expandedWorkspaceParallelProperCarrier
            ε w theta d₁ d₂)) 1 q =
      relu
        (expandedWorkspaceParallelFinalVariable ε w theta d₁ d₂ x 1 q +
          scale * expandedWorkspaceParallelFinalCarrier ε w d₁ d₂ 1 q +
          bias) := by
  rw [zeroExtend_of_lt _ (by omega) q.isLt]
  change relu
    (fullConv
        (parallelStripePackedFactorThree ε
          (expandedWorkspacePackedWeights w)).kernel
        (expandedWorkspaceParallelProperVariable ε w theta d₁ d₂ x +
          scale • expandedWorkspaceParallelProperCarrier
            ε w theta d₁ d₂) 1 q + bias) = _
  rw [fullConv_add]
  have hsmul := congrFun
    (congrFun (fullConvImage_smul
      (parallelStripePackedFactorThree ε
        (expandedWorkspacePackedWeights w)).kernel scale
      (expandedWorkspaceParallelProperCarrier ε w theta d₁ d₂))
      (1 : Fin 7)) q
  change fullConv
      (parallelStripePackedFactorThree ε
        (expandedWorkspacePackedWeights w)).kernel
      (scale • expandedWorkspaceParallelProperCarrier
        ε w theta d₁ d₂) 1 q =
    scale * fullConv
      (parallelStripePackedFactorThree ε
        (expandedWorkspacePackedWeights w)).kernel
      (expandedWorkspaceParallelProperCarrier ε w theta d₁ d₂)
      1 q at hsmul
  rw [hsmul]
  congr 1

private theorem expandedWorkspace_relu_mul_of_pos
    (ε z : ℝ) (hε : 0 < ε) :
    relu (ε * z) = ε * relu z := by
  by_cases hz : 0 ≤ z
  · rw [relu_of_nonneg hz, relu_of_nonneg (mul_nonneg hε.le hz)]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    rw [relu_of_nonpos hz',
      relu_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hε.le hz')]
    ring

/-- **Two arbitrary affine ReLU ridges from the original width-two input.**

For every compact input family, one genuine depth-six expansive `2 × 2`,
one-channel network with one scalar bias per layer internally generates its
own expanded workspace and simultaneously computes two independently shifted
affine ReLU ridges at output sites `(1,2)` and `(1,4)`. -/
theorem exists_depthSix_expandedWorkspace_twoRidge_on_compact
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → Fin 2 → ℝ) (theta : Fin 2 → ℝ) :
    ∃ ε scale : ℝ,
      ∃ net : SharedBiasNetworkTo 2 2 1 2 7 8,
        0 < ε ∧ 0 < scale ∧ net.net.depth = 6 ∧
          ∀ x ∈ K,
            net.eval x 1 2 =
                ε * relu
                  (w 0 0 * x 0 0 + w 0 1 * x 0 1 + theta 0) ∧
              net.eval x 1 4 =
                ε * relu
                  (w 1 0 * x 0 0 + w 1 1 * x 0 1 + theta 1) := by
  rcases exists_expandedWorkspaceParallel_unitLower w theta with
    ⟨ε, d₁, d₂, hε, hcarrier⟩
  have hsignal : ContinuousFeatureOn K (fun x : Image 1 2 ↦ x) :=
    continuousFeatureOn_identity K
  rcases exists_affineCompensatedNorthTwoNetwork_scale_on_compact
      hK (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂)
      (fun x : Image 1 2 ↦ x) hsignal (0 : Image 1 2) hcarrier with
    ⟨scale₀, hscale₀, hproper⟩
  let scale := max scale₀ 1
  have hscaleBound : scale₀ ≤ scale := le_max_left _ _
  have hscale : 0 < scale := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let net := expandedWorkspaceParallelNetwork ε w theta d₁ d₂ scale
  refine ⟨ε, scale, net, hε, hscale,
    expandedWorkspaceParallelNetwork_depth ε w theta d₁ d₂ scale, ?_⟩
  intro x hx
  let actual :=
    (affineCompensatedBilinearNetwork
      (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂) scale).eval x
  let formal :=
    affineCompensatedVariableChain
        (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂) x +
      scale • affineCompensatedCarrierChain
        (expandedWorkspaceParallelProperSteps ε w theta d₁ d₂)
        (0 : Image 1 2)
  have hagree : NorthTwoAgree actual formal := by
    intro p hp q
    have h := hproper scale hscaleBound x hx p hp q
    have hinput : x + scale • (0 : Image 1 2) = x := by simp
    rw [hinput] at h
    simpa [actual, formal, zeroExtend_add, zeroExtend_smul] using h
  have hfinalAgree := northTwoAgree_sharedLayerEval
    (parallelStripePackedFactorThree ε
      (expandedWorkspacePackedWeights w)).kernel
    (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale) hagree
  have hcoordinate : ∀ q : Fin 8,
      net.eval x 1 q =
        zeroExtend (sharedLayerEval
          (parallelStripePackedFactorThree ε
            (expandedWorkspacePackedWeights w)).kernel
          (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
          formal) 1 q := by
    intro q
    have h := hfinalAgree 1 (by omega) q
    calc
      net.eval x 1 q = zeroExtend (net.eval x) 1 q := by
        symm
        exact zeroExtend_inside _ (1 : Fin 7) q
      _ = zeroExtend (sharedLayerEval
            (parallelStripePackedFactorThree ε
              (expandedWorkspacePackedWeights w)).kernel
            (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
            actual) 1 q := by
              simpa [net, actual] using
                (zeroExtend_expandedWorkspaceParallelNetwork_eval
                  ε w theta d₁ d₂ scale x 1 q)
      _ = zeroExtend (sharedLayerEval
            (parallelStripePackedFactorThree ε
              (expandedWorkspacePackedWeights w)).kernel
            (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
            formal) 1 q := h
  have hformal : ∀ q : Fin 8,
      zeroExtend (sharedLayerEval
          (parallelStripePackedFactorThree ε
            (expandedWorkspacePackedWeights w)).kernel
          (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
          formal) 1 q =
        relu
          (expandedWorkspaceParallelFinalVariable ε w theta d₁ d₂ x 1 q +
            scale * expandedWorkspaceParallelFinalCarrier ε w d₁ d₂ 1 q +
            expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale) := by
    intro q
    change zeroExtend (sharedLayerEval
        (parallelStripePackedFactorThree ε
          (expandedWorkspacePackedWeights w)).kernel
        (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale)
        (expandedWorkspaceParallelProperVariable ε w theta d₁ d₂ x +
          scale • expandedWorkspaceParallelProperCarrier
            ε w theta d₁ d₂)) 1 q = _
    exact expandedWorkspaceParallelFormalFinal ε w theta d₁ d₂ scale
      (expandedWorkspaceParallelFinalBias ε w theta d₁ d₂ scale) x q
  constructor
  · rw [hcoordinate (2 : Fin 8), hformal (2 : Fin 8),
      expandedWorkspaceParallelFinalVariable_target_zero,
      expandedWorkspaceParallelFinalCarrier_common_targets,
      expandedWorkspaceParallelFinalBias]
    rw [← expandedWorkspace_relu_mul_of_pos ε
      (w 0 0 * x 0 0 + w 0 1 * x 0 1 + theta 0) hε]
    congr 1
    have hoff := expandedWorkspaceOffsetResponse_difference ε w
      (expandedWorkspaceOffsetSignalBias ε theta)
    rw [expandedWorkspaceOffsetSignalBias] at hoff
    rw [expandedWorkspaceOffsetSignalBias]
    ring_nf at hoff ⊢
    linarith
  · rw [hcoordinate (4 : Fin 8), hformal (4 : Fin 8),
      expandedWorkspaceParallelFinalVariable_target_one,
      expandedWorkspaceParallelFinalBias]
    convert expandedWorkspace_relu_mul_of_pos ε
      (w 1 0 * x 0 0 + w 1 1 * x 0 1 + theta 1) hε using 1
    all_goals ring_nf

end OneChannelCNNUniversality
