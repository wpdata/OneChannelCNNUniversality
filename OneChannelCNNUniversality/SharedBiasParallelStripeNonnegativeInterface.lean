import OneChannelCNNUniversality.SharedBiasParallelStripeInitializationObstruction
import OneChannelCNNUniversality.SharedBiasOneLayerObstruction

/-!
# The residual exact-size obstruction for the nonnegative packed interface

The packed two-ridge input can be chosen nonnegative on every fixed compact
input family.  Nonnegativity alone, however, does not make the old `2 × 3`
interface internally generable from a raw `1 × 2` state.  With expansive
`2 × 2` kernels, that exact size forces depth one, and the existing one-layer
shared-bias obstruction excludes a concrete nonnegative loaded state whose
southern row is input-independent and spatially nonuniform.

Thus the next compositional interface must use a larger spatial state or a
different encoding.  The result here is not a universality obstruction.
-/

namespace OneChannelCNNUniversality

open Set

namespace SharedBiasNetwork

/-- Every expansive `2 × 2` shared-bias layer adds one output row. -/
theorem outRows_eq_add_depth_two {rows cols : ℕ}
    (net : SharedBiasNetwork 2 2 rows cols) :
    net.outRows = rows + net.depth := by
  induction net with
  | nil => rfl
  | cons kernel bias tail ih =>
      simp only [SharedBiasNetwork.outRows, SharedBiasNetwork.toNetwork,
        Network.outRows, SharedBiasNetwork.depth] at ih ⊢
      omega

/-- Every expansive `2 × 2` shared-bias layer adds one output column. -/
theorem outCols_eq_add_depth_two {rows cols : ℕ}
    (net : SharedBiasNetwork 2 2 rows cols) :
    net.outCols = cols + net.depth := by
  induction net with
  | nil => rfl
  | cons kernel bias tail ih =>
      simp only [SharedBiasNetwork.outCols, SharedBiasNetwork.toNetwork,
        Network.outCols, SharedBiasNetwork.depth] at ih ⊢
      omega

end SharedBiasNetwork

namespace SharedBiasNetworkTo

/-- An exact-size `1 × 2 → 2 × 3` expansive `2 × 2` network necessarily has
depth one. -/
theorem depth_eq_one_of_oneTwo_to_twoThree
    (net : SharedBiasNetworkTo 2 2 1 2 2 3) :
    net.net.depth = 1 := by
  have hrows := net.net.outRows_eq_add_depth_two
  rw [net.rows_eq] at hrows
  omega

/-- Consequently every such explicitly typed network is extensionally one
shared-bias convolution/ReLU layer. -/
theorem exists_single_layer_representation_oneTwo_to_twoThree
    (net : SharedBiasNetworkTo 2 2 1 2 2 3) :
    ∃ kernel : Kernel 2 2, ∃ bias : ℝ, ∀ x : Image 1 2,
      net.eval x = sharedLayerEval kernel bias x := by
  have hdepth := net.depth_eq_one_of_oneTwo_to_twoThree
  rcases net with ⟨raw, hrows, hcols⟩
  cases raw with
  | nil =>
      simp [SharedBiasNetwork.depth] at hdepth
  | cons kernel bias tail =>
      cases tail with
      | nil =>
          refine ⟨kernel, bias, ?_⟩
          intro x
          cases hrows
          cases hcols
          rfl
      | cons nextKernel nextBias nextTail =>
          change (nextTail.depth + 1) + 1 = 1 at hdepth
          omega

end SharedBiasNetworkTo

/-- The strengthened compact two-ridge theorem expressed through the named
loaded-input interface: the very state consumed by the depth-four block can
be chosen nonnegative on the whole compact input family. -/
theorem exists_parallelStripePackedAffineNetwork_nonnegative_loaded_input_on_compact
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    ∃ ε s : ℝ, 0 < ε ∧ 0 < s ∧
      (parallelStripePackedAffineNetwork ε w s).net.depth = 4 ∧
      (∀ x ∈ K, ImageNonnegative
        (parallelStripeLoadedAffineInput ε s w θ x)) ∧
      ∀ x ∈ K,
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeLoadedAffineInput ε s w θ x) 1 2 =
          ε * relu (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) ∧
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeLoadedAffineInput ε s w θ x) 1 4 =
          ε * relu (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  simpa [parallelStripeLoadedAffineInput] using
    exists_parallelStripePackedAffineNetwork_nonnegative_input_on_compact
      hK w θ

/-- A fixed pair of offsets producing the southern row `(42,80,84)` at
packing scale one and carrier scale ten. -/
def parallelStripeNonnegativeExampleOffsets : Fin 2 → ℝ :=
  ![367, 0]

/-- The concrete loaded state's southern row is independent of the input and
has the exact nonuniform values `(42,80,84)`. -/
theorem parallelStripeLoadedAffineInput_example_south
    (x : Image 1 2) (q : Fin 3) :
    parallelStripeLoadedAffineInput 1 10 parallelStripeZeroWeights
        parallelStripeNonnegativeExampleOffsets x 1 q =
      ![42, 80, 84] q := by
  fin_cases q <;>
    norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy,
      parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo]

/-- The complete concrete loaded state is coordinatewise nonnegative on the
compact symmetric box `[-1,1]²`. -/
theorem parallelStripeLoadedAffineInput_example_nonnegative
    (x : Image 1 2) (hx : x ∈ twoPointSymmetricBox 1) :
    ImageNonnegative
      (parallelStripeLoadedAffineInput 1 10 parallelStripeZeroWeights
        parallelStripeNonnegativeExampleOffsets x) := by
  intro p q
  fin_cases p <;> fin_cases q
  · have h := hx.1 (0 : Fin 1) (0 : Fin 2)
    norm_num [twoPointSymmetricBox, constantImage] at h
    norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy]
    linarith
  · have h := hx.1 (0 : Fin 1) (1 : Fin 2)
    norm_num [twoPointSymmetricBox, constantImage] at h
    norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy]
    linarith
  · norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy]
  · norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy,
      parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo]
  · norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy,
      parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo]
  · norm_num [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
      parallelStripeNonnegativeExampleOffsets, parallelStripeCorrectedCarrier,
      parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy,
      parallelStripeOffsetSeedZero, parallelStripeOffsetSeedTwo]

/-- The existing one-layer theorem rules out the concrete nonnegative loaded
interface on `[-1,1]²`: its southern row is input-independent but nonuniform. -/
theorem not_oneLayer_parallelStripe_nonnegative_example
    (kernel : Kernel 2 2) (bias : ℝ) :
    ¬ ∀ x ∈ twoPointSymmetricBox 1,
      sharedLayerEval kernel bias x =
        parallelStripeLoadedAffineInput 1 10 parallelStripeZeroWeights
          parallelStripeNonnegativeExampleOffsets x := by
  intro hrealize
  apply not_oneLayer_south_nonuniform_inputIndependent_on_symmetricBox
    1 (by norm_num) kernel bias
  refine ⟨![42, 80, 84], ⟨0, 1, by norm_num⟩, ?_⟩
  intro x hx q
  have heq := congrFun (congrFun (hrealize x hx) (1 : Fin 2)) q
  exact heq.trans (parallelStripeLoadedAffineInput_example_south x q)

/-- No exact-size shared-bias network can internally generate the concrete
nonnegative packed interface on the compact symmetric box. -/
theorem not_exists_exactSize_parallelStripe_nonnegative_initializer :
    ¬ ∃ net : SharedBiasNetworkTo 2 2 1 2 2 3,
      ∀ x ∈ twoPointSymmetricBox 1,
        net.eval x =
          parallelStripeLoadedAffineInput 1 10 parallelStripeZeroWeights
            parallelStripeNonnegativeExampleOffsets x := by
  rintro ⟨net, hnet⟩
  rcases net.exists_single_layer_representation_oneTwo_to_twoThree with
    ⟨kernel, bias, heval⟩
  exact not_oneLayer_parallelStripe_nonnegative_example kernel bias
    (fun x hx ↦ (heval x).symm.trans (hnet x hx))

end OneChannelCNNUniversality
