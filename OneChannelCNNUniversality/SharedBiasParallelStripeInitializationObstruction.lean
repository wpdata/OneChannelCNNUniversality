import OneChannelCNNUniversality.SharedBiasParallelStripeAffineNetwork
import OneChannelCNNUniversality.SharedBiasSeedTransport

/-!
# An initialization obstruction for the packed two-ridge block

The verified packed two-ridge network takes an explicitly carrier-loaded
`2 × 3` affine state as its input.  This module proves that this signed state
cannot simply be internalized unchanged by prefixing a positive-depth ReLU
network.  For every positive packing scale and every nonnegative carrier
scale, an explicit choice of affine offsets makes the southwest coordinate of
the required state strictly negative, whereas every positive-depth ReLU
network has coordinatewise nonnegative output.

This is an interface obstruction, not a non-universality theorem.  It shows
that a compositional construction must translate the packed state into a
nonnegative representation or replace the interface.
-/

namespace OneChannelCNNUniversality

open Set

/-- The exact external state consumed by the packed two-ridge network. -/
noncomputable def parallelStripeLoadedAffineInput
    (ε s : ℝ) (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ)
    (x : Image 1 2) : Image 2 3 :=
  parallelStripeAffineSeed ε θ x +
    s • parallelStripeCorrectedCarrier ε w

/-- The existing compact two-ridge theorem, restated through the named loaded
input interface used in this module. -/
theorem exists_parallelStripePackedAffineNetwork_on_compact_loaded
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    ∃ ε s : ℝ, 0 < ε ∧ 0 < s ∧
      (parallelStripePackedAffineNetwork ε w s).net.depth = 4 ∧
      ∀ x ∈ K,
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeLoadedAffineInput ε s w θ x) 1 2 =
          ε * relu (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) ∧
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeLoadedAffineInput ε s w θ x) 1 4 =
          ε * relu (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  simpa [parallelStripeLoadedAffineInput] using
    exists_parallelStripePackedAffineNetwork_on_compact hK w θ

/-- Zero packed ridge weights, used to isolate the offset obstruction. -/
def parallelStripeZeroWeights : Fin 2 → Fin 2 → ℝ :=
  fun _ _ ↦ 0

/-- Offsets whose first component defeats any prescribed nonnegative carrier
scale while the second component is zero. -/
noncomputable def parallelStripeObstructingOffsets
    (ε s : ℝ) : Fin 2 → ℝ :=
  ![367 * (s + 1) / ε, 0]

/-- Exact southwest coordinate of the obstructing carrier-loaded state. -/
theorem parallelStripeLoadedAffineInput_obstructing_southwest
    {ε s : ℝ} (hε : 0 < ε) (x : Image 1 2) :
    parallelStripeLoadedAffineInput ε s parallelStripeZeroWeights
        (parallelStripeObstructingOffsets ε s) x 1 0 =
      -30 * s - 38 := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp [parallelStripeLoadedAffineInput, parallelStripeAffineSeed,
    parallelStripeObstructingOffsets, parallelStripeCorrectedCarrier,
    parallelStripeZeroWeights, parallelStripePackedCarrierDiscrepancy,
    parallelStripeOffsetSeedZero]
  field_simp
  ring

/-- The obstructing southwest coordinate is negative for every nonnegative
carrier scale. -/
theorem parallelStripeLoadedAffineInput_obstructing_southwest_neg
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (x : Image 1 2) :
    parallelStripeLoadedAffineInput ε s parallelStripeZeroWeights
        (parallelStripeObstructingOffsets ε s) x 1 0 < 0 := by
  rw [parallelStripeLoadedAffineInput_obstructing_southwest hε x]
  nlinarith

/-- No positive-depth shared-bias ReLU network can produce the obstructing
loaded state even at one input. -/
theorem not_exists_positiveDepth_parallelStripe_initializer_at
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (x : Image 1 2) :
    ¬ ∃ net : SharedBiasNetworkTo 2 2 1 2 2 3,
        0 < net.net.depth ∧
          net.eval x =
            parallelStripeLoadedAffineInput ε s parallelStripeZeroWeights
              (parallelStripeObstructingOffsets ε s) x := by
  rintro ⟨net, hdepth, heval⟩
  have hnonneg := net.eval_nonnegative_of_pos_depth x hdepth
  have hsw : 0 ≤ net.eval x 1 0 := hnonneg 1 0
  rw [heval] at hsw
  exact (not_lt_of_ge hsw)
    (parallelStripeLoadedAffineInput_obstructing_southwest_neg hε hs x)

/-- Hence the exact external representation cannot be realized on any
nonempty input domain by a positive-depth shared-bias ReLU initializer. -/
theorem not_exists_positiveDepth_parallelStripe_initializer_on_nonempty
    {K : Set (Image 1 2)} (hK : K.Nonempty)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    ¬ ∃ net : SharedBiasNetworkTo 2 2 1 2 2 3,
        0 < net.net.depth ∧
          ∀ x ∈ K,
            net.eval x =
              parallelStripeLoadedAffineInput ε s parallelStripeZeroWeights
                (parallelStripeObstructingOffsets ε s) x := by
  rintro ⟨net, hdepth, hnet⟩
  rcases hK with ⟨x, hx⟩
  exact not_exists_positiveDepth_parallelStripe_initializer_at hε hs x
    ⟨net, hdepth, hnet x hx⟩

end OneChannelCNNUniversality
