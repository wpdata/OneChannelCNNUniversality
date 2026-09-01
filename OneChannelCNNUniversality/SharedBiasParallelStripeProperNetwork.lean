import OneChannelCNNUniversality.SharedBiasParallelStripeCarrierCorrection

/-!
# Genuine proper network for two packed width-two ridges

This file instantiates the general compact compensated-carrier bridge with
the corrected packed two-target carrier.  The result is a genuine three-layer
shared-bias ReLU network whose northern two rows have exact signal-plus-carrier
semantics, uniformly on an arbitrary compact input family.
-/

namespace OneChannelCNNUniversality

open Set

/-- For every compact continuous width-three two-row signal family and every
pair of width-two weights, there is a positive packing scale and then one
upward-closed network scale threshold.  Above that threshold the genuine
three-layer shared-bias ReLU network has exact northern-two-row formal
semantics.  The same packing scale retains a strict terminal selector gap. -/
theorem exists_parallelStripeCorrectedProperNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (V : X → Image 2 3) (hV : ContinuousFeatureOn K V)
    (w : Fin 2 → Fin 2 → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
        (parallelStripeCorrectedFinalCarrier ε w).coeff 2 ∧
      ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s : ℝ, s₀ ≤ s → ∀ x ∈ K,
        ∀ p, p ≤ 1 → ∀ q,
          zeroExtend
              ((compensatedBilinearNetwork
                  (parallelStripePackedProperSteps ε w) s).eval
                (V x + s • parallelStripeCorrectedCarrier ε w)) p q =
            zeroExtend
                (compensatedVariableChain
                  (parallelStripePackedProperSteps ε w) (V x)) p q +
              s * zeroExtend
                (compensatedCarrierChain
                  (parallelStripePackedProperSteps ε w)
                  (parallelStripeCorrectedCarrier ε w)) p q := by
  rcases exists_parallelStripeCorrected_unitLower_and_gap w with
    ⟨ε, hε, hcarrier, hgap⟩
  rcases exists_compensatedNorthTwoNetwork_scale_on_compact
      hK (parallelStripePackedProperSteps ε w) V hV
      (parallelStripeCorrectedCarrier ε w) hcarrier with
    ⟨s₀, hs₀, hnetwork⟩
  exact ⟨ε, hε, hgap, s₀, hs₀, hnetwork⟩

end OneChannelCNNUniversality
