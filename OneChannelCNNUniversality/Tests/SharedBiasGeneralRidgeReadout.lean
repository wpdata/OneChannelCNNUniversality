import OneChannelCNNUniversality.SharedBiasGeneralRidgeReadout

/-!
# Regression tests for arbitrary-width terminal ridge readouts
-/

namespace OneChannelCNNUniversality

#check generalRidgeNormalizedNorthLinearMap
#check generalRidgeNormalizedNorthLinearMap_injective
#check generalRidgeNormalizedNorthLeftInverse
#check generalRidgeNormalizedNorthLeftInverse_apply
#check generalRidgeAffineInputLinearMap
#check generalRidgeNorthProjection
#check generalRidgeAffineRecoveryLinearMap
#check generalRidgeAffineReadoutWeight
#check generalRidgeAffineReadoutConstant
#check generalRidgeAffineReadout_spec
#check generalRidgeTargetLinearMap
#check generalRidgeMinReadoutWeight
#check generalRidgeMaxReadoutWeight
#check exists_generalRidgeMinMaxReadouts_on_compact

#print axioms generalRidgeNormalizedNorthLeftInverse_apply
#print axioms generalRidgeAffineReadout_spec
#print axioms exists_generalRidgeMinMaxReadouts_on_compact

/-- The first arbitrary-width instance gives one depth-two network with
ordinary affine readouts for two arbitrary affine minima and maxima. -/
example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → Image 1 3) (hF : ContinuousFeatureOn K F)
    (a b : Fin 3 → ℝ) (alpha beta : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 3 3 5),
      net.net.depth = 2 ∧
        ∃ minWeight maxWeight : Image 3 5,
          ∃ minConstant maxConstant : ℝ,
            (∀ x ∈ K,
              (∑ p, ∑ q, minWeight p q * net.eval (F x) p q) +
                  minConstant =
                min ((∑ j, a j * F x 0 j) + alpha)
                  ((∑ j, b j * F x 0 j) + beta)) ∧
            (∀ x ∈ K,
              (∑ p, ∑ q, maxWeight p q * net.eval (F x) p q) +
                  maxConstant =
                max ((∑ j, a j * F x 0 j) + alpha)
                  ((∑ j, b j * F x 0 j) + beta)) := by
  exact exists_generalRidgeMinMaxReadouts_on_compact
    (n := 0) hK F hF a alpha b beta

end OneChannelCNNUniversality
