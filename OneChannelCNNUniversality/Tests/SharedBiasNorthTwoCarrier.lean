import OneChannelCNNUniversality.SharedBiasNorthTwoCarrier

/-!
# Regression tests for compact northern-two-row carrier domination
-/

namespace OneChannelCNNUniversality

#check NorthTwoUnitLowerAlong
#check northTwoUnitLowerAlong_append_iff
#check exists_northTwoLinearAlong_add_smul_of_unitLower
#check exists_sharedBiasSeed_threshold_on_compact

example {rows cols : ℕ} (carrier : Image rows cols) :
    NorthTwoUnitLowerAlong [] carrier := by
  trivial

private def unitLowerRegressionFactor : BilinearKernelFactor where
  a0 := 1
  a1 := 1
  b0 := 1
  b1 := 1

/-- The nonempty recursive branch is exercised by an all-positive kernel. -/
example : NorthTwoUnitLowerAlong [unitLowerRegressionFactor]
    (constantImage 2 2 1) := by
  constructor
  · intro p hp q
    change 1 ≤ fullConv (bilinearKernel 1 1 1 1)
      (constantImage 2 2 1) p q
    fin_cases p <;> fin_cases q <;>
      norm_num [fullConv_bilinearKernel_nat, bilinearKernel,
        deltaKernel, zeroExtend, constantImage]
  · trivial

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ} (V : X → Image rows cols)
    (hV : ContinuousFeatureOn K V) (carrier : Image rows cols) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s : ℝ, s₀ ≤ s → ∀ x ∈ K,
      NorthTwoLinearAlong [] (V x + s • carrier) := by
  exact exists_northTwoLinearAlong_add_smul_of_unitLower
    hK [] V hV carrier trivial

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) :
    ∃ b : ℝ, 0 < b ∧ ∀ c : ℝ, b ≤ c → ∀ x ∈ K,
      (sharedBiasSeedLayer c).eval (F x) =
        fullConvImage expansiveIdentityKernel (F x) +
          constantImage (rows + 2 - 1) (cols + 2 - 1) c := by
  exact exists_sharedBiasSeed_threshold_on_compact hK F hF

end OneChannelCNNUniversality
