import OneChannelCNNUniversality.SharedBiasGeneralRidgeNetwork

/-!
# Regression tests for the protected arbitrary-width ridge network
-/

namespace OneChannelCNNUniversality

#check grownSize_two_eq_add
#check generalRidgeTerminalPureSignal_target
#check generalRidgeTerminalPureSignal_north
#check exists_protectedGeneralRidgeNetwork_behavior_on_compact
#check exists_protectedGeneralRidgeNetwork_on_compact
#print axioms exists_protectedGeneralRidgeNetwork_behavior_on_compact
#print axioms exists_protectedGeneralRidgeNetwork_on_compact

/-- The first arbitrary-width instance specializes to the certified
three-register, depth-two, `3 × 5` output shape. -/
example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → Image 1 3) (hF : ContinuousFeatureOn K F)
    (w : Fin 3 → ℝ) (gamma : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 3 3 5) (_offset : Image 3 5),
      net.net.depth = 2 ∧
        ∀ x ∈ K,
          zeroExtend (net.eval (F x)) 1 2 =
            relu ((∑ j : Fin 3, w j * F x 0 j) + gamma) := by
  obtain ⟨net, offset, hdepth, hbehavior⟩ :=
    exists_protectedGeneralRidgeNetwork_behavior_on_compact
      (n := 0) hK F hF w gamma
  exact ⟨net, offset, hdepth, fun x hx ↦ (hbehavior x hx).1⟩

/-- The same concrete instance preserves injectivity on the compact family. -/
example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → Image 1 3) (hF : ContinuousFeatureOn K F)
    (hFinjective : Set.InjOn F K) (w : Fin 3 → ℝ) (gamma : ℝ) :
    ∃ net : SharedBiasNetworkTo 2 2 1 3 3 5,
      Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨net, _offset, _hdepth, _hbehavior, hinjective⟩ :=
    exists_protectedGeneralRidgeNetwork_on_compact
      (n := 0) hK F hF hFinjective w gamma
  exact ⟨net, hinjective⟩

end OneChannelCNNUniversality
