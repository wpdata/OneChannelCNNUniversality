import OneChannelCNNUniversality.SharedBiasGridGate

/-!
# Composition of two protected shared-bias grid gates

The output of one protected grid gate is a continuous, injective finite image
family, so compactness supplies a new bound for a second gate.  Appending the
two genuine depth-two blocks yields a depth-four shared-bias CNN whose northern
row computes a nested signed affine ReLU while the complete representation
remains injective.
-/

namespace OneChannelCNNUniversality

universe u

/-- Sequential composition of two protected grid-gate blocks. -/
def twoStageProtectedGridGateNetwork {rows cols : ℕ}
    (a₁ c₁ M₁ a₂ c₂ M₂ : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 + 2) (cols + 2 + 2) :=
  (protectedGridGateNetwork (rows := rows) (cols := cols) a₁ c₁ M₁).append
    (protectedGridGateNetwork
      (rows := rows + 2) (cols := cols + 2) a₂ c₂ M₂)

/-- Two depth-two protected gates contribute exactly four hidden layers. -/
theorem twoStageProtectedGridGateNetwork_depth {rows cols : ℕ}
    (a₁ c₁ M₁ a₂ c₂ M₂ : ℝ) :
    (twoStageProtectedGridGateNetwork (rows := rows) (cols := cols)
      a₁ c₁ M₁ a₂ c₂ M₂).net.depth = 4 := by
  rw [twoStageProtectedGridGateNetwork,
    SharedBiasNetworkTo.depth_append,
    protectedGridGateNetwork_depth,
    protectedGridGateNetwork_depth]

/-- The northern row of the appended four-layer CNN is the requested nested
signed affine ReLU of the original northern row. -/
theorem twoStageProtectedGridGateNetwork_gate
    {rows cols : ℕ} (x : Image rows cols)
    (a₁ c₁ M₁ a₂ c₂ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hbound₁ : ∀ i j, |x i j| ≤ M₁)
    (hM₂ : 0 ≤ M₂)
    (hbound₂ : ∀ i j,
      |(protectedGridGateNetwork a₁ c₁ M₁).eval x i j| ≤ M₂)
    (j : Fin cols) :
    zeroExtend
        ((twoStageProtectedGridGateNetwork
          a₁ c₁ M₁ a₂ c₂ M₂).eval x) 0 j =
      relu (a₂ * relu (a₁ * zeroExtend x 0 j + c₁) + c₂) := by
  rw [twoStageProtectedGridGateNetwork,
    SharedBiasNetworkTo.eval_append]
  rw [protectedGridGateNetwork_gate
      ((protectedGridGateNetwork a₁ c₁ M₁).eval x)
      a₂ c₂ M₂ hM₂ hbound₂
      (⟨j, by omega⟩ : Fin (cols + 2)),
    protectedGridGateNetwork_gate x a₁ c₁ M₁ hM₁ hbound₁ j]

/-- Sequential protected gates preserve injectivity because each complete
intermediate feature image is injectively encoded. -/
theorem twoStageProtectedGridGateNetwork_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (a₁ c₁ M₁ a₂ c₂ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁)
    (hbound₁ : ∀ x ∈ K, ∀ i j, |F x i j| ≤ M₁)
    (hM₂ : 0 ≤ M₂)
    (hbound₂ : ∀ x ∈ K, ∀ i j,
      |(protectedGridGateNetwork a₁ c₁ M₁).eval (F x) i j| ≤ M₂)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (twoStageProtectedGridGateNetwork
        a₁ c₁ M₁ a₂ c₂ M₂).eval (F x)) K := by
  let first : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2) :=
    protectedGridGateNetwork a₁ c₁ M₁
  have hfirst : Set.InjOn (fun x ↦ first.eval (F x)) K := by
    exact protectedGridGateNetwork_injectiveOn
      F a₁ c₁ M₁ hM₁ hbound₁ hFinjective
  have hsecond : Set.InjOn
      (fun x ↦ (protectedGridGateNetwork
        (rows := rows + 2) (cols := cols + 2) a₂ c₂ M₂).eval
          (first.eval (F x))) K := by
    exact protectedGridGateNetwork_injectiveOn
      (fun x ↦ first.eval (F x)) a₂ c₂ M₂ hM₂
      (fun x hx i j ↦ hbound₂ x hx i j) hfirst
  simpa [twoStageProtectedGridGateNetwork,
    SharedBiasNetworkTo.eval_append, first] using hsecond

/-- Compactness chooses one uniform bound at each stage.  The resulting
depth-four genuine shared-bias CNN computes the nested gate on every northern
row coordinate and remains injective on the compact input family. -/
theorem exists_twoStageProtectedGridGateNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (a₁ c₁ a₂ c₂ : ℝ) :
    ∃ M₁ : ℝ, 0 < M₁ ∧
      ∃ M₂ : ℝ, 0 < M₂ ∧
        ∃ net : SharedBiasNetworkTo 2 2 rows cols
            (rows + 2 + 2) (cols + 2 + 2),
          net.net.depth = 4 ∧
          (∀ x ∈ K, ∀ j : Fin cols,
            zeroExtend (net.eval (F x)) 0 j =
              relu (a₂ * relu
                (a₁ * zeroExtend (F x) 0 j + c₁) + c₂)) ∧
          Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M₁, hM₁, hbound₁⟩ :=
    exists_uniform_feature_margin hK F hF 0
  let first : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2) :=
    protectedGridGateNetwork a₁ c₁ M₁
  let G : X → Image (rows + 2) (cols + 2) :=
    fun x ↦ first.eval (F x)
  have hG : ContinuousFeatureOn K G := by
    exact first.continuousFeatureOn_eval F hF
  have hGinjective : Set.InjOn G K := by
    exact protectedGridGateNetwork_injectiveOn
      F a₁ c₁ M₁ hM₁.le
      (fun x hx i j ↦ by
        have := hbound₁ x hx i j
        simpa using this.le)
      hFinjective
  obtain ⟨M₂, hM₂, hbound₂⟩ :=
    exists_uniform_feature_margin hK G hG 0
  refine ⟨M₁, hM₁, M₂, hM₂,
    twoStageProtectedGridGateNetwork a₁ c₁ M₁ a₂ c₂ M₂,
    twoStageProtectedGridGateNetwork_depth
      a₁ c₁ M₁ a₂ c₂ M₂, ?_, ?_⟩
  · intro x hx j
    exact twoStageProtectedGridGateNetwork_gate
      (F x) a₁ c₁ M₁ a₂ c₂ M₂ hM₁.le
      (fun i j ↦ by
        have := hbound₁ x hx i j
        simpa using this.le)
      hM₂.le
      (fun i j ↦ by
        have := hbound₂ x hx i j
        simpa [G, first] using this.le)
      j
  · exact twoStageProtectedGridGateNetwork_injectiveOn
      F a₁ c₁ M₁ a₂ c₂ M₂ hM₁.le
      (fun x hx i j ↦ by
        have := hbound₁ x hx i j
        simpa using this.le)
      hM₂.le
      (fun x hx i j ↦ by
        have := hbound₂ x hx i j
        simpa [G, first] using this.le)
      hFinjective

end OneChannelCNNUniversality
