import OneChannelCNNUniversality.SharedBiasAddress

open OneChannelCNNUniversality

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols) :
    protectedNorthwestAddress rows cols c b₁ b₂
        ⟨0, hrows⟩ ⟨0, hcols⟩ = c + b₁ + b₂ := by
  exact protectedNorthwestAddress_northwest c b₁ b₂ hrows hcols

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (j : Fin cols) (hj : 0 < (j : ℕ)) :
    protectedNorthwestAddress rows cols c b₁ b₂
        ⟨0, hrows⟩ j = 2 * c + b₁ + b₂ := by
  exact protectedNorthwestAddress_top c b₁ b₂ hrows j hj

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (i : Fin rows) (hi : 0 < (i : ℕ)) (hcols : 0 < cols) :
    protectedNorthwestAddress rows cols c b₁ b₂
        i ⟨0, hcols⟩ = 2 * c + 2 * b₁ + b₂ := by
  exact protectedNorthwestAddress_left c b₁ b₂ i hi hcols

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (i : Fin rows) (j : Fin cols)
    (hi : 0 < (i : ℕ)) (hj : 0 < (j : ℕ)) :
    protectedNorthwestAddress rows cols c b₁ b₂ i j =
      4 * c + 2 * b₁ + b₂ := by
  exact protectedNorthwestAddress_interior c b₁ b₂ i j hi hj

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 1 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ i j, (i, j) ≠ (⟨0, hrows⟩, ⟨0, hcols⟩) →
      1 ≤ protectedNorthwestAddress rows cols c b₁ b₂ i j -
        protectedNorthwestAddress rows cols c b₁ b₂
          ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  exact protectedNorthwestAddress_unit_gap c b₁ b₂ hrows hcols hc hb₁

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 0 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ i j, (i, j) ≠ (⟨0, hrows⟩, ⟨0, hcols⟩) →
      c ≤ protectedNorthwestAddress rows cols c b₁ b₂ i j -
        protectedNorthwestAddress rows cols c b₁ b₂
          ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  exact protectedNorthwestAddress_gap c b₁ b₂ hrows hcols hc hb₁

example {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 0 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ p q, originalRectangleProtected rows cols p q →
      (p, q) ≠ northwestOutputTarget rows cols hrows hcols →
      c ≤ northwestAddressCarrier rows cols c b₁ b₂ p q -
        northwestAddressCarrier rows cols c b₁ b₂
          (northwestOutputTarget rows cols hrows hcols).1
          (northwestOutputTarget rows cols hrows hcols).2 := by
  exact northwestAddressCarrier_gap_on c b₁ b₂ hrows hcols hc hb₁

example {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage horizontalAccumulationKernel x) := by
  exact horizontalAccumulationTransform_injective

example {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage verticalAccumulationKernel x) := by
  exact verticalAccumulationTransform_injective

example {rows cols : ℕ} :
    Function.Injective (fun x : Image rows cols ↦
      fullConvImage verticalAccumulationKernel
        (fullConvImage horizontalAccumulationKernel x)) := by
  exact twoLayerAccumulationTransform_injective

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) (c : ℝ) :
    ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ ∀ x ∈ K,
      sharedLayerEval verticalAccumulationKernel b₂
          (sharedLayerEval horizontalAccumulationKernel b₁
            (V x + constantImage rows cols c)) =
        fullConvImage verticalAccumulationKernel
            (fullConvImage horizontalAccumulationKernel (V x)) +
          northwestAddressCarrier rows cols c b₁ b₂ := by
  exact exists_northwest_address_layers hK V hV c

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 0 < cols)
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) (θ : ℝ) :
    ∃ c b₁ b₂ : ℝ, 0 < c ∧ 0 < b₁ ∧ 0 < b₂ ∧
      NorthwestProtectedSelectionSpec K V θ hrows hcols c b₁ b₂ := by
  exact exists_northwest_protected_selection_layers
    hK hrows hcols V hV θ
