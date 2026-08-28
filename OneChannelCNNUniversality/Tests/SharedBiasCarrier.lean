import OneChannelCNNUniversality.SharedBiasCarrier

open Set
open OneChannelCNNUniversality

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols kRows kCols : ℕ}
    (F : X → Image rows cols) (hF : ContinuousFeatureOn K F)
    (w : Kernel kRows kCols) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ∀ p q,
      sharedLayerEval w b (F x) p q = fullConv w (F x) p q + b := by
  exact exists_shared_bias_linearization hK F hF w

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols kRows kCols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) (w : Kernel kRows kCols) :
    ∃ (b : ℝ) (carrier : Image (rows + kRows - 1) (cols + kCols - 1)),
      0 < b ∧ ∀ x ∈ K,
        sharedLayerEval w b (F x) = fullConvImage w (V x) + carrier := by
  exact exists_shared_bias_carrier_layer hK F V known hdecomp hV w

-- Horizontal boundary generation does not destroy the transported image:
-- the full first-difference transform is injective.
example {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage horizontalBoundaryKernel x) := by
  exact horizontalBoundaryTransform_injective

example {rows cols : ℕ} (c b : ℝ) (i : Fin rows) (hcols : 0 < cols) :
    horizontalSharedCarrier rows cols c b
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨0, by omega⟩ : Fin (cols + 2 - 1)) = c + b := by
  exact horizontalSharedCarrier_left c b i hcols

example {rows cols : ℕ} (c b : ℝ) (i : Fin rows) (j : Fin cols)
    (hj : 0 < (j : ℕ)) :
    horizontalSharedCarrier rows cols c b
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨j, by omega⟩ : Fin (cols + 2 - 1)) = b := by
  exact horizontalSharedCarrier_interior c b i j hj

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) (c : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K,
      sharedLayerEval horizontalBoundaryKernel b
          (V x + constantImage rows cols c) =
        fullConvImage horizontalBoundaryKernel (V x) +
          horizontalSharedCarrier rows cols c b := by
  exact exists_horizontal_shared_carrier_layer hK V hV c
