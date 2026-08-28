import OneChannelCNNUniversality.SharedBiasChainSelection

open OneChannelCNNUniversality

example {n : ℕ} {x y : Image 1 n} {target : Fin n} :
    RowPrefixAgree x y target ↔
      AgreeOutsideStrictSoutheast x y rowZero target := by
  exact rowPrefixAgree_iff_agreeOutsideStrictSoutheast

example {X : Type*} {K : Set X} {n : ℕ}
    {V : X → Image 1 n} {θ : ℝ} {rowSteps extraColSteps : ℕ}
    {target : Fin n} {c b : ℝ}
    {net : RowChainSelectionNetwork n rowSteps extraColSteps}
    (hspec : BundledRowChainSelectionSpec K V θ rowSteps extraColSteps
      target c b net) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hprefix : RowPrefixAgree (V x) (V y) target)
    (heval : net.eval (V x + constantImage 1 n c) =
      net.eval (V y + constantImage 1 n c)) :
    V x = V y := by
  exact hspec.injective_of_rowPrefixAgree hx hy hprefix heval

example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (V : X → Image 1 n) (hV : ContinuousFeatureOn K V)
    (rowSteps extraColSteps : ℕ) (target : Fin n) (θ : ℝ)
    (hcolSteps : n - 1 ≤ extraColSteps + 1) :
    ∃ c b : ℝ, ∃ net : RowChainSelectionNetwork n rowSteps extraColSteps,
      0 < c ∧ 0 < b ∧ net.net.depth = rowSteps + extraColSteps + 2 ∧
        BundledRowChainSelectionSpec K V θ rowSteps extraColSteps
          target c b net ∧
        ∀ {x y : X}, x ∈ K → y ∈ K →
          RowPrefixAgree (V x) (V y) target →
          net.eval (V x + constantImage 1 n c) =
            net.eval (V y + constantImage 1 n c) →
          V x = V y := by
  exact exists_bundled_rowChain_protected_selection
    hK V hV rowSteps extraColSteps target θ hcolSteps
