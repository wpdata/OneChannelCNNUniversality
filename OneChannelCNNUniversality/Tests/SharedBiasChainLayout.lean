import OneChannelCNNUniversality.SharedBiasChainLayout

open OneChannelCNNUniversality

example {rows cols : ℕ} (x : Image rows cols) :
    rowMajorChainDecode rows cols (rowMajorChainEncode x) = x := by
  exact rowMajorChainDecode_encode x

example {rows cols : ℕ} :
    Function.Injective (rowMajorChainEncode (rows := rows) (cols := cols)) := by
  exact rowMajorChainEncode_injective

example {n : ℕ} (a b : Fin n) :
    southeastProtected (rowChainLayout a).1 (rowChainLayout a).2
      (rowChainLayout b).1 (rowChainLayout b).2 ↔ a ≤ b := by
  exact southeastProtected_rowChainLayout_iff a b

example {n rows cols : ℕ} (hrows : 2 ≤ rows) (hcols : 2 ≤ cols)
    (layout : Fin n → Fin rows × Fin cols)
    (hmono : SoutheastMonotoneLayout layout) :
    ¬ Function.Surjective layout := by
  exact not_surjective_of_southeastMonotoneLayout hrows hcols layout hmono

example {n rows cols : ℕ} {layout : Fin n → Fin rows × Fin cols}
    (hmono : SoutheastMonotoneLayout layout)
    (hinjective : Function.Injective layout) :
    n ≤ rows + cols - 1 := by
  exact hmono.length_le hinjective
