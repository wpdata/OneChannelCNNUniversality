import OneChannelCNNUniversality.SharedBiasTwoStageRecovery

open OneChannelCNNUniversality

example {rows cols : ℕ} :
    Function.Injective
      (fullConvImage expansiveIdentityKernel :
        Image rows cols → Image (rows + 2 - 1) (cols + 2 - 1)) := by
  exact fullConvImage_expansiveIdentityKernel_injective

example {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast
      (fullConvImage expansiveIdentityKernel x)
      (fullConvImage expansiveIdentityKernel y) r s := by
  exact agreeOutsideStrictSoutheast_fullConvImage_expansiveIdentity hxy

example {X : Type*} {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) {x y : X}
    {r s : ℕ} (hxy : AgreeOutsideStrictSoutheast (F x) (F y) r s) :
    AgreeOutsideStrictSoutheast
      (successorFeature head F x) (successorFeature head F y) r s := by
  exact agreeOutsideStrictSoutheast_successorFeature head F hxy

example {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols}
    {rowSteps₁ extraColSteps₁ rowSteps₂ extraColSteps₂ : ℕ}
    {targetRow₁ : Fin rows} {targetCol₁ : Fin cols}
    {targetRow₂ : Fin
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)}
    {targetCol₂ : Fin
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)}
    {θ₁ θ₂ c₁ b₁ c₂ b₂ : ℝ}
    {head : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁)
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁)}
    {tail : SharedBiasNetworkTo 2 2
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
      (protectedSelectionSize
        (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
        rowSteps₂ extraColSteps₂)
      (protectedSelectionSize
        (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
        rowSteps₂ extraColSteps₂)}
    (hspec₁ : BundledPascalGridSelectionSpec K V θ₁
      rowSteps₁ extraColSteps₁ targetRow₁ targetCol₁ c₁ b₁ head)
    (hspec₂ : BundledPascalGridSelectionSpec K
      (successorFeature head
        (fun z ↦ V z + constantImage rows cols c₁)) θ₂
      rowSteps₂ extraColSteps₂ targetRow₂ targetCol₂ c₂ b₂ tail)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K) (hc₂ : 0 ≤ c₂)
    (hvar₁ : AgreeOutsideStrictSoutheast
      (V x) (V y) targetRow₁ targetCol₁)
    (hvar₂ : AgreeOutsideStrictSoutheast
      (V x) (V y) targetRow₂ targetCol₂)
    (heval : (head.appendWithSeed c₂ tail).eval
        (V x + constantImage rows cols c₁) =
      (head.appendWithSeed c₂ tail).eval
        (V y + constantImage rows cols c₁)) :
    V x = V y := by
  exact twoStage_pascal_selection_injective_on_rootPuncturedSoutheast
    hspec₁ hspec₂ hx hy hc₂ hvar₁ hvar₂ heval
