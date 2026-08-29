import OneChannelCNNUniversality.SharedBiasSuccessorSelection
import OneChannelCNNUniversality.SharedBiasRelativeInjectivity

/-!
# Relative recovery through two protected selection stages

The second selector recovers its successor feature, the expansive delta
embedding recovers the first selector's output, and the first selector then
recovers the original feature image.  This closes the recovery argument for
the genuine two-stage network constructed in `SharedBiasSuccessorSelection`.
-/

namespace OneChannelCNNUniversality

/-- Expansive convolution by the northwest delta kernel is injective: the
whole original rectangle occurs unchanged in the northwest output block. -/
theorem fullConvImage_expansiveIdentityKernel_injective
    {rows cols : ℕ} :
    Function.Injective
      (fullConvImage expansiveIdentityKernel :
        Image rows cols → Image (rows + 2 - 1) (cols + 2 - 1)) := by
  intro x y hxy
  funext i j
  have hentry := congrFun (congrFun hxy
    (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
    (⟨j, by omega⟩ : Fin (cols + 2 - 1))
  change fullConv expansiveIdentityKernel x i j =
    fullConv expansiveIdentityKernel y i j at hentry
  simpa only [fullConv_expansiveIdentityKernel_original] using hentry

/-- The expansive delta embedding preserves a root-punctured southeast
support relation at the same natural coordinate. -/
theorem agreeOutsideStrictSoutheast_fullConvImage_expansiveIdentity
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast
      (fullConvImage expansiveIdentityKernel x)
      (fullConvImage expansiveIdentityKernel y) r s := by
  refine ⟨agreeOutsideSoutheast_fullConvImage
    expansiveIdentityKernel hxy.1, ?_⟩
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_expansiveIdentityKernel_nat,
    fullConv_expansiveIdentityKernel_nat]
  exact hxy.2

/-- The complete successor transformation preserves root-punctured
southeast support through the preceding network and the delta embedding. -/
theorem agreeOutsideStrictSoutheast_successorFeature
    {X : Type*} {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) {x y : X} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast (F x) (F y) r s) :
    AgreeOutsideStrictSoutheast
      (successorFeature head F x) (successorFeature head F y) r s := by
  apply agreeOutsideStrictSoutheast_fullConvImage_expansiveIdentity
  exact agreeOutsideStrictSoutheast_sharedBiasNetworkTo_eval head hxy

/-- Equality of successor features reflects equality of the preceding
network outputs. -/
theorem headEval_eq_of_successorFeature_eq
    {X : Type*} {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) {x y : X}
    (hxy : successorFeature head F x = successorFeature head F y) :
    head.eval (F x) = head.eval (F y) := by
  exact fullConvImage_expansiveIdentityKernel_injective hxy

/-- Two consecutive protected Pascal selectors are jointly injective under
the two root-punctured southeast variation invariants.  The proof runs the
certified recovery interfaces backward through the genuine composed CNN. -/
theorem twoStage_pascal_selection_injective_on_rootPuncturedSoutheast
    {X : Type*} {K : Set X} {rows cols : ℕ}
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
  let F : X → Image rows cols :=
    fun z ↦ V z + constantImage rows cols c₁
  have hseeded₂ : AgreeOutsideStrictSoutheast (F x) (F y)
      targetRow₂ targetCol₂ := by
    exact hvar₂.add_right (constantImage rows cols c₁)
  have hsuccessor₂ : AgreeOutsideStrictSoutheast
      (successorFeature head F x) (successorFeature head F y)
      targetRow₂ targetCol₂ :=
    agreeOutsideStrictSoutheast_successorFeature head F hseeded₂
  have hdepth₁ : 0 < head.net.depth := by
    rw [hspec₁.1, pascalGridSelectionNetwork_depth]
    omega
  have hxbridge := head.eval_appendWithSeed_of_nonnegative tail
    (head.eval_nonnegative_of_pos_depth (F x) hdepth₁) hc₂
  have hybridge := head.eval_appendWithSeed_of_nonnegative tail
    (head.eval_nonnegative_of_pos_depth (F y) hdepth₁) hc₂
  have htail :
      tail.eval
          (successorFeature head F x +
            constantImage
              (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
              (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
              c₂) =
        tail.eval
          (successorFeature head F y +
            constantImage
              (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
              (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
              c₂) := by
    exact hxbridge.symm.trans (heval.trans hybridge)
  have hsuccessorEq : successorFeature head F x =
      successorFeature head F y :=
    hspec₂.injective_on_rootPuncturedSoutheast
      hx hy hsuccessor₂ htail
  have hheadEq : head.eval (F x) = head.eval (F y) :=
    headEval_eq_of_successorFeature_eq head F hsuccessorEq
  exact hspec₁.injective_on_rootPuncturedSoutheast
    hx hy hvar₁ hheadEq

end OneChannelCNNUniversality
