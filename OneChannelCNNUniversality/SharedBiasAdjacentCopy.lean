import OneChannelCNNUniversality.SharedBiasRedundantRecovery
import OneChannelCNNUniversality.SharedBiasSuccessorSelection
import OneChannelCNNUniversality.SharedBiasTwoStageRecovery

/-!
# A genuine adjacent-copy layer

The recovery theorem for a selected northwest register assumes that its
value is also present in the eastern neighbor.  This file realizes that
relation by one genuine zero-bias shared-scalar-bias ReLU layer.  The input
layout reserves the eastern neighbor as zero.  Horizontal Pascal
accumulation then copies the root into that site while remaining injective
on the whole nonnegative image.
-/

namespace OneChannelCNNUniversality

/-- The site immediately east of the northwest work register is reserved as
zero.  Zero extension makes the predicate meaningful for every image size. -/
def EastNeighborVacant {rows cols : ℕ} (x : Image rows cols) : Prop :=
  zeroExtend x 0 1 = 0

/-- One genuine expansive `2 × 2` shared-bias layer whose two horizontal
taps are both one and whose shared scalar bias is zero. -/
def adjacentCopyLayer {rows cols : ℕ} :
    SharedBiasNetworkTo 2 2 rows cols (rows + 2 - 1) (cols + 2 - 1) :=
  SharedBiasNetworkTo.single horizontalAccumulationKernel 0

/-- On a nonnegative input, the ReLU in the copy layer stays in its linear
branch, so evaluation is exactly horizontal Pascal accumulation. -/
theorem adjacentCopyLayer_eval_of_nonnegative
    {rows cols : ℕ} {x : Image rows cols} (hx : ImageNonnegative x) :
    (adjacentCopyLayer (rows := rows) (cols := cols)).eval x =
      fullConvImage horizontalAccumulationKernel x := by
  rw [adjacentCopyLayer, SharedBiasNetworkTo.eval_single]
  exact sharedLayerEval_zero_of_nonnegative
    horizontalAccumulationKernel_nonnegative hx

/-- The copy layer loses no information on nonnegative states. -/
theorem adjacentCopyLayer_injective_of_nonnegative
    {rows cols : ℕ} {x y : Image rows cols}
    (hx : ImageNonnegative x) (hy : ImageNonnegative y)
    (heval : (adjacentCopyLayer (rows := rows) (cols := cols)).eval x =
      (adjacentCopyLayer (rows := rows) (cols := cols)).eval y) :
    x = y := by
  apply horizontalAccumulationTransform_injective
  change fullConvImage horizontalAccumulationKernel x =
    fullConvImage horizontalAccumulationKernel y
  calc
    _ = (adjacentCopyLayer (rows := rows) (cols := cols)).eval x :=
      (adjacentCopyLayer_eval_of_nonnegative hx).symm
    _ = (adjacentCopyLayer (rows := rows) (cols := cols)).eval y := heval
    _ = _ := adjacentCopyLayer_eval_of_nonnegative hy

/-- If the eastern input neighbor is vacant, the genuine copy layer stores
the northwest root in both output columns zero and one. -/
theorem adjacentCopyLayer_eastRootDuplicate
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    {x : Image rows cols} (hx : ImageNonnegative x)
    (hvacant : EastNeighborVacant x) :
    EastRootDuplicate
      ((adjacentCopyLayer (rows := rows) (cols := cols)).eval x) := by
  rw [adjacentCopyLayer_eval_of_nonnegative hx]
  unfold EastNeighborVacant at hvacant
  unfold EastRootDuplicate
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_horizontalAccumulationKernel_nat,
    fullConv_horizontalAccumulationKernel_nat]
  have hroot : zeroExtend x 0 0 = x ⟨0, hrows⟩ ⟨0, hcols⟩ := by
    simp [zeroExtend, hrows, hcols]
  simp [hvacant, hroot]

/-- The northwest duplicate survives the expansive delta bridge used to
insert the next selector's positive seed. -/
theorem EastRootDuplicate.successorFeature
    {X : Type*} {inRows inCols midRows midCols : ℕ}
    {head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols}
    {F : X → Image inRows inCols} {x : X}
    (hdup : EastRootDuplicate (head.eval (F x))) :
    EastRootDuplicate (successorFeature (X := X) head F x) := by
  unfold EastRootDuplicate at hdup ⊢
  unfold OneChannelCNNUniversality.successorFeature
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_expansiveIdentityKernel_nat,
    fullConv_expansiveIdentityKernel_nat]
  exact hdup

/-- A compact family of nonnegative states with one vacant eastern work site
admits a single genuine copy--seed--select CNN that is injective on the
family.  The returned selector acts at the northwest root of the duplicated
successor state, so its selected ReLU may vary with the input without losing
the original feature image. -/
theorem exists_injective_adjacentCopy_selection
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (F : X → Image rows cols) (hF : ContinuousFeatureOn K F)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFvacant : ∀ x ∈ K, EastNeighborVacant (F x))
    (hFinjective : Set.InjOn F K)
    (rowSteps extraColSteps : ℕ) (θ : ℝ)
    (hrowSteps :
      ((rows + 2 - 1) + 2 - 1) - 1 ≤ rowSteps)
    (hcolSteps :
      ((cols + 2 - 1) + 2 - 1) - 1 ≤ extraColSteps + 1) :
    ∃ c b : ℝ, ∃ tail : SharedBiasNetworkTo 2 2
        ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1)
        (protectedSelectionSize
          ((rows + 2 - 1) + 2 - 1) rowSteps extraColSteps)
        (protectedSelectionSize
          ((cols + 2 - 1) + 2 - 1) rowSteps extraColSteps),
      0 < c ∧ 0 < b ∧
      BundledPascalGridSelectionSpec K
        (successorFeature
          (adjacentCopyLayer (rows := rows) (cols := cols)) F)
        θ rowSteps extraColSteps
        (⟨0, by omega⟩ : Fin ((rows + 2 - 1) + 2 - 1))
        (⟨0, by omega⟩ : Fin ((cols + 2 - 1) + 2 - 1)) c b tail ∧
      Set.InjOn
        (fun x ↦
          ((adjacentCopyLayer (rows := rows) (cols := cols)).appendWithSeed
            c tail).eval (F x)) K := by
  let head := adjacentCopyLayer (rows := rows) (cols := cols)
  have hdepth : 0 < head.net.depth := by
    simp [head, adjacentCopyLayer, SharedBiasNetworkTo.single,
      SharedBiasNetworkTo.cons, SharedBiasNetworkTo.nil,
      SharedBiasNetwork.depth]
  let targetRow : Fin ((rows + 2 - 1) + 2 - 1) := ⟨0, by omega⟩
  let targetCol : Fin ((cols + 2 - 1) + 2 - 1) := ⟨0, by omega⟩
  obtain ⟨c, b, tail, hc, hb, hspec, heval⟩ :=
    exists_bundled_pascal_selection_after hK head hdepth F hF
      rowSteps extraColSteps targetRow targetCol θ hrowSteps hcolSteps
  refine ⟨c, b, tail, hc, hb, ?_, ?_⟩
  · simpa [head, targetRow, targetCol] using hspec
  · intro x hx y hy hfinal
    have htail :
        tail.eval
            (successorFeature head F x +
              constantImage ((rows + 2 - 1) + 2 - 1)
                ((cols + 2 - 1) + 2 - 1) c) =
          tail.eval
            (successorFeature head F y +
              constantImage ((rows + 2 - 1) + 2 - 1)
                ((cols + 2 - 1) + 2 - 1) c) := by
      rw [← heval x hx, ← heval y hy]
      simpa [head] using hfinal
    have hxdup : EastRootDuplicate (successorFeature head F x) :=
      (adjacentCopyLayer_eastRootDuplicate hrows hcols
        (hFnonnegative x hx) (hFvacant x hx)).successorFeature
    have hydup : EastRootDuplicate (successorFeature head F y) :=
      (adjacentCopyLayer_eastRootDuplicate hrows hcols
        (hFnonnegative y hy) (hFvacant y hy)).successorFeature
    have hsucc : successorFeature head F x = successorFeature head F y := by
      apply hspec.injective_on_eastRootDuplicate (by omega) (by omega)
        hx hy hxdup hydup htail
    have hhead : head.eval (F x) = head.eval (F y) :=
      fullConvImage_expansiveIdentityKernel_injective hsucc
    have hfeature : F x = F y := by
      exact adjacentCopyLayer_injective_of_nonnegative
        (hFnonnegative x hx) (hFnonnegative y hy) hhead
    exact hFinjective hx hy hfeature

end OneChannelCNNUniversality
