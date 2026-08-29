import OneChannelCNNUniversality.SharedBiasSuccessorSelection

open OneChannelCNNUniversality

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) (hF : ContinuousFeatureOn K F) :
    ContinuousFeatureOn K (successorFeature head F) := by
  exact continuousFeatureOn_successorFeature head F hF

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (hhead : 0 < head.net.depth)
    (F : X → Image inRows inCols) (hF : ContinuousFeatureOn K F)
    (rowSteps extraColSteps : ℕ)
    (targetRow : Fin (midRows + 2 - 1))
    (targetCol : Fin (midCols + 2 - 1)) (θ : ℝ)
    (hrowSteps : (midRows + 2 - 1) - 1 ≤ rowSteps)
    (hcolSteps : (midCols + 2 - 1) - 1 ≤ extraColSteps + 1) :
    ∃ c b : ℝ, ∃ tail : SharedBiasNetworkTo 2 2
        (midRows + 2 - 1) (midCols + 2 - 1)
        (grownSize 2
          (grownSize 2 ((midRows + 2 - 1) + 2 - 1)
            extraColSteps) rowSteps + 2 - 1)
        (grownSize 2
          (grownSize 2 ((midCols + 2 - 1) + 2 - 1)
            extraColSteps) rowSteps + 2 - 1),
      0 < c ∧ 0 < b ∧
      BundledPascalGridSelectionSpec K (successorFeature head F) θ
        rowSteps extraColSteps targetRow targetCol c b tail ∧
      ∀ x ∈ K,
        (head.appendWithSeed c tail).eval (F x) =
          tail.eval
            (successorFeature head F x +
              constantImage (midRows + 2 - 1) (midCols + 2 - 1) c) := by
  exact exists_bundled_pascal_selection_after hK head hhead F hF
    rowSteps extraColSteps targetRow targetCol θ hrowSteps hcolSteps

#check exists_two_bundled_pascal_selection_stages
