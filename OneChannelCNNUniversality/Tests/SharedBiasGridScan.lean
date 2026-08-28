import OneChannelCNNUniversality.SharedBiasGridScan

open OneChannelCNNUniversality

example {rows cols : ℕ} (rowSteps colSteps : ℕ) (c : ℝ)
    (i : Fin rows) (j : Fin cols) :
    protectedPascalGridAddress rowSteps colSteps rows cols c i j =
      c * pascalPrefix rowSteps i * pascalPrefix colSteps j := by
  exact protectedPascalGridAddress_eq rowSteps colSteps c i j

/-- An asymmetric numerical case locks the row/column step ordering:
`2 * (1 + 2) * (1 + 3 + 3) = 42`. -/
example :
    protectedPascalGridAddress 2 3 2 3 2
      (⟨1, by omega⟩ : Fin 2) (⟨2, by omega⟩ : Fin 3) = 42 := by
  rw [protectedPascalGridAddress_eq]
  norm_num [pascalPrefix, Finset.sum_range_succ, Nat.choose]

example {rows cols : ℕ} (rowSteps colSteps : ℕ) (c : ℝ)
    (targetRow : Fin rows) (targetCol : Fin cols)
    (hrowSteps : rows - 1 ≤ rowSteps) (hcolSteps : cols - 1 ≤ colSteps)
    (hc : 0 ≤ c) :
    ∀ i j, southeastProtected targetRow targetCol i j →
      (i, j) ≠ (targetRow, targetCol) →
      c ≤ protectedPascalGridAddress rowSteps colSteps rows cols c i j -
        protectedPascalGridAddress rowSteps colSteps rows cols c
          targetRow targetCol := by
  exact protectedPascalGridAddress_gap_on rowSteps colSteps c
    targetRow targetCol hrowSteps hcolSteps hc

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (signal : X → Image rows cols) (hSignal : ContinuousFeatureOn K signal)
    (rowSteps colSteps : ℕ) (targetRow : Fin rows) (targetCol : Fin cols)
    (θ : ℝ) (hrowSteps : rows - 1 ≤ rowSteps)
    (hcolSteps : cols - 1 ≤ colSteps) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i j,
      southeastProtected targetRow targetCol i j →
      relu (signal x i j +
          protectedPascalGridAddress rowSteps colSteps rows cols c i j +
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol)) =
        if (i, j) = (targetRow, targetCol) then relu (signal x i j + θ)
        else signal x i j +
          protectedPascalGridAddress rowSteps colSteps rows cols c i j +
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol) := by
  exact exists_southeast_selected_relu hK signal hSignal rowSteps colSteps
    targetRow targetCol θ hrowSteps hcolSteps

example {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    Function.Injective (fun x : Image rows cols ↦
      iterateFullConv
        (verticalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
        rowSteps
        (iterateFullConv
          (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
          colSteps x)) := by
  exact pascalGridTransform_injective rowSteps colSteps
