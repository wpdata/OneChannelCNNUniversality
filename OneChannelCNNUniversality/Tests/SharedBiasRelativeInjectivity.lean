import OneChannelCNNUniversality.SharedBiasRelativeInjectivity

open OneChannelCNNUniversality

example {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (fullConvImage horizontalAccumulationKernel x)
      (fullConvImage horizontalAccumulationKernel y) r s) :
    NorthwestAgree x y r s := by
  exact northwestAgree_of_horizontalAccumulation hout

example {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (fullConvImage verticalAccumulationKernel x)
      (fullConvImage verticalAccumulationKernel y) r s) :
    NorthwestAgree x y r s := by
  exact northwestAgree_of_verticalAccumulation hout

example {rows cols : ℕ} (steps : ℕ) {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (iterateFullConv horizontalAccumulationKernel steps x)
      (iterateFullConv horizontalAccumulationKernel steps y) r s) :
    NorthwestAgree x y r s := by
  exact northwestAgree_of_horizontalAccumulationIterations steps hout

example {rows cols : ℕ} (steps : ℕ) {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (iterateFullConv verticalAccumulationKernel steps x)
      (iterateFullConv verticalAccumulationKernel steps y) r s) :
    NorthwestAgree x y r s := by
  exact northwestAgree_of_verticalAccumulationIterations steps hout

example {rows cols : ℕ} (rowSteps extraColSteps : ℕ) :
    Function.Injective
      (protectedLinearizedPascalSignal
        (rows := rows) (cols := cols) rowSteps extraColSteps) := by
  exact protectedLinearizedPascalSignal_injective rowSteps extraColSteps

example {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {θ : ℝ} {rowSteps extraColSteps : ℕ}
    {targetRow : Fin rows} {targetCol : Fin cols} {c b : ℝ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 (grownSize 2 (rows + 2 - 1) extraColSteps) rowSteps + 2 - 1)
      (grownSize 2 (grownSize 2 (cols + 2 - 1) extraColSteps) rowSteps + 2 - 1)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      targetRow targetCol c b net) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hvar : AgreeOutsideStrictSoutheast
      (V x) (V y) targetRow targetCol)
    (heval : net.eval (V x + constantImage rows cols c) =
      net.eval (V y + constantImage rows cols c)) :
    V x = V y := by
  exact hspec.injective_on_rootPuncturedSoutheast hx hy hvar heval
