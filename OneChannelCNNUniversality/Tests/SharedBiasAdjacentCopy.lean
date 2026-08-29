import OneChannelCNNUniversality.SharedBiasAdjacentCopy

open OneChannelCNNUniversality

example {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (rowSteps extraColSteps : ℕ) (x : Image rows cols) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x
        (⟨0, hrows⟩ : Fin rows) (⟨0, hcols⟩ : Fin cols) =
      x ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  exact protectedLinearizedPascalSignal_northwest_zero
    hrows hcols rowSteps extraColSteps x

example {rows cols : ℕ} (hrows : 0 < rows) (hcols : 2 ≤ cols)
    (rowSteps extraColSteps : ℕ) (x : Image rows cols) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x
        (⟨0, hrows⟩ : Fin rows) (⟨1, by omega⟩ : Fin cols) =
      x ⟨0, hrows⟩ ⟨1, by omega⟩ +
        (extraColSteps + 1 : ℕ) * x ⟨0, hrows⟩ ⟨0, by omega⟩ := by
  exact protectedLinearizedPascalSignal_northwest_one
    hrows hcols rowSteps extraColSteps x

example {rows cols : ℕ} {x : Image rows cols}
    (hx : ImageNonnegative x) :
    adjacentCopyLayer.eval x =
      fullConvImage horizontalAccumulationKernel x := by
  exact adjacentCopyLayer_eval_of_nonnegative hx

example {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    {x : Image rows cols} (hx : ImageNonnegative x)
    (hvacant : EastNeighborVacant x) :
    EastRootDuplicate (adjacentCopyLayer.eval x) := by
  exact adjacentCopyLayer_eastRootDuplicate hrows hcols hx hvacant

example {rows cols : ℕ} {x y : Image rows cols}
    (hx : ImageNonnegative x) (hy : ImageNonnegative y)
    (heval : adjacentCopyLayer.eval x = adjacentCopyLayer.eval y) :
    x = y := by
  exact adjacentCopyLayer_injective_of_nonnegative hx hy heval

#check exists_injective_adjacentCopy_selection
