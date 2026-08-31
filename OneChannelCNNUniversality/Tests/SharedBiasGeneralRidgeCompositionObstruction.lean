import OneChannelCNNUniversality.SharedBiasGeneralRidgeCompositionObstruction

/-!
# Regression tests for the present general-ridge composition boundary

These statements concern the existing separated single-ridge construction.
They do not assert non-universality of the shared-bias architecture.
-/

namespace OneChannelCNNUniversality

#check generalRidgeFactorList_rowPolynomial_one
#check generalRidgeFactorList_rowOne_reflects_lowerRow
#check fullConv_generalRidgeSeparatedLastKernel_row_one_interior_eq
#check generalRidgeSeparatedLastKernel_row_one_interior_flat
#check not_generalRidgeSeparatedLastKernel_unit_gap_on_row_one

/-- A general-ridge factor chain applied to a multirow image has an exact
old-row-one contribution in addition to the intended northern-row term. -/
example {d rows cols : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hη : ∑ i, η i = w 0) (z : Image rows cols) :
    rowPolynomial
        (fullConvChain (generalRidgeFactorList w η) z) 1 =
      generalRidgeNodalProduct d * rowPolynomial z 1 +
        generalRidgeTargetPolynomial w * rowPolynomial z 0 := by
  exact generalRidgeFactorList_rowPolynomial_one w η hη z

/-- With the northern row fixed, equality of output row one reflects
equality of the old row one. -/
example {d rows cols : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    {x y : Image rows cols}
    (hnorth : rowPolynomial x 0 = rowPolynomial y 0)
    (hout :
      rowPolynomial
          (fullConvChain (generalRidgeFactorList w η) x) 1 =
        rowPolynomial
          (fullConvChain (generalRidgeFactorList w η) y) 1) :
    rowPolynomial x 1 = rowPolynomial y 1 := by
  exact generalRidgeFactorList_rowOne_reflects_lowerRow
    w η hnorth hout

/-- The current terminal address cannot have a unit gap from the target to
every other coordinate of row one. -/
example {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ) :
    ¬ 1 ≤
      fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 1 (d - 1) -
        fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 1 d := by
  exact not_generalRidgeSeparatedLastKernel_unit_gap_on_row_one hd w

end OneChannelCNNUniversality
