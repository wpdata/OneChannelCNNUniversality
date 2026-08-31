import OneChannelCNNUniversality.SharedBiasGeneralRidgeSeparation

/-!
# Composition boundary of the present arbitrary-width ridge block

The separated arbitrary-width construction is exact for a one-row input.
This file records why that theorem cannot simply be appended as a black-box
ridge compiler after its own multirow output.  A new factor chain retains a
nonzero contribution from the old row one, and the current one-directional
terminal address is flat along the interior of that row.

These are obstruction theorems for the present construction and its naive
sequential reuse.  They are not non-universality statements for the full
one-channel shared-bias architecture.
-/

namespace OneChannelCNNUniversality

open Polynomial

/-- On a general multirow input, row one after the ridge factor chain is the
sum of the intended northern-row term and a nonzero nodal transform of the
old row one.  The latter term vanishes in the one-row theorem only because
the input is zero-extended below its northern row. -/
theorem generalRidgeFactorList_rowPolynomial_one
    {d rows cols : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hη : ∑ i, η i = w 0) (z : Image rows cols) :
    rowPolynomial
        (fullConvChain (generalRidgeFactorList w η) z) 1 =
      generalRidgeNodalProduct d * rowPolynomial z 1 +
        generalRidgeTargetPolynomial w * rowPolynomial z 0 := by
  rw [rowPolynomial_fullConvChain_one,
    generalRidgeFactorList_horizontalProduct]
  rw [← bivariateProduct_coeff_one,
    generalRidgeFactorList_bivariateProduct,
    generalRidgeBiProduct_vertical_one w η hη]

/-- With the northern input row fixed, equality of the factor-chain output
row one forces equality of the old row one.  In the intended nondegenerate
multirow setting, this row of the chain therefore cannot ignore the old
second row. -/
theorem generalRidgeFactorList_rowOne_reflects_lowerRow
    {d rows cols : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    {x y : Image rows cols}
    (hnorth : rowPolynomial x 0 = rowPolynomial y 0)
    (hout :
      rowPolynomial
          (fullConvChain (generalRidgeFactorList w η) x) 1 =
        rowPolynomial
          (fullConvChain (generalRidgeFactorList w η) y) 1) :
    rowPolynomial x 1 = rowPolynomial y 1 := by
  rw [rowPolynomial_fullConvChain_one,
    rowPolynomial_fullConvChain_one, hnorth] at hout
  have hhorizontal :
      horizontalProduct (generalRidgeFactorList w η) ≠ 0 := by
    rw [generalRidgeFactorList_horizontalProduct]
    exact (generalRidgeNodalProduct_monic d).ne_zero
  apply mul_left_cancel₀ hhorizontal
  exact add_right_cancel hout

/-- Every interior coordinate of row one sees all four entries of the last
kernel on the unit constant carrier, and hence has the same response as the
distinguished ridge target. -/
theorem fullConv_generalRidgeSeparatedLastKernel_row_one_interior_eq
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ)
    (q : Fin (2 * d + 1))
    (hq0 : 1 ≤ (q : ℕ)) (hqend : (q : ℕ) < 2 * d) :
    fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 q =
      generalRidgeBeta w (generalRidgeLastIndex hd) -
        |generalRidgeBeta w (generalRidgeLastIndex hd)| - 1 := by
  have hdpos : 0 < d := by omega
  have hone_lt : 1 < d := by omega
  have hqpred_lt : (q : ℕ) - 1 < 2 * d := by omega
  rw [generalRidgeSeparatedLastKernel_eq,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [generalRidgeKernelFactor, zeroExtend, constantImage,
    hdpos, hone_lt, hq0, hqend, hqpred_lt,
    generalRidgeSeparatedAllocation_last]
  have hscale := generalRidgeCarrierScale_mul_succ hd w
  nlinarith

/-- The whole interior of row one is flat in the current terminal address;
in particular, the target is not a unique address minimum there. -/
theorem generalRidgeSeparatedLastKernel_row_one_interior_flat
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ)
    (q : Fin (2 * d + 1))
    (hq0 : 1 ≤ (q : ℕ)) (hqend : (q : ℕ) < 2 * d) :
    fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 q =
      fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 d := by
  rw [fullConv_generalRidgeSeparatedLastKernel_row_one_interior_eq
      hd w q hq0 hqend,
    fullConv_generalRidgeSeparatedLastKernel_target_eq]

/-- The predecessor of the target is a distinct interior site with exactly
the same address.  Consequently the present carrier cannot provide the unit
gap needed to protect the complete second row while selecting the target. -/
theorem not_generalRidgeSeparatedLastKernel_unit_gap_on_row_one
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ) :
    ¬ 1 ≤
      fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 1 (d - 1) -
        fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 1 d := by
  let q : Fin (2 * d + 1) := ⟨d - 1, by omega⟩
  have hq0 : 1 ≤ (q : ℕ) := by
    simp only [q]
    omega
  have hqend : (q : ℕ) < 2 * d := by
    simp only [q]
    omega
  have hflat := generalRidgeSeparatedLastKernel_row_one_interior_flat
    hd w q hq0 hqend
  have hflatNat :
    fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 (d - 1) =
      fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 d := by
    simpa only [q] using hflat
  rw [hflatNat]
  norm_num

end OneChannelCNNUniversality
