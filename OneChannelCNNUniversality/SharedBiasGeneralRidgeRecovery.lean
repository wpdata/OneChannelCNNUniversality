import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution

/-!
# Exact recovery from the arbitrary-width northern row

The northern boundary of the pure general-ridge convolution carries the
input row multiplied by the monic nodal polynomial

\[
  \prod_{i=0}^{d-1} (X+i+1).
\]

Since the input row has a faithful polynomial encoding and this nodal
product is nonzero, equality of the complete finite northern output rows
forces equality of the inputs.  The conclusion is independent of the ridge
weights and of the lower-factor allocation.  Adding the same fixed northern
offset also preserves injectivity.
-/

namespace OneChannelCNNUniversality

open Polynomial

/-- The finite generating polynomial faithfully encodes every one-row
image, including the zero-width boundary case. -/
theorem rowPolynomial_zero_injective (cols : ℕ) :
    Function.Injective
      (fun x : Image 1 cols ↦ rowPolynomial x 0) := by
  intro x y hxy
  funext i j
  fin_cases i
  have hcoeff := congrArg (fun P : ℝ[X] ↦ P.coeff (j : ℕ)) hxy
  rw [rowPolynomial_coeff, rowPolynomial_coeff] at hcoeff
  simpa using hcoeff

/-- The complete finite northern row of the pure general-ridge convolution,
with its column type normalized from the factor-list length to the declared
depth. -/
noncomputable def generalRidgeFullConvNorthRow {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) :
    Fin (grownSize 2 (d + 1) d) → ℝ :=
  fun q ↦ zeroExtend (generalRidgeFullConv w η x) 0 q

@[simp] theorem generalRidgeFullConvNorthRow_apply {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) (q : Fin (grownSize 2 (d + 1) d)) :
    generalRidgeFullConvNorthRow w η x q =
      zeroExtend (generalRidgeFullConv w η x) 0 q := rfl

/-- Every coordinate of the normalized finite row is literally the
corresponding in-bounds coordinate of the convolution output. -/
theorem generalRidgeFullConvNorthRow_eq_output_apply {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) (q : Fin (grownSize 2 (d + 1) d)) :
    generalRidgeFullConvNorthRow w η x q =
      generalRidgeFullConv w η x
        ⟨0, by
          have hge := grownSize_ge_add_steps 2 1
            (generalRidgeFactorList w η).length (by omega)
          omega⟩
        ⟨q, by
          simpa only [generalRidgeFactorList_length] using q.isLt⟩ := by
  have hrow : 0 < grownSize 2 1 (generalRidgeFactorList w η).length := by
    have hge := grownSize_ge_add_steps 2 1
      (generalRidgeFactorList w η).length (by omega)
    omega
  have hcol : (q : ℕ) <
      grownSize 2 (d + 1) (generalRidgeFactorList w η).length := by
    simpa only [generalRidgeFactorList_length] using q.isLt
  rw [generalRidgeFullConvNorthRow_apply,
    zeroExtend_of_lt _ hrow hcol]

/-- If two arbitrary-width pure-convolution outputs agree at every
coordinate of their complete northern rows, then their one-row inputs are
equal. -/
theorem generalRidgeFullConv_north_eq_imp_eq {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    {x y : Image 1 (d + 1)}
    (hxy : ∀ q : Fin (grownSize 2 (d + 1) d),
      generalRidgeFullConvNorthRow w η x q =
        generalRidgeFullConvNorthRow w η y q) :
    x = y := by
  have hpolyOut :
      rowPolynomial (generalRidgeFullConv w η x) 0 =
        rowPolynomial (generalRidgeFullConv w η y) 0 := by
    ext q
    rw [rowPolynomial_coeff, rowPolynomial_coeff]
    by_cases hq : q < grownSize 2 (d + 1) d
    · exact hxy ⟨q, hq⟩
    · have hq' : grownSize 2 (d + 1) d ≤ q := Nat.le_of_not_gt hq
      have hxzero : zeroExtend (generalRidgeFullConv w η x) 0 q = 0 := by
        apply zeroExtend_col_outside
        simpa only [generalRidgeFactorList_length] using hq'
      have hyzero : zeroExtend (generalRidgeFullConv w η y) 0 q = 0 := by
        apply zeroExtend_col_outside
        simpa only [generalRidgeFactorList_length] using hq'
      rw [hxzero, hyzero]
  rw [generalRidgeFullConv_north w η x,
    generalRidgeFullConv_north w η y] at hpolyOut
  have hnodal : generalRidgeNodalProduct d ≠ 0 :=
    (generalRidgeNodalProduct_monic d).ne_zero
  have hrow : rowPolynomial x 0 = rowPolynomial y 0 :=
    mul_left_cancel₀ hnodal hpolyOut
  exact rowPolynomial_zero_injective (d + 1) hrow

/-- The map from a one-row input to the complete finite northern output row
of the arbitrary-width pure convolution is injective. -/
theorem generalRidgeFullConv_north_injective {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Function.Injective
      (fun x : Image 1 (d + 1) ↦
        generalRidgeFullConvNorthRow w η x) := by
  intro x y hxy
  apply generalRidgeFullConv_north_eq_imp_eq w η
  exact fun q ↦ congrFun hxy q

/-- Adding an arbitrary fixed offset to the complete northern output row
preserves injectivity. -/
theorem generalRidgeFullConv_north_add_injective {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (offset : Fin (grownSize 2 (d + 1) d) → ℝ) :
    Function.Injective
      (fun x : Image 1 (d + 1) ↦
        fun q : Fin (grownSize 2 (d + 1) d) ↦
          generalRidgeFullConvNorthRow w η x q + offset q) := by
  intro x y hxy
  apply generalRidgeFullConv_north_injective w η
  funext q
  exact add_right_cancel (congrFun hxy q)

end OneChannelCNNUniversality
