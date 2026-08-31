import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeWidthSeedAddress
import OneChannelCNNUniversality.SharedBiasParallelRidgeAlgebra

/-!
# A baseline obstruction for the standard parallel stripe

The independent-width proper network and final local address remove the
prefix and boundary obstacles to parallel ridge packing.  They do not,
however, make the original nodal horizontal carrier constant on several
packed targets.

The smallest nontrivial packed example has two width-two targets.  Its
factor depth is four and its target columns are `2` and `4`.  For

\[
  G_4(X)=(X+1)(X+2)(X+3)(X+4)
        =24+50X+35X^2+10X^3+X^4
\]

and `C_2(X)=1+X+X^2`, the relevant coefficients are

\[
  [X^2](G_4C_2)=109,
  \qquad [X^4](G_4C_2)=46.
\]

Lean therefore proves that, for every nonzero reciprocal scale, even the
zero-weight instance gives different row-one seed addresses at the two
packed targets.  This is a negative result about direct reuse of the
standard single-target stripe carrier, not an impossibility theorem for the
architecture or for a redesigned horizontal carrier.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- The zero weights in the minimal two-target, width-two instance. -/
def parallelStripeTwoTargetZeroWeights : Fin 4 → ℝ := fun _ ↦ 0

private theorem parallelStripeTwoTargetPolynomial_zero :
    generalRidgeTargetPolynomial
        (generalRidgeExtendedWeights parallelStripeTwoTargetZeroWeights) =
      0 := by
  have hW :
      generalRidgeExtendedWeights parallelStripeTwoTargetZeroWeights = 0 := by
    funext k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simp only [generalRidgeExtendedWeights, Fin.lastCases_last]
      rfl
    · simp [parallelStripeTwoTargetZeroWeights]
  rw [hW]
  exact Polynomial.ofFn_zero 5

theorem parallelStripeTwoTargetPerturbation_zero (q : ℕ) :
    generalRidgeStripeWidthSeedPerturbation
      parallelStripeTwoTargetZeroWeights 2 q = 0 := by
  simp [generalRidgeStripeWidthSeedPerturbation,
    parallelStripeTwoTargetPolynomial_zero]

private theorem generalRidgeNodalProduct_four_explicit :
    generalRidgeNodalProduct 4 =
      24 + 50 * X + 35 * X^2 + 10 * X^3 + X^4 := by
  norm_num [generalRidgeNodalProduct, generalRidgeNodalFactor,
    Fin.prod_univ_succ]
  ring

/-- The standard horizontal carrier has coefficient `109` at the first
packed target. -/
theorem generalRidgeNodalProduct_four_boxcar_two_coeff_two :
    (generalRidgeNodalProduct 4 * generalRidgeBoxcar 2).coeff 2 = 109 := by
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [generalRidgeBoxcar_coeff,
    generalRidgeNodalProduct_four_explicit, coeff_X,
    Finset.sum_range_succ]

/-- The same carrier has coefficient `46` at the second packed target. -/
theorem generalRidgeNodalProduct_four_boxcar_two_coeff_four :
    (generalRidgeNodalProduct 4 * generalRidgeBoxcar 2).coeff 4 = 46 := by
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [generalRidgeBoxcar_coeff,
    generalRidgeNodalProduct_four_explicit, coeff_X,
    Finset.sum_range_succ]

/-- Exact standard-stripe seed address at the first packed target. -/
theorem parallelStripeTwoTargetSeedAddress_two (T : ℝ) (hT : T ≠ 0) :
    generalRidgeStripeWidthSeedAddressRowOne
        parallelStripeTwoTargetZeroWeights T 2 2 = -109 * T := by
  rw [generalRidgeStripeWidthSeedAddressRowOne_eq
    parallelStripeTwoTargetZeroWeights T hT]
  rw [generalRidgeNodalProduct_four_boxcar_two_coeff_two,
    parallelStripeTwoTargetPerturbation_zero]
  ring

/-- Exact standard-stripe seed address at the second packed target. -/
theorem parallelStripeTwoTargetSeedAddress_four (T : ℝ) (hT : T ≠ 0) :
    generalRidgeStripeWidthSeedAddressRowOne
        parallelStripeTwoTargetZeroWeights T 2 4 = -46 * T := by
  rw [generalRidgeStripeWidthSeedAddressRowOne_eq
    parallelStripeTwoTargetZeroWeights T hT]
  rw [generalRidgeNodalProduct_four_boxcar_two_coeff_four,
    parallelStripeTwoTargetPerturbation_zero]
  ring

/-- For every nonzero reciprocal scale, the two packed targets fail the
common-baseline hypothesis required by direct simultaneous selection. -/
theorem parallelStripeTwoTargetSeedAddress_ne (T : ℝ) (hT : T ≠ 0) :
    generalRidgeStripeWidthSeedAddressRowOne
        parallelStripeTwoTargetZeroWeights T 2 2 ≠
      generalRidgeStripeWidthSeedAddressRowOne
        parallelStripeTwoTargetZeroWeights T 2 4 := by
  rw [parallelStripeTwoTargetSeedAddress_two T hT,
    parallelStripeTwoTargetSeedAddress_four T hT]
  intro h
  apply hT
  linarith

end OneChannelCNNUniversality
