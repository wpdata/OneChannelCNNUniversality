import OneChannelCNNUniversality.SharedBiasParallelStripeCandidate

/-!
# A compensated sign-changing two-target stripe

The real-rooted carrier from `SharedBiasParallelStripeCandidate` has the
right final two-target geometry, but one of its proper prefixes changes sign.
This file gives an exact layerwise-bias certificate which removes that
obstruction.

For a scale `s`, start with the width-two seed `4s C₂` and use the ordered
horizontal factors

\[
  X+\frac14,\qquad 1-X,\qquad X-2,\qquad X-3.
\]

After the first three factors add the shared scalar biases `0`, `5s`, and
`13s`.  Every coefficient of every proper state is then at least `s`.  The
complete address has values

\[
  A(2)=A(4)=-35s,\qquad A(3)=-18s.
\]

Thus the intervening protected non-target lies exactly `17s` above the two
common-baseline targets.  Unlike the uncompensated candidate, this carrier
has a uniform positive margin at every proper ReLU stage.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

set_option maxHeartbeats 800000

/-- State after the first factor.  The first shared bias is zero. -/
noncomputable def parallelStripeCompensatedStageOne (s : ℝ) : ℝ[X] :=
  (X + C (1 / 4 : ℝ)) * (C (4 * s) * generalRidgeBoxcar 2)

/-- State after the second factor and shared bias `5s`. -/
noncomputable def parallelStripeCompensatedStageTwo (s : ℝ) : ℝ[X] :=
  (C 1 - X) * parallelStripeCompensatedStageOne s +
    C (5 * s) * generalRidgeBoxcar 4

/-- State after the third factor and shared bias `13s`. -/
noncomputable def parallelStripeCompensatedStageThree (s : ℝ) : ℝ[X] :=
  (X - C 2) * parallelStripeCompensatedStageTwo s +
    C (13 * s) * generalRidgeBoxcar 5

/-- Complete preactivation address after the fourth factor. -/
noncomputable def parallelStripeCompensatedFinal (s : ℝ) : ℝ[X] :=
  (X - C 3) * parallelStripeCompensatedStageThree s

/-- Every coordinate after the first factor has margin at least `s`. -/
theorem parallelStripeCompensatedStageOne_ge (s : ℝ) (hs : 0 ≤ s)
    (q : ℕ) (hq : q ≤ 3) :
    s ≤ (parallelStripeCompensatedStageOne s).coeff q := by
  interval_cases q <;>
    norm_num [parallelStripeCompensatedStageOne,
      generalRidgeBoxcar_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;> linarith

/-- Every coordinate after the second factor has margin at least `s`. -/
theorem parallelStripeCompensatedStageTwo_ge (s : ℝ) (hs : 0 ≤ s)
    (q : ℕ) (hq : q ≤ 4) :
    s ≤ (parallelStripeCompensatedStageTwo s).coeff q := by
  interval_cases q <;>
    norm_num [parallelStripeCompensatedStageTwo,
      parallelStripeCompensatedStageOne, generalRidgeBoxcar_coeff,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;> linarith

/-- Every coordinate after the third factor has margin at least `s`. -/
theorem parallelStripeCompensatedStageThree_ge (s : ℝ) (hs : 0 ≤ s)
    (q : ℕ) (hq : q ≤ 5) :
    s ≤ (parallelStripeCompensatedStageThree s).coeff q := by
  interval_cases q <;>
    norm_num [parallelStripeCompensatedStageThree,
      parallelStripeCompensatedStageTwo,
      parallelStripeCompensatedStageOne, generalRidgeBoxcar_coeff,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_X, coeff_C, coeff_one] <;> linarith

/-- Exact address at the first packed target. -/
theorem parallelStripeCompensatedFinal_target_two (s : ℝ) :
    (parallelStripeCompensatedFinal s).coeff 2 = -35 * s := by
  norm_num [parallelStripeCompensatedFinal,
    parallelStripeCompensatedStageThree,
    parallelStripeCompensatedStageTwo,
    parallelStripeCompensatedStageOne, generalRidgeBoxcar_coeff,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]
  all_goals ring

/-- Exact address at the protected intervening non-target. -/
theorem parallelStripeCompensatedFinal_middle (s : ℝ) :
    (parallelStripeCompensatedFinal s).coeff 3 = -18 * s := by
  norm_num [parallelStripeCompensatedFinal,
    parallelStripeCompensatedStageThree,
    parallelStripeCompensatedStageTwo,
    parallelStripeCompensatedStageOne, generalRidgeBoxcar_coeff,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]
  all_goals ring

/-- Exact address at the second packed target. -/
theorem parallelStripeCompensatedFinal_target_four (s : ℝ) :
    (parallelStripeCompensatedFinal s).coeff 4 = -35 * s := by
  norm_num [parallelStripeCompensatedFinal,
    parallelStripeCompensatedStageThree,
    parallelStripeCompensatedStageTwo,
    parallelStripeCompensatedStageOne, generalRidgeBoxcar_coeff,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X, coeff_C, coeff_one]
  all_goals ring

/-- Both packed targets have one common compensated baseline. -/
theorem parallelStripeCompensatedFinal_common_targets (s : ℝ) :
    (parallelStripeCompensatedFinal s).coeff 2 =
      (parallelStripeCompensatedFinal s).coeff 4 := by
  rw [parallelStripeCompensatedFinal_target_two,
    parallelStripeCompensatedFinal_target_four]

/-- The middle protected non-target is exactly `17s` above the targets. -/
theorem parallelStripeCompensatedFinal_middle_gap (s : ℝ) :
    (parallelStripeCompensatedFinal s).coeff 3 -
        (parallelStripeCompensatedFinal s).coeff 2 = 17 * s := by
  rw [parallelStripeCompensatedFinal_middle,
    parallelStripeCompensatedFinal_target_two]
  ring

/-- At scale at least `1/17`, the compensated carrier meets the selector's
unit-gap normalization at the middle protected non-target. -/
theorem parallelStripeCompensatedFinal_middle_unit_gap (s : ℝ)
    (hs : 1 / 17 ≤ s) :
    1 ≤ (parallelStripeCompensatedFinal s).coeff 3 -
      (parallelStripeCompensatedFinal s).coeff 2 := by
  rw [parallelStripeCompensatedFinal_middle_gap]
  linarith

end OneChannelCNNUniversality
