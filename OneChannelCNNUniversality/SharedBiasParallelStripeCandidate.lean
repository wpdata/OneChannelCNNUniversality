import OneChannelCNNUniversality.SharedBiasParallelStripeObstruction

/-!
# A sign-changing two-target stripe candidate

The positive-prefix obstruction identifies the property that a successful
two-target horizontal carrier must abandon.  This module gives an exact
algebraic witness.  Define

\[
  Q(X)=X^4-\frac{23}{4}X^3+\frac{19}{2}X^2
       -\frac{13}{4}X-\frac32.
\]

Lean verifies the four distinct real roots

\[
  1,\quad 2,\quad 3,\quad -\frac14,
\]

so equivalently

\[
  Q(X)=(X-1)(X-2)(X-3)\left(X+\frac14\right).
\]

For the width-two boxcar, the packed target columns `2` and `4` both have
value `19/4`, while the intervening non-target column `3` has value `1/2`.
Thus the positive target-to-middle gap is `17/4`, exactly the geometry that
the standard positive-prefix carrier could not provide.

The price is also explicit: after the positive factor `X+1/4` and the first
negative factor `X-1`, the constant coefficient of the boxcar-propagated
prefix is `-1/4`.  Hence the old positive constant carrier cannot keep this
prefix in ReLU's linear branch.  A future genuine construction must use a
different prefix-linearization mechanism, such as a second signed carrier
or protected sequential transport.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Explicit monic real-rooted horizontal polynomial for the minimal
two-target geometry. -/
noncomputable def parallelStripeTwoTargetCandidatePolynomial : ℝ[X] :=
  C (-3 / 2 : ℝ) + C (-13 / 4 : ℝ) * X +
    C (19 / 2 : ℝ) * X ^ 2 + C (-23 / 4 : ℝ) * X ^ 3 + X ^ 4

theorem parallelStripeTwoTargetCandidate_root_one :
    parallelStripeTwoTargetCandidatePolynomial.eval 1 = 0 := by
  norm_num [parallelStripeTwoTargetCandidatePolynomial]

theorem parallelStripeTwoTargetCandidate_root_two :
    parallelStripeTwoTargetCandidatePolynomial.eval 2 = 0 := by
  norm_num [parallelStripeTwoTargetCandidatePolynomial]

theorem parallelStripeTwoTargetCandidate_root_three :
    parallelStripeTwoTargetCandidatePolynomial.eval 3 = 0 := by
  norm_num [parallelStripeTwoTargetCandidatePolynomial]

theorem parallelStripeTwoTargetCandidate_root_neg_quarter :
    parallelStripeTwoTargetCandidatePolynomial.eval (-1 / 4) = 0 := by
  norm_num [parallelStripeTwoTargetCandidatePolynomial]

theorem parallelStripeTwoTargetCandidate_leading_coeff :
    parallelStripeTwoTargetCandidatePolynomial.coeff 4 = 1 := by
  norm_num [parallelStripeTwoTargetCandidatePolynomial, coeff_X]

/-- The first packed target receives address value `19/4`. -/
theorem parallelStripeTwoTargetCandidate_target_two :
    (parallelStripeTwoTargetCandidatePolynomial *
        generalRidgeBoxcar 2).coeff 2 = 19 / 4 := by
  rw [coeff_mul_generalRidgeBoxcar_two_at_two]
  norm_num [parallelStripeTwoTargetCandidatePolynomial, coeff_X]

/-- The intervening non-target receives only `1/2`. -/
theorem parallelStripeTwoTargetCandidate_middle :
    (parallelStripeTwoTargetCandidatePolynomial *
        generalRidgeBoxcar 2).coeff 3 = 1 / 2 := by
  rw [coeff_mul_generalRidgeBoxcar_two_at_three]
  norm_num [parallelStripeTwoTargetCandidatePolynomial, coeff_X]

/-- The second packed target again receives `19/4`. -/
theorem parallelStripeTwoTargetCandidate_target_four :
    (parallelStripeTwoTargetCandidatePolynomial *
        generalRidgeBoxcar 2).coeff 4 = 19 / 4 := by
  rw [coeff_mul_generalRidgeBoxcar_two_at_four]
  norm_num [parallelStripeTwoTargetCandidatePolynomial, coeff_X]

/-- The two packed targets have exactly one common horizontal baseline. -/
theorem parallelStripeTwoTargetCandidate_common_targets :
    (parallelStripeTwoTargetCandidatePolynomial *
        generalRidgeBoxcar 2).coeff 2 =
      (parallelStripeTwoTargetCandidatePolynomial *
        generalRidgeBoxcar 2).coeff 4 := by
  rw [parallelStripeTwoTargetCandidate_target_two,
    parallelStripeTwoTargetCandidate_target_four]

/-- The common target address exceeds the middle non-target address by
exactly `17/4`. -/
theorem parallelStripeTwoTargetCandidate_middle_gap :
    (parallelStripeTwoTargetCandidatePolynomial *
          generalRidgeBoxcar 2).coeff 2 -
        (parallelStripeTwoTargetCandidatePolynomial *
          generalRidgeBoxcar 2).coeff 3 = 17 / 4 := by
  rw [parallelStripeTwoTargetCandidate_target_two,
    parallelStripeTwoTargetCandidate_middle]
  norm_num

/-- The first sign-changing proper prefix in the displayed factor order. -/
noncomputable def parallelStripeTwoTargetCandidatePrefixTwo : ℝ[X] :=
  (X + C (1 / 4 : ℝ)) * (X - C 1)

/-- Its propagated constant coefficient is negative, so the old positive
constant carrier cannot linearize this prefix. -/
theorem parallelStripeTwoTargetCandidatePrefixTwo_negative :
    (parallelStripeTwoTargetCandidatePrefixTwo *
        generalRidgeBoxcar 2).coeff 0 = -1 / 4 := by
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [parallelStripeTwoTargetCandidatePrefixTwo,
    generalRidgeBoxcar_coeff, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_X]

theorem parallelStripeTwoTargetCandidatePrefixTwo_not_nonnegative :
    ¬ 0 ≤ (parallelStripeTwoTargetCandidatePrefixTwo *
      generalRidgeBoxcar 2).coeff 0 := by
  rw [parallelStripeTwoTargetCandidatePrefixTwo_negative]
  norm_num

end OneChannelCNNUniversality
