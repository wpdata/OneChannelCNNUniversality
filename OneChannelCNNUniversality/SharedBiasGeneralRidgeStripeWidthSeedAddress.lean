import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeSeedAddress

/-!
# Full-chain stripe seed addresses with independent input width

For a `1 × m` input, the identity seed produces equal unit boxcars
`C_m=1+X+⋯+X^m` on the northern two rows.  The factor depth is still
determined independently by `w : Fin (n+2) → ℝ`.  Thus the complete formal
seed addresses are

\[
  A_0(q)=[X^q]\,(-T G_{n+2})C_m,
\]

and, for `T ≠ 0`,

\[
  A_1(q)=-T[X^q](G_{n+2}C_m)
    +[X^q](P_wC_m).
\]

These identities expose the exact horizontal common-baseline obligation in
parallel ridge packing without imposing the old width-depth equality.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Northern complete-chain seed address for arbitrary seed width `m+1`. -/
noncomputable def generalRidgeStripeWidthSeedAddressRowZero {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (m q : ℕ) : ℝ :=
  (horizontalProduct (generalRidgeStripeTwistedFactors w T) *
      generalRidgeBoxcar m).coeff q

/-- Row-one complete-chain seed address for arbitrary seed width `m+1`. -/
noncomputable def generalRidgeStripeWidthSeedAddressRowOne {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (m q : ℕ) : ℝ :=
  ((horizontalProduct (generalRidgeStripeTwistedFactors w T) +
        verticalOne (generalRidgeStripeTwistedFactors w T)) *
      generalRidgeBoxcar m).coeff q

/-- Fixed target-polynomial perturbation at arbitrary seed width. -/
noncomputable def generalRidgeStripeWidthSeedPerturbation {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m q : ℕ) : ℝ :=
  (generalRidgeTargetPolynomial (generalRidgeExtendedWeights w) *
      generalRidgeBoxcar m).coeff q

/-- Exact arbitrary-width northern decomposition into the scalable nodal
boxcar address. -/
theorem generalRidgeStripeWidthSeedAddressRowZero_eq {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (m q : ℕ) :
    generalRidgeStripeWidthSeedAddressRowZero w T m q =
      -T * (generalRidgeNodalProduct (n + 2) *
        generalRidgeBoxcar m).coeff q := by
  rw [generalRidgeStripeWidthSeedAddressRowZero,
    generalRidgeStripeTwistedFactors_horizontalProduct]
  rw [mul_assoc, coeff_C_mul]

/-- Exact arbitrary-width row-one decomposition into the scalable nodal
boxcar address and the fixed packed-weight perturbation. -/
theorem generalRidgeStripeWidthSeedAddressRowOne_eq {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0) (m q : ℕ) :
    generalRidgeStripeWidthSeedAddressRowOne w T m q =
      -T * (generalRidgeNodalProduct (n + 2) *
          generalRidgeBoxcar m).coeff q +
        generalRidgeStripeWidthSeedPerturbation w m q := by
  rw [generalRidgeStripeWidthSeedAddressRowOne,
    generalRidgeStripeTwistedFactors_horizontalProduct,
    generalRidgeStripeTwistedFactors_verticalOne w T hT]
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul]
  rfl

/-- The earlier width-tied seed addresses are recovered by setting
`m=n+2`. -/
theorem generalRidgeStripeWidthSeedAddress_specializes_row_zero {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ) :
    generalRidgeStripeWidthSeedAddressRowZero w T (n + 2) q =
      generalRidgeStripeSeedAddressRowZero w T q := by
  rfl

/-- Row one likewise specializes definitionally to the original address. -/
theorem generalRidgeStripeWidthSeedAddress_specializes_row_one {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ) :
    generalRidgeStripeWidthSeedAddressRowOne w T (n + 2) q =
      generalRidgeStripeSeedAddressRowOne w T q := by
  rfl

end OneChannelCNNUniversality
