import OneChannelCNNUniversality.SharedBiasGeneralRidgeIdealAddress
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAlgebra

/-!
# Full-chain seed address for the signed stripe schedule

The identity seed produces a unit boxcar in both northern rows.  For a
factor chain with horizontal and vertical-one polynomials `H` and `V`, its
formal propagated address is therefore

\[
  \mathrm{row}_0=H C_m,
  \qquad
  \mathrm{row}_1=(H+V)C_m,
\]

where `m = n + 2` and `C_m = 1 + X + \cdots + X^m`.  For the signed stripe
chain, `H = -T G_m` and `V` is the target polynomial for the zero-extended
weights.  The first term has an arbitrarily scalable unique center minimum;
the second is a fixed finite perturbation.

This file proves a monotone threshold statement: every `T` above one
explicit finite threshold gives a unit gap at the row-one target.  These are
algebraic address statements, not a realization theorem for a genuine ReLU
network.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Northern address obtained by propagating the unit identity-seed boxcar
through the complete twisted factor chain. -/
noncomputable def generalRidgeStripeSeedAddressRowZero {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ) : ℝ :=
  (horizontalProduct (generalRidgeStripeTwistedFactors w T) *
      generalRidgeBoxcar (n + 2)).coeff q

/-- Row-one address obtained from equal unit boxcars in input rows zero and
one. -/
noncomputable def generalRidgeStripeSeedAddressRowOne {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ) : ℝ :=
  ((horizontalProduct (generalRidgeStripeTwistedFactors w T) +
        verticalOne (generalRidgeStripeTwistedFactors w T)) *
      generalRidgeBoxcar (n + 2)).coeff q

/-- Fixed row-one perturbation contributed by the target polynomial. -/
noncomputable def generalRidgeStripeSeedPerturbation {n : ℕ}
    (w : Fin (n + 2) → ℝ) (q : ℕ) : ℝ :=
  (generalRidgeTargetPolynomial (generalRidgeExtendedWeights w) *
      generalRidgeBoxcar (n + 2)).coeff q

/-- Perturbation at the central target column. -/
noncomputable def generalRidgeStripeSeedBTarget {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  generalRidgeStripeSeedPerturbation w (n + 2)

/-- A finite explicit scale threshold dominating every perturbation
difference on the complete output window. -/
noncomputable def generalRidgeStripeSeedAddressThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  1 + ∑ q : Fin (2 * (n + 2) + 1),
    |generalRidgeStripeSeedBTarget w -
      generalRidgeStripeSeedPerturbation w q|

theorem generalRidgeStripeSeedAddressThreshold_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    1 ≤ generalRidgeStripeSeedAddressThreshold w := by
  unfold generalRidgeStripeSeedAddressThreshold
  have hsum : 0 ≤ ∑ q : Fin (2 * (n + 2) + 1),
      |generalRidgeStripeSeedBTarget w -
        generalRidgeStripeSeedPerturbation w q| := by
    exact Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  linarith

/-- Exact northern decomposition into the negative ideal address. -/
theorem generalRidgeStripeSeedAddressRowZero_eq {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (q : ℕ) :
    generalRidgeStripeSeedAddressRowZero w T q =
      -T * generalRidgeIdealAddress (n + 2) q := by
  rw [generalRidgeStripeSeedAddressRowZero,
    generalRidgeStripeTwistedFactors_horizontalProduct]
  rw [mul_assoc, coeff_C_mul]
  rw [generalRidgeIdealAddress_eq_coeff_mul_boxcar]

/-- Exact row-one decomposition into the scalable negative ideal address and
the fixed target-polynomial perturbation. -/
theorem generalRidgeStripeSeedAddressRowOne_eq {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0) (q : ℕ) :
    generalRidgeStripeSeedAddressRowOne w T q =
      -T * generalRidgeIdealAddress (n + 2) q +
        generalRidgeStripeSeedPerturbation w q := by
  rw [generalRidgeStripeSeedAddressRowOne,
    generalRidgeStripeTwistedFactors_horizontalProduct,
    generalRidgeStripeTwistedFactors_verticalOne w T hT]
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul]
  rw [generalRidgeIdealAddress_eq_coeff_mul_boxcar]
  rfl

/-- Every scale above the explicit threshold gives the central row-one site
a unit gap below every other output column. -/
theorem generalRidgeStripeSeedAddress_row_one_gap_of_threshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeSeedAddressThreshold w ≤ T)
    (q : ℕ) (hq : q ≤ 2 * (n + 2)) (hne : q ≠ n + 2) :
    1 ≤ generalRidgeStripeSeedAddressRowOne w T q -
      generalRidgeStripeSeedAddressRowOne w T (n + 2) := by
  have hthreshold := generalRidgeStripeSeedAddressThreshold_one_le w
  have hTone : 1 ≤ T := hthreshold.trans hT
  have hTne : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hTone)
  rw [generalRidgeStripeSeedAddressRowOne_eq w T hTne q,
    generalRidgeStripeSeedAddressRowOne_eq w T hTne (n + 2)]
  let q' : Fin (2 * (n + 2) + 1) := ⟨q, by omega⟩
  have hsingle :
      |generalRidgeStripeSeedBTarget w -
          generalRidgeStripeSeedPerturbation w q| ≤
        ∑ r : Fin (2 * (n + 2) + 1),
          |generalRidgeStripeSeedBTarget w -
            generalRidgeStripeSeedPerturbation w r| := by
    simpa only [q'] using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (2 * (n + 2) + 1))))
        (f := fun r : Fin (2 * (n + 2) + 1) ↦
          |generalRidgeStripeSeedBTarget w -
            generalRidgeStripeSeedPerturbation w r|)
        (fun r _ ↦ abs_nonneg
          (generalRidgeStripeSeedBTarget w -
            generalRidgeStripeSeedPerturbation w r))
        (Finset.mem_univ q'))
  have hdominate :
      1 + generalRidgeStripeSeedBTarget w -
          generalRidgeStripeSeedPerturbation w q ≤ T := by
    have habs : generalRidgeStripeSeedBTarget w -
        generalRidgeStripeSeedPerturbation w q ≤
          |generalRidgeStripeSeedBTarget w -
            generalRidgeStripeSeedPerturbation w q| :=
      le_abs_self _
    unfold generalRidgeStripeSeedAddressThreshold at hT
    linarith
  have hideal := generalRidgeIdealAddress_unit_gap
    (d := n + 2) (q := q) hne
  unfold generalRidgeStripeSeedBTarget at hdominate
  nlinarith

/-- Monotone-threshold existential interface, suitable for taking a later
maximum with an independently chosen proper-prefix threshold. -/
theorem exists_generalRidgeStripeSeedAddressThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T ≥ T₀, ∀ q ≤ 2 * (n + 2), q ≠ n + 2 →
        1 ≤ generalRidgeStripeSeedAddressRowOne w T q -
          generalRidgeStripeSeedAddressRowOne w T (n + 2) := by
  refine ⟨generalRidgeStripeSeedAddressThreshold w,
    generalRidgeStripeSeedAddressThreshold_one_le w, ?_⟩
  intro T hT q hq hne
  exact generalRidgeStripeSeedAddress_row_one_gap_of_threshold
    w T hT q hq hne

/-- At any northern coordinate, the seed address relative to the row-one
target is bounded below by the negative central perturbation. -/
theorem generalRidgeStripeSeedAddress_north_lower_bound {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T) (q : ℕ) :
    -generalRidgeStripeSeedBTarget w ≤
      generalRidgeStripeSeedAddressRowZero w T q -
        generalRidgeStripeSeedAddressRowOne w T (n + 2) := by
  have hTne : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
  rw [generalRidgeStripeSeedAddressRowZero_eq,
    generalRidgeStripeSeedAddressRowOne_eq w T hTne]
  by_cases hq : q = n + 2
  · subst q
    unfold generalRidgeStripeSeedBTarget
    linarith
  · have hideal := generalRidgeIdealAddress_unit_gap
      (d := n + 2) (q := q) hq
    unfold generalRidgeStripeSeedBTarget
    nlinarith

/-- The target perturbation is the evaluation at one of the target
polynomial. -/
theorem generalRidgeStripeSeedBTarget_eq_eval_one {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    generalRidgeStripeSeedBTarget w =
      (generalRidgeTargetPolynomial
        (generalRidgeExtendedWeights w)).eval 1 := by
  let P := generalRidgeTargetPolynomial (generalRidgeExtendedWeights w)
  have hdegree : P.natDegree ≤ n + 2 := by
    unfold P generalRidgeTargetPolynomial
    exact Nat.lt_succ_iff.mp
      (Polynomial.ofFn_natDegree_lt (by omega)
        (fun j ↦ generalRidgeExtendedWeights w (Fin.rev j)))
  have hcoeff := coeff_mul_generalRidgeBoxcar_eq_eval_one P
    (s := n + 2) (N := n + 3) (q := n + 2)
    hdegree le_rfl (by omega)
  simpa [generalRidgeStripeSeedBTarget,
    generalRidgeStripeSeedPerturbation, P] using hcoeff

/-- Appending a zero coordinate leaves the central perturbation equal to the
sum of the original weights. -/
theorem generalRidgeStripeSeedBTarget_eq_sum {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    generalRidgeStripeSeedBTarget w = ∑ j, w j := by
  rw [generalRidgeStripeSeedBTarget_eq_eval_one]
  let w' := generalRidgeExtendedWeights w
  let P := generalRidgeTargetPolynomial w'
  have hdegree : P.natDegree < n + 3 := by
    unfold P generalRidgeTargetPolynomial
    exact Polynomial.ofFn_natDegree_lt (by omega)
      (fun j ↦ w' (Fin.rev j))
  rw [P.eval_eq_sum_range' (n := n + 3) hdegree 1]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [one_pow, mul_one]
  change (∑ j : Fin (n + 3), P.coeff j) = _
  dsimp only [P]
  simp_rw [generalRidgeTargetPolynomial_coeff]
  calc
    (∑ j : Fin (n + 3), w' (Fin.rev j)) = ∑ j, w' j := by
      simpa using (Equiv.sum_comp Fin.revPerm w')
    _ = _ := by
      rw [Fin.sum_univ_castSucc]
      simp [w']

end OneChannelCNNUniversality
