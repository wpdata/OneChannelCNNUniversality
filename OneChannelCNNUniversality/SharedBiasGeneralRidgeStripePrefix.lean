import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAlgebra
import OneChannelCNNUniversality.SharedBiasGeneralRidgeIdealAddress

/-!
# Positive proper prefixes of the signed stripe schedule

The signed stripe twist changes only the lower polynomial of every factor
before the final factor.  Hence every proper horizontal prefix is still the
positive nodal product

\[
  G_k(X)=\prod_{i=1}^{k}(X+i).
\]

In particular, all coefficients of a proper prefix are nonnegative and every
coefficient in its support is at least one.  After multiplication by a
boxcar of width `m + 1`, every coefficient on the complete product support
`0 \le q \le k + m` is still at least one.  On the full-window coordinates
`k \le q \le m`, the coefficient has the exact constant value `(k+1)!`.

These are polynomial facts about the signed factor schedule.  They do not
yet prove that all proper-prefix preactivations of a genuine ReLU network are
nonnegative on a compact signal family.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- The first `k` original ridge factors with the signed stripe's reciprocal
lower scaling.  In the proper range `k < n + 2`, these are exactly the
factors before the negatively scaled final factor. -/
noncomputable def generalRidgeStripeProperPrefix {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (k : ℕ) :
    List BilinearKernelFactor :=
  ((generalRidgeFactorList (generalRidgeExtendedWeights w)
      (generalRidgeStripeAllocation w)).take k).map
    (BilinearKernelFactor.scaleLower (-T⁻¹))

/-- All factors before the final negatively scaled horizontal factor. -/
noncomputable def generalRidgeStripeTwistedProperFactors {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) : List BilinearKernelFactor :=
  generalRidgeStripeProperPrefix w T (n + 1)

@[simp] theorem generalRidgeStripeTwistedProperFactors_length {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    (generalRidgeStripeTwistedProperFactors w T).length = n + 1 := by
  simp [generalRidgeStripeTwistedProperFactors,
    generalRidgeStripeProperPrefix, generalRidgeFactorList_length]

private theorem generalRidgeFactorList_take_horizontalProduct
    {d k : ℕ} (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hk : k ≤ d) :
    horizontalProduct ((generalRidgeFactorList w η).take k) =
      generalRidgeNodalProduct k := by
  rw [generalRidgeFactorList, ← Fin.ofFn_take_eq_take_ofFn hk]
  rw [horizontalProduct, List.map_ofFn, List.prod_ofFn,
    generalRidgeNodalProduct]
  apply Finset.prod_congr rfl
  intro i hi
  simp [Fin.take, generalRidgeKernelFactor, BilinearKernelFactor.A,
    linearPolynomial, generalRidgeNodalFactor]
  ring

private theorem generalRidgeFactorList_take_before_last
    {n : ℕ} (w : Fin (n + 3) → ℝ) (η : Fin (n + 2) → ℝ) :
    (generalRidgeFactorList w η).take (n + 1) =
      generalRidgeFactorPrefix (d := n + 2) (by omega) w η ++
        [generalRidgeKernelFactor w η
          (generalRidgePenultimateIndex (d := n + 2) (by omega))] := by
  rw [generalRidgeFactorList_split_last_two]
  rw [List.take_append]
  have hlength :
      (generalRidgeFactorPrefix (d := n + 2) (by omega) w η).length = n := by
    simp [generalRidgeFactorPrefix_length]
  rw [List.take_of_length_le (by omega), hlength]
  simp

/-- In the proper range, the explicit prefix above is literally the first
`k` factors of the complete twisted factor list. -/
theorem generalRidgeStripeProperPrefix_eq_take_twistedFactors
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hk : k < n + 2) :
    generalRidgeStripeProperPrefix w T k =
      (generalRidgeStripeTwistedFactors w T).take k := by
  let w' := generalRidgeExtendedWeights w
  let η := generalRidgeStripeAllocation w
  let c := BilinearKernelFactor.scaleLower (-T⁻¹)
  have hk' : k ≤ n + 1 := by omega
  change ((generalRidgeFactorList w' η).take k).map c =
    ((generalRidgeFactorPrefix (d := n + 2) (by omega) w' η ++
        [generalRidgeKernelFactor w' η
          (generalRidgePenultimateIndex (d := n + 2) (by omega))]).map c ++
      [BilinearKernelFactor.scaleHorizontal (-T)
        (generalRidgeStripeLastFactor w)]).take k
  rw [← generalRidgeFactorList_take_before_last w' η]
  have hlength :
      (((generalRidgeFactorList w' η).take (n + 1)).map c).length =
        n + 1 := by
    rw [List.length_map, List.length_take_of_le]
    simp
  rw [List.take_append_of_le_length (by omega)]
  rw [← List.map_take, List.take_take, min_eq_left hk']

/-- The complete proper factor block is the length-`n+1` prefix of the
twisted schedule. -/
theorem generalRidgeStripeTwistedProperFactors_eq_take {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeTwistedProperFactors w T =
      (generalRidgeStripeTwistedFactors w T).take (n + 1) := by
  exact generalRidgeStripeProperPrefix_eq_take_twistedFactors
    w T (by omega)

/-- Every proper prefix of the signed stripe has the same horizontal product
as the first `k` positive nodal factors.  The statement is independent of the
ridge weights and of the reciprocal scale `T`. -/
theorem generalRidgeStripeProperPrefix_horizontalProduct
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hk : k < n + 2) :
    horizontalProduct (generalRidgeStripeProperPrefix w T k) =
      generalRidgeNodalProduct k := by
  rw [generalRidgeStripeProperPrefix, horizontalProduct_map_scaleLower]
  exact generalRidgeFactorList_take_horizontalProduct _ _ (by omega)

/-- Equivalent direct form: taking any proper prefix of the complete twisted
factor list yields the positive nodal product. -/
theorem generalRidgeStripeTwistedFactors_take_horizontalProduct
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hk : k < n + 2) :
    horizontalProduct ((generalRidgeStripeTwistedFactors w T).take k) =
      generalRidgeNodalProduct k := by
  rw [← generalRidgeStripeProperPrefix_eq_take_twistedFactors w T hk]
  exact generalRidgeStripeProperPrefix_horizontalProduct w T hk

/-- Every coefficient of a proper signed-stripe horizontal prefix is
nonnegative. -/
theorem generalRidgeStripeProperPrefix_coeff_nonneg
    {n k : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ) (hk : k < n + 2)
    (q : ℕ) :
    0 ≤ (horizontalProduct
      (generalRidgeStripeProperPrefix w T k)).coeff q := by
  rw [generalRidgeStripeProperPrefix_horizontalProduct w T hk]
  exact generalRidgeNodalProduct_coeff_nonneg k q

/-- Every coefficient in the full support of a proper signed-stripe
horizontal prefix is at least one. -/
theorem generalRidgeStripeProperPrefix_coeff_one_le
    {n k q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (hq : q ≤ k) :
    1 ≤ (horizontalProduct
      (generalRidgeStripeProperPrefix w T k)).coeff q := by
  rw [generalRidgeStripeProperPrefix_horizontalProduct w T hk]
  exact generalRidgeNodalProduct_coeff_one_le hq

/-- At one, the `k`-factor nodal product is exactly `(k+1)!`. -/
theorem generalRidgeNodalProduct_eval_one (k : ℕ) :
    (generalRidgeNodalProduct k).eval 1 =
      (Nat.factorial (k + 1) : ℝ) := by
  induction k with
  | zero => simp [generalRidgeNodalProduct]
  | succ k ih =>
      rw [generalRidgeNodalProduct_succ, eval_mul, ih]
      simp [Nat.factorial_succ]
      ring

/-- Every coefficient on the complete support `0 ≤ q ≤ k+m` of a
`k`-factor nodal product times a width-`m+1` boxcar is at least one.  The
proof selects the convolution contribution at index `min q k`; all remaining
contributions are nonnegative. -/
theorem generalRidgeNodalProduct_mul_boxcar_coeff_one_le
    (k m q : ℕ) (hq : q ≤ k + m) :
    1 ≤ (generalRidgeNodalProduct k * generalRidgeBoxcar m).coeff q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [generalRidgeBoxcar_coeff]
  let i := min q k
  have hiq : i ≤ q := min_le_left q k
  have hik : i ≤ k := min_le_right q k
  have hi_mem : i ∈ Finset.range (q + 1) := by
    simp
    omega
  have hwindow : q - i ≤ m := by
    dsimp [i]
    omega
  have hterm :
      1 ≤ (generalRidgeNodalProduct k).coeff i *
        (if q - i ≤ m then 1 else 0) := by
    rw [if_pos hwindow, mul_one]
    exact generalRidgeNodalProduct_coeff_one_le hik
  calc
    1 ≤ (generalRidgeNodalProduct k).coeff i *
        (if q - i ≤ m then 1 else 0) := hterm
    _ ≤ ∑ j ∈ Finset.range (q + 1),
          (generalRidgeNodalProduct k).coeff j *
            (if q - j ≤ m then 1 else 0) := by
      exact Finset.single_le_sum
        (s := Finset.range (q + 1))
        (f := fun j ↦ (generalRidgeNodalProduct k).coeff j *
          (if q - j ≤ m then 1 else 0))
        (by
          intro j hj
          split_ifs <;> simp [generalRidgeNodalProduct_coeff_nonneg])
        hi_mem

/-- The same complete-support lower bound for every proper prefix of the
signed stripe schedule. -/
theorem generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_one_le
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (hq : q ≤ k + m) :
    1 ≤ ((horizontalProduct
      (generalRidgeStripeProperPrefix w T k)) *
        generalRidgeBoxcar m).coeff q := by
  rw [generalRidgeStripeProperPrefix_horizontalProduct w T hk]
  exact generalRidgeNodalProduct_mul_boxcar_coeff_one_le k m q hq

/-- Hence every coefficient on the complete support is strictly positive. -/
theorem generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_pos
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (hq : q ≤ k + m) :
    0 < ((horizontalProduct
      (generalRidgeStripeProperPrefix w T k)) *
        generalRidgeBoxcar m).coeff q :=
  lt_of_lt_of_le zero_lt_one
    (generalRidgeStripeProperPrefix_boxcar_fullSupport_coeff_one_le
      w T hk hq)

/-- A boxcar of width `m+1` sees the complete support of a `k`-factor proper
prefix at every coordinate `k ≤ q ≤ m`.  The resulting coefficient is
the explicit positive constant `(k+1)!`. -/
theorem generalRidgeStripeProperPrefix_boxcar_coeff_eq_factorial
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (hkq : k ≤ q) (hqm : q ≤ m) :
    ((horizontalProduct (generalRidgeStripeProperPrefix w T k)) *
        generalRidgeBoxcar m).coeff q =
      (Nat.factorial (k + 1) : ℝ) := by
  rw [generalRidgeStripeProperPrefix_horizontalProduct w T hk]
  calc
    (generalRidgeNodalProduct k * generalRidgeBoxcar m).coeff q =
        (generalRidgeNodalProduct k).eval 1 := by
      simpa using
        (coeff_mul_generalRidgeBoxcar_eq_eval_one
          (generalRidgeNodalProduct k) (s := k) (N := m + 1) (q := q)
          (by rw [generalRidgeNodalProduct_natDegree]) hkq (by omega))
    _ = (Nat.factorial (k + 1) : ℝ) :=
      generalRidgeNodalProduct_eval_one k

/-- Consequently, every full-window boxcar coefficient of a proper prefix is
at least one. -/
theorem generalRidgeStripeProperPrefix_boxcar_coeff_one_le
    {n k m q : ℕ} (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hk : k < n + 2) (hkq : k ≤ q) (hqm : q ≤ m) :
    1 ≤ ((horizontalProduct
      (generalRidgeStripeProperPrefix w T k)) *
        generalRidgeBoxcar m).coeff q := by
  rw [generalRidgeStripeProperPrefix_boxcar_coeff_eq_factorial
    w T hk hkq hqm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))

end OneChannelCNNUniversality
