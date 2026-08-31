import OneChannelCNNUniversality.SharedBiasGeneralRidgePolynomial

/-!
# An ideal boxcar address for arbitrary-width ridge factors

Let

\[
  G_d(X)=\prod_{i=1}^{d}(X+i),
  \qquad C_d(X)=1+X+\cdots+X^d.
\]

Every coefficient of `G_d` between degrees zero and `d` is at least one.
Consequently, the coefficient of `G_d C_d` at degree `d` contains every
coefficient of `G_d`, whereas every other coefficient misses at least one of
them.  The central coefficient is therefore the unique maximum, with gap at
least one.

This is an algebraic address theorem.  It does not assert that a shared-bias
CNN has already generated the boxcar carrier internally.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Add the last nodal factor to the arbitrary-width product. -/
theorem generalRidgeNodalProduct_succ (d : ℕ) :
    generalRidgeNodalProduct (d + 1) =
      generalRidgeNodalProduct d * (X + C ((d + 1 : ℕ) : ℝ)) := by
  classical
  simp [generalRidgeNodalProduct, generalRidgeNodalFactor,
    Fin.prod_univ_castSucc]

private theorem generalRidgeNodalProduct_coeff_zero_succ (d : ℕ) :
    (generalRidgeNodalProduct (d + 1)).coeff 0 =
      (generalRidgeNodalProduct d).coeff 0 * (d + 1 : ℝ) := by
  rw [generalRidgeNodalProduct_succ, mul_add, coeff_add,
    coeff_mul_X_zero, coeff_mul_C]
  simp

private theorem generalRidgeNodalProduct_coeff_succ (d q : ℕ) :
    (generalRidgeNodalProduct (d + 1)).coeff (q + 1) =
      (generalRidgeNodalProduct d).coeff q +
        (generalRidgeNodalProduct d).coeff (q + 1) * (d + 1 : ℝ) := by
  rw [generalRidgeNodalProduct_succ, mul_add, coeff_add,
    coeff_mul_X, coeff_mul_C]
  norm_num

/-- Every coefficient of the nodal product is nonnegative. -/
theorem generalRidgeNodalProduct_coeff_nonneg (d q : ℕ) :
    0 ≤ (generalRidgeNodalProduct d).coeff q := by
  induction d generalizing q with
  | zero =>
      change 0 ≤ (1 : ℝ[X]).coeff q
      rw [coeff_one]
      split_ifs <;> norm_num
  | succ d ih =>
      rcases q with _ | q
      · rw [generalRidgeNodalProduct_coeff_zero_succ]
        have hcoeff := ih 0
        positivity
      · rw [generalRidgeNodalProduct_coeff_succ]
        have hcoeff := ih q
        have hcoeff' := ih (q + 1)
        positivity

/-- Every coefficient inside the full support of the nodal product is at
least one. -/
theorem generalRidgeNodalProduct_coeff_one_le {d q : ℕ} (hq : q ≤ d) :
    1 ≤ (generalRidgeNodalProduct d).coeff q := by
  induction d generalizing q with
  | zero =>
      have hq0 : q = 0 := by omega
      subst q
      simp [generalRidgeNodalProduct]
  | succ d ih =>
      by_cases htop : q = d + 1
      · subst q
        rw [generalRidgeNodalProduct_coeff_succ]
        have hzero : (generalRidgeNodalProduct d).coeff (d + 1) = 0 := by
          exact coeff_eq_zero_of_natDegree_lt (by
            rw [generalRidgeNodalProduct_natDegree]
            omega)
        rw [hzero]
        simpa using ih (q := d) (by omega)
      · have hqd : q ≤ d := by omega
        rcases q with _ | q
        · rw [generalRidgeNodalProduct_coeff_zero_succ]
          have hone := ih (q := 0) (by omega)
          have hfactor : (1 : ℝ) ≤ (d + 1 : ℕ) := by
            exact_mod_cast Nat.succ_pos d
          nlinarith
        · rw [generalRidgeNodalProduct_coeff_succ]
          have hone := ih (q := q + 1) (by omega)
          have hfactor : (1 : ℝ) ≤ (d + 1 : ℕ) := by
            exact_mod_cast Nat.succ_pos d
          have hnonneg := generalRidgeNodalProduct_coeff_nonneg d q
          nlinarith

/-- The length-`d+1` boxcar polynomial `1 + X + ... + X^d`. -/
noncomputable def generalRidgeBoxcar (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1), X ^ j

@[simp] theorem generalRidgeBoxcar_coeff (d q : ℕ) :
    (generalRidgeBoxcar d).coeff q = if q ≤ d then 1 else 0 := by
  classical
  simp [generalRidgeBoxcar, Finset.mem_range]

/-- Convolution with a sufficiently long boxcar is flat wherever its window
contains the complete support of the other polynomial. -/
theorem coeff_mul_generalRidgeBoxcar_eq_eval_one
    (Q : ℝ[X]) {s N q : ℕ}
    (hdegree : Q.natDegree ≤ s) (hsq : s ≤ q) (hqN : q < N) :
    (Q * generalRidgeBoxcar (N - 1)).coeff q = Q.eval 1 := by
  classical
  have hN : 0 < N := by omega
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [generalRidgeBoxcar_coeff]
  rw [Q.eval_eq_sum_range' (n := q + 1) (by omega) 1]
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hwindow : q - k ≤ N - 1 := by omega
  rw [if_pos hwindow]
  simp

/-- Indices of `G_d` that contribute to coefficient `q` of `G_d C_d`. -/
def generalRidgeIdealActiveSet (d q : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter fun k ↦ k ≤ q ∧ q - k ≤ d

/-- The ideal boxcar address at output coordinate `q`. -/
noncomputable def generalRidgeIdealAddress (d q : ℕ) : ℝ :=
  ∑ k ∈ generalRidgeIdealActiveSet d q,
    (generalRidgeNodalProduct d).coeff k

private theorem generalRidgeIdealActiveSet_mem_iff {d q k : ℕ} :
    k ∈ generalRidgeIdealActiveSet d q ↔
      k ≤ d ∧ k ≤ q ∧ q - k ≤ d := by
  simp [generalRidgeIdealActiveSet]

/-- At the center, every index in the block is active. -/
@[simp] theorem generalRidgeIdealActiveSet_center (d : ℕ) :
    generalRidgeIdealActiveSet d d = Finset.range (d + 1) := by
  ext k
  simp [generalRidgeIdealActiveSet]

private theorem generalRidgeIdealActiveSet_subset (d q : ℕ) :
    generalRidgeIdealActiveSet d q ⊆ Finset.range (d + 1) := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

/-- Window sum for an arbitrary polynomial over the ideal active set. -/
noncomputable def generalRidgeBlockAddress (Q : ℝ[X]) (d q : ℕ) : ℝ :=
  ∑ k ∈ generalRidgeIdealActiveSet d q, Q.coeff k

@[simp] theorem generalRidgeBlockAddress_center (Q : ℝ[X]) (d : ℕ) :
    generalRidgeBlockAddress Q d d =
      ∑ k ∈ Finset.range (d + 1), Q.coeff k := by
  simp [generalRidgeBlockAddress]

/-- If `Q` has degree at most `d`, its boxcar-product coefficient is exactly
the corresponding block address. -/
theorem generalRidgeBlockAddress_eq_coeff_mul_boxcar
    (Q : ℝ[X]) {d q : ℕ} (hdegree : Q.natDegree ≤ d) :
    generalRidgeBlockAddress Q d q =
      (Q * generalRidgeBoxcar d).coeff q := by
  classical
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [generalRidgeBoxcar_coeff, mul_ite, mul_one, mul_zero]
  rw [generalRidgeBlockAddress, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro k hk
    rcases generalRidgeIdealActiveSet_mem_iff.mp hk with
      ⟨hkd, hkq, hwindow⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hwindow⟩
  · intro k hkq hkideal
    have hkq' : k ≤ q := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hkq).1)
    have hwindow : q - k ≤ d := (Finset.mem_filter.mp hkq).2
    have hkd : d < k := by
      by_contra hnotlt
      exact hkideal (generalRidgeIdealActiveSet_mem_iff.mpr
        ⟨Nat.le_of_not_gt hnotlt, hkq', hwindow⟩)
    exact coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt hkd)

private theorem generalRidgeBlockAddress_le_center_minus_missing
    (Q : ℝ[X]) {d q missing : ℕ}
    (hnonneg : ∀ k ≤ d, 0 ≤ Q.coeff k)
    (hmissing : missing ∈ Finset.range (d + 1))
    (hnot : missing ∉ generalRidgeIdealActiveSet d q) :
    generalRidgeBlockAddress Q d q + Q.coeff missing ≤
      generalRidgeBlockAddress Q d d := by
  rw [generalRidgeBlockAddress_center, generalRidgeBlockAddress]
  have hdisjoint : Disjoint (generalRidgeIdealActiveSet d q) {missing} := by
    simp [Finset.disjoint_singleton_right, hnot]
  have hsingle :
      (∑ k ∈ ({missing} : Finset ℕ), Q.coeff k) = Q.coeff missing := by
    simp
  rw [← hsingle, ← Finset.sum_union hdisjoint]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact generalRidgeIdealActiveSet_subset d q hk
    · have hkEq : k = missing := Finset.mem_singleton.mp hk
      subst k
      exact hmissing
  · intro k hk houtside
    apply hnonneg k
    have hklt := Finset.mem_range.mp hk
    omega

/-- If all coefficients of `Q` in its block are at least one, the center is
the unique maximum with unit gap. -/
theorem generalRidgePositiveBlockAddress_unit_gap
    (Q : ℝ[X]) {d q : ℕ}
    (hcoeff : ∀ k ≤ d, 1 ≤ Q.coeff k) (hq : q ≠ d) :
    1 ≤ generalRidgeBlockAddress Q d d -
      generalRidgeBlockAddress Q d q := by
  have hnonneg : ∀ k ≤ d, 0 ≤ Q.coeff k := by
    intro k hk
    exact le_trans (by norm_num) (hcoeff k hk)
  by_cases hleft : q < d
  · have hmissing : d ∈ Finset.range (d + 1) := by simp
    have hnot : d ∉ generalRidgeIdealActiveSet d q := by
      simp [generalRidgeIdealActiveSet]
      omega
    have hsum := generalRidgeBlockAddress_le_center_minus_missing Q
      hnonneg hmissing hnot
    have hone := hcoeff d le_rfl
    linarith
  · have hright : d < q := by omega
    have hmissing : 0 ∈ Finset.range (d + 1) := by simp
    have hnot : 0 ∉ generalRidgeIdealActiveSet d q := by
      simp [generalRidgeIdealActiveSet]
      omega
    have hsum := generalRidgeBlockAddress_le_center_minus_missing Q
      hnonneg hmissing hnot
    have hone := hcoeff 0 (by omega)
    linarith

@[simp] private theorem generalRidgeBlockAddress_neg
    (Q : ℝ[X]) (d q : ℕ) :
    generalRidgeBlockAddress (-Q) d q =
      -generalRidgeBlockAddress Q d q := by
  simp [generalRidgeBlockAddress, ← Finset.sum_neg_distrib]

/-- If all coefficients of `Q` in the block are at most `-1`, the center is
the unique minimum with unit gap. -/
theorem generalRidgeNegativeBlockAddress_unit_gap
    (Q : ℝ[X]) {d q : ℕ}
    (hcoeff : ∀ k ≤ d, Q.coeff k ≤ -1) (hq : q ≠ d) :
    1 ≤ generalRidgeBlockAddress Q d q -
      generalRidgeBlockAddress Q d d := by
  have hpositive : ∀ k ≤ d, 1 ≤ (-Q).coeff k := by
    intro k hk
    rw [coeff_neg]
    linarith [hcoeff k hk]
  have hgap := generalRidgePositiveBlockAddress_unit_gap (-Q) hpositive hq
  simp only [generalRidgeBlockAddress_neg] at hgap
  linarith

/-- The explicit window sum is exactly the corresponding coefficient of the
nodal product times the boxcar polynomial. -/
theorem generalRidgeIdealAddress_eq_coeff_mul_boxcar (d q : ℕ) :
    generalRidgeIdealAddress d q =
      (generalRidgeNodalProduct d * generalRidgeBoxcar d).coeff q := by
  classical
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [generalRidgeBoxcar_coeff]
  rw [generalRidgeIdealAddress]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro k hk
    rcases generalRidgeIdealActiveSet_mem_iff.mp hk with
      ⟨hkd, hkq, hwindow⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hwindow⟩
  · intro k hkq hkideal
    have hkq' : k ≤ q := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hkq).1)
    have hwindow : q - k ≤ d := (Finset.mem_filter.mp hkq).2
    have hkd : d < k := by
      by_contra hnotlt
      exact hkideal (generalRidgeIdealActiveSet_mem_iff.mpr
        ⟨Nat.le_of_not_gt hnotlt, hkq', hwindow⟩)
    have hcoeff : (generalRidgeNodalProduct d).coeff k = 0 := by
      exact coeff_eq_zero_of_natDegree_lt (by
        rw [generalRidgeNodalProduct_natDegree]
        omega)
    exact hcoeff

/-- Exact central address as the sum of all nodal-product coefficients. -/
theorem generalRidgeIdealAddress_center (d : ℕ) :
    generalRidgeIdealAddress d d =
      ∑ k ∈ Finset.range (d + 1),
        (generalRidgeNodalProduct d).coeff k := by
  simp [generalRidgeIdealAddress]

private theorem generalRidgeIdealAddress_le_center_minus_missing
    {d q missing : ℕ}
    (hmissing : missing ∈ Finset.range (d + 1))
    (hnot : missing ∉ generalRidgeIdealActiveSet d q) :
    generalRidgeIdealAddress d q +
        (generalRidgeNodalProduct d).coeff missing ≤
      generalRidgeIdealAddress d d := by
  rw [generalRidgeIdealAddress_center, generalRidgeIdealAddress]
  have hdisjoint : Disjoint (generalRidgeIdealActiveSet d q) {missing} := by
    simp [Finset.disjoint_singleton_right, hnot]
  have hsingle :
      (∑ k ∈ ({missing} : Finset ℕ),
        (generalRidgeNodalProduct d).coeff k) =
      (generalRidgeNodalProduct d).coeff missing := by simp
  rw [← hsingle]
  rw [← Finset.sum_union hdisjoint]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact generalRidgeIdealActiveSet_subset d q hk
    · have hkEq : k = missing := Finset.mem_singleton.mp hk
      subst k
      exact hmissing
  · intro k hk houtside
    exact generalRidgeNodalProduct_coeff_nonneg d k

/-- Every noncentral coordinate misses a coefficient of size at least one,
so the central address has a unit gap. -/
theorem generalRidgeIdealAddress_unit_gap {d q : ℕ} (hq : q ≠ d) :
    1 ≤ generalRidgeIdealAddress d d - generalRidgeIdealAddress d q := by
  by_cases hleft : q < d
  · have hmissing : d ∈ Finset.range (d + 1) := by simp
    have hnot : d ∉ generalRidgeIdealActiveSet d q := by
      simp [generalRidgeIdealActiveSet]
      omega
    have hsum := generalRidgeIdealAddress_le_center_minus_missing
      hmissing hnot
    have hone := generalRidgeNodalProduct_coeff_one_le (d := d) (q := d) le_rfl
    linarith
  · have hright : d < q := by omega
    have hmissing : 0 ∈ Finset.range (d + 1) := by simp
    have hnot : 0 ∉ generalRidgeIdealActiveSet d q := by
      simp [generalRidgeIdealActiveSet]
      omega
    have hsum := generalRidgeIdealAddress_le_center_minus_missing
      hmissing hnot
    have hone := generalRidgeNodalProduct_coeff_one_le (d := d) (q := 0) (by omega)
    linarith

/-- The boxcar product has a unique maximum coefficient at degree `d`. -/
theorem generalRidgeIdealAddress_unique_max (d : ℕ) :
    ∀ q, generalRidgeIdealAddress d d ≤ generalRidgeIdealAddress d q → q = d := by
  intro q hq
  by_contra hne
  have hgap := generalRidgeIdealAddress_unit_gap hne
  linarith

/-- Negating the boxcar address turns the unique central maximum into the
unique central minimum, with the same unit gap. -/
theorem generalRidgeIdealNegativeAddress_unit_gap {d q : ℕ} (hq : q ≠ d) :
    1 ≤ -generalRidgeIdealAddress d q -
      (-generalRidgeIdealAddress d d) := by
  have hgap := generalRidgeIdealAddress_unit_gap hq
  linarith

/-- The negated boxcar product has its unique minimum at degree `d`. -/
theorem generalRidgeIdealNegativeAddress_unique_min (d : ℕ) :
    ∀ q, -generalRidgeIdealAddress d q ≤
        -generalRidgeIdealAddress d d → q = d := by
  intro q hq
  apply generalRidgeIdealAddress_unique_max d q
  linarith

end OneChannelCNNUniversality
