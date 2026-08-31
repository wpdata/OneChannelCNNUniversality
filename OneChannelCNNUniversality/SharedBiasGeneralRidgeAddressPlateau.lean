import OneChannelCNNUniversality.SharedBiasGeneralRidgeIdealAddress

/-!
# The common plateau of linear shared-bias carrier directions

This module studies an abstract polynomial carrier model for a depth-`L`
expansive computation starting from width `m`.  Its hypotheses posit that the
direction associated with the bias inserted at layer `k+1` has the form

\[
  [X^q]\,Q_k(X)(1+X+\cdots+X^{m+k}),
  \qquad \deg Q_k\le L-k-1.
\]

Every such direction is constant on the common interval
`L - 1 ≤ q ≤ m`.  Hence every real linear combination of the bias directions,
including a final shared scalar bias, is constant there as well.

This is a sharp obstruction inside the stated *polynomial linear-carrier
model*.  No theorem in this module derives that representation from every
genuine shared-bias ReLU CNN, and a genuinely nonlinear intermediate mask may
escape the hypothesis.  It is therefore not an architecture-wide depth lower
bound.
-/

namespace OneChannelCNNUniversality

open scoped BigOperators Polynomial
open Polynomial

/-- Address direction produced by the bias of layer `k+1`. -/
noncomputable def linearBiasAddressDirection
    (m L : ℕ) (Q : Fin L → ℝ[X]) (k : Fin L) (q : ℕ) : ℝ :=
  (Q k * generalRidgeBoxcar (m + (k : ℕ))).coeff q

/-- An arbitrary real linear combination of all propagated bias directions,
plus the final spatially constant bias. -/
noncomputable def linearBiasAddress
    (m L : ℕ) (Q : Fin L → ℝ[X])
    (scale : Fin L → ℝ) (finalBias : ℝ) (q : ℕ) : ℝ :=
  (∑ k : Fin L, scale k * linearBiasAddressDirection m L Q k q) + finalBias

/-- Each individual bias direction equals `Q_k(1)` throughout the common
core interval. -/
theorem linearBiasAddressDirection_eq_eval_one_on_core
    {m L : ℕ} (Q : Fin L → ℝ[X])
    (hdegree : ∀ k, (Q k).natDegree ≤ L - ((k : ℕ) + 1))
    (k : Fin L) {q : ℕ} (hleft : L - 1 ≤ q) (hright : q ≤ m) :
    linearBiasAddressDirection m L Q k q = (Q k).eval 1 := by
  have hsuffix : L - ((k : ℕ) + 1) ≤ q := by
    have hk : (k : ℕ) < L := k.isLt
    omega
  have hwidth : q < m + (k : ℕ) + 1 := by omega
  have hflat := coeff_mul_generalRidgeBoxcar_eq_eval_one
    (Q k) (hdegree k) hsuffix hwidth
  simpa [linearBiasAddressDirection, Nat.add_assoc] using hflat

/-- Every linear combination of propagated scalar-bias directions is flat on
the same core interval. -/
theorem linearBiasAddress_flat_on_core
    {m L : ℕ} (Q : Fin L → ℝ[X])
    (hdegree : ∀ k, (Q k).natDegree ≤ L - ((k : ℕ) + 1))
    (scale : Fin L → ℝ) (finalBias : ℝ) {q r : ℕ}
    (hqleft : L - 1 ≤ q) (hqright : q ≤ m)
    (hrleft : L - 1 ≤ r) (hrright : r ≤ m) :
    linearBiasAddress m L Q scale finalBias q =
      linearBiasAddress m L Q scale finalBias r := by
  unfold linearBiasAddress
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [linearBiasAddressDirection_eq_eval_one_on_core Q hdegree k
      hqleft hqright,
    linearBiasAddressDirection_eq_eval_one_on_core Q hdegree k
      hrleft hrright]

/-- If `L ≤ m` and a target coordinate can see all `m` inputs
(`m-1 ≤ q ≤ L`), another distinct coordinate lies in the common bias-address
plateau. -/
theorem exists_competing_linearBiasAddress_core_coordinate
    {m L q : ℕ} (hm : 2 ≤ m) (_hlower : m - 1 ≤ L) (hupper : L ≤ m)
    (hqleft : m - 1 ≤ q) (hqright : q ≤ L) :
    ∃ q' ≠ q, L - 1 ≤ q' ∧ q' ≤ m := by
  by_cases hqm : q = m
  · refine ⟨m - 1, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · refine ⟨m, Ne.symm hqm, ?_, le_rfl⟩
    omega

/-- Consequently, no address assembled only from linearly propagated shared
biases can uniquely distinguish a full-input target when `L ≤ m`. -/
theorem exists_competing_linearBiasAddress_coordinate
    {m L q : ℕ} (hm : 2 ≤ m) (hlower : m - 1 ≤ L) (hupper : L ≤ m)
    (hqleft : m - 1 ≤ q) (hqright : q ≤ L)
    (Q : Fin L → ℝ[X])
    (hdegree : ∀ k, (Q k).natDegree ≤ L - ((k : ℕ) + 1))
    (scale : Fin L → ℝ) (finalBias : ℝ) :
    ∃ q' ≠ q,
      linearBiasAddress m L Q scale finalBias q' =
        linearBiasAddress m L Q scale finalBias q := by
  obtain ⟨q', hne, hq'left, hq'right⟩ :=
    exists_competing_linearBiasAddress_core_coordinate
      hm hlower hupper hqleft hqright
  refine ⟨q', hne, ?_⟩
  apply linearBiasAddress_flat_on_core Q hdegree scale finalBias
  · exact hq'left
  · exact hq'right
  · omega
  · exact hqright.trans hupper

/-- With two extra layers, `L=m+1`, the former common plateau
`L-1 ≤ q ≤ m` has shrunk to the singleton `{m}`. -/
theorem linearBiasAddress_core_singleton_at_two_extra_layers
    {m q : ℕ} (hleft : m + 1 - 1 ≤ q) (hright : q ≤ m) :
    q = m := by
  omega

end OneChannelCNNUniversality
