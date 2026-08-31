import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeMinMax

/-!
# Exact affine-plus-ridge readouts from the completed signed stripe

The completed signed-stripe network exposes both one arbitrary affine ReLU
ridge and exact affine access to its original input.  A single ordinary
finite affine readout therefore realizes every function of the form

\[
  \lambda\,\mathrm{ReLU}\!\left(\sum_j w_jx_j+\theta\right)
    +\sum_j a_jx_j+\alpha.
\]

This is the exact one-hidden-unit ReLU class with an affine skip term.  The
complete output state remains injective on compact injective input families.
-/

namespace OneChannelCNNUniversality

open Set

/-- Linear part of an affine readout combining recovered input-affine data
with a scalar multiple of the protected ridge coordinate. -/
noncomputable def generalRidgeStripeAffineRidgeLinearMap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (a : Fin (n + 2) → ℝ)
    (lambda : ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) →ₗ[ℝ] ℝ :=
  generalRidgeStripeAffineRecoveryLinearMap w T a +
    lambda • generalRidgeStripeTargetLinearMap n

/-- Ordinary finite output weights for an affine term plus a scalar multiple
of the protected ridge. -/
noncomputable def generalRidgeStripeAffineRidgeReadoutWeight {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (a : Fin (n + 2) → ℝ)
    (lambda : ℝ) : Image (n + 4) (2 * (n + 2) + 1) :=
  linearReadoutWeights
    (generalRidgeStripeAffineRidgeLinearMap w T a lambda)

/-- One genuine completed signed-stripe network, followed by one ordinary
finite affine readout, exactly realizes an arbitrary affine function plus a
scalar multiple of an arbitrary affine ReLU ridge.  The hidden state remains
injective on the compact input family. -/
theorem exists_generalRidgeStripeAffineRidgeReadout_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (w : Fin (n + 2) → ℝ) (theta : ℝ)
    (a : Fin (n + 2) → ℝ) (alpha lambda : ℝ) :
    ∃ (T c t : ℝ)
      (weight : Image (n + 4) (2 * (n + 2) + 1))
      (constant : ℝ),
      1 ≤ T ∧ 0 < c ∧ 0 < t ∧
      (generalRidgeStripeNetwork w T c t theta).net.depth = n + 3 ∧
      (∀ x ∈ K,
        (∑ p, ∑ q, weight p q *
            (generalRidgeStripeNetwork w T c t theta).eval (F x) p q) +
            constant =
          lambda * relu ((∑ j, w j * F x 0 j) + theta) +
            (∑ j, a j * F x 0 j) + alpha) ∧
      Set.InjOn
        (fun x ↦ (generalRidgeStripeNetwork w T c t theta).eval (F x)) K := by
  obtain ⟨T, c, t, hT, hc, ht, hdepth, hbehavior, hinjective⟩ :=
    exists_injective_generalRidgeStripeNetwork_on_compact
      hK F hF hFinjective w theta
  let weight := generalRidgeStripeAffineRidgeReadoutWeight w T a lambda
  let constant :=
    generalRidgeStripeAffineReadoutConstant w T c t theta a alpha
  refine ⟨T, c, t, weight, constant, hT, hc, ht, hdepth, ?_, hinjective⟩
  intro x hx
  let z := (generalRidgeStripeNetwork w T c t theta).eval (F x)
  have hnorth : ∀ q : Fin (2 * (n + 2) + 1),
      z ⟨0, by omega⟩ q =
        generalRidgeStripeVariableNorthLinearMap w T (F x) q +
          generalRidgeStripeNorthOffset w T c t theta q := by
    intro q
    exact generalRidgeStripeNetwork_row_zero_eq_code_add_offset
      w T c t theta (F x) (hbehavior x hx) q
  have hrecover := generalRidgeStripeAffineReadout_spec
    w T c t theta (ne_of_gt (zero_lt_one.trans_le hT))
    a alpha z (F x) hnorth
  have hrecover' :
      generalRidgeStripeAffineRecoveryLinearMap w T a z + constant =
        (∑ j, a j * F x 0 j) + alpha := by
    simpa [generalRidgeStripeAffineReadoutWeight, constant,
      linearReadoutWeights_apply] using hrecover
  have htarget : generalRidgeStripeTargetLinearMap n z =
      relu ((∑ j, w j * F x 0 j) + theta) := by
    have htgt := hbehavior x hx
      (generalRidgeStripeTarget n).1
      (generalRidgeStripeTarget n).2
      (by simp [generalRidgeStripeTarget])
    simpa [generalRidgeStripeTargetLinearMap, z] using htgt
  change
    (∑ p, ∑ q,
      generalRidgeStripeAffineRidgeReadoutWeight w T a lambda p q * z p q) +
        constant = _
  rw [generalRidgeStripeAffineRidgeReadoutWeight,
    linearReadoutWeights_apply]
  simp only [generalRidgeStripeAffineRidgeLinearMap,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [htarget]
  linarith

end OneChannelCNNUniversality
