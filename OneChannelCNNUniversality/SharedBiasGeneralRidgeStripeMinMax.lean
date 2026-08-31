import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeRecovery

/-!
# Exact terminal min/max readouts from the completed signed stripe

One signed-stripe ridge block computes `ReLU(A-B)` while its injective
northern code retains exact affine access to the original input.  Ordinary
finite affine readouts therefore realize

\[
  \min(A,B)=A-\mathrm{ReLU}(A-B),\qquad
  \max(A,B)=B+\mathrm{ReLU}(A-B).
\]

The Lean source uses `relu`; the displayed identity is only explanatory.
-/

namespace OneChannelCNNUniversality

open Set

/-- Linear extraction of the protected signed-stripe ridge coordinate. -/
def generalRidgeStripeTargetLinearMap (n : ℕ) :
    Image (n + 4) (2 * (n + 2) + 1) →ₗ[ℝ] ℝ where
  toFun z := z (generalRidgeStripeTarget n).1
    (generalRidgeStripeTarget n).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear part of the signed-stripe minimum readout. -/
noncomputable def generalRidgeStripeMinLinearMap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (a : Fin (n + 2) → ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) →ₗ[ℝ] ℝ :=
  generalRidgeStripeAffineRecoveryLinearMap w T a -
    generalRidgeStripeTargetLinearMap n

/-- Linear part of the signed-stripe maximum readout. -/
noncomputable def generalRidgeStripeMaxLinearMap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (b : Fin (n + 2) → ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) →ₗ[ℝ] ℝ :=
  generalRidgeStripeAffineRecoveryLinearMap w T b +
    generalRidgeStripeTargetLinearMap n

/-- Ordinary finite weights for the minimum readout. -/
noncomputable def generalRidgeStripeMinReadoutWeight {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (a : Fin (n + 2) → ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) :=
  linearReadoutWeights (generalRidgeStripeMinLinearMap w T a)

/-- Ordinary finite weights for the maximum readout. -/
noncomputable def generalRidgeStripeMaxReadoutWeight {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (b : Fin (n + 2) → ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) :=
  linearReadoutWeights (generalRidgeStripeMaxLinearMap w T b)

/-- One genuine completed signed-stripe network has exact terminal affine
readouts for the minimum and maximum of any two input affine functions.  Its
complete state remains injective on every compact injective feature family. -/
theorem exists_generalRidgeStripeMinMaxReadouts_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (a : Fin (n + 2) → ℝ) (alpha : ℝ)
    (b : Fin (n + 2) → ℝ) (beta : ℝ) :
    ∃ (T c t : ℝ)
      (minWeight maxWeight : Image (n + 4) (2 * (n + 2) + 1))
      (minConstant maxConstant : ℝ),
      1 ≤ T ∧ 0 < c ∧ 0 < t ∧
      (generalRidgeStripeNetwork (fun j ↦ a j - b j)
          T c t (alpha - beta)).net.depth = n + 3 ∧
      (∀ x ∈ K,
        (∑ p, ∑ q, minWeight p q *
            (generalRidgeStripeNetwork (fun j ↦ a j - b j)
              T c t (alpha - beta)).eval (F x) p q) + minConstant =
          min ((∑ j, a j * F x 0 j) + alpha)
            ((∑ j, b j * F x 0 j) + beta)) ∧
      (∀ x ∈ K,
        (∑ p, ∑ q, maxWeight p q *
            (generalRidgeStripeNetwork (fun j ↦ a j - b j)
              T c t (alpha - beta)).eval (F x) p q) + maxConstant =
          max ((∑ j, a j * F x 0 j) + alpha)
            ((∑ j, b j * F x 0 j) + beta)) ∧
      Set.InjOn (fun x ↦
        (generalRidgeStripeNetwork (fun j ↦ a j - b j)
          T c t (alpha - beta)).eval (F x)) K := by
  let w : Fin (n + 2) → ℝ := fun j ↦ a j - b j
  let gamma : ℝ := alpha - beta
  obtain ⟨T, c, t, hT, hc, ht, hdepth, hbehavior, hinjective⟩ :=
    exists_injective_generalRidgeStripeNetwork_on_compact
      hK F hF hFinjective w gamma
  let minWeight := generalRidgeStripeMinReadoutWeight w T a
  let maxWeight := generalRidgeStripeMaxReadoutWeight w T b
  let minConstant :=
    generalRidgeStripeAffineReadoutConstant w T c t gamma a alpha
  let maxConstant :=
    generalRidgeStripeAffineReadoutConstant w T c t gamma b beta
  refine ⟨T, c, t, minWeight, maxWeight, minConstant, maxConstant,
    hT, hc, ht, hdepth, ?_, ?_, hinjective⟩
  · intro x hx
    let z := (generalRidgeStripeNetwork w T c t gamma).eval (F x)
    have hnorth : ∀ q : Fin (2 * (n + 2) + 1),
        z ⟨0, by omega⟩ q =
          generalRidgeStripeVariableNorthLinearMap w T (F x) q +
            generalRidgeStripeNorthOffset w T c t gamma q := by
      intro q
      exact generalRidgeStripeNetwork_row_zero_eq_code_add_offset
        w T c t gamma (F x) (hbehavior x hx) q
    have hrecover := generalRidgeStripeAffineReadout_spec
      w T c t gamma (ne_of_gt (zero_lt_one.trans_le hT))
      a alpha z (F x) hnorth
    have hrecover' :
        generalRidgeStripeAffineRecoveryLinearMap w T a z + minConstant =
          (∑ j, a j * F x 0 j) + alpha := by
      simpa [generalRidgeStripeAffineReadoutWeight, minConstant,
        linearReadoutWeights_apply] using hrecover
    have htarget : generalRidgeStripeTargetLinearMap n z =
        relu (((∑ j, a j * F x 0 j) + alpha) -
          ((∑ j, b j * F x 0 j) + beta)) := by
      have htgt := hbehavior x hx
        (generalRidgeStripeTarget n).1
        (generalRidgeStripeTarget n).2
        (by simp [generalRidgeStripeTarget])
      have harg :
          (∑ j, w j * F x 0 j) + gamma =
            ((∑ j, a j * F x 0 j) + alpha) -
              ((∑ j, b j * F x 0 j) + beta) := by
        simp_rw [w, sub_mul]
        rw [Finset.sum_sub_distrib]
        simp [gamma]
        ring
      rw [if_pos rfl, harg] at htgt
      exact htgt
    change
      (∑ p, ∑ q, generalRidgeStripeMinReadoutWeight w T a p q *
        z p q) + minConstant = _
    rw [generalRidgeStripeMinReadoutWeight, linearReadoutWeights_apply]
    simp only [generalRidgeStripeMinLinearMap, LinearMap.sub_apply]
    calc
      generalRidgeStripeAffineRecoveryLinearMap w T a z -
            generalRidgeStripeTargetLinearMap n z + minConstant =
          (generalRidgeStripeAffineRecoveryLinearMap w T a z + minConstant) -
            generalRidgeStripeTargetLinearMap n z := by ring
      _ = ((∑ j, a j * F x 0 j) + alpha) -
          relu (((∑ j, a j * F x 0 j) + alpha) -
            ((∑ j, b j * F x 0 j) + beta)) := by
        rw [hrecover', htarget]
      _ = min ((∑ j, a j * F x 0 j) + alpha)
          ((∑ j, b j * F x 0 j) + beta) :=
        sub_relu_sub_eq_min _ _
  · intro x hx
    let z := (generalRidgeStripeNetwork w T c t gamma).eval (F x)
    have hnorth : ∀ q : Fin (2 * (n + 2) + 1),
        z ⟨0, by omega⟩ q =
          generalRidgeStripeVariableNorthLinearMap w T (F x) q +
            generalRidgeStripeNorthOffset w T c t gamma q := by
      intro q
      exact generalRidgeStripeNetwork_row_zero_eq_code_add_offset
        w T c t gamma (F x) (hbehavior x hx) q
    have hrecover := generalRidgeStripeAffineReadout_spec
      w T c t gamma (ne_of_gt (zero_lt_one.trans_le hT))
      b beta z (F x) hnorth
    have hrecover' :
        generalRidgeStripeAffineRecoveryLinearMap w T b z + maxConstant =
          (∑ j, b j * F x 0 j) + beta := by
      simpa [generalRidgeStripeAffineReadoutWeight, maxConstant,
        linearReadoutWeights_apply] using hrecover
    have htarget : generalRidgeStripeTargetLinearMap n z =
        relu (((∑ j, a j * F x 0 j) + alpha) -
          ((∑ j, b j * F x 0 j) + beta)) := by
      have htgt := hbehavior x hx
        (generalRidgeStripeTarget n).1
        (generalRidgeStripeTarget n).2
        (by simp [generalRidgeStripeTarget])
      have harg :
          (∑ j, w j * F x 0 j) + gamma =
            ((∑ j, a j * F x 0 j) + alpha) -
              ((∑ j, b j * F x 0 j) + beta) := by
        simp_rw [w, sub_mul]
        rw [Finset.sum_sub_distrib]
        simp [gamma]
        ring
      rw [if_pos rfl, harg] at htgt
      exact htgt
    change
      (∑ p, ∑ q, generalRidgeStripeMaxReadoutWeight w T b p q *
        z p q) + maxConstant = _
    rw [generalRidgeStripeMaxReadoutWeight, linearReadoutWeights_apply]
    simp only [generalRidgeStripeMaxLinearMap, LinearMap.add_apply]
    calc
      generalRidgeStripeAffineRecoveryLinearMap w T b z +
            generalRidgeStripeTargetLinearMap n z + maxConstant =
          (generalRidgeStripeAffineRecoveryLinearMap w T b z + maxConstant) +
            generalRidgeStripeTargetLinearMap n z := by ring
      _ = ((∑ j, b j * F x 0 j) + beta) +
          relu (((∑ j, a j * F x 0 j) + alpha) -
            ((∑ j, b j * F x 0 j) + beta)) := by
        rw [hrecover', htarget]
      _ = max ((∑ j, a j * F x 0 j) + alpha)
          ((∑ j, b j * F x 0 j) + beta) :=
        add_relu_sub_eq_max _ _

end OneChannelCNNUniversality
