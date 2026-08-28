import ICM2022NumCS97.Carrier

open Set
open ICM2022NumCS97

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (f : X → ℝ) (hf : ContinuousOn f K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |f x| < C :=
  exists_uniform_abs_bound hK f hf

example (z b : ℝ) (h : 0 ≤ z + b) :
    relu (z + b) = z + b :=
  mask_with_bias_keep h

example (z b : ℝ) (h : z + b ≤ 0) :
    relu (z + b) = 0 :=
  mask_with_bias_kill h

example {rows cols : ℕ} (z carrier : Image rows cols)
    (keep : Fin rows → Fin cols → Prop) [DecidableRel keep]
    (hkeep : ∀ i j, keep i j → 0 ≤ z i j + carrier i j)
    (hkill : ∀ i j, ¬ keep i j → z i j + carrier i j ≤ 0) :
    applyBiasMask z carrier keep = fun i j ↦ if keep i j then z i j + carrier i j else 0 :=
  applyBiasMask_eq z carrier keep hkeep hkill

example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop)
    [DecidableRel keep]
    (carrier : Image (rows + kRows - 1) (cols + kCols - 1))
    (hpositive : ∀ x ∈ K, ∀ p q, keep p q →
      0 < fullConv w (F x) p q + carrier p q) :
    ∃ bias, ∀ x ∈ K, ∀ p q,
      layerEval w bias (F x) p q =
        if keep p q then fullConv w (F x) p q + carrier p q else 0 :=
  exists_masking_bias hK F hF w keep carrier hpositive
