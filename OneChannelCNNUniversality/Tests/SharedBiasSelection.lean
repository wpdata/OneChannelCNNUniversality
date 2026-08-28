import OneChannelCNNUniversality.SharedBiasSelection

open OneChannelCNNUniversality

example {rows cols : ℕ} (signal carrier : Image rows cols)
    (target : Fin rows × Fin cols) (theta margin : ℝ)
    (hgap : ∀ p q, (p, q) ≠ target →
      margin ≤ carrier p q - carrier target.1 target.2)
    (hbound : ∀ p q, |signal p q + theta| < margin) :
    (fun p q ↦ relu
      (signal p q + carrier p q + (theta - carrier target.1 target.2))) =
      selectedReluImage signal carrier target theta := by
  exact sharedBiasSelectiveActivation_eq signal carrier target theta margin hgap hbound

example {inRows inCols kRows kCols : ℕ}
    (F : Image inRows inCols) (w : Kernel kRows kCols)
    (signal carrier : Image (inRows + kRows - 1) (inCols + kCols - 1))
    (target : Fin (inRows + kRows - 1) × Fin (inCols + kCols - 1))
    (theta margin : ℝ)
    (hdecomp : ∀ (p : Fin (inRows + kRows - 1))
      (q : Fin (inCols + kCols - 1)),
      fullConv w F p q = signal p q + carrier p q)
    (hgap : ∀ p q, (p, q) ≠ target →
      margin ≤ carrier p q - carrier target.1 target.2)
    (hbound : ∀ p q, |signal p q + theta| < margin) :
    sharedLayerEval w (theta - carrier target.1 target.2) F =
      selectedReluImage signal carrier target theta := by
  exact sharedLayer_select_target_of_carrier_gap F w signal carrier target theta margin
    hdecomp hgap hbound

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (signal : X → Image rows cols) (hSignal : ContinuousFeatureOn K signal)
    (theta : ℝ) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ x ∈ K, ∀ p q,
      |signal x p q + theta| < margin := by
  exact exists_uniform_feature_margin hK signal hSignal theta

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (signal : X → Image rows cols) (hSignal : ContinuousFeatureOn K signal)
    (address : Image rows cols) (target : Fin rows × Fin cols) (theta : ℝ)
    (haddress : ∀ p q, (p, q) ≠ target →
      1 ≤ address p q - address target.1 target.2) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ x ∈ K,
      (fun p q ↦ relu
        (signal x p q + scale * address p q +
          (theta - scale * address target.1 target.2))) =
        selectedReluImage (signal x) (fun p q ↦ scale * address p q)
          target theta := by
  exact exists_sharedBias_select_from_unit_address
    hK signal hSignal address target theta haddress
