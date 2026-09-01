import OneChannelCNNUniversality.SharedBiasSelection

/-!
# Simultaneous compact selection at finitely many spatial targets

A shared scalar bias can apply ReLU at more than one coordinate at once.  It
is enough that a fixed carrier has one common baseline on every target and a
unit gap above that baseline at every protected non-target coordinate.
Compactness supplies one scale dominating the signal uniformly.  This is the
multi-target selection interface needed by collision-free parallel ridge
packing.
-/

namespace OneChannelCNNUniversality

open Set

/-- Affine preactivation normalized to `signal + theta` wherever the carrier
equals `base`. -/
def multiTargetPreactivation {rows cols : ℕ}
    (signal carrier : Image rows cols) (base theta scale : ℝ)
    (p : Fin rows) (q : Fin cols) : ℝ :=
  signal p q + scale * carrier p q + (theta - scale * base)

/-- A common carrier baseline on a finite target set and a unit protected
gap elsewhere let one shared scalar bias apply ReLU simultaneously at every
target.  Every protected non-target stays exactly in the linear branch. -/
theorem exists_multiTargetSelectiveActivation_on
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (carrier : Image rows cols) (base : ℝ)
    (targets protect : Fin rows → Fin cols → Prop)
    [targetsDecidable : ∀ p q, Decidable (targets p q)]
    (theta : ℝ)
    (htarget : ∀ p q, targets p q → carrier p q = base)
    (hgap : ∀ p q, protect p q → ¬ targets p q →
      1 ≤ carrier p q - base) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ x ∈ K, ∀ p q, protect p q →
        relu (multiTargetPreactivation
          (signal x) carrier base theta scale p q) =
          if targets p q then relu (signal x p q + theta)
          else multiTargetPreactivation
            (signal x) carrier base theta scale p q := by
  classical
  obtain ⟨scale, hscale, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  refine ⟨scale, hscale, ?_⟩
  intro x hx p q hpq
  by_cases hpt : targets p q
  · rw [if_pos hpt]
    rw [multiTargetPreactivation, htarget p q hpt]
    congr 1
    ring
  · rw [if_neg hpt]
    apply relu_of_nonneg
    have hsignal : -scale < signal x p q + theta :=
      neg_lt_of_abs_lt (hbound x hx p q)
    have hcarrier : scale ≤ scale * (carrier p q - base) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hgap p q hpq hpt) hscale.le
    rw [multiTargetPreactivation]
    linarith

/-- Upward-closed version of simultaneous compact selection.  One positive
threshold works for every larger carrier scale, allowing the selector scale
to be synchronized with thresholds imposed by earlier proper ReLU layers. -/
theorem exists_multiTargetSelectiveActivation_threshold_on
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (carrier : Image rows cols) (base : ℝ)
    (targets protect : Fin rows → Fin cols → Prop)
    [targetsDecidable : ∀ p q, Decidable (targets p q)]
    (theta : ℝ)
    (htarget : ∀ p q, targets p q → carrier p q = base)
    (hgap : ∀ p q, protect p q → ¬ targets p q →
      1 ≤ carrier p q - base) :
    ∃ scale₀ : ℝ, 0 < scale₀ ∧ ∀ scale : ℝ, scale₀ ≤ scale →
      ∀ x ∈ K, ∀ p q, protect p q →
        relu (multiTargetPreactivation
          (signal x) carrier base theta scale p q) =
          if targets p q then relu (signal x p q + theta)
          else multiTargetPreactivation
            (signal x) carrier base theta scale p q := by
  classical
  obtain ⟨scale₀, hscale₀, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  refine ⟨scale₀, hscale₀, ?_⟩
  intro scale hscale x hx p q hpq
  have hscalePos : 0 < scale := hscale₀.trans_le hscale
  by_cases hpt : targets p q
  · rw [if_pos hpt]
    rw [multiTargetPreactivation, htarget p q hpt]
    congr 1
    ring
  · rw [if_neg hpt]
    apply relu_of_nonneg
    have hsignal : -scale₀ < signal x p q + theta :=
      neg_lt_of_abs_lt (hbound x hx p q)
    have hcarrier : scale ≤ scale * (carrier p q - base) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hgap p q hpq hpt) hscalePos.le
    rw [multiTargetPreactivation]
    linarith

/-- Exact final-layer form of simultaneous selection.  If the convolutional
preactivation decomposes as a variable signal plus a scaled carrier, the one
broadcast bias `theta - scale*base` produces the multi-target mask on all
protected coordinates. -/
theorem sharedLayer_multiTarget_of_decomposition
    {inRows inCols kRows kCols : ℕ}
    (F : Image inRows inCols) (kernel : Kernel kRows kCols)
    (signal carrier : Image (inRows + kRows - 1) (inCols + kCols - 1))
    (base theta scale : ℝ)
    (targets protect : Fin (inRows + kRows - 1) →
      Fin (inCols + kCols - 1) → Prop)
    [targetsDecidable : ∀ p q, Decidable (targets p q)]
    (hdecomp : ∀ (p : Fin (inRows + kRows - 1))
      (q : Fin (inCols + kCols - 1)),
      fullConv kernel F p q = signal p q + scale * carrier p q)
    (htarget : ∀ p q, targets p q → carrier p q = base)
    (hlinear : ∀ p q, protect p q → ¬ targets p q →
      0 ≤ multiTargetPreactivation signal carrier base theta scale p q) :
    ∀ p q, protect p q →
      sharedLayerEval kernel (theta - scale * base) F p q =
        if targets p q then relu (signal p q + theta)
        else multiTargetPreactivation signal carrier base theta scale p q := by
  classical
  intro p q hpq
  change relu (fullConv kernel F p q + (theta - scale * base)) = _
  rw [hdecomp]
  by_cases hpt : targets p q
  · rw [if_pos hpt, htarget p q hpt]
    congr 1
    ring
  · rw [if_neg hpt]
    apply relu_of_nonneg
    exact hlinear p q hpq hpt

end OneChannelCNNUniversality
