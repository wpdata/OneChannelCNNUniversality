import OneChannelCNNUniversality.SharedBiasCarrier

/-!
# Selecting one ReLU with a shared scalar bias

A spatial carrier can replace position-dependent biases when one site lies
strictly below all the others by more than the possible signal variation.
Subtracting the target carrier with one broadcast scalar places the target at
the requested ReLU threshold while every other site remains in ReLU's linear
branch.
-/

namespace OneChannelCNNUniversality

/-- The exact result of applying ReLU only at `target`, while retaining the
full affine preactivation at every other spatial coordinate. -/
def selectedReluImage {rows cols : ℕ} (signal carrier : Image rows cols)
    (target : Fin rows × Fin cols) (theta : ℝ) : Image rows cols :=
  fun p q ↦
    if (p, q) = target then
      relu (signal p q + theta)
    else
      signal p q + carrier p q + (theta - carrier target.1 target.2)

/-- A carrier-gap certificate turns one broadcast bias into one selected
ReLU.  The target is allowed to cross zero; every other coordinate is proven
to remain in the linear branch. -/
theorem sharedBiasSelectiveActivation_eq {rows cols : ℕ}
    (signal carrier : Image rows cols) (target : Fin rows × Fin cols)
    (theta margin : ℝ)
    (hgap : ∀ p q, (p, q) ≠ target →
      margin ≤ carrier p q - carrier target.1 target.2)
    (hbound : ∀ p q, |signal p q + theta| < margin) :
    (fun p q ↦ relu
      (signal p q + carrier p q + (theta - carrier target.1 target.2))) =
      selectedReluImage signal carrier target theta := by
  funext p q
  by_cases htarget : (p, q) = target
  · rw [selectedReluImage, if_pos htarget]
    have hp : p = target.1 := congrArg Prod.fst htarget
    have hq : q = target.2 := congrArg Prod.snd htarget
    subst p
    subst q
    congr 1
    ring
  · rw [selectedReluImage, if_neg htarget]
    apply relu_of_nonneg
    have hcarrier := hgap p q htarget
    have hsignal := neg_abs_le (signal p q + theta)
    have hsignalBound := hbound p q
    linarith

/-- Exact network-layer form of `sharedBiasSelectiveActivation_eq`.  If the
convolutional preactivation decomposes as `signal + carrier`, then the scalar
bias `theta - carrier(target)` performs the selected update. -/
theorem sharedLayer_select_target_of_carrier_gap
    {inRows inCols kRows kCols : ℕ}
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
  have hselected :=
    sharedBiasSelectiveActivation_eq signal carrier target theta margin hgap hbound
  funext p q
  have hentry := congrFun (congrFun hselected p) q
  change relu
      (fullConv w F p q + (theta - carrier target.1 target.2)) = _
  rw [hdecomp]
  exact hentry

/-- A continuous finite feature image has one strict absolute bound, uniform
over both the compact input set and all of its spatial coordinates. -/
theorem exists_uniform_feature_margin
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal) (theta : ℝ) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ x ∈ K, ∀ p q,
      |signal x p q + theta| < margin := by
  have hbound : ∀ p : Fin rows, ∀ q : Fin cols,
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |signal x p q + theta| < C := by
    intro p q
    exact exists_uniform_abs_bound hK _ ((hSignal p q).add continuousOn_const)
  choose C hCpos hClt using hbound
  let margin : ℝ := (∑ p, ∑ q, C p q) + 1
  have hCnonneg : ∀ p q, 0 ≤ C p q := fun p q ↦ (hCpos p q).le
  have hsum_nonneg : 0 ≤ ∑ p, ∑ q, C p q := by
    exact Finset.sum_nonneg fun p _ ↦ Finset.sum_nonneg fun q _ ↦ hCnonneg p q
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  refine ⟨margin, hmargin, ?_⟩
  intro x hx p q
  have hq_le : C p q ≤ ∑ q', C p q' := by
    exact Finset.single_le_sum (fun q' _ ↦ hCnonneg p q') (Finset.mem_univ q)
  have hp_le : (∑ q', C p q') ≤ ∑ p', ∑ q', C p' q' := by
    exact Finset.single_le_sum
      (fun p' _ ↦ Finset.sum_nonneg fun q' _ ↦ hCnonneg p' q')
      (Finset.mem_univ p)
  have hentry := hClt p q x hx
  dsimp [margin]
  linarith

/-- A normalized spatial address is sufficient for shared-bias selection on
an arbitrary compact signal family.  Compactness supplies one scale large
enough for the same carrier and scalar bias to work for every input. -/
theorem exists_sharedBias_select_from_unit_address
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal) (address : Image rows cols)
    (target : Fin rows × Fin cols) (theta : ℝ)
    (haddress : ∀ p q, (p, q) ≠ target →
      1 ≤ address p q - address target.1 target.2) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ x ∈ K,
      (fun p q ↦ relu
        (signal x p q + scale * address p q +
          (theta - scale * address target.1 target.2))) =
        selectedReluImage (signal x) (fun p q ↦ scale * address p q)
          target theta := by
  obtain ⟨scale, hscale, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  refine ⟨scale, hscale, ?_⟩
  intro x hx
  apply sharedBiasSelectiveActivation_eq _ _ target theta scale
  · intro p q hne
    have hunit := haddress p q hne
    have hscaled := mul_le_mul_of_nonneg_left hunit hscale.le
    linarith
  · exact hbound x hx

end OneChannelCNNUniversality
