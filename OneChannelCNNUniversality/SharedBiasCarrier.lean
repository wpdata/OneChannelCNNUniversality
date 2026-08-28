import OneChannelCNNUniversality.Carrier
import OneChannelCNNUniversality.SharedBiasGeometry

/-!
# Non-destructive shared-bias carrier layers

A single scalar bias can put every coordinate of a finite output rectangle in
ReLU's linear region at once.  Consequently, if the incoming feature image is
the sum of an input-dependent signal and a fixed image, then one shared-bias
layer preserves the convolved signal and turns the fixed image into a new,
generally position-dependent carrier.
-/

namespace OneChannelCNNUniversality

open Set

/-- On a compact input set, one positive scalar bias linearizes a whole
shared-bias convolutional layer simultaneously at every output coordinate. -/
theorem exists_shared_bias_linearization
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ∀ p q,
      sharedLayerEval w b (F x) p q = fullConv w (F x) p q + b := by
  have hbound : ∀ p : Fin (rows + kRows - 1),
      ∀ q : Fin (cols + kCols - 1),
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |fullConv w (F x) p q| < C := by
    intro p q
    exact exists_uniform_abs_bound hK _ (continuousFeatureOn_fullConv hF w p q)
  choose C hCpos hClt using hbound
  let b : ℝ := (∑ p, ∑ q, C p q) + 1
  have hCnonneg : ∀ p q, 0 ≤ C p q := fun p q ↦ (hCpos p q).le
  have hsum_nonneg : 0 ≤ ∑ p, ∑ q, C p q := by
    exact Finset.sum_nonneg fun p _ ↦ Finset.sum_nonneg fun q _ ↦ hCnonneg p q
  have hbpos : 0 < b := by
    dsimp [b]
    linarith
  refine ⟨b, hbpos, ?_⟩
  intro x hx p q
  have hq_le : C p q ≤ ∑ q', C p q' := by
    exact Finset.single_le_sum (fun q' _ ↦ hCnonneg p q') (Finset.mem_univ q)
  have hp_le : (∑ q', C p q') ≤ ∑ p', ∑ q', C p' q' := by
    exact Finset.single_le_sum
      (fun p' _ ↦ Finset.sum_nonneg fun q' _ ↦ hCnonneg p' q')
      (Finset.mem_univ p)
  have hz_lower : -|fullConv w (F x) p q| ≤ fullConv w (F x) p q :=
    neg_abs_le _
  have hz_bound := hClt p q x hx
  unfold sharedLayerEval layerEval
  apply relu_of_nonneg
  dsimp [constantImage, b]
  linarith

/-- A shared-bias layer transports an input-dependent signal without loss
while updating its fixed spatial carrier.  The output carrier is allowed to
vary with position, but it is generated solely by convolution of the known
input image and addition of the one broadcast scalar bias. -/
theorem exists_shared_bias_carrier_layer
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) (w : Kernel kRows kCols) :
    ∃ (b : ℝ) (carrier : Image (rows + kRows - 1) (cols + kCols - 1)),
      0 < b ∧ ∀ x ∈ K,
        sharedLayerEval w b (F x) = fullConvImage w (V x) + carrier := by
  have hF : ContinuousFeatureOn K F := by
    intro i j
    apply ((hV i j).add continuousOn_const).congr
    intro x hx
    have h := congrFun (congrFun (hdecomp x hx) i) j
    simpa using h
  obtain ⟨b, hbpos, hlinear⟩ := exists_shared_bias_linearization hK F hF w
  let carrier : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ fullConv w known p q + b
  refine ⟨b, carrier, hbpos, ?_⟩
  intro x hx
  funext p q
  rw [hlinear x hx p q, hdecomp x hx, fullConv_add]
  simp only [fullConvImage, carrier, Pi.add_apply]
  ring

/-- The fixed carrier produced by horizontal differencing of a constant image
and addition of a broadcast scalar bias. -/
def horizontalSharedCarrier (rows cols : ℕ) (c b : ℝ) :
    Image (rows + 2 - 1) (cols + 2 - 1) :=
  fun p q ↦ fullConv horizontalBoundaryKernel (constantImage rows cols c) p q + b

/-- On every nonempty row, the left boundary carrier is `c + b`. -/
theorem horizontalSharedCarrier_left {rows cols : ℕ} (c b : ℝ)
    (i : Fin rows) (hcols : 0 < cols) :
    horizontalSharedCarrier rows cols c b
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨0, by omega⟩ : Fin (cols + 2 - 1)) = c + b := by
  unfold horizontalSharedCarrier horizontalBoundaryKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend, constantImage, i.isLt, hcols]

/-- At every original non-left-boundary coordinate, the constant terms in
the first difference cancel, leaving exactly the broadcast bias `b`. -/
theorem horizontalSharedCarrier_interior {rows cols : ℕ} (c b : ℝ)
    (i : Fin rows) (j : Fin cols) (hj : 0 < (j : ℕ)) :
    horizontalSharedCarrier rows cols c b
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨j, by omega⟩ : Fin (cols + 2 - 1)) = b := by
  unfold horizontalSharedCarrier horizontalBoundaryKernel
  rw [fullConv_twoTapKernel]
  have hjpred : (j : ℕ) - 1 < cols := by omega
  have hjone : 1 ≤ (j : ℕ) := by omega
  simp [zeroExtend, constantImage, i.isLt, j.isLt, hjone, hjpred]

/-- A concrete non-destructive boundary-carrier layer.  The signal passes
through the injective horizontal first-difference transform, while the fixed
constant summand becomes the explicit `horizontalSharedCarrier`. -/
theorem exists_horizontal_shared_carrier_layer
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (V : X → Image rows cols)
    (hV : ContinuousFeatureOn K V) (c : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K,
      sharedLayerEval horizontalBoundaryKernel b
          (V x + constantImage rows cols c) =
        fullConvImage horizontalBoundaryKernel (V x) +
          horizontalSharedCarrier rows cols c b := by
  let F : X → Image rows cols := fun x ↦ V x + constantImage rows cols c
  have hF : ContinuousFeatureOn K F := by
    intro i j
    exact (hV i j).add continuousOn_const
  obtain ⟨b, hbpos, hlinear⟩ :=
    exists_shared_bias_linearization hK F hF horizontalBoundaryKernel
  refine ⟨b, hbpos, ?_⟩
  intro x hx
  funext p q
  rw [hlinear x hx p q]
  change fullConv horizontalBoundaryKernel
      (V x + constantImage rows cols c) p q + b = _
  rw [fullConv_add]
  simp only [fullConvImage, horizontalSharedCarrier, Pi.add_apply]
  ring

private theorem horizontalBoundaryTransform_zero
    {rows n : ℕ} (x : Image rows (n + 1)) (i : Fin rows) :
    fullConv horizontalBoundaryKernel x i 0 = x i 0 := by
  unfold horizontalBoundaryKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend, i.isLt]

private theorem horizontalBoundaryTransform_succ
    {rows n : ℕ} (x : Image rows (n + 1)) (i : Fin rows) (j : Fin n) :
    fullConv horizontalBoundaryKernel x i ((j : ℕ) + 1) =
      x i j.succ - x i j.castSucc := by
  unfold horizontalBoundaryKernel
  rw [fullConv_twoTapKernel]
  have hsucc : (j : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (j : ℕ) + 1 := by omega
  simp [zeroExtend, i.isLt, hsucc, hone]
  congr 1

/-- The horizontal first-difference transform used to generate a boundary
carrier is injective.  Thus its position signal is not obtained by discarding
the input: the original finite image is uniquely determined by the complete
expanded output image. -/
theorem horizontalBoundaryTransform_injective {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage horizontalBoundaryKernel x) := by
  intro x y hxy
  by_cases hcols : cols = 0
  · subst cols
    funext i j
    exact Fin.elim0 j
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcols
    funext i j
    induction j using Fin.induction with
    | zero =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv horizontalBoundaryKernel x i 0 =
          fullConv horizontalBoundaryKernel y i 0 at hentry
        simpa only [horizontalBoundaryTransform_zero] using hentry
    | succ j ih =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨(j : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv horizontalBoundaryKernel x i ((j : ℕ) + 1) =
          fullConv horizontalBoundaryKernel y i ((j : ℕ) + 1) at hentry
        rw [horizontalBoundaryTransform_succ,
          horizontalBoundaryTransform_succ] at hentry
        linarith

end OneChannelCNNUniversality
