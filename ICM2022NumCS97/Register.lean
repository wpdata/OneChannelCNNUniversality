import ICM2022NumCS97.Encoder

/-!
# Sparse register primitives

This file proves the exact shared-kernel identities used by every routing
instruction.  A two-tap kernel has one identity tap and one shifted tap; the
spatial bias from `Carrier` then decides which complete preactivations are
retained.  In particular, no bias is ever used to remove one unknown summand
from a collision.
-/

namespace ICM2022NumCS97

/-- A kernel containing one weighted delta tap. -/
def deltaKernel {kRows kCols : ℕ} (row : Fin kRows) (col : Fin kCols) (a : ℝ) :
    Kernel kRows kCols :=
  fun i j ↦ if i = row ∧ j = col then a else 0

/-- Exact shift formula for a delta kernel. -/
theorem fullConv_deltaKernel {kRows kCols rows cols : ℕ}
    (row : Fin kRows) (col : Fin kCols) (a : ℝ)
    (x : Image rows cols) (p q : ℕ) :
    fullConv (deltaKernel row col a) x p q =
      if (row : ℕ) ≤ p ∧ (col : ℕ) ≤ q then
        a * zeroExtend x (p - row) (q - col)
      else 0 := by
  classical
  unfold fullConv
  rw [Fintype.sum_eq_single row]
  · rw [Fintype.sum_eq_single col]
    · simp [deltaKernel]
    · intro b hb
      simp [deltaKernel, hb]
  · intro r hr
    simp [deltaKernel, hr]

theorem fullConv_kernel_add {kRows kCols rows cols : ℕ}
    (w₁ w₂ : Kernel kRows kCols) (x : Image rows cols) (p q : ℕ) :
    fullConv (fun i j ↦ w₁ i j + w₂ i j) x p q =
      fullConv w₁ x p q + fullConv w₂ x p q := by
  classical
  simp only [fullConv]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- Identity plus one shifted tap. -/
def twoTapKernel {kRows kCols : ℕ}
    (baseRow : Fin kRows) (baseCol : Fin kCols)
    (shiftRow : Fin kRows) (shiftCol : Fin kCols) (a : ℝ) :
    Kernel kRows kCols :=
  fun i j ↦ deltaKernel baseRow baseCol 1 i j +
    deltaKernel shiftRow shiftCol a i j

theorem fullConv_twoTapKernel {kRows kCols rows cols : ℕ}
    (x : Image rows cols) (baseRow : Fin kRows) (baseCol : Fin kCols)
    (shiftRow : Fin kRows) (shiftCol : Fin kCols) (a : ℝ) (p q : ℕ) :
    fullConv (twoTapKernel baseRow baseCol shiftRow shiftCol a) x p q =
      (if (baseRow : ℕ) ≤ p ∧ (baseCol : ℕ) ≤ q then
        zeroExtend x (p - baseRow) (q - baseCol) else 0) +
      (if (shiftRow : ℕ) ≤ p ∧ (shiftCol : ℕ) ≤ q then
        a * zeroExtend x (p - shiftRow) (q - shiftCol) else 0) := by
  unfold twoTapKernel
  rw [fullConv_kernel_add,
    fullConv_deltaKernel baseRow baseCol 1 x p q,
    fullConv_deltaKernel shiftRow shiftCol a x p q]
  simp only [one_mul]

/-- At an empty destination, a diagonal two-tap layer moves/scales the
unique predecessor exactly. -/
theorem twoTap_move_to_empty {rows cols : ℕ} (x : Image rows cols)
    (a : ℝ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hempty : zeroExtend x p q = 0) :
    fullConv (twoTapKernel (0 : Fin 2) (0 : Fin 2)
      (1 : Fin 2) (1 : Fin 2) a) x p q =
        a * zeroExtend x (p - 1) (q - 1) := by
  rw [fullConv_twoTapKernel]
  simp [hp, hq, hempty]

/-- If the shifted predecessor is empty, the identity tap preserves a
register exactly. -/
theorem twoTap_preserve_without_predecessor {rows cols : ℕ} (x : Image rows cols)
    (a : ℝ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpred : zeroExtend x (p - 1) (q - 1) = 0) :
    fullConv (twoTapKernel (0 : Fin 2) (0 : Fin 2)
      (1 : Fin 2) (1 : Fin 2) a) x p q = zeroExtend x p q := by
  rw [fullConv_twoTapKernel]
  simp [hp, hq, hpred]

/-- At an occupied destination the same formula is the intended merge. -/
theorem twoTap_merge {rows cols : ℕ} (x : Image rows cols)
    (a : ℝ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    fullConv (twoTapKernel (0 : Fin 2) (0 : Fin 2)
      (1 : Fin 2) (1 : Fin 2) a) x p q =
        zeroExtend x p q + a * zeroExtend x (p - 1) (q - 1) := by
  rw [fullConv_twoTapKernel]
  simp [hp, hq]

/-- The compact masking lemma returns an actual one-layer `Network`, not
merely an abstract register transition. -/
theorem localUpdate_refines_layer {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop)
    [DecidableRel keep]
    (carrier : Image (rows + kRows - 1) (cols + kCols - 1))
    (hpositive : ∀ x ∈ K, ∀ p q, keep p q →
      0 < fullConv w (F x) p q + carrier p q) :
    ∃ bias, ∀ x ∈ K, ∀ p q,
      (NetworkTo.single w bias).eval (F x) p q =
        if keep p q then fullConv w (F x) p q + carrier p q else 0 := by
  simpa using exists_masking_bias hK F hF w keep carrier hpositive

/-- Repeated formal convolutions can be implemented by an actual sequence
of one-channel ReLU layers.  Compactly chosen carriers keep every coordinate
in the linear branch, so the variable part is exactly `iterateFullConv`. -/
theorem exists_linearized_full_iterations
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps : ℕ) (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols
        (grownSize kRows rows steps) (grownSize kCols cols steps))
      (carrier : Image (grownSize kRows rows steps) (grownSize kCols cols steps)),
      ∀ x ∈ K, net.eval (F x) = iterateFullConv w steps (V x) + carrier := by
  induction steps generalizing rows cols F V known with
  | zero =>
      exact ⟨NetworkTo.nil rows cols kRows kCols, known, hdecomp⟩
  | succ steps ih =>
      let keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop :=
        fun _ _ ↦ True
      obtain ⟨bias, nextCarrier, hpositive, hfirst⟩ :=
        exists_positive_linearized_masking_layer hK F V known hdecomp hV w keep
      let nextF : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ layerEval w bias (F x)
      let nextV : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ fullConvImage w (V x)
      have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + nextCarrier := by
        intro x hx
        funext p q
        simpa [nextF, nextV, fullConvImage, keep] using hfirst x hx p q
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV w p q
      obtain ⟨tail, finalCarrier, htail⟩ :=
        ih nextF nextV nextCarrier hnextDecomp hnextV
      refine ⟨NetworkTo.cons w bias tail, finalCarrier, ?_⟩
      intro x hx
      rw [NetworkTo.eval_cons]
      exact htail x hx

/-- Repeated linearized convolutions followed by one exact spatial mask,
again returning a concrete typed network. -/
theorem exists_linearized_iterations_then_mask
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ} (w finalKernel : Kernel kRows kCols)
    (steps : ℕ) (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V)
    (keep : Fin (grownSize kRows rows (steps + 1)) →
      Fin (grownSize kCols cols (steps + 1)) → Prop)
    [DecidableRel keep] :
    ∃ (net : NetworkTo kRows kCols rows cols
        (grownSize kRows rows (steps + 1)) (grownSize kCols cols (steps + 1)))
      (carrier : Image (grownSize kRows rows (steps + 1))
        (grownSize kCols cols (steps + 1))),
      ∀ x ∈ K, net.eval (F x) =
        maskedImage keep (iterateThenConv w finalKernel steps (V x)) + carrier := by
  induction steps generalizing rows cols F V known with
  | zero =>
      simp only [grownSize, iterateThenConv] at keep ⊢
      obtain ⟨bias, nextCarrier, hpositive, hfirst⟩ :=
        exists_positive_linearized_masking_layer hK F V known hdecomp hV finalKernel keep
      let carrier : Image (rows + kRows - 1) (cols + kCols - 1) :=
        maskedImage keep nextCarrier
      refine ⟨NetworkTo.single finalKernel bias, carrier, ?_⟩
      intro x hx
      rw [NetworkTo.eval_single]
      funext p q
      change layerEval finalKernel bias (F x) p q =
        maskedImage keep (fullConvImage finalKernel (V x)) p q +
          maskedImage keep nextCarrier p q
      rw [hfirst x hx p q]
      by_cases hpq : keep p q
      · simp [maskedImage, fullConvImage, hpq]
      · simp [maskedImage, fullConvImage, hpq]
  | succ steps ih =>
      let keepAll : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop :=
        fun _ _ ↦ True
      obtain ⟨bias, nextCarrier, hpositive, hfirst⟩ :=
        exists_positive_linearized_masking_layer hK F V known hdecomp hV w keepAll
      let nextF : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ layerEval w bias (F x)
      let nextV : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ fullConvImage w (V x)
      have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + nextCarrier := by
        intro x hx
        funext p q
        simpa [nextF, nextV, fullConvImage, keepAll] using hfirst x hx p q
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV w p q
      obtain ⟨tail, finalCarrier, htail⟩ :=
        ih nextF nextV nextCarrier hnextDecomp hnextV keep
      refine ⟨NetworkTo.cons w bias tail, finalCarrier, ?_⟩
      intro x hx
      rw [NetworkTo.eval_cons]
      exact htail x hx

/-- A proof-level sparse register state on a compact input set. -/
structure SparseState {X : Type*} [TopologicalSpace X] (K : Set X)
    {rows cols : ℕ} (F : X → Image rows cols) where
  support : Finset (Fin rows × Fin cols)
  signal : Fin rows × Fin cols → X → ℝ
  carrier : Fin rows × Fin cols → ℝ
  on_support : ∀ x ∈ K, ∀ s ∈ support,
    F x s.1 s.2 = signal s x + carrier s
  off_support : ∀ x ∈ K, ∀ i j, (i, j) ∉ support → F x i j = 0
  positive : ∀ x ∈ K, ∀ s ∈ support, 0 < signal s x + carrier s
  continuous_signal : ∀ s ∈ support, ContinuousOn (signal s) K

end ICM2022NumCS97
