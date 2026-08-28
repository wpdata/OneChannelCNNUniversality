import OneChannelCNNUniversality.Basic

/-!
# Compact carriers and exact ReLU masks

The shared convolution kernel does not prevent us from choosing a different
bias at every spatial coordinate.  The lemmas below isolate the two facts
used by the register construction:

* every continuous scalar signal is uniformly bounded on a compact input set;
* after a bias has put a preactivation on the chosen side of zero, ReLU is
  exactly either the identity or zero.

No approximation occurs in these lemmas.
-/

namespace OneChannelCNNUniversality

open Set

/-- A continuous real-valued signal on a compact set has a positive strict
uniform bound in absolute value.  This formulation also handles the empty
compact set without a separate case. -/
theorem exists_uniform_abs_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (f : X → ℝ) (hf : ContinuousOn f K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |f x| < C := by
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hf.abs)
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro x hx
  have hfx : |f x| ≤ B := hB |f x| ⟨x, hx, rfl⟩
  exact lt_of_le_of_lt (hfx.trans (le_abs_self B)) (lt_add_one |B|)

/-- On the nonnegative side, applying a bias and then ReLU preserves the
whole affine preactivation exactly. -/
theorem mask_with_bias_keep {z b : ℝ} (h : 0 ≤ z + b) :
    relu (z + b) = z + b :=
  relu_of_nonneg h

/-- On the nonpositive side, applying a bias and then ReLU erases the
coordinate exactly. -/
theorem mask_with_bias_kill {z b : ℝ} (h : z + b ≤ 0) :
    relu (z + b) = 0 :=
  relu_of_nonpos h

/-- Entrywise ReLU after adding a spatial bias.  `keep` is a proof-level mask;
it is an argument of the definition so that the exact result records which
branch each coordinate is intended to occupy. -/
def applyBiasMask {rows cols : ℕ} (z carrier : Image rows cols)
    (keep : Fin rows → Fin cols → Prop) [DecidableRel keep] : Image rows cols :=
  fun i j ↦ relu (z i j + carrier i j)

/-- A coordinatewise sign certificate turns a biased ReLU image into the
specified exact mask. -/
theorem applyBiasMask_eq {rows cols : ℕ} (z carrier : Image rows cols)
    (keep : Fin rows → Fin cols → Prop) [DecidableRel keep]
    (hkeep : ∀ i j, keep i j → 0 ≤ z i j + carrier i j)
    (hkill : ∀ i j, ¬ keep i j → z i j + carrier i j ≤ 0) :
    applyBiasMask z carrier keep =
      fun i j ↦ if keep i j then z i j + carrier i j else 0 := by
  funext i j
  by_cases h : keep i j
  · change relu (z i j + carrier i j) =
      (if keep i j then z i j + carrier i j else 0)
    rw [if_pos h]
    exact relu_of_nonneg (hkeep i j h)
  · change relu (z i j + carrier i j) =
      (if keep i j then z i j + carrier i j else 0)
    rw [if_neg h]
    exact relu_of_nonpos (hkill i j h)

/-- Replacing a carrier constant by a new one is implemented by the spatial
bias `newCarrier - oldCarrier`, provided the new affine value stays
nonnegative on the input set. -/
theorem replace_carrier_with_bias (signal oldCarrier newCarrier : ℝ)
    (hnew : 0 ≤ signal + newCarrier) :
    relu ((signal + oldCarrier) + (newCarrier - oldCarrier)) =
      signal + newCarrier := by
  have hrewrite : (signal + oldCarrier) + (newCarrier - oldCarrier) =
      signal + newCarrier := by ring
  rw [hrewrite]
  exact relu_of_nonneg hnew

/-- Coordinatewise continuity of a feature map on an input set. -/
def ContinuousFeatureOn {X : Type*} [TopologicalSpace X]
    {rows cols : ℕ} (K : Set X) (F : X → Image rows cols) : Prop :=
  ∀ i j, ContinuousOn (fun x ↦ F x i j) K

theorem continuousFeatureOn_zeroExtend {X : Type*} [TopologicalSpace X]
    {K : Set X} {rows cols : ℕ} {F : X → Image rows cols}
    (hF : ContinuousFeatureOn K F) (i j : ℕ) :
    ContinuousOn (fun x ↦ zeroExtend (F x) i j) K := by
  by_cases hi : i < rows
  · by_cases hj : j < cols
    · simpa [zeroExtend, hi, hj] using hF ⟨i, hi⟩ ⟨j, hj⟩
    · simpa [zeroExtend, hi, hj] using (continuousOn_const : ContinuousOn (fun _ : X ↦ (0 : ℝ)) K)
  · simpa [zeroExtend, hi] using (continuousOn_const : ContinuousOn (fun _ : X ↦ (0 : ℝ)) K)

theorem continuousFeatureOn_fullConv {X : Type*} [TopologicalSpace X]
    {K : Set X} {rows cols kRows kCols : ℕ} {F : X → Image rows cols}
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols) (p q : ℕ) :
    ContinuousOn (fun x ↦ fullConv w (F x) p q) K := by
  unfold fullConv
  apply continuousOn_finsetSum Finset.univ
  intro a ha
  apply continuousOn_finsetSum Finset.univ
  intro b hb
  split_ifs
  · exact continuousOn_const.mul (continuousFeatureOn_zeroExtend hF (p - a) (q - b))
  · exact continuousOn_const

theorem continuousFeatureOn_layerEval {X : Type*} [TopologicalSpace X]
    {K : Set X} {rows cols kRows kCols : ℕ} {F : X → Image rows cols}
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1)) :
    ContinuousFeatureOn K (fun x ↦ layerEval w bias (F x)) := by
  intro p q
  have hpre : ContinuousOn (fun x ↦ fullConv w (F x) p q + bias p q) K :=
    (continuousFeatureOn_fullConv hF w p q).add continuousOn_const
  intro x hx
  change Filter.Tendsto
    (fun y ↦ max (fullConv w (F y) p q + bias p q) 0)
    (nhdsWithin x K) (nhds (max (fullConv w (F x) p q + bias p q) 0))
  exact (hpre x hx).max (continuousWithinAt_const :
    ContinuousWithinAt (fun _ : X ↦ (0 : ℝ)) K x)

theorem continuousFeatureOn_identity {rows cols : ℕ} (K : Set (Image rows cols)) :
    ContinuousFeatureOn K (fun x : Image rows cols ↦ x) := by
  intro i j
  fun_prop

theorem Network.continuousFeatureOn_eval {X : Type*} [TopologicalSpace X]
    {K : Set X} {kRows kCols rows cols : ℕ}
    (net : Network kRows kCols rows cols) (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) :
    ContinuousFeatureOn K (fun x ↦ net.eval (F x)) := by
  induction net with
  | nil => exact hF
  | cons kernel bias tail ih =>
      exact ih _ (continuousFeatureOn_layerEval hF kernel bias)

/-- Compact carrier linearization for one exact convolutional layer.  A
single spatial bias keeps every designated preactivation in ReLU's linear
region and suppresses every other output coordinate. -/
theorem exists_masking_bias {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (w : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop)
    [DecidableRel keep]
    (carrier : Image (rows + kRows - 1) (cols + kCols - 1))
    (hpositive : ∀ x ∈ K, ∀ p q, keep p q →
      0 < fullConv w (F x) p q + carrier p q) :
    ∃ bias, ∀ x ∈ K, ∀ p q,
      layerEval w bias (F x) p q =
        if keep p q then fullConv w (F x) p q + carrier p q else 0 := by
  have hb : ∀ p : Fin (rows + kRows - 1), ∀ q : Fin (cols + kCols - 1),
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |fullConv w (F x) p q| < C := by
    intro p q
    exact exists_uniform_abs_bound hK _ (continuousFeatureOn_fullConv hF w p q)
  choose C hCpos hCbound using hb
  let bias : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ if keep p q then carrier p q else -C p q
  refine ⟨bias, ?_⟩
  intro x hx p q
  by_cases hpq : keep p q
  · rw [if_pos hpq]
    change relu (fullConv w (F x) p q + bias p q) =
      fullConv w (F x) p q + carrier p q
    simp only [bias, if_pos hpq]
    apply relu_of_nonneg
    exact (hpositive x hx p q hpq).le
  · rw [if_neg hpq]
    change relu (fullConv w (F x) p q + bias p q) = 0
    apply relu_of_nonpos
    simp only [bias, if_neg hpq]
    have hzle : fullConv w (F x) p q ≤ |fullConv w (F x) p q| := le_abs_self _
    have hzlt : fullConv w (F x) p q < C p q :=
      hzle.trans_lt (hCbound p q x hx)
    linarith

/-- A carrier-producing version of `exists_masking_bias`.  If the current
state is `variable + knownConstant`, this theorem chooses both a new positive
carrier and an actual spatial bias so that the next state has exactly the
masked variable convolution plus that carrier. -/
theorem exists_positive_linearized_masking_layer
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) (w : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Prop)
    [DecidableRel keep] :
    ∃ (bias carrier : Image (rows + kRows - 1) (cols + kCols - 1)),
      (∀ x ∈ K, ∀ p q, keep p q →
        0 < fullConv w (V x) p q + carrier p q) ∧
      (∀ x ∈ K, ∀ p q,
        layerEval w bias (F x) p q =
          if keep p q then fullConv w (V x) p q + carrier p q else 0) := by
  have hb : ∀ p : Fin (rows + kRows - 1), ∀ q : Fin (cols + kCols - 1),
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |fullConv w (V x) p q| < C := by
    intro p q
    exact exists_uniform_abs_bound hK _ (continuousFeatureOn_fullConv hV w p q)
  choose carrier hcarrier_pos hcarrier_bound using hb
  let correction : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ carrier p q - fullConv w known p q
  have hF : ContinuousFeatureOn K F := by
    intro i j
    have hc : ContinuousOn (fun _ : X ↦ known i j) K := continuousOn_const
    apply ((hV i j).add hc).congr
    intro x hx
    have h := congrFun (congrFun (hdecomp x hx) i) j
    simpa using h
  have hpositiveF : ∀ x ∈ K, ∀ p q, keep p q →
      0 < fullConv w (F x) p q + correction p q := by
    intro x hx p q hpq
    rw [hdecomp x hx, fullConv_add]
    dsimp [correction]
    have hzle : -|fullConv w (V x) p q| ≤ fullConv w (V x) p q := neg_abs_le _
    have hbound := hcarrier_bound p q x hx
    linarith
  obtain ⟨bias, hbias⟩ :=
    exists_masking_bias hK F hF w keep correction hpositiveF
  refine ⟨bias, carrier, ?_, ?_⟩
  · intro x hx p q hpq
    have hzle : -|fullConv w (V x) p q| ≤ fullConv w (V x) p q := neg_abs_le _
    have hbound := hcarrier_bound p q x hx
    linarith
  · intro x hx p q
    rw [hbias x hx p q]
    by_cases hpq : keep p q
    · rw [if_pos hpq, if_pos hpq, hdecomp x hx, fullConv_add]
      dsimp [correction]
      ring
    · simp [hpq]

end OneChannelCNNUniversality
