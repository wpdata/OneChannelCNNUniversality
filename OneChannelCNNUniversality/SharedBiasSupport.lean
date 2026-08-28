import OneChannelCNNUniversality.SharedBiasRecovery

/-!
# Southeast support propagation

Causal expansive convolution cannot move a change toward the northwest.  This
file states that fact as an agreement invariant, first for a southeast
quadrant and then for the strict quadrant with its root removed.
-/

namespace OneChannelCNNUniversality

/-- Two equally sized images may differ only in the southeast quadrant rooted
at the natural coordinate `(r,s)`. -/
def AgreeOutsideSoutheast {rows cols : ℕ}
    (x y : Image rows cols) (r s : ℕ) : Prop :=
  ∀ i j, ¬ (r ≤ i ∧ s ≤ j) → zeroExtend x i j = zeroExtend y i j

/-- One full convolution cannot propagate a southeast-supported difference
outside its southeast quadrant. -/
theorem agreeOutsideSoutheast_fullConvImage
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (fullConvImage w x) (fullConvImage w y) r s := by
  intro i j hij
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage]
  unfold fullConv
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  split_ifs with hab
  · rw [hxy (i - a) (j - b) (by
      intro hse
      apply hij
      exact ⟨le_trans hse.1 (Nat.sub_le i a),
        le_trans hse.2 (Nat.sub_le j b)⟩)]
  · rfl

/-- A genuine shared-bias convolution/ReLU layer preserves the same
southeast support invariant. -/
theorem agreeOutsideSoutheast_sharedLayerEval
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (bias : ℝ)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (sharedLayerEval w bias x)
      (sharedLayerEval w bias y) r s := by
  intro i j hij
  by_cases hir : i < rows + kRows - 1
  · by_cases hjc : j < cols + kCols - 1
    · have hconv : fullConv w x i j = fullConv w y i j := by
        have hfull := agreeOutsideSoutheast_fullConvImage w hxy i j hij
        simpa [zeroExtend, hir, hjc, fullConvImage] using hfull
      simp [zeroExtend, hir, hjc, sharedLayerEval, layerEval,
        constantImage, hconv]
    · simp [zeroExtend, hjc]
  · simp [zeroExtend, hir]

/-- Every finite shared-bias ReLU network preserves southeast-supported
differences. -/
theorem agreeOutsideSoutheast_sharedBiasNetwork_eval
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (net.eval x) (net.eval y) r s := by
  induction net with
  | nil => exact hxy
  | cons kernel bias tail ih =>
      exact ih (agreeOutsideSoutheast_sharedLayerEval kernel bias hxy)

/-- The explicitly output-typed network interface preserves southeast
support as well. -/
theorem agreeOutsideSoutheast_sharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (net.eval x) (net.eval y) r s := by
  intro i j hij
  by_cases hir : i < outRows
  · by_cases hjc : j < outCols
    · have hir' : i < net.net.outRows := by simpa [net.rows_eq] using hir
      have hjc' : j < net.net.outCols := by simpa [net.cols_eq] using hjc
      have hnet := agreeOutsideSoutheast_sharedBiasNetwork_eval
        net.net hxy i j hij
      simpa [zeroExtend, hir, hjc, hir', hjc', SharedBiasNetworkTo.eval]
        using hnet
    · simp [zeroExtend, hjc]
  · simp [zeroExtend, hir]

/-- Two images may differ only strictly southeast of `(r,s)`: they agree
outside the southeast quadrant and also agree at its root. -/
def AgreeOutsideStrictSoutheast {rows cols : ℕ}
    (x y : Image rows cols) (r s : ℕ) : Prop :=
  AgreeOutsideSoutheast x y r s ∧
    zeroExtend x r s = zeroExtend y r s

/-- Strict southeast variation implies agreement on the entire northwest
rectangle rooted at the same coordinate.  Here "strict" means the southeast
quadrant with its root removed, not strict inequality in both coordinates. -/
theorem AgreeOutsideStrictSoutheast.northwestAgree
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    NorthwestAgree x y r s := by
  intro i hi j hj
  by_cases hir : i = r
  · subst i
    by_cases hjs : j = s
    · subst j
      exact hxy.2
    · exact hxy.1 r j (by
        intro hse
        exact hjs (Nat.le_antisymm hj hse.2))
  · exact hxy.1 i j (by
      intro hse
      exact hir (Nat.le_antisymm hi hse.1))

/-- An arbitrary finite shared-bias ReLU network keeps a root-punctured
southeast variation root-punctured: it remains in the southeast quadrant and
the root output is unchanged. -/
theorem agreeOutsideStrictSoutheast_sharedBiasNetwork_eval
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast (net.eval x) (net.eval y) r s := by
  refine ⟨agreeOutsideSoutheast_sharedBiasNetwork_eval net hxy.1, ?_⟩
  exact northwestAgree_sharedBiasNetwork_eval net hxy.northwestAgree
    r le_rfl s le_rfl

/-- Root-punctured southeast support is also preserved through the explicitly
typed network interface. -/
theorem agreeOutsideStrictSoutheast_sharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast (net.eval x) (net.eval y) r s := by
  refine ⟨agreeOutsideSoutheast_sharedBiasNetworkTo_eval net hxy.1, ?_⟩
  exact northwestAgree_sharedBiasNetworkTo_eval net hxy.northwestAgree
    r le_rfl s le_rfl

end OneChannelCNNUniversality
