import OneChannelCNNUniversality.SharedBiasGridNetwork

/-!
# Northwest causality for repeated expansive convolution

Full convolution at `(p,q)` reads only input sites weakly northwest of that
coordinate.  This file packages that causal invariant for arbitrary finite
iterations and for the Pascal signal transform used by protected selection.
-/

namespace OneChannelCNNUniversality

/-- Two equally sized images agree throughout the finite northwest rectangle
rooted at the natural coordinate `(p,q)`. -/
def NorthwestAgree {rows cols : ℕ} (x y : Image rows cols) (p q : ℕ) : Prop :=
  ∀ i, i ≤ p → ∀ j, j ≤ q → zeroExtend x i j = zeroExtend y i j

/-- One full-convolution layer preserves agreement on every fixed northwest
rectangle. -/
theorem northwestAgree_fullConvImage
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    {x y : Image rows cols} {p q : ℕ} (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (fullConvImage w x) (fullConvImage w y) p q := by
  intro i hi j hj
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage]
  unfold fullConv
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  split_ifs with hab
  · rw [hxy (i - a) (le_trans (Nat.sub_le i a) hi)
      (j - b) (le_trans (Nat.sub_le j b) hj)]
  · rfl

/-- A genuine shared-scalar-bias convolution/ReLU layer is northwest causal.
The conclusion includes both the broadcast bias and the nonlinear activation,
not merely the underlying linear convolution. -/
theorem northwestAgree_sharedLayerEval
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (b : ℝ)
    {x y : Image rows cols} {p q : ℕ} (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (sharedLayerEval w b x) (sharedLayerEval w b y) p q := by
  intro i hi j hj
  by_cases hir : i < rows + kRows - 1
  · by_cases hjc : j < cols + kCols - 1
    · have hconv : fullConv w x i j = fullConv w y i j := by
        have hfull := northwestAgree_fullConvImage w hxy i hi j hj
        simpa [zeroExtend, hir, hjc, fullConvImage] using hfull
      simp [zeroExtend, hir, hjc, sharedLayerEval, layerEval,
        constantImage, hconv]
    · simp [zeroExtend, hjc]
  · simp [zeroExtend, hir]

/-- Arbitrarily many expansive convolution layers preserve northwest
agreement, independently of the kernel coefficients. -/
theorem northwestAgree_iterateFullConv
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps : ℕ) {x y : Image rows cols} {p q : ℕ}
    (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (iterateFullConv w steps x)
      (iterateFullConv w steps y) p q := by
  induction steps generalizing rows cols with
  | zero => exact hxy
  | succ steps ih =>
      exact ih (northwestAgree_fullConvImage w hxy)

/-- Every finite one-channel expansive shared-bias ReLU network is northwest
causal.  Thus arbitrary later layers cannot make information stored outside a
fixed northwest rectangle flow back into that rectangle. -/
theorem northwestAgree_sharedBiasNetwork_eval
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    {x y : Image rows cols} {p q : ℕ} (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (net.eval x) (net.eval y) p q := by
  induction net with
  | nil => exact hxy
  | cons kernel bias tail ih =>
      exact ih (northwestAgree_sharedLayerEval kernel bias hxy)

/-- The explicitly output-typed shared-bias network interface inherits the
same northwest-causality law. -/
theorem northwestAgree_sharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} {p q : ℕ} (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (net.eval x) (net.eval y) p q := by
  intro i hi j hj
  by_cases hir : i < outRows
  · by_cases hjc : j < outCols
    · have hir' : i < net.net.outRows := by simpa [net.rows_eq] using hir
      have hjc' : j < net.net.outCols := by simpa [net.cols_eq] using hjc
      have hnet := northwestAgree_sharedBiasNetwork_eval net.net hxy i hi j hj
      simpa [zeroExtend, hir, hjc, hir', hjc', SharedBiasNetworkTo.eval] using hnet
    · simp [zeroExtend, hjc]
  · simp [zeroExtend, hir]

/-- The protected Pascal signal at a target depends only on the input's
northwest rectangle rooted at that target.  In particular, changing strictly
southeast stored features cannot alter a later northwest activation. -/
theorem protectedLinearizedPascalSignal_eq_of_northwestAgree
    {rows cols : ℕ} (rowSteps extraColSteps : ℕ)
    {x y : Image rows cols} (i : Fin rows) (j : Fin cols)
    (hxy : NorthwestAgree x y i j) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x i j =
      protectedLinearizedPascalSignal rowSteps extraColSteps y i j := by
  have hfirst := northwestAgree_fullConvImage
    horizontalAccumulationKernel hxy
  have hhorizontal := northwestAgree_iterateFullConv
    horizontalAccumulationKernel extraColSteps hfirst
  have hvertical := northwestAgree_iterateFullConv
    verticalAccumulationKernel rowSteps hhorizontal
  exact hvertical i le_rfl j le_rfl

end OneChannelCNNUniversality
