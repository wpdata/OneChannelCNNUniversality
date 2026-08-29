import OneChannelCNNUniversality.SharedBiasSupport

/-!
# Internal seed transport between shared-bias selection blocks

A later protected-selection block needs an input of the form `V + c`.  This
file realizes that new constant seed by a genuine expansive shared-bias ReLU
layer.  Because the preceding block has a ReLU output, its image is
nonnegative; a nonnegative bias therefore leaves ReLU in its linear regime.
-/

namespace OneChannelCNNUniversality

/-- Adding the same image to both inputs does not change the southeast
support of their difference. -/
theorem AgreeOutsideSoutheast.add_right
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) (z : Image rows cols) :
    AgreeOutsideSoutheast (x + z) (y + z) r s := by
  intro i j hij
  rw [zeroExtend_add, zeroExtend_add, hxy i j hij]

/-- The root-punctured version is likewise invariant under a common
additive carrier. -/
theorem AgreeOutsideStrictSoutheast.add_right
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) (z : Image rows cols) :
    AgreeOutsideStrictSoutheast (x + z) (y + z) r s := by
  refine ⟨hxy.1.add_right z, ?_⟩
  rw [zeroExtend_add, zeroExtend_add, hxy.2]

/-- A genuine one-layer network that embeds its input by the northwest
delta kernel and broadcasts a fresh scalar seed over the expanded output. -/
def sharedBiasSeedLayer {rows cols : ℕ} (c : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1) (cols + 2 - 1) :=
  SharedBiasNetworkTo.single expansiveIdentityKernel c

/-- On a nonnegative image and with a nonnegative seed, the seed layer is
exactly linear: northwest delta convolution plus the new constant image. -/
theorem sharedBiasSeedLayer_eval_of_nonnegative
    {rows cols : ℕ} {x : Image rows cols} {c : ℝ}
    (hx : ImageNonnegative x) (hc : 0 ≤ c) :
    (sharedBiasSeedLayer c).eval x =
      fullConvImage expansiveIdentityKernel x +
        constantImage (rows + 2 - 1) (cols + 2 - 1) c := by
  funext i j
  change relu (fullConv expansiveIdentityKernel x i j + c) =
    fullConv expansiveIdentityKernel x i j + c
  apply relu_of_nonneg
  rw [fullConv_expansiveIdentityKernel_nat]
  exact add_nonneg (zeroExtend_nonnegative hx i j) hc

/-- The seed layer preserves every old coordinate and adds precisely `c`. -/
theorem sharedBiasSeedLayer_original
    {rows cols : ℕ} {x : Image rows cols} {c : ℝ}
    (hx : ImageNonnegative x) (hc : 0 ≤ c)
    (i : Fin rows) (j : Fin cols) :
    (sharedBiasSeedLayer c).eval x
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨j, by omega⟩ : Fin (cols + 2 - 1)) = x i j + c := by
  rw [sharedBiasSeedLayer_eval_of_nonnegative hx hc]
  change fullConv expansiveIdentityKernel x i j + c = x i j + c
  rw [fullConv_expansiveIdentityKernel_original]

/-- A nonnegative input stays nonnegative through every shared-bias ReLU
network, including the depth-zero case. -/
theorem SharedBiasNetwork.eval_nonnegative_of_nonnegative_input
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    (x : Image rows cols) (hx : ImageNonnegative x) :
    ImageNonnegative (net.eval x) := by
  induction net with
  | nil => exact hx
  | cons kernel bias tail ih =>
      exact ih _ (sharedLayerEval_nonnegative kernel bias x)

/-- Every positive-depth shared-bias network has a nonnegative output,
without any sign assumption on its input. -/
theorem SharedBiasNetwork.eval_nonnegative_of_pos_depth
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    (x : Image rows cols) (hdepth : 0 < net.depth) :
    ImageNonnegative (net.eval x) := by
  cases net with
  | nil => simp [SharedBiasNetwork.depth] at hdepth
  | cons kernel bias tail =>
      exact tail.eval_nonnegative_of_nonnegative_input _
        (sharedLayerEval_nonnegative kernel bias x)

/-- Evaluation by an explicitly output-typed shared-bias network preserves
coordinatewise continuity of a feature family. -/
theorem SharedBiasNetworkTo.continuousFeatureOn_eval
    {X : Type*} [TopologicalSpace X] {K : Set X}
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (F : X → Image inRows inCols) (hF : ContinuousFeatureOn K F) :
    ContinuousFeatureOn K (fun x ↦ net.eval (F x)) := by
  intro i j
  simpa [SharedBiasNetworkTo.eval] using
    (net.net.toNetwork.continuousFeatureOn_eval F hF
      ⟨i, by simpa [net.rows_eq] using i.isLt⟩
      ⟨j, by simpa [net.cols_eq] using j.isLt⟩)

namespace SharedBiasNetworkTo

/-- The output-typed interface inherits nonnegativity at positive depth. -/
theorem eval_nonnegative_of_pos_depth
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols
      inRows inCols outRows outCols)
    (x : Image inRows inCols) (hdepth : 0 < net.net.depth) :
    ImageNonnegative (net.eval x) := by
  intro i j
  exact net.net.eval_nonnegative_of_pos_depth x hdepth
    ⟨i, by simpa [net.rows_eq] using i.isLt⟩
    ⟨j, by simpa [net.cols_eq] using j.isLt⟩

/-- Sequential composition with a genuine expansive seed layer between the
two supplied network blocks. -/
def appendWithSeed
    {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (c : ℝ)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols) :
    SharedBiasNetworkTo 2 2 inRows inCols outRows outCols :=
  head.append ((sharedBiasSeedLayer c).append tail)

/-- Exact evaluation formula for composition through a seed layer. -/
theorem eval_appendWithSeed_of_nonnegative
    {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols)
    {x : Image inRows inCols} {c : ℝ}
    (hx : ImageNonnegative (head.eval x)) (hc : 0 ≤ c) :
    (head.appendWithSeed c tail).eval x =
      tail.eval
        (fullConvImage expansiveIdentityKernel (head.eval x) +
          constantImage (midRows + 2 - 1) (midCols + 2 - 1) c) := by
  rw [appendWithSeed, eval_append, eval_append]
  rw [sharedBiasSeedLayer_eval_of_nonnegative hx hc]

/-- The bridge contributes exactly one additional convolution/ReLU layer. -/
theorem depth_appendWithSeed
    {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (c : ℝ)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols) :
    (head.appendWithSeed c tail).net.depth =
      head.net.depth + 1 + tail.net.depth := by
  rw [appendWithSeed, depth_append, depth_append]
  change head.net.depth + (1 + tail.net.depth) =
    head.net.depth + 1 + tail.net.depth
  omega

end SharedBiasNetworkTo

end OneChannelCNNUniversality
