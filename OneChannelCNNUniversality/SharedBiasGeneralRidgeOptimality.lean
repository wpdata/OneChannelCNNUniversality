import OneChannelCNNUniversality.SharedBiasDepthLowerBound
import OneChannelCNNUniversality.SharedBiasGeneralRidgeNetwork

/-!
# Sharp depth for an endpoint affine-ReLU ridge

Place two variables at columns `0` and `L + 1` of a one-row input and consider

\[
  x \longmapsto \mathrm{ReLU}(x_0+x_{L+1}).
\]

On the four endpoint-sign inputs this target takes the values `0,0,0,2`, so
its mixed difference is two.  Every affine readout of a depth-at-most-`L`
expansive `2 × 2` shared-bias network has mixed difference zero by receptive
locality.  The triangle inequality therefore gives the sharp four-point
error lower bound `1/2`.

For endpoint distance at least two, the protected arbitrary-width ridge theorem
supplies the matching exact-depth construction.  A one-coordinate affine
readout exposes its certified target feature.
-/

namespace OneChannelCNNUniversality

/-- The affine-ReLU ridge coupling the two separated endpoint coordinates. -/
def endpointReluSum (L : ℕ) (x : Image 1 (L + 2)) : ℝ :=
  relu (x (0 : Fin 1) ⟨0, by omega⟩ +
    x (0 : Fin 1) ⟨L + 1, by omega⟩)

@[simp] theorem endpointReluSum_endpointSignImage
    (L : ℕ) (left right : ℝ) :
    endpointReluSum L (endpointSignImage L left right) =
      relu (left + right) := by
  simp [endpointReluSum, endpointSignImage]

/-- The endpoint affine-ReLU ridge is continuous on the full input space. -/
theorem continuous_endpointReluSum (L : ℕ) :
    Continuous (endpointReluSum L) := by
  unfold endpointReluSum relu
  fun_prop

/-- Coefficients selecting the two endpoints with unit weight. -/
def endpointReluSumWeights (L : ℕ) : Fin (L + 2) → ℝ :=
  fun j ↦
    (if j = (0 : Fin (L + 2)) then 1 else 0) +
      if j = ⟨L + 1, by omega⟩ then 1 else 0

/-- The endpoint coefficient vector computes the sum of the two endpoint
coordinates. -/
theorem endpointReluSumWeights_dot (L : ℕ) (x : Image 1 (L + 2)) :
    ∑ j : Fin (L + 2), endpointReluSumWeights L j * x 0 j =
      x 0 ⟨0, by omega⟩ + x 0 ⟨L + 1, by omega⟩ := by
  classical
  simp [endpointReluSumWeights, add_mul, Finset.sum_add_distrib]

/-- Quantitative four-corner obstruction for the endpoint affine-ReLU
ridge.  The constant `1/2` is sharp on these four points. -/
theorem endpointReluSum_four_point_error_lower_bound
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (hdepth : net.depth ≤ L)
    (weight : Image net.outRows net.outCols) (constant : ℝ) :
    (1 : ℝ) / 2 ≤ max
      |net.realize weight constant (endpointSignImage L (-1) (-1))|
      (max
        |net.realize weight constant (endpointSignImage L (-1) 1)|
        (max
          |net.realize weight constant (endpointSignImage L 1 (-1))|
          |net.realize weight constant (endpointSignImage L 1 1) - 2|)) := by
  let rmm := net.realize weight constant (endpointSignImage L (-1) (-1))
  let rmp := net.realize weight constant (endpointSignImage L (-1) 1)
  let rpm := net.realize weight constant (endpointSignImage L 1 (-1))
  let rpp := net.realize weight constant (endpointSignImage L 1 1)
  have hmixed : rmm + rpp = rmp + rpm := by
    exact endpoint_mixedDifference_zero L net hdepth weight constant
  have hcomb : rmm + (rpp - 2) + (-rmp) + (-rpm) = -2 := by
    linarith
  have htriangle :
      |rmm + (rpp - 2) + (-rmp) + (-rpm)| ≤
        |rmm| + |rpp - 2| + |rmp| + |rpm| := by
    calc
      |rmm + (rpp - 2) + (-rmp) + (-rpm)| ≤
          |rmm + (rpp - 2) + (-rmp)| + |-rpm| :=
        abs_add_le _ _
      _ ≤ (|rmm + (rpp - 2)| + |-rmp|) + |-rpm| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|rmm| + |rpp - 2|) + |-rmp|) + |-rpm| := by
        gcongr
        exact abs_add_le _ _
      _ = |rmm| + |rpp - 2| + |rmp| + |rpm| := by
        rw [abs_neg, abs_neg]
  rw [hcomb] at htriangle
  norm_num at htriangle
  let errorMax := max |rmm|
    (max |rmp| (max |rpm| |rpp - 2|))
  have hmm : |rmm| ≤ errorMax := le_max_left _ _
  have hmp : |rmp| ≤ errorMax :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hpm : |rpm| ≤ errorMax :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hpp : |rpp - 2| ≤ errorMax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  change (1 : ℝ) / 2 ≤ errorMax
  linarith

/-- Uniform error strictly below `1/2` on the four endpoint-sign inputs
forces depth at least the endpoint distance `L + 1`. -/
theorem depth_ge_endpointDistance_of_endpointReluSum_error_lt_half
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (happrox : ∀ x ∈ endpointCornerSet L,
      |net.realize weight constant x - endpointReluSum L x| < (1 : ℝ) / 2) :
    L + 1 ≤ net.depth := by
  by_contra hnot
  have hdepth : net.depth ≤ L := by omega
  have hlower := endpointReluSum_four_point_error_lower_bound
    L net hdepth weight constant
  have hmm := happrox (endpointSignImage L (-1) (-1)) (by
    simp [endpointCornerSet])
  have hmp := happrox (endpointSignImage L (-1) 1) (by
    simp [endpointCornerSet])
  have hpm := happrox (endpointSignImage L 1 (-1)) (by
    simp [endpointCornerSet])
  have hpp := happrox (endpointSignImage L 1 1) (by
    simp [endpointCornerSet])
  simp only [endpointReluSum_endpointSignImage] at hmm hmp hpm hpp
  norm_num [relu] at hmm hmp hpm hpp
  have hmax :
      max
        |net.realize weight constant (endpointSignImage L (-1) (-1))|
        (max
          |net.realize weight constant (endpointSignImage L (-1) 1)|
          (max
            |net.realize weight constant (endpointSignImage L 1 (-1))|
            |net.realize weight constant (endpointSignImage L 1 1) - 2|)) <
        (1 : ℝ) / 2 := by
    exact max_lt hmm (max_lt hmp (max_lt hpm hpp))
  linarith

/-- A point-mass affine readout on the explicit output rectangle, transported
to the underlying dependently sized network. -/
def sharedBiasNetworkToPointReadoutWeight
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (row : Fin outRows) (col : Fin outCols) :
    Image net.net.outRows net.net.outCols :=
  fun i j ↦
    if i = Fin.cast net.rows_eq.symm row then
      if j = Fin.cast net.cols_eq.symm col then 1 else 0
    else 0

/-- The transported point-mass readout extracts exactly the selected explicit
output coordinate. -/
theorem sharedBiasNetworkTo_pointReadout
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (row : Fin outRows) (col : Fin outCols) (x : Image inRows inCols) :
    net.net.realize (sharedBiasNetworkToPointReadoutWeight net row col) 0 x =
      net.eval x row col := by
  classical
  simp [SharedBiasNetwork.realize, sharedBiasNetworkToPointReadoutWeight,
    SharedBiasNetworkTo.eval]
  congr 2

/-- For endpoint distance `n + 2`, a genuine network of the matching exact
depth `n + 2` realizes the endpoint affine-ReLU ridge on the four-corner
compact set through a coordinate affine readout. -/
theorem exists_exactDepth_endpointReluSum_on_corners {n : ℕ} :
    ∃ (net : SharedBiasNetworkTo 2 2 1 (n + 3)
          (n + 3) (2 * (n + 2) + 1))
      (weight : Image net.net.outRows net.net.outCols),
      net.net.depth = n + 2 ∧
        ∀ x ∈ endpointCornerSet (n + 1),
          net.net.realize weight 0 x = endpointReluSum (n + 1) x := by
  let K : Set (Image 1 (n + 3)) := endpointCornerSet (n + 1)
  let F : Image 1 (n + 3) → Image 1 (n + 3) := fun x ↦ x
  let w : Fin (n + 3) → ℝ := endpointReluSumWeights (n + 1)
  have hK : IsCompact K := by
    simpa [K] using endpointCornerSet_compact (n + 1)
  have hF : ContinuousFeatureOn K F := by
    simpa [F] using continuousFeatureOn_identity K
  obtain ⟨net, _offset, hdepth, hbehavior⟩ :=
    exists_protectedGeneralRidgeNetwork_behavior_on_compact
      (n := n) hK F hF w 0
  let row : Fin (n + 3) := ⟨1, by omega⟩
  let col : Fin (2 * (n + 2) + 1) := ⟨n + 2, by omega⟩
  let weight : Image net.net.outRows net.net.outCols :=
    sharedBiasNetworkToPointReadoutWeight net row col
  refine ⟨net, weight, hdepth, ?_⟩
  intro x hx
  calc
    net.net.realize weight 0 x = net.eval x row col := by
      exact sharedBiasNetworkTo_pointReadout net row col x
    _ = zeroExtend (net.eval x) 1 (n + 2) := by
      symm
      exact zeroExtend_of_lt _ (by omega) (by omega)
    _ = relu ((∑ j : Fin (n + 3), w j * F x 0 j) + 0) := by
      exact (hbehavior x hx).1
    _ = endpointReluSum (n + 1) x := by
      rw [endpointReluSumWeights_dot]
      simp [F, endpointReluSum]

end OneChannelCNNUniversality
