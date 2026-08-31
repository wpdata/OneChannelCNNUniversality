import OneChannelCNNUniversality.SharedBiasCausality

/-!
# A depth lower bound for long-range nonlinear interaction

For a depth-`L` expansive `2 × 2` network, one output coordinate sees an
input window of radius at most `L` in each spatial direction.  Consequently,
if two scalar variables are placed in columns `0` and `L + 1`, no final
feature can depend on both variables.  This remains true after an arbitrary
affine readout.

The four-corner mixed difference of every such readout is therefore zero,
whereas the product of the two endpoint variables has mixed difference four.
The resulting uniform error lower bound is one.  In particular, error
strictly below one on the four endpoint-sign inputs forces depth at least
`L + 1`.
-/

namespace OneChannelCNNUniversality

/-- Agreement on the square input window of radius `radius` ending at the
natural output coordinate `(p,q)`.  Zero extension makes the definition
valid without separate boundary cases. -/
def ReceptiveAgree {rows cols : ℕ} (radius p q : ℕ)
    (x y : Image rows cols) : Prop :=
  ∀ i, p - radius ≤ i → i ≤ p →
    ∀ j, q - radius ≤ j → j ≤ q →
      zeroExtend x i j = zeroExtend y i j

/-- One expansive `2 × 2` shared-bias layer consumes at most one unit of
receptive radius. -/
theorem receptiveAgree_sharedLayerEval
    {rows cols : ℕ} (w : Kernel 2 2) (bias : ℝ)
    {x y : Image rows cols} {radius p q : ℕ}
    (hxy : ReceptiveAgree (radius + 1) p q x y) :
    ReceptiveAgree radius p q
      (sharedLayerEval w bias x) (sharedLayerEval w bias y) := by
  intro i hiLower hiUpper j hjLower hjUpper
  by_cases hir : i < rows + 2 - 1
  · by_cases hjc : j < cols + 2 - 1
    · rw [zeroExtend_of_lt _ hir hjc, zeroExtend_of_lt _ hir hjc]
      change relu (fullConv w x i j + bias) =
        relu (fullConv w y i j + bias)
      congr 1
      congr 1
      unfold fullConv
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      split_ifs with hab
      · rw [hxy (i - a) (by omega) (by omega)
          (j - b) (by omega) (by omega)]
      · rfl
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hjc),
        zeroExtend_col_outside _ (Nat.le_of_not_gt hjc)]
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hir),
      zeroExtend_row_outside _ (Nat.le_of_not_gt hir)]

/-- Exact depth-dependent receptive-field theorem for arbitrary finite
expansive `2 × 2` one-channel shared-bias ReLU networks. -/
theorem sharedBiasNetwork_eval_eq_of_receptiveAgree
    {rows cols : ℕ} (net : SharedBiasNetwork 2 2 rows cols)
    {x y : Image rows cols} {p q : ℕ}
    (hxy : ReceptiveAgree net.depth p q x y) :
    zeroExtend (net.eval x) p q = zeroExtend (net.eval y) p q := by
  induction net with
  | nil =>
      exact hxy p (by simp [SharedBiasNetwork.depth]) le_rfl
        q (by simp [SharedBiasNetwork.depth]) le_rfl
  | cons kernel bias tail ih =>
      apply ih
      apply receptiveAgree_sharedLayerEval kernel bias
      simpa [SharedBiasNetwork.depth] using hxy

/-- A one-row image whose only possibly nonzero entries are the two endpoints
in columns `0` and `L + 1`. -/
def endpointSignImage (L : ℕ) (left right : ℝ) : Image 1 (L + 2) :=
  fun _ j ↦
    if (j : ℕ) = 0 then left
    else if (j : ℕ) = L + 1 then right
    else 0

/-- The continuous target that multiplies the two separated endpoint
coordinates. -/
def endpointProduct (L : ℕ) (x : Image 1 (L + 2)) : ℝ :=
  x (0 : Fin 1) ⟨0, by omega⟩ * x (0 : Fin 1) ⟨L + 1, by omega⟩

@[simp] theorem endpointProduct_endpointSignImage
    (L : ℕ) (left right : ℝ) :
    endpointProduct L (endpointSignImage L left right) = left * right := by
  simp [endpointProduct, endpointSignImage]

/-- The endpoint-product target is continuous on the entire finite image
space, hence also on every compact subset used below. -/
theorem continuous_endpointProduct (L : ℕ) :
    Continuous (endpointProduct L) := by
  unfold endpointProduct
  fun_prop

/-- The four endpoint-sign images used by the lower bound. -/
def endpointCornerSet (L : ℕ) : Set (Image 1 (L + 2)) :=
  {endpointSignImage L (-1) (-1), endpointSignImage L (-1) 1,
    endpointSignImage L 1 (-1), endpointSignImage L 1 1}

theorem endpointCornerSet_finite (L : ℕ) :
    (endpointCornerSet L).Finite := by
  simp [endpointCornerSet]

theorem endpointCornerSet_compact (L : ℕ) :
    IsCompact (endpointCornerSet L) :=
  (endpointCornerSet_finite L).isCompact

private theorem endpointSignImage_zeroExtend_eq_of_right_ne
    (L : ℕ) (left right₁ right₂ : ℝ) (i j : ℕ)
    (hj : j ≠ L + 1) :
    zeroExtend (endpointSignImage L left right₁) i j =
      zeroExtend (endpointSignImage L left right₂) i j := by
  by_cases hi : i < 1
  · by_cases hjin : j < L + 2
    · simp [zeroExtend, endpointSignImage, hi, hjin, hj]
    · simp [zeroExtend, hi, hjin]
  · simp [zeroExtend, hi]

private theorem endpointSignImage_zeroExtend_eq_of_left_ne
    (L : ℕ) (left₁ left₂ right : ℝ) (i j : ℕ)
    (hj : j ≠ 0) :
    zeroExtend (endpointSignImage L left₁ right) i j =
      zeroExtend (endpointSignImage L left₂ right) i j := by
  by_cases hi : i < 1
  · by_cases hjin : j < L + 2
    · simp [zeroExtend, endpointSignImage, hi, hjin, hj]
    · simp [zeroExtend, hi, hjin]
  · simp [zeroExtend, hi]

/-- At output columns through `L`, changing only the right endpoint cannot
change any feature, independently of network depth. -/
theorem endpoint_eval_eq_of_same_left
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (left right₁ right₂ : ℝ) (p q : ℕ) (hq : q ≤ L) :
    zeroExtend (net.eval (endpointSignImage L left right₁)) p q =
      zeroExtend (net.eval (endpointSignImage L left right₂)) p q := by
  apply sharedBiasNetwork_eval_eq_of_receptiveAgree net
  intro i _hiLower _hiUpper j _hjLower hjUpper
  apply endpointSignImage_zeroExtend_eq_of_right_ne
  omega

/-- If network depth is at most `L`, then output columns strictly beyond `L`
cannot see the left endpoint in column zero. -/
theorem endpoint_eval_eq_of_same_right
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (hdepth : net.depth ≤ L) (left₁ left₂ right : ℝ)
    (p q : ℕ) (hq : L < q) :
    zeroExtend (net.eval (endpointSignImage L left₁ right)) p q =
      zeroExtend (net.eval (endpointSignImage L left₂ right)) p q := by
  apply sharedBiasNetwork_eval_eq_of_receptiveAgree net
  intro i _hiLower _hiUpper j hjLower _hjUpper
  apply endpointSignImage_zeroExtend_eq_of_left_ne
  have hpositive : 0 < q - net.depth := by omega
  omega

/-- The four-corner mixed difference of every depth-at-most-`L` network and
every affine final readout is exactly zero.  This is the key statement that
extends the locality obstruction to arbitrary output weights. -/
theorem endpoint_mixedDifference_zero
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (hdepth : net.depth ≤ L)
    (weight : Image net.outRows net.outCols) (constant : ℝ) :
    net.realize weight constant (endpointSignImage L (-1) (-1)) +
        net.realize weight constant (endpointSignImage L 1 1) =
      net.realize weight constant (endpointSignImage L (-1) 1) +
        net.realize weight constant (endpointSignImage L 1 (-1)) := by
  let xmm := endpointSignImage L (-1) (-1)
  let xmp := endpointSignImage L (-1) 1
  let xpm := endpointSignImage L 1 (-1)
  let xpp := endpointSignImage L 1 1
  have hfeature (i : Fin net.outRows) (j : Fin net.outCols) :
      net.eval xmm i j + net.eval xpp i j =
        net.eval xmp i j + net.eval xpm i j := by
    by_cases hq : (j : ℕ) ≤ L
    · have hmm : net.eval xmm i j = net.eval xmp i j := by
        have h := endpoint_eval_eq_of_same_left L net (-1) (-1) 1 i j hq
        simpa [xmm, xmp] using h
      have hpp : net.eval xpp i j = net.eval xpm i j := by
        have h := endpoint_eval_eq_of_same_left L net 1 1 (-1) i j hq
        simpa [xpp, xpm] using h
      rw [hmm, hpp]
    · have hq' : L < (j : ℕ) := by omega
      have hmm : net.eval xmm i j = net.eval xpm i j := by
        have h := endpoint_eval_eq_of_same_right
          L net hdepth (-1) 1 (-1) i j hq'
        simpa [xmm, xpm] using h
      have hpp : net.eval xpp i j = net.eval xmp i j := by
        have h := endpoint_eval_eq_of_same_right
          L net hdepth 1 (-1) 1 i j hq'
        simpa [xpp, xmp] using h
      rw [hmm, hpp]
      ring
  have hrow (i : Fin net.outRows) :
      (∑ j, weight i j * net.eval xmm i j) +
          (∑ j, weight i j * net.eval xpp i j) =
        (∑ j, weight i j * net.eval xmp i j) +
          (∑ j, weight i j * net.eval xpm i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← mul_add, hfeature i j, mul_add]
  have hsum :
      (∑ i, ∑ j, weight i j * net.eval xmm i j) +
          (∑ i, ∑ j, weight i j * net.eval xpp i j) =
        (∑ i, ∑ j, weight i j * net.eval xmp i j) +
          (∑ i, ∑ j, weight i j * net.eval xpm i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact hrow i
  change
    ((∑ i, ∑ j, weight i j * net.eval xmm i j) + constant) +
        ((∑ i, ∑ j, weight i j * net.eval xpp i j) + constant) =
      ((∑ i, ∑ j, weight i j * net.eval xmp i j) + constant) +
        ((∑ i, ∑ j, weight i j * net.eval xpm i j) + constant)
  linarith

/-- Quantitative four-point lower bound: at least one endpoint-sign input has
absolute product-approximation error at least one.  The bound is sharp, since
the zero function has error exactly one on these four inputs. -/
theorem endpoint_four_point_error_lower_bound
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (hdepth : net.depth ≤ L)
    (weight : Image net.outRows net.outCols) (constant : ℝ) :
    1 ≤ max
      |net.realize weight constant (endpointSignImage L (-1) (-1)) - 1|
      (max
        |net.realize weight constant (endpointSignImage L (-1) 1) + 1|
        (max
          |net.realize weight constant (endpointSignImage L 1 (-1)) + 1|
          |net.realize weight constant (endpointSignImage L 1 1) - 1|)) := by
  let rmm := net.realize weight constant (endpointSignImage L (-1) (-1))
  let rmp := net.realize weight constant (endpointSignImage L (-1) 1)
  let rpm := net.realize weight constant (endpointSignImage L 1 (-1))
  let rpp := net.realize weight constant (endpointSignImage L 1 1)
  have hmixed : rmm + rpp = rmp + rpm := by
    exact endpoint_mixedDifference_zero L net hdepth weight constant
  have hcomb : (rmm - 1) + (rpp - 1) + (-(rmp + 1)) + (-(rpm + 1)) = -4 := by
    linarith
  have htriangle :
      |(rmm - 1) + (rpp - 1) + (-(rmp + 1)) + (-(rpm + 1))| ≤
        |rmm - 1| + |rpp - 1| + |rmp + 1| + |rpm + 1| := by
    calc
      |(rmm - 1) + (rpp - 1) + (-(rmp + 1)) + (-(rpm + 1))| ≤
          |(rmm - 1) + (rpp - 1) + (-(rmp + 1))| + |-(rpm + 1)| :=
        abs_add_le _ _
      _ ≤ (|(rmm - 1) + (rpp - 1)| + |-(rmp + 1)|) +
          |-(rpm + 1)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|rmm - 1| + |rpp - 1|) + |-(rmp + 1)|) +
          |-(rpm + 1)| := by
        gcongr
        exact abs_add_le _ _
      _ = |rmm - 1| + |rpp - 1| + |rmp + 1| + |rpm + 1| := by
        rw [abs_neg, abs_neg]
  rw [hcomb] at htriangle
  norm_num at htriangle
  let errorMax := max |rmm - 1|
    (max |rmp + 1| (max |rpm + 1| |rpp - 1|))
  have hmm : |rmm - 1| ≤ errorMax := by
    exact le_max_left _ _
  have hmp : |rmp + 1| ≤ errorMax := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hpm : |rpm + 1| ≤ errorMax := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))
  have hpp : |rpp - 1| ≤ errorMax := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))
  change 1 ≤ errorMax
  linarith

/-- Approximating the endpoint product with strict error below one on the
four-point compact set forces depth at least the endpoint distance `L + 1`.
The hidden kernels, scalar biases, final weights, and final constant are all
otherwise arbitrary. -/
theorem depth_ge_endpointDistance_of_error_lt_one
    (L : ℕ) (net : SharedBiasNetwork 2 2 1 (L + 2))
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (happrox : ∀ x ∈ endpointCornerSet L,
      |net.realize weight constant x - endpointProduct L x| < 1) :
    L + 1 ≤ net.depth := by
  by_contra hnot
  have hdepth : net.depth ≤ L := by omega
  have hlower := endpoint_four_point_error_lower_bound
    L net hdepth weight constant
  have hmm := happrox (endpointSignImage L (-1) (-1)) (by
    simp [endpointCornerSet])
  have hmp := happrox (endpointSignImage L (-1) 1) (by
    simp [endpointCornerSet])
  have hpm := happrox (endpointSignImage L 1 (-1)) (by
    simp [endpointCornerSet])
  have hpp := happrox (endpointSignImage L 1 1) (by
    simp [endpointCornerSet])
  simp only [endpointProduct_endpointSignImage] at hmm hmp hpm hpp
  norm_num at hmm hmp hpm hpp
  have hmax :
      max
        |net.realize weight constant (endpointSignImage L (-1) (-1)) - 1|
        (max
          |net.realize weight constant (endpointSignImage L (-1) 1) + 1|
          (max
            |net.realize weight constant (endpointSignImage L 1 (-1)) + 1|
            |net.realize weight constant (endpointSignImage L 1 1) - 1|)) < 1 := by
    exact max_lt hmm (max_lt hmp (max_lt hpm hpp))
  linarith

end OneChannelCNNUniversality
