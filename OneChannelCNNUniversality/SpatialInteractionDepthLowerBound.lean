import OneChannelCNNUniversality.SharedBias

/-!
# Anisotropic depth lower bounds for spatial interaction

For a depth-`d` expansive network with fixed kernel shape
`kRows × kCols`, a final feature at `(p,q)` only sees the rectangular
input window of row radius `d * (kRows - 1)` and column radius
`d * (kCols - 1)` ending at `(p,q)`.

Place two variables at `(0,0)` and `(rowDistance,colDistance)`.  If either
separation exceeds the corresponding receptive radius, no final feature can
depend on both variables.  Consequently every affine readout has zero
four-corner mixed difference, whereas the product of the two variables has
mixed difference four.  The resulting uniform error lower bound is one.

The proof is stated first for `Network`, whose hidden biases may vary with
spatial position.  The shared-scalar-bias result follows by embedding
`SharedBiasNetwork` into this more general class.
-/

namespace OneChannelCNNUniversality

/-- Agreement on an anisotropic rectangular input window ending at the
natural output coordinate `(p,q)`. -/
def RectReceptiveAgree {rows cols : ℕ}
    (rowRadius colRadius p q : ℕ) (x y : Image rows cols) : Prop :=
  ∀ i, p - rowRadius ≤ i → i ≤ p →
    ∀ j, q - colRadius ≤ j → j ≤ q →
      zeroExtend x i j = zeroExtend y i j

/-- One expansive layer consumes at most `kRows - 1` units of row radius
and `kCols - 1` units of column radius.  The bias may be different at every
output site. -/
theorem rectReceptiveAgree_layerEval
    {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    {x y : Image rows cols} {rowRadius colRadius p q : ℕ}
    (hxy : RectReceptiveAgree
      (rowRadius + (kRows - 1)) (colRadius + (kCols - 1)) p q x y) :
    RectReceptiveAgree rowRadius colRadius p q
      (layerEval w bias x) (layerEval w bias y) := by
  intro i hiLower hiUpper j hjLower hjUpper
  by_cases hir : i < rows + kRows - 1
  · by_cases hjc : j < cols + kCols - 1
    · rw [zeroExtend_of_lt _ hir hjc, zeroExtend_of_lt _ hir hjc]
      change relu (fullConv w x i j + bias ⟨i, hir⟩ ⟨j, hjc⟩) =
        relu (fullConv w y i j + bias ⟨i, hir⟩ ⟨j, hjc⟩)
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

/-- Anisotropic receptive-field dependency bound for an arbitrary finite
one-channel expansive ReLU network with position-dependent hidden biases. -/
theorem network_eval_eq_of_rectReceptiveAgree
    {kRows kCols rows cols : ℕ}
    (net : Network kRows kCols rows cols)
    {x y : Image rows cols} {p q : ℕ}
    (hxy : RectReceptiveAgree
      (net.depth * (kRows - 1)) (net.depth * (kCols - 1)) p q x y) :
    zeroExtend (net.eval x) p q = zeroExtend (net.eval y) p q := by
  induction net with
  | nil =>
      exact hxy p (by simp [Network.depth]) le_rfl
        q (by simp [Network.depth]) le_rfl
  | cons kernel bias tail ih =>
      apply ih
      apply rectReceptiveAgree_layerEval kernel bias
      simpa [Network.depth, Nat.add_mul] using hxy

/-- An image supported on two sites, the northwest corner `(0,0)` and the
site `(rowDistance,colDistance)`. -/
def twoSiteSignImage (rowDistance colDistance : ℕ)
    (left right : ℝ) : Image (rowDistance + 1) (colDistance + 1) :=
  fun i j ↦
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then left
    else if (i : ℕ) = rowDistance ∧ (j : ℕ) = colDistance then right
    else 0

/-- The continuous target which multiplies the values at the two selected
sites. -/
def twoSiteProduct (rowDistance colDistance : ℕ)
    (x : Image (rowDistance + 1) (colDistance + 1)) : ℝ :=
  x ⟨0, by omega⟩ ⟨0, by omega⟩ *
    x ⟨rowDistance, by omega⟩ ⟨colDistance, by omega⟩

@[simp] theorem twoSiteProduct_twoSiteSignImage
    (rowDistance colDistance : ℕ) (left right : ℝ)
    (hdistinct : 0 < rowDistance ∨ 0 < colDistance) :
    twoSiteProduct rowDistance colDistance
        (twoSiteSignImage rowDistance colDistance left right) = left * right := by
  have hne : ¬ (rowDistance = 0 ∧ colDistance = 0) := by omega
  simp [twoSiteProduct, twoSiteSignImage, hne]

/-- The two-site product target is continuous on the whole finite image
space. -/
theorem continuous_twoSiteProduct (rowDistance colDistance : ℕ) :
    Continuous (twoSiteProduct rowDistance colDistance) := by
  unfold twoSiteProduct
  fun_prop

/-- The full coordinatewise unit cube in the finite input image space. -/
def spatialUnitCube (rowDistance colDistance : ℕ) :
    Set (Image (rowDistance + 1) (colDistance + 1)) :=
  Set.Icc (-1) 1

/-- The spatial unit cube is compact. -/
theorem spatialUnitCube_compact (rowDistance colDistance : ℕ) :
    IsCompact (spatialUnitCube rowDistance colDistance) :=
  isCompact_Icc

private theorem twoSiteSignImage_zeroExtend_eq_of_far_ne
    (rowDistance colDistance : ℕ) (left right₁ right₂ : ℝ)
    (i j : ℕ)
    (hfar : i ≠ rowDistance ∨ j ≠ colDistance) :
    zeroExtend (twoSiteSignImage rowDistance colDistance left right₁) i j =
      zeroExtend (twoSiteSignImage rowDistance colDistance left right₂) i j := by
  have hfar' : ¬ (i = rowDistance ∧ j = colDistance) := by tauto
  by_cases hi : i < rowDistance + 1
  · by_cases hj : j < colDistance + 1
    · simp [zeroExtend, twoSiteSignImage, hi, hj, hfar']
    · simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

private theorem twoSiteSignImage_zeroExtend_eq_of_root_ne
    (rowDistance colDistance : ℕ) (left₁ left₂ right : ℝ)
    (i j : ℕ) (hroot : i ≠ 0 ∨ j ≠ 0) :
    zeroExtend (twoSiteSignImage rowDistance colDistance left₁ right) i j =
      zeroExtend (twoSiteSignImage rowDistance colDistance left₂ right) i j := by
  have hroot' : ¬ (i = 0 ∧ j = 0) := by tauto
  by_cases hi : i < rowDistance + 1
  · by_cases hj : j < colDistance + 1
    · simp [zeroExtend, twoSiteSignImage, hi, hj, hroot']
    · simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

private theorem twoSite_eval_eq_of_same_left
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (net : Network kRows kCols (rowDistance + 1) (colDistance + 1))
    (left right₁ right₂ : ℝ) (p q : ℕ)
    (hbefore : p < rowDistance ∨ q < colDistance) :
    zeroExtend (net.eval
        (twoSiteSignImage rowDistance colDistance left right₁)) p q =
      zeroExtend (net.eval
        (twoSiteSignImage rowDistance colDistance left right₂)) p q := by
  apply network_eval_eq_of_rectReceptiveAgree net
  intro i _hiLower hiUpper j _hjLower hjUpper
  apply twoSiteSignImage_zeroExtend_eq_of_far_ne
  rcases hbefore with hp | hq
  · left
    omega
  · right
    omega

private theorem twoSite_eval_eq_of_same_right
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (net : Network kRows kCols (rowDistance + 1) (colDistance + 1))
    (hseparated :
      net.depth * (kRows - 1) < rowDistance ∨
        net.depth * (kCols - 1) < colDistance)
    (left₁ left₂ right : ℝ) (p q : ℕ)
    (hp : rowDistance ≤ p) (hq : colDistance ≤ q) :
    zeroExtend (net.eval
        (twoSiteSignImage rowDistance colDistance left₁ right)) p q =
      zeroExtend (net.eval
        (twoSiteSignImage rowDistance colDistance left₂ right)) p q := by
  apply network_eval_eq_of_rectReceptiveAgree net
  intro i hiLower _hiUpper j hjLower _hjUpper
  apply twoSiteSignImage_zeroExtend_eq_of_root_ne
  rcases hseparated with hrow | hcol
  · left
    have hpositive : 0 < p - net.depth * (kRows - 1) := by omega
    omega
  · right
    have hpositive : 0 < q - net.depth * (kCols - 1) := by omega
    omega

/-- If the two selected sites do not fit in one final receptive field, every
affine readout has zero four-corner mixed difference. -/
theorem twoSite_mixedDifference_zero
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (net : Network kRows kCols (rowDistance + 1) (colDistance + 1))
    (hseparated :
      net.depth * (kRows - 1) < rowDistance ∨
        net.depth * (kCols - 1) < colDistance)
    (weight : Image net.outRows net.outCols) (constant : ℝ) :
    net.realize weight constant
          (twoSiteSignImage rowDistance colDistance (-1) (-1)) +
        net.realize weight constant
          (twoSiteSignImage rowDistance colDistance 1 1) =
      net.realize weight constant
          (twoSiteSignImage rowDistance colDistance (-1) 1) +
        net.realize weight constant
          (twoSiteSignImage rowDistance colDistance 1 (-1)) := by
  let xmm := twoSiteSignImage rowDistance colDistance (-1) (-1)
  let xmp := twoSiteSignImage rowDistance colDistance (-1) 1
  let xpm := twoSiteSignImage rowDistance colDistance 1 (-1)
  let xpp := twoSiteSignImage rowDistance colDistance 1 1
  have hfeature (i : Fin net.outRows) (j : Fin net.outCols) :
      net.eval xmm i j + net.eval xpp i j =
        net.eval xmp i j + net.eval xpm i j := by
    by_cases hbefore : (i : ℕ) < rowDistance ∨ (j : ℕ) < colDistance
    · have hmm : net.eval xmm i j = net.eval xmp i j := by
        have h := twoSite_eval_eq_of_same_left rowDistance colDistance net
          (-1) (-1) 1 i j hbefore
        simpa [xmm, xmp] using h
      have hpp : net.eval xpp i j = net.eval xpm i j := by
        have h := twoSite_eval_eq_of_same_left rowDistance colDistance net
          1 1 (-1) i j hbefore
        simpa [xpp, xpm] using h
      rw [hmm, hpp]
    · have hp : rowDistance ≤ (i : ℕ) := by omega
      have hq : colDistance ≤ (j : ℕ) := by omega
      have hmm : net.eval xmm i j = net.eval xpm i j := by
        have h := twoSite_eval_eq_of_same_right rowDistance colDistance net
          hseparated (-1) 1 (-1) i j hp hq
        simpa [xmm, xpm] using h
      have hpp : net.eval xpp i j = net.eval xmp i j := by
        have h := twoSite_eval_eq_of_same_right rowDistance colDistance net
          hseparated 1 (-1) 1 i j hp hq
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

/-- Quantitative four-point lower bound.  At least one of the four sign
inputs has product-approximation error at least one. -/
theorem twoSite_four_point_error_lower_bound
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (net : Network kRows kCols (rowDistance + 1) (colDistance + 1))
    (hseparated :
      net.depth * (kRows - 1) < rowDistance ∨
        net.depth * (kCols - 1) < colDistance)
    (weight : Image net.outRows net.outCols) (constant : ℝ) :
    1 ≤ max
      |net.realize weight constant
          (twoSiteSignImage rowDistance colDistance (-1) (-1)) - 1|
      (max
        |net.realize weight constant
          (twoSiteSignImage rowDistance colDistance (-1) 1) + 1|
        (max
          |net.realize weight constant
            (twoSiteSignImage rowDistance colDistance 1 (-1)) + 1|
          |net.realize weight constant
            (twoSiteSignImage rowDistance colDistance 1 1) - 1|)) := by
  let rmm := net.realize weight constant
    (twoSiteSignImage rowDistance colDistance (-1) (-1))
  let rmp := net.realize weight constant
    (twoSiteSignImage rowDistance colDistance (-1) 1)
  let rpm := net.realize weight constant
    (twoSiteSignImage rowDistance colDistance 1 (-1))
  let rpp := net.realize weight constant
    (twoSiteSignImage rowDistance colDistance 1 1)
  have hmixed : rmm + rpp = rmp + rpm := by
    exact twoSite_mixedDifference_zero rowDistance colDistance net
      hseparated weight constant
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

private theorem twoSiteSignImage_mem_spatialUnitCube
    (rowDistance colDistance : ℕ) (left right : ℝ)
    (hleft : left ∈ Set.Icc (-1) 1) (hright : right ∈ Set.Icc (-1) 1) :
    twoSiteSignImage rowDistance colDistance left right ∈
      spatialUnitCube rowDistance colDistance := by
  change
    (-(1 : Image (rowDistance + 1) (colDistance + 1)) ≤
      twoSiteSignImage rowDistance colDistance left right) ∧
    (twoSiteSignImage rowDistance colDistance left right ≤
      (1 : Image (rowDistance + 1) (colDistance + 1)))
  constructor
  · intro i j
    simp only [twoSiteSignImage]
    split_ifs <;> simp_all
  · intro i j
    simp only [twoSiteSignImage]
    split_ifs <;> simp_all

/-- Uniform error below one on the entire compact unit cube forces the
receptive span to reach the second site in both spatial directions. -/
theorem spatialInteraction_depth_requirements_of_error_lt_one
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (_hkRows : 2 ≤ kRows) (_hkCols : 2 ≤ kCols)
    (hdistinct : 0 < rowDistance ∨ 0 < colDistance)
    (net : Network kRows kCols (rowDistance + 1) (colDistance + 1))
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (happrox : ∀ x ∈ spatialUnitCube rowDistance colDistance,
      |net.realize weight constant x -
        twoSiteProduct rowDistance colDistance x| < 1) :
    rowDistance ≤ net.depth * (kRows - 1) ∧
      colDistance ≤ net.depth * (kCols - 1) := by
  have hnotSeparated :
      ¬ (net.depth * (kRows - 1) < rowDistance ∨
        net.depth * (kCols - 1) < colDistance) := by
    intro hseparated
    have hlower := twoSite_four_point_error_lower_bound
      rowDistance colDistance net hseparated weight constant
    have hmm := happrox
      (twoSiteSignImage rowDistance colDistance (-1) (-1))
      (twoSiteSignImage_mem_spatialUnitCube rowDistance colDistance
        (-1) (-1) (by norm_num) (by norm_num))
    have hmp := happrox
      (twoSiteSignImage rowDistance colDistance (-1) 1)
      (twoSiteSignImage_mem_spatialUnitCube rowDistance colDistance
        (-1) 1 (by norm_num) (by norm_num))
    have hpm := happrox
      (twoSiteSignImage rowDistance colDistance 1 (-1))
      (twoSiteSignImage_mem_spatialUnitCube rowDistance colDistance
        1 (-1) (by norm_num) (by norm_num))
    have hpp := happrox
      (twoSiteSignImage rowDistance colDistance 1 1)
      (twoSiteSignImage_mem_spatialUnitCube rowDistance colDistance
        1 1 (by norm_num) (by norm_num))
    rw [twoSiteProduct_twoSiteSignImage _ _ _ _ hdistinct] at hmm
    rw [twoSiteProduct_twoSiteSignImage _ _ _ _ hdistinct] at hmp
    rw [twoSiteProduct_twoSiteSignImage _ _ _ _ hdistinct] at hpm
    rw [twoSiteProduct_twoSiteSignImage _ _ _ _ hdistinct] at hpp
    norm_num at hmm hmp hpm hpp
    have hmax :
        max
          |net.realize weight constant
            (twoSiteSignImage rowDistance colDistance (-1) (-1)) - 1|
          (max
            |net.realize weight constant
              (twoSiteSignImage rowDistance colDistance (-1) 1) + 1|
            (max
              |net.realize weight constant
                (twoSiteSignImage rowDistance colDistance 1 (-1)) + 1|
              |net.realize weight constant
                (twoSiteSignImage rowDistance colDistance 1 1) - 1|)) < 1 := by
      exact max_lt hmm (max_lt hmp (max_lt hpm hpp))
    linarith
  constructor <;> omega

private theorem sharedBiasNetwork_depth_toNetwork
    {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols) :
    net.toNetwork.depth = net.depth := by
  induction net with
  | nil => rfl
  | cons kernel bias tail ih =>
      simp [SharedBiasNetwork.toNetwork, Network.depth,
        SharedBiasNetwork.depth, ih]

/-- Shared-scalar-bias specialization of the anisotropic spatial-interaction
depth lower bound. -/
theorem sharedBias_spatialInteraction_depth_requirements_of_error_lt_one
    {kRows kCols : ℕ} (rowDistance colDistance : ℕ)
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hdistinct : 0 < rowDistance ∨ 0 < colDistance)
    (net : SharedBiasNetwork kRows kCols
      (rowDistance + 1) (colDistance + 1))
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (happrox : ∀ x ∈ spatialUnitCube rowDistance colDistance,
      |net.realize weight constant x -
        twoSiteProduct rowDistance colDistance x| < 1) :
    rowDistance ≤ net.depth * (kRows - 1) ∧
      colDistance ≤ net.depth * (kCols - 1) := by
  have hgeneral := spatialInteraction_depth_requirements_of_error_lt_one
    rowDistance colDistance hkRows hkCols hdistinct net.toNetwork
      weight constant (by
        intro x hx
        simpa using happrox x hx)
  simpa [sharedBiasNetwork_depth_toNetwork net] using hgeneral

end OneChannelCNNUniversality
