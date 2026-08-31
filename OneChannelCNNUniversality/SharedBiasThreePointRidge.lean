import OneChannelCNNUniversality.SharedBiasGridGate

/-!
# A protected arbitrary ridge on three registers

Two genuine expansive `2 × 2` shared-bias layers internalize the ReLU of
an arbitrary affine functional on a three-register row.  The construction
uses the second spatial direction as one temporary channel.  The second shared
bias cancels the first-layer carrier contribution at the interior gate
coordinate, while the northern boundary omits its southern taps and therefore
retains a strictly positive carrier.  Three northern outputs form a triangular
affine code of the complete input.
-/

namespace OneChannelCNNUniversality

universe u

/-- A positive scale used both as a kernel coefficient and in the carrier. -/
def threePointRidgeScale (r0 r1 r2 : ℝ) : ℝ :=
  1 + |r0| + |r1| + |r2|

/-- One explicit carrier that linearizes the first layer and the three
northern recovery coordinates. -/
def threePointRidgeCarrier (r0 r1 r2 gamma M : ℝ) : ℝ :=
  (threePointRidgeScale r0 r1 r2 + |r0| + 2) * M + |gamma| + 1

/-- The first layer copies the northern row and also creates its
current-plus-western version one row to the south. -/
def threePointRidgeFirstKernel : Kernel 2 2 :=
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) 1 i j +
      (deltaKernel (1 : Fin 2) (0 : Fin 2) 1 i j +
        deltaKernel (1 : Fin 2) (1 : Fin 2) 1 i j)

/-- The second kernel.  At `(1,2)` its four taps combine the temporary
two-row representation into `r0*x0 + r1*x1 + r2*x2`. -/
def threePointRidgeSecondKernel (r0 r1 r2 : ℝ) : Kernel 2 2 :=
  let e := threePointRidgeScale r0 r1 r2
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) e i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) r0 i j +
        (deltaKernel (1 : Fin 2) (0 : Fin 2) (r2 - e) i j +
          deltaKernel (1 : Fin 2) (1 : Fin 2) (r1 - e - r0) i j))

/-- The second bias cancels the first-layer carrier exactly at the interior
ridge coordinate. -/
def threePointRidgeSecondBias (r0 r1 r2 gamma M : ℝ) : ℝ :=
  gamma - threePointRidgeCarrier r0 r1 r2 gamma M *
    (r1 + r2 - threePointRidgeScale r0 r1 r2)

/-- The genuine depth-two network, of shape `1 × 3 → 2 × 4 → 3 × 5`. -/
def protectedThreePointRidgeNetwork (r0 r1 r2 gamma M : ℝ) :
    SharedBiasNetworkTo 2 2 1 3 3 5 :=
  SharedBiasNetworkTo.cons threePointRidgeFirstKernel
    (threePointRidgeCarrier r0 r1 r2 gamma M)
    (SharedBiasNetworkTo.single (threePointRidgeSecondKernel r0 r1 r2)
      (threePointRidgeSecondBias r0 r1 r2 gamma M))

theorem protectedThreePointRidgeNetwork_depth
    (r0 r1 r2 gamma M : ℝ) :
    (protectedThreePointRidgeNetwork r0 r1 r2 gamma M).net.depth = 2 := by
  rfl

theorem fullConv_threePointRidgeFirstKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (p q : ℕ) :
    fullConv threePointRidgeFirstKernel x p q =
      zeroExtend x p q +
        (if 1 ≤ p then zeroExtend x (p - 1) q else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then zeroExtend x (p - 1) (q - 1) else 0) := by
  unfold threePointRidgeFirstKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_deltaKernel]
  simp
  ring_nf

theorem fullConv_threePointRidgeSecondKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (r0 r1 r2 : ℝ) (p q : ℕ) :
    fullConv (threePointRidgeSecondKernel r0 r1 r2) x p q =
      threePointRidgeScale r0 r1 r2 * zeroExtend x p q +
        (if 1 ≤ q then r0 * zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p then
          (r2 - threePointRidgeScale r0 r1 r2) *
            zeroExtend x (p - 1) q
        else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then
          (r1 - threePointRidgeScale r0 r1 r2 - r0) *
            zeroExtend x (p - 1) (q - 1)
        else 0) := by
  unfold threePointRidgeSecondKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_kernel_add, fullConv_deltaKernel,
    fullConv_deltaKernel]
  simp
  ring_nf

private theorem abs_zeroExtend_le_threePoint
    (x : Image 1 3) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    |zeroExtend x p q| ≤ M := by
  by_cases hp : p < 1
  · by_cases hq : q < 3
    · have hp0 : p = 0 := by omega
      subst p
      simpa [zeroExtend, hq] using hbound ⟨q, hq⟩
    · simp [zeroExtend, hp, hq, hM]
  · simp [zeroExtend, hp, hM]

private theorem threePointRidgeFirstKernel_lower
    (x : Image 1 3) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    -(3 * M) ≤ fullConv threePointRidgeFirstKernel x p q := by
  rw [fullConv_threePointRidgeFirstKernel_nat]
  have h0abs := abs_zeroExtend_le_threePoint x M hM hbound p q
  have h1abs := abs_zeroExtend_le_threePoint x M hM hbound (p - 1) q
  have h2abs := abs_zeroExtend_le_threePoint x M hM hbound (p - 1) (q - 1)
  have h0 := neg_abs_le (zeroExtend x p q)
  have h1 := neg_abs_le (zeroExtend x (p - 1) q)
  have h2 := neg_abs_le (zeroExtend x (p - 1) (q - 1))
  split_ifs <;> linarith

private theorem threePointRidgeScale_pos (r0 r1 r2 : ℝ) :
    0 < threePointRidgeScale r0 r1 r2 := by
  dsimp [threePointRidgeScale]
  linarith [abs_nonneg r0, abs_nonneg r1, abs_nonneg r2]

private theorem threePointRidgeCarrier_nonneg
    (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M) :
    0 ≤ threePointRidgeCarrier r0 r1 r2 gamma M := by
  dsimp [threePointRidgeCarrier]
  have he := (threePointRidgeScale_pos r0 r1 r2).le
  have hcoef : 0 ≤ threePointRidgeScale r0 r1 r2 + |r0| + 2 := by
    positivity
  positivity

private theorem threePointRidgeCarrier_ge_three_mul
    (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M) :
    3 * M ≤ threePointRidgeCarrier r0 r1 r2 gamma M := by
  have hscale : 1 ≤ threePointRidgeScale r0 r1 r2 := by
    dsimp [threePointRidgeScale]
    linarith [abs_nonneg r0, abs_nonneg r1, abs_nonneg r2]
  have hcoefficient :
      3 ≤ threePointRidgeScale r0 r1 r2 + |r0| + 2 := by
    linarith [abs_nonneg r0]
  have hmul := mul_le_mul_of_nonneg_right hcoefficient hM
  dsimp [threePointRidgeCarrier]
  linarith [abs_nonneg gamma]

private theorem protectedThreePointRidgeNetwork_first_linear
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p : Fin 2) (q : Fin 4) :
    sharedLayerEval threePointRidgeFirstKernel
        (threePointRidgeCarrier r0 r1 r2 gamma M) x p q =
      fullConv threePointRidgeFirstKernel x p q +
        threePointRidgeCarrier r0 r1 r2 gamma M := by
  change relu
      (fullConv threePointRidgeFirstKernel x p q +
        threePointRidgeCarrier r0 r1 r2 gamma M) = _
  rw [relu_of_nonneg]
  have hlower := threePointRidgeFirstKernel_lower x M hM hbound p q
  have hcarrier :=
    threePointRidgeCarrier_ge_three_mul r0 r1 r2 gamma M hM
  linarith

private theorem protectedThreePointRidgeNetwork_first_linear_nat
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ)
    (hp : p < 2) (hq : q < 4) :
    zeroExtend
        (sharedLayerEval threePointRidgeFirstKernel
          (threePointRidgeCarrier r0 r1 r2 gamma M) x) p q =
      fullConv threePointRidgeFirstKernel x p q +
        threePointRidgeCarrier r0 r1 r2 gamma M := by
  rw [zeroExtend_of_lt _ hp hq]
  exact protectedThreePointRidgeNetwork_first_linear
    x r0 r1 r2 gamma M hM hbound ⟨p, hp⟩ ⟨q, hq⟩

private theorem fullConv_threePointRidgeFirstKernel_north
    (x : Image 1 3) (j : Fin 3) :
    fullConv threePointRidgeFirstKernel x 0 j = x 0 j := by
  rw [fullConv_threePointRidgeFirstKernel_nat]
  simp [zeroExtend, j.isLt]

private theorem fullConv_threePointRidgeFirstKernel_north_zero
    (x : Image 1 3) :
    fullConv threePointRidgeFirstKernel x 0 0 = x 0 0 := by
  simpa using fullConv_threePointRidgeFirstKernel_north x (0 : Fin 3)

private theorem fullConv_threePointRidgeFirstKernel_north_one
    (x : Image 1 3) :
    fullConv threePointRidgeFirstKernel x 0 1 = x 0 1 := by
  simpa using fullConv_threePointRidgeFirstKernel_north x (1 : Fin 3)

private theorem fullConv_threePointRidgeFirstKernel_north_two
    (x : Image 1 3) :
    fullConv threePointRidgeFirstKernel x 0 2 = x 0 2 := by
  simpa using fullConv_threePointRidgeFirstKernel_north x (2 : Fin 3)

private theorem fullConv_threePointRidgeFirstKernel_south_one
    (x : Image 1 3) :
    fullConv threePointRidgeFirstKernel x 1 1 = x 0 1 + x 0 0 := by
  rw [fullConv_threePointRidgeFirstKernel_nat]
  simp [zeroExtend]

private theorem fullConv_threePointRidgeFirstKernel_south_two
    (x : Image 1 3) :
    fullConv threePointRidgeFirstKernel x 1 2 = x 0 2 + x 0 1 := by
  rw [fullConv_threePointRidgeFirstKernel_nat]
  simp [zeroExtend]

private theorem threePointRidge_northZero_margin
    (r0 r1 r2 : ℝ) :
    1 ≤ 2 * threePointRidgeScale r0 r1 r2 - r1 - r2 := by
  dsimp [threePointRidgeScale]
  linarith [abs_nonneg r0, abs_nonneg r1, abs_nonneg r2,
    le_abs_self r1, le_abs_self r2]

private theorem threePointRidge_northSucc_margin
    (r0 r1 r2 : ℝ) :
    1 ≤ 2 * threePointRidgeScale r0 r1 r2 + r0 - r1 - r2 := by
  dsimp [threePointRidgeScale]
  linarith [abs_nonneg r0, abs_nonneg r1, abs_nonneg r2,
    neg_le_abs r0, le_abs_self r1, le_abs_self r2]

private theorem threePointRidgeCarrier_ge_zeroBound
    (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M) :
    threePointRidgeScale r0 r1 r2 * M + |gamma| ≤
      threePointRidgeCarrier r0 r1 r2 gamma M := by
  dsimp [threePointRidgeCarrier]
  have hrest : 0 ≤ (|r0| + 2) * M := by positivity
  nlinarith

private theorem threePointRidgeCarrier_ge_succBound
    (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M) :
    (threePointRidgeScale r0 r1 r2 + |r0|) * M + |gamma| ≤
      threePointRidgeCarrier r0 r1 r2 gamma M := by
  dsimp [threePointRidgeCarrier]
  nlinarith

/-- The interior coordinate `(1,2)` is the requested arbitrary three-point
affine ReLU. -/
theorem protectedThreePointRidgeNetwork_ridge
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x) 1 2 =
      relu (r0 * x 0 0 + r1 * x 0 1 + r2 * x 0 2 + gamma) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (threePointRidgeSecondKernel r0 r1 r2)
          (sharedLayerEval threePointRidgeFirstKernel
            (threePointRidgeCarrier r0 r1 r2 gamma M) x) 1 2 +
        threePointRidgeSecondBias r0 r1 r2 gamma M) = _
  rw [fullConv_threePointRidgeSecondKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (2 : ℕ)),
    if_pos (by omega : 1 ≤ (1 : ℕ)),
    if_pos (by omega : 1 ≤ (1 : ℕ) ∧ 1 ≤ (2 : ℕ)),
    Nat.reduceSubDiff]
  rw [protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 1 2 (by omega) (by omega),
    protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 1 1 (by omega) (by omega),
    protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 2 (by omega) (by omega),
    protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 1 (by omega) (by omega),
    fullConv_threePointRidgeFirstKernel_south_two,
    fullConv_threePointRidgeFirstKernel_south_one,
    fullConv_threePointRidgeFirstKernel_north_two,
    fullConv_threePointRidgeFirstKernel_north_one]
  congr 1
  dsimp [threePointRidgeSecondBias]
  ring

/-- The first northern coordinate remains in the linear branch and is the
first equation of a triangular affine recovery code. -/
theorem protectedThreePointRidgeNetwork_north_zero
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x) 0 0 =
      threePointRidgeScale r0 r1 r2 * x 0 0 +
        threePointRidgeCarrier r0 r1 r2 gamma M *
          (2 * threePointRidgeScale r0 r1 r2 - r1 - r2) + gamma := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (threePointRidgeSecondKernel r0 r1 r2)
          (sharedLayerEval threePointRidgeFirstKernel
            (threePointRidgeCarrier r0 r1 r2 gamma M) x) 0 0 +
        threePointRidgeSecondBias r0 r1 r2 gamma M) = _
  rw [fullConv_threePointRidgeSecondKernel_nat]
  simp only [if_neg (by omega : ¬1 ≤ (0 : ℕ)),
    if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ (0 : ℕ))), add_zero]
  rw [protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 0 (by omega) (by omega),
    fullConv_threePointRidgeFirstKernel_north_zero]
  have hxlower := neg_abs_le (x 0 0)
  have hxbound := hbound 0
  have he := (threePointRidgeScale_pos r0 r1 r2).le
  have heMul :
      -(threePointRidgeScale r0 r1 r2 * M) ≤
        threePointRidgeScale r0 r1 r2 * x 0 0 := by
    nlinarith
  have hB := threePointRidgeCarrier_nonneg r0 r1 r2 gamma M hM
  have hmargin := threePointRidge_northZero_margin r0 r1 r2
  have hBmargin := mul_le_mul_of_nonneg_left hmargin hB
  have hcarrierBound :=
    threePointRidgeCarrier_ge_zeroBound r0 r1 r2 gamma M hM
  have hgamma := neg_le_abs gamma
  change relu
      (threePointRidgeScale r0 r1 r2 *
          (x 0 0 + threePointRidgeCarrier r0 r1 r2 gamma M) +
        threePointRidgeSecondBias r0 r1 r2 gamma M) = _
  rw [relu_of_nonneg]
  · dsimp [threePointRidgeSecondBias]
    ring
  · dsimp [threePointRidgeSecondBias]
    nlinarith

/-- The second northern coordinate is the second triangular recovery
equation. -/
theorem protectedThreePointRidgeNetwork_north_one
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x) 0 1 =
      threePointRidgeScale r0 r1 r2 * x 0 1 + r0 * x 0 0 +
        threePointRidgeCarrier r0 r1 r2 gamma M *
          (2 * threePointRidgeScale r0 r1 r2 + r0 - r1 - r2) + gamma := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (threePointRidgeSecondKernel r0 r1 r2)
          (sharedLayerEval threePointRidgeFirstKernel
            (threePointRidgeCarrier r0 r1 r2 gamma M) x) 0 1 +
        threePointRidgeSecondBias r0 r1 r2 gamma M) = _
  rw [fullConv_threePointRidgeSecondKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (1 : ℕ)),
    if_neg (by omega : ¬1 ≤ (0 : ℕ)),
    if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ (1 : ℕ))),
    add_zero, Nat.reduceSubDiff]
  rw [protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 1 (by omega) (by omega),
    protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 0 (by omega) (by omega),
    fullConv_threePointRidgeFirstKernel_north_one,
    fullConv_threePointRidgeFirstKernel_north_zero]
  have hx1abs := hbound 1
  have hx0abs := hbound 0
  have hx1lower := neg_abs_le (x 0 1)
  have hr0lower := neg_abs_le (r0 * x 0 0)
  have hr0abs : |r0 * x 0 0| ≤ |r0| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx0abs (abs_nonneg r0)
  have he := (threePointRidgeScale_pos r0 r1 r2).le
  have heMul :
      -(threePointRidgeScale r0 r1 r2 * M) ≤
        threePointRidgeScale r0 r1 r2 * x 0 1 := by
    nlinarith
  have hr0Mul : -(|r0| * M) ≤ r0 * x 0 0 := by linarith
  have hB := threePointRidgeCarrier_nonneg r0 r1 r2 gamma M hM
  have hmargin := threePointRidge_northSucc_margin r0 r1 r2
  have hBmargin := mul_le_mul_of_nonneg_left hmargin hB
  have hcarrierBound :=
    threePointRidgeCarrier_ge_succBound r0 r1 r2 gamma M hM
  have hgamma := neg_le_abs gamma
  rw [relu_of_nonneg]
  · dsimp [threePointRidgeSecondBias]
    ring
  · dsimp [threePointRidgeSecondBias]
    nlinarith

/-- The third northern coordinate completes the triangular affine recovery
code. -/
theorem protectedThreePointRidgeNetwork_north_two
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x) 0 2 =
      threePointRidgeScale r0 r1 r2 * x 0 2 + r0 * x 0 1 +
        threePointRidgeCarrier r0 r1 r2 gamma M *
          (2 * threePointRidgeScale r0 r1 r2 + r0 - r1 - r2) + gamma := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (threePointRidgeSecondKernel r0 r1 r2)
          (sharedLayerEval threePointRidgeFirstKernel
            (threePointRidgeCarrier r0 r1 r2 gamma M) x) 0 2 +
        threePointRidgeSecondBias r0 r1 r2 gamma M) = _
  rw [fullConv_threePointRidgeSecondKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (2 : ℕ)),
    if_neg (by omega : ¬1 ≤ (0 : ℕ)),
    if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ (2 : ℕ))),
    add_zero, Nat.reduceSubDiff]
  rw [protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 2 (by omega) (by omega),
    protectedThreePointRidgeNetwork_first_linear_nat
      x r0 r1 r2 gamma M hM hbound 0 1 (by omega) (by omega),
    fullConv_threePointRidgeFirstKernel_north_two,
    fullConv_threePointRidgeFirstKernel_north_one]
  have hx2abs := hbound 2
  have hx1abs := hbound 1
  have hx2lower := neg_abs_le (x 0 2)
  have hr0lower := neg_abs_le (r0 * x 0 1)
  have hr0abs : |r0 * x 0 1| ≤ |r0| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx1abs (abs_nonneg r0)
  have he := (threePointRidgeScale_pos r0 r1 r2).le
  have heMul :
      -(threePointRidgeScale r0 r1 r2 * M) ≤
        threePointRidgeScale r0 r1 r2 * x 0 2 := by
    nlinarith
  have hr0Mul : -(|r0| * M) ≤ r0 * x 0 1 := by linarith
  have hB := threePointRidgeCarrier_nonneg r0 r1 r2 gamma M hM
  have hmargin := threePointRidge_northSucc_margin r0 r1 r2
  have hBmargin := mul_le_mul_of_nonneg_left hmargin hB
  have hcarrierBound :=
    threePointRidgeCarrier_ge_succBound r0 r1 r2 gamma M hM
  have hgamma := neg_le_abs gamma
  rw [relu_of_nonneg]
  · dsimp [threePointRidgeSecondBias]
    ring
  · dsimp [threePointRidgeSecondBias]
    nlinarith

/-- The explicit triangular affine decoder. -/
noncomputable def threePointRidgeAffineRecovery (r0 r1 r2 gamma M : ℝ)
    (z : Image 3 5) : Image 1 3 :=
  let e := threePointRidgeScale r0 r1 r2
  let B := threePointRidgeCarrier r0 r1 r2 gamma M
  let C0 := B * (2 * e - r1 - r2) + gamma
  let C1 := B * (2 * e + r0 - r1 - r2) + gamma
  let x0 := (z 0 0 - C0) / e
  let x1 := (z 0 1 - r0 * x0 - C1) / e
  let x2 := (z 0 2 - r0 * x1 - C1) / e
  fun _ j ↦ if (j : ℕ) = 0 then x0 else if (j : ℕ) = 1 then x1 else x2

/-- Applying the explicit affine decoder to the complete output recovers the
three-register input exactly. -/
theorem protectedThreePointRidgeNetwork_affineRecovery
    (x : Image 1 3) (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    threePointRidgeAffineRecovery r0 r1 r2 gamma M
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x) = x := by
  have he : threePointRidgeScale r0 r1 r2 ≠ 0 :=
    ne_of_gt (threePointRidgeScale_pos r0 r1 r2)
  have hzero :
      (protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x 0 0 =
        threePointRidgeScale r0 r1 r2 * x 0 0 +
          threePointRidgeCarrier r0 r1 r2 gamma M *
            (2 * threePointRidgeScale r0 r1 r2 - r1 - r2) + gamma := by
    simpa using protectedThreePointRidgeNetwork_north_zero
      x r0 r1 r2 gamma M hM hbound
  have hone :
      (protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x 0 1 =
        threePointRidgeScale r0 r1 r2 * x 0 1 + r0 * x 0 0 +
          threePointRidgeCarrier r0 r1 r2 gamma M *
            (2 * threePointRidgeScale r0 r1 r2 + r0 - r1 - r2) + gamma := by
    simpa using protectedThreePointRidgeNetwork_north_one
      x r0 r1 r2 gamma M hM hbound
  have htwo :
      (protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval x 0 2 =
        threePointRidgeScale r0 r1 r2 * x 0 2 + r0 * x 0 1 +
          threePointRidgeCarrier r0 r1 r2 gamma M *
            (2 * threePointRidgeScale r0 r1 r2 + r0 - r1 - r2) + gamma := by
    simpa using protectedThreePointRidgeNetwork_north_two
      x r0 r1 r2 gamma M hM hbound
  funext i j
  fin_cases i
  fin_cases j
  · simp [threePointRidgeAffineRecovery, hzero]
    field_simp [he]
  · simp [threePointRidgeAffineRecovery, hzero, hone]
    field_simp [he]
    ring
  · simp [threePointRidgeAffineRecovery, hzero, hone, htwo]
    field_simp [he]
    ring

/-- Since the output has an explicit affine left inverse, the protected
network preserves every injectively parameterized bounded family. -/
theorem protectedThreePointRidgeNetwork_injectiveOn
    {X : Type u} {K : Set X} (F : X → Image 1 3)
    (r0 r1 r2 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ∀ j, |F x 0 j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedThreePointRidgeNetwork
        r0 r1 r2 gamma M).eval (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  calc
    F x = threePointRidgeAffineRecovery r0 r1 r2 gamma M
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval (F x)) :=
      (protectedThreePointRidgeNetwork_affineRecovery
        (F x) r0 r1 r2 gamma M hM (hbound x hx)).symm
    _ = threePointRidgeAffineRecovery r0 r1 r2 gamma M
        ((protectedThreePointRidgeNetwork r0 r1 r2 gamma M).eval (F y)) :=
      congrArg (threePointRidgeAffineRecovery r0 r1 r2 gamma M) heval
    _ = F y := protectedThreePointRidgeNetwork_affineRecovery
      (F y) r0 r1 r2 gamma M hM (hbound y hy)

/-- Compactness supplies one uniform input bound.  The resulting depth-two
network computes the requested arbitrary ridge, admits the explicit affine
left inverse on the compact family, and preserves injectivity. -/
theorem exists_protectedThreePointRidgeNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → Image 1 3) (hF : ContinuousFeatureOn K F)
    (hFinjective : Set.InjOn F K) (r0 r1 r2 gamma : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 3 3 5,
        net.net.depth = 2 ∧
        (∀ x ∈ K,
          zeroExtend (net.eval (F x)) 1 2 =
            relu (r0 * F x 0 0 + r1 * F x 0 1 + r2 * F x 0 2 + gamma) ∧
          threePointRidgeAffineRecovery r0 r1 r2 gamma M
            (net.eval (F x)) = F x) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  refine ⟨M, hM, protectedThreePointRidgeNetwork r0 r1 r2 gamma M,
    protectedThreePointRidgeNetwork_depth r0 r1 r2 gamma M, ?_, ?_⟩
  · intro x hx
    have hxbound : ∀ j, |F x 0 j| ≤ M := fun j ↦ by
      have := hbound x hx 0 j
      simpa using this.le
    exact ⟨protectedThreePointRidgeNetwork_ridge
        (F x) r0 r1 r2 gamma M hM.le hxbound,
      protectedThreePointRidgeNetwork_affineRecovery
        (F x) r0 r1 r2 gamma M hM.le hxbound⟩
  · exact protectedThreePointRidgeNetwork_injectiveOn
      F r0 r1 r2 gamma M hM.le
      (fun x hx j ↦ by
        have := hbound x hx 0 j
        simpa using this.le)
      hFinjective

end OneChannelCNNUniversality
