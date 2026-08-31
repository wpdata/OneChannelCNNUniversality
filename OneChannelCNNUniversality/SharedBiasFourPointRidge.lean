import OneChannelCNNUniversality.SharedBiasGridGate

/-!
# A protected arbitrary ridge on four registers

Three genuine expansive `2 × 2` shared-bias layers internalize the ReLU of
an arbitrary affine functional on a four-register row.  The construction is
the coefficient-of-the-first-vertical-power identity for three bilinear
kernels.  Its northern boundary is the fixed triangular filter
`(1 + z)(1 + 2z)(1 + 3z)`, so four northern outputs retain an explicit affine
left inverse.
-/

namespace OneChannelCNNUniversality

universe u

noncomputable section

/-- First coefficient in the three-path decomposition of a cubic ridge. -/
def fourPointRidgeBetaOne (r0 r1 r2 r3 : ℝ) : ℝ :=
  (r3 - r2 + r1 - r0) / 2

/-- Second coefficient in the three-path decomposition of a cubic ridge. -/
def fourPointRidgeBetaTwo (r0 r1 r2 r3 : ℝ) : ℝ :=
  -4 * r3 + 2 * r2 - r1 + r0 / 2

/-- Third coefficient in the three-path decomposition of a cubic ridge. -/
def fourPointRidgeBetaThree (r0 r1 r2 r3 : ℝ) : ℝ :=
  (9 / 2 : ℝ) * r3 - (3 / 2 : ℝ) * r2 + r1 / 2 - r0 / 6

/-- The correction which supplies the leading cubic coefficient. -/
def fourPointRidgeLeadingCorrection (r0 : ℝ) : ℝ := r0 / 6

/-- A separation parameter which makes every northern carrier coefficient
strictly positive, independently of the ridge coefficients. -/
def fourPointRidgeSeparation (r0 r1 r2 r3 : ℝ) : ℝ :=
  (|fourPointRidgeBetaThree r0 r1 r2 r3| + 5) / 4

private abbrev fpB1 (r0 r1 r2 r3 : ℝ) : ℝ :=
  fourPointRidgeBetaOne r0 r1 r2 r3

private abbrev fpB2 (r0 r1 r2 r3 : ℝ) : ℝ :=
  fourPointRidgeBetaTwo r0 r1 r2 r3

private abbrev fpB3 (r0 r1 r2 r3 : ℝ) : ℝ :=
  fourPointRidgeBetaThree r0 r1 r2 r3

private abbrev fpC (r0 : ℝ) : ℝ := fourPointRidgeLeadingCorrection r0

private abbrev fpT (r0 r1 r2 r3 : ℝ) : ℝ :=
  fourPointRidgeSeparation r0 r1 r2 r3

/-- The first bilinear kernel.  Its northern polynomial is `1 + z`; its
southern polynomial contains the leading-coefficient correction. -/
def fourPointRidgeFirstKernel (r0 r1 r2 r3 : ℝ) : Kernel 2 2 :=
  let beta1 := fourPointRidgeBetaOne r0 r1 r2 r3
  let c := fourPointRidgeLeadingCorrection r0
  let T := fourPointRidgeSeparation r0 r1 r2 r3
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) 1 i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) 1 i j +
        (deltaKernel (1 : Fin 2) (0 : Fin 2) (beta1 + c + T) i j +
          deltaKernel (1 : Fin 2) (1 : Fin 2) (c + T) i j))

/-- The second bilinear kernel, with northern polynomial `1 + 2z`. -/
def fourPointRidgeSecondKernel (r0 r1 r2 r3 : ℝ) : Kernel 2 2 :=
  let beta2 := fourPointRidgeBetaTwo r0 r1 r2 r3
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) 1 i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) 2 i j +
        deltaKernel (1 : Fin 2) (0 : Fin 2) beta2 i j)

/-- The third bilinear kernel, with northern polynomial `1 + 3z`. -/
def fourPointRidgeThirdKernel (r0 r1 r2 r3 : ℝ) : Kernel 2 2 :=
  let beta3 := fourPointRidgeBetaThree r0 r1 r2 r3
  let T := fourPointRidgeSeparation r0 r1 r2 r3
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) 1 i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) 3 i j +
        (deltaKernel (1 : Fin 2) (0 : Fin 2) (beta3 - T) i j +
          deltaKernel (1 : Fin 2) (1 : Fin 2) (-3 * T) i j))

private def fourPointRidgeFirstNorm (r0 r1 r2 r3 : ℝ) : ℝ :=
  2 + |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| +
    |fpC r0 + fpT r0 r1 r2 r3|

/-- Explicit first-layer carrier; it exceeds the full first-kernel variation
on every input with coordinate bound `M`. -/
def fourPointRidgeFirstCarrier
    (r0 r1 r2 r3 M : ℝ) : ℝ :=
  fourPointRidgeFirstNorm r0 r1 r2 r3 * M + 1

private def fourPointRidgeFirstOutputBound
    (r0 r1 r2 r3 M : ℝ) : ℝ :=
  fourPointRidgeFirstNorm r0 r1 r2 r3 * M +
    fourPointRidgeFirstCarrier r0 r1 r2 r3 M

/-- Coefficient of the first carrier in the calibrated interior output. -/
def fourPointRidgeFirstCarrierCoefficient (r0 r1 r2 r3 : ℝ) : ℝ :=
  4 * (3 + fpB2 r0 r1 r2 r3) +
    3 * (fpB3 r0 r1 r2 r3 - 4 * fpT r0 r1 r2 r3)

/-- Coefficient of the second carrier in the calibrated interior output. -/
def fourPointRidgeSecondCarrierCoefficient (r0 r1 r2 r3 : ℝ) : ℝ :=
  4 + fpB3 r0 r1 r2 r3 - 4 * fpT r0 r1 r2 r3

/-- Explicit second-layer carrier.  Its first summand linearizes layer two;
the remaining summands protect all four northern recovery coordinates after
the calibrated final bias is applied. -/
def fourPointRidgeSecondCarrier
    (r0 r1 r2 r3 gamma M : ℝ) : ℝ :=
  let beta2 := fpB2 r0 r1 r2 r3
  let D := fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3
  let B := fourPointRidgeFirstCarrier r0 r1 r2 r3 M
  let Y := fourPointRidgeFirstOutputBound r0 r1 r2 r3 M
  (3 + |beta2|) * Y + 24 * M + (12 + |D|) * B + |gamma| + 2

/-- The final shared bias cancels both earlier carriers at the interior ridge
coordinate `(1,3)` and installs the requested affine offset. -/
def fourPointRidgeThirdBias
    (r0 r1 r2 r3 gamma M : ℝ) : ℝ :=
  gamma -
    fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3 *
      fourPointRidgeFirstCarrier r0 r1 r2 r3 M -
    fourPointRidgeSecondCarrierCoefficient r0 r1 r2 r3 *
      fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M

/-- The genuine depth-three network, of shape `1 × 4 → 2 × 5 → 3 × 6 → 4 × 7`. -/
def protectedFourPointRidgeNetwork (r0 r1 r2 r3 gamma M : ℝ) :
    SharedBiasNetworkTo 2 2 1 4 4 7 :=
  SharedBiasNetworkTo.cons (fourPointRidgeFirstKernel r0 r1 r2 r3)
    (fourPointRidgeFirstCarrier r0 r1 r2 r3 M)
    (SharedBiasNetworkTo.cons (fourPointRidgeSecondKernel r0 r1 r2 r3)
      (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
      (SharedBiasNetworkTo.single (fourPointRidgeThirdKernel r0 r1 r2 r3)
        (fourPointRidgeThirdBias r0 r1 r2 r3 gamma M)))

theorem protectedFourPointRidgeNetwork_depth
    (r0 r1 r2 r3 gamma M : ℝ) :
    (protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).net.depth = 3 := by
  rfl

theorem fullConv_fourPointRidgeFirstKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (r0 r1 r2 r3 : ℝ) (p q : ℕ) :
    fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x p q =
      zeroExtend x p q +
        (if 1 ≤ q then zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p then
          (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
            zeroExtend x (p - 1) q
        else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then
          (fpC r0 + fpT r0 r1 r2 r3) *
            zeroExtend x (p - 1) (q - 1)
        else 0) := by
  unfold fourPointRidgeFirstKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_kernel_add, fullConv_deltaKernel,
    fullConv_deltaKernel]
  simp
  ring_nf

theorem fullConv_fourPointRidgeSecondKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (r0 r1 r2 r3 : ℝ) (p q : ℕ) :
    fullConv (fourPointRidgeSecondKernel r0 r1 r2 r3) x p q =
      zeroExtend x p q +
        (if 1 ≤ q then 2 * zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p then
          fpB2 r0 r1 r2 r3 * zeroExtend x (p - 1) q
        else 0) := by
  unfold fourPointRidgeSecondKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_deltaKernel]
  simp
  ring_nf

theorem fullConv_fourPointRidgeThirdKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (r0 r1 r2 r3 : ℝ) (p q : ℕ) :
    fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3) x p q =
      zeroExtend x p q +
        (if 1 ≤ q then 3 * zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p then
          (fpB3 r0 r1 r2 r3 - fpT r0 r1 r2 r3) *
            zeroExtend x (p - 1) q
        else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then
          (-3 * fpT r0 r1 r2 r3) *
            zeroExtend x (p - 1) (q - 1)
        else 0) := by
  unfold fourPointRidgeThirdKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_kernel_add, fullConv_deltaKernel,
    fullConv_deltaKernel]
  simp
  ring_nf

private theorem abs_zeroExtend_le_fourPoint
    (x : Image 1 4) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    |zeroExtend x p q| ≤ M := by
  by_cases hp : p < 1
  · by_cases hq : q < 4
    · have hp0 : p = 0 := by omega
      subst p
      simpa [zeroExtend, hq] using hbound ⟨q, hq⟩
    · simp [zeroExtend, hp, hq, hM]
  · simp [zeroExtend, hp, hM]

private theorem fourPointRidgeFirstNorm_nonneg (r0 r1 r2 r3 : ℝ) :
    0 ≤ fourPointRidgeFirstNorm r0 r1 r2 r3 := by
  dsimp [fourPointRidgeFirstNorm]
  positivity

private theorem fourPointRidgeFirstKernel_lower
    (x : Image 1 4) (r0 r1 r2 r3 M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    -(fourPointRidgeFirstNorm r0 r1 r2 r3 * M) ≤
      fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x p q := by
  rw [fullConv_fourPointRidgeFirstKernel_nat]
  have h0abs := abs_zeroExtend_le_fourPoint x M hM hbound p q
  have h1abs := abs_zeroExtend_le_fourPoint x M hM hbound p (q - 1)
  have h2abs := abs_zeroExtend_le_fourPoint x M hM hbound (p - 1) q
  have h3abs := abs_zeroExtend_le_fourPoint x M hM hbound (p - 1) (q - 1)
  have h0 := neg_abs_le (zeroExtend x p q)
  have h1 := neg_abs_le (zeroExtend x p (q - 1))
  have h2 := neg_abs_le
    ((fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
      zeroExtend x (p - 1) q)
  have h3 := neg_abs_le
    ((fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1))
  have h2abs' :
      |(fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x (p - 1) q| ≤
        |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2abs (abs_nonneg _)
  have h3abs' :
      |(fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1)| ≤
        |fpC r0 + fpT r0 r1 r2 r3| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h3abs (abs_nonneg _)
  have h0lower : -M ≤ zeroExtend x p q := by linarith
  have h1lower : -M ≤ zeroExtend x p (q - 1) := by linarith
  have h2lower :
      -(|fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M) ≤
        (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x (p - 1) q :=
    le_trans (neg_le_neg h2abs') h2
  have h3lower :
      -(|fpC r0 + fpT r0 r1 r2 r3| * M) ≤
        (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1) :=
    le_trans (neg_le_neg h3abs') h3
  have haM :
      0 ≤ |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M :=
    mul_nonneg (abs_nonneg _) hM
  have hdM : 0 ≤ |fpC r0 + fpT r0 r1 r2 r3| * M :=
    mul_nonneg (abs_nonneg _) hM
  have hnormExpand :
      (2 + |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| +
          |fpC r0 + fpT r0 r1 r2 r3|) * M =
        2 * M +
          |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M +
          |fpC r0 + fpT r0 r1 r2 r3| * M := by ring
  have hwest :
      -M ≤ (if 1 ≤ q then zeroExtend x p (q - 1) else 0) := by
    split_ifs <;> linarith
  have hsouth :
      -(|fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M) ≤
        (if 1 ≤ p then
          (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
            zeroExtend x (p - 1) q
        else 0) := by
    split_ifs <;> linarith
  have hdiag :
      -(|fpC r0 + fpT r0 r1 r2 r3| * M) ≤
        (if 1 ≤ p ∧ 1 ≤ q then
          (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1)
        else 0) := by
    split_ifs <;> linarith
  dsimp [fourPointRidgeFirstNorm]
  rw [hnormExpand]
  linarith

private theorem fourPointRidgeFirstKernel_upper
    (x : Image 1 4) (r0 r1 r2 r3 M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x p q ≤
      fourPointRidgeFirstNorm r0 r1 r2 r3 * M := by
  rw [fullConv_fourPointRidgeFirstKernel_nat]
  have h0abs := abs_zeroExtend_le_fourPoint x M hM hbound p q
  have h1abs := abs_zeroExtend_le_fourPoint x M hM hbound p (q - 1)
  have h2abs := abs_zeroExtend_le_fourPoint x M hM hbound (p - 1) q
  have h3abs := abs_zeroExtend_le_fourPoint x M hM hbound (p - 1) (q - 1)
  have h0 := le_abs_self (zeroExtend x p q)
  have h1 := le_abs_self (zeroExtend x p (q - 1))
  have h2 := le_abs_self
    ((fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
      zeroExtend x (p - 1) q)
  have h3 := le_abs_self
    ((fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1))
  have h2abs' :
      |(fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x (p - 1) q| ≤
        |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2abs (abs_nonneg _)
  have h3abs' :
      |(fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1)| ≤
        |fpC r0 + fpT r0 r1 r2 r3| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h3abs (abs_nonneg _)
  have h0upper : zeroExtend x p q ≤ M := by linarith
  have h1upper : zeroExtend x p (q - 1) ≤ M := by linarith
  have h2upper :
      (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x (p - 1) q ≤
        |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M :=
    le_trans h2 h2abs'
  have h3upper :
      (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1) ≤
        |fpC r0 + fpT r0 r1 r2 r3| * M :=
    le_trans h3 h3abs'
  have haM :
      0 ≤ |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M :=
    mul_nonneg (abs_nonneg _) hM
  have hdM : 0 ≤ |fpC r0 + fpT r0 r1 r2 r3| * M :=
    mul_nonneg (abs_nonneg _) hM
  have hnormExpand :
      (2 + |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| +
          |fpC r0 + fpT r0 r1 r2 r3|) * M =
        2 * M +
          |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M +
          |fpC r0 + fpT r0 r1 r2 r3| * M := by ring
  have hwest :
      (if 1 ≤ q then zeroExtend x p (q - 1) else 0) ≤ M := by
    split_ifs <;> linarith
  have hsouth :
      (if 1 ≤ p then
        (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x (p - 1) q
      else 0) ≤
        |fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3| * M := by
    split_ifs <;> linarith
  have hdiag :
      (if 1 ≤ p ∧ 1 ≤ q then
        (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x (p - 1) (q - 1)
      else 0) ≤ |fpC r0 + fpT r0 r1 r2 r3| * M := by
    split_ifs <;> linarith
  dsimp [fourPointRidgeFirstNorm]
  rw [hnormExpand]
  linarith

private theorem protectedFourPointRidgeNetwork_first_linear_nat
    (x : Image 1 4) (r0 r1 r2 r3 _gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) (hp : p < 2) (hq : q < 5) :
    zeroExtend
        (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
          (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) p q =
      fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x p q +
        fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
  rw [zeroExtend_of_lt _ hp hq]
  change relu
      (fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x p q +
        fourPointRidgeFirstCarrier r0 r1 r2 r3 M) = _
  rw [relu_of_nonneg]
  have hlower := fourPointRidgeFirstKernel_lower
    x r0 r1 r2 r3 M hM hbound p q
  dsimp [fourPointRidgeFirstCarrier]
  linarith

private theorem firstLayer_zeroExtend_nonneg
    (x : Image 1 4) (r0 r1 r2 r3 M : ℝ) (p q : ℕ) :
    0 ≤ zeroExtend
      (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
        (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) p q := by
  by_cases hp : p < 2
  · by_cases hq : q < 5
    · rw [zeroExtend_of_lt _ hp hq]
      change 0 ≤ max _ 0
      exact le_max_right _ _
    · simp [zeroExtend, hp, hq]
  · simp [zeroExtend, hp]

private theorem firstLayer_zeroExtend_upper
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) :
    zeroExtend
        (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
          (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) p q ≤
      fourPointRidgeFirstOutputBound r0 r1 r2 r3 M := by
  by_cases hp : p < 2
  · by_cases hq : q < 5
    · rw [protectedFourPointRidgeNetwork_first_linear_nat
        x r0 r1 r2 r3 gamma M hM hbound p q hp hq]
      have hu := fourPointRidgeFirstKernel_upper
        x r0 r1 r2 r3 M hM hbound p q
      simpa [fourPointRidgeFirstOutputBound] using
        add_le_add_right hu (fourPointRidgeFirstCarrier r0 r1 r2 r3 M)
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hq)]
      dsimp [fourPointRidgeFirstOutputBound, fourPointRidgeFirstCarrier]
      have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
      positivity
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hp)]
    dsimp [fourPointRidgeFirstOutputBound, fourPointRidgeFirstCarrier]
    have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
    positivity

private theorem fourPointRidgeSecondCarrier_nonneg
    (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M) :
    0 ≤ fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M := by
  dsimp [fourPointRidgeSecondCarrier, fourPointRidgeFirstOutputBound,
    fourPointRidgeFirstCarrier]
  have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
  positivity

private theorem protectedFourPointRidgeNetwork_second_linear_nat
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (p q : ℕ) (hp : p < 3) (hq : q < 6) :
    zeroExtend
        (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
          (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
          (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
            (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) p q =
      fullConv (fourPointRidgeSecondKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
            (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) p q +
        fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M := by
  rw [zeroExtend_of_lt _ hp hq]
  change relu (_ + fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M) = _
  rw [relu_of_nonneg]
  rw [fullConv_fourPointRidgeSecondKernel_nat]
  have hy0 := firstLayer_zeroExtend_nonneg x r0 r1 r2 r3 M p q
  have hy1 := firstLayer_zeroExtend_nonneg x r0 r1 r2 r3 M p (q - 1)
  have hy2 := firstLayer_zeroExtend_nonneg x r0 r1 r2 r3 M (p - 1) q
  have hy2upper := firstLayer_zeroExtend_upper
    x r0 r1 r2 r3 gamma M hM hbound (p - 1) q
  have hbetaLower := neg_abs_le
    (fpB2 r0 r1 r2 r3 * zeroExtend
      (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
        (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) (p - 1) q)
  have hbetaAbs :
      |fpB2 r0 r1 r2 r3 * zeroExtend
          (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
            (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x) (p - 1) q| ≤
        |fpB2 r0 r1 r2 r3| *
          fourPointRidgeFirstOutputBound r0 r1 r2 r3 M := by
    rw [abs_mul, abs_of_nonneg hy2]
    exact mul_le_mul_of_nonneg_left hy2upper (abs_nonneg _)
  have hY : 0 ≤ fourPointRidgeFirstOutputBound r0 r1 r2 r3 M := by
    dsimp [fourPointRidgeFirstOutputBound, fourPointRidgeFirstCarrier]
    have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
    positivity
  have hB : 0 ≤ fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
    dsimp [fourPointRidgeFirstCarrier]
    have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
    positivity
  have hbetaY :
      0 ≤ |fpB2 r0 r1 r2 r3| *
        fourPointRidgeFirstOutputBound r0 r1 r2 r3 M :=
    mul_nonneg (abs_nonneg _) hY
  have hDY :
      0 ≤ (12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) *
        fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by positivity
  dsimp [fourPointRidgeSecondCarrier]
  split_ifs <;> nlinarith [abs_nonneg gamma]

private theorem fullConv_first_north
    (x : Image 1 4) (r0 r1 r2 r3 : ℝ) (q : ℕ) (_hq : q < 4) :
    fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x 0 q =
      zeroExtend x 0 q + if 1 ≤ q then zeroExtend x 0 (q - 1) else 0 := by
  rw [fullConv_fourPointRidgeFirstKernel_nat]
  simp

private theorem fullConv_first_south
    (x : Image 1 4) (r0 r1 r2 r3 : ℝ) (q : ℕ) :
    fullConv (fourPointRidgeFirstKernel r0 r1 r2 r3) x 1 q =
      (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) *
          zeroExtend x 0 q +
        (if 1 ≤ q then
          (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x 0 (q - 1)
        else 0) := by
  rw [fullConv_fourPointRidgeFirstKernel_nat]
  simp [zeroExtend]

private theorem secondLayer_north_formula
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (q : ℕ) (hq : q < 4) :
    zeroExtend
        (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
          (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
          (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
            (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 0 q =
      (zeroExtend x 0 q + if 1 ≤ q then zeroExtend x 0 (q - 1) else 0) +
        (if 1 ≤ q then
          2 * (zeroExtend x 0 (q - 1) +
            if 1 ≤ q - 1 then zeroExtend x 0 (q - 2) else 0)
        else 0) +
        (if q = 0 then fourPointRidgeFirstCarrier r0 r1 r2 r3 M
          else 3 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M) +
        fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_second_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 0 q (by omega) (by omega),
    fullConv_fourPointRidgeSecondKernel_nat]
  simp only [if_neg (by omega : ¬1 ≤ (0 : ℕ)), add_zero]
  rw [protectedFourPointRidgeNetwork_first_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 0 q (by omega) (by omega),
    fullConv_first_north x r0 r1 r2 r3 q hq]
  by_cases hq0 : q = 0
  · subst q
    simp
  · have hq1 : 1 ≤ q := by omega
    have hsub : q - 1 - 1 = q - 2 := by omega
    rw [if_pos hq1,
      protectedFourPointRidgeNetwork_first_linear_nat
        x r0 r1 r2 r3 gamma M hM hbound 0 (q - 1) (by omega) (by omega),
      fullConv_first_north x r0 r1 r2 r3 (q - 1) (by omega), if_neg hq0,
      hsub]
    simp only [if_pos hq1]
    ring

private theorem secondLayer_south_formula
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (q : ℕ) (hq : 2 ≤ q) (hq4 : q < 4) :
    zeroExtend
        (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
          (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
          (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
            (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 1 q =
      (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3 +
          fpB2 r0 r1 r2 r3) * zeroExtend x 0 q +
        (fpC r0 + fpT r0 r1 r2 r3 +
          2 * (fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3) +
          fpB2 r0 r1 r2 r3) * zeroExtend x 0 (q - 1) +
        2 * (fpC r0 + fpT r0 r1 r2 r3) * zeroExtend x 0 (q - 2) +
        (3 + fpB2 r0 r1 r2 r3) *
          fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
        fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_second_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 1 q (by omega) (by omega),
    fullConv_fourPointRidgeSecondKernel_nat]
  simp only [if_pos (by omega : 1 ≤ q), if_pos (by omega : 1 ≤ (1 : ℕ)),
    Nat.reduceSubDiff]
  rw [protectedFourPointRidgeNetwork_first_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 1 q (by omega) (by omega),
    protectedFourPointRidgeNetwork_first_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 1 (q - 1) (by omega) (by omega),
    protectedFourPointRidgeNetwork_first_linear_nat
      x r0 r1 r2 r3 gamma M hM hbound 0 q (by omega) (by omega),
    fullConv_first_south, fullConv_first_south,
    fullConv_first_north x r0 r1 r2 r3 q hq4]
  simp only [if_pos (by omega : 1 ≤ q), if_pos (by omega : 1 ≤ q - 1)]
  have hsub : q - 1 - 1 = q - 2 := by omega
  rw [hsub]
  ring

private theorem fourPointRidge_polynomial_identity
    (r0 r1 r2 r3 x0 x1 x2 x3 : ℝ) :
    let a := fpB1 r0 r1 r2 r3 + fpC r0 + fpT r0 r1 r2 r3
    let b := fpC r0 + fpT r0 r1 r2 r3
    let d := fpB3 r0 r1 r2 r3 - fpT r0 r1 r2 r3
    let e := -3 * fpT r0 r1 r2 r3
    let h13 := (a + fpB2 r0 r1 r2 r3) * x3 +
      (b + 2 * a + fpB2 r0 r1 r2 r3) * x2 + 2 * b * x1
    let h12 := (a + fpB2 r0 r1 r2 r3) * x2 +
      (b + 2 * a + fpB2 r0 r1 r2 r3) * x1 + 2 * b * x0
    let h03 := x3 + 3 * x2 + 2 * x1
    let h02 := x2 + 3 * x1 + 2 * x0
    h13 + 3 * h12 + d * h03 + e * h02 =
      r0 * x0 + r1 * x1 + r2 * x2 + r3 * x3 := by
  dsimp [fpB1, fpB2, fpB3, fpC, fpT, fourPointRidgeBetaOne,
    fourPointRidgeBetaTwo, fourPointRidgeBetaThree,
    fourPointRidgeLeadingCorrection, fourPointRidgeSeparation]
  ring

/-- The interior coordinate `(1,3)` is the requested arbitrary four-point
affine ReLU. -/
theorem protectedFourPointRidgeNetwork_ridge
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend
        ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 1 3 =
      relu (r0 * x 0 0 + r1 * x 0 1 + r2 * x 0 2 + r3 * x 0 3 + gamma) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
            (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
            (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
              (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 1 3 +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M) = _
  rw [fullConv_fourPointRidgeThirdKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (3 : ℕ)),
    if_pos (by omega : 1 ≤ (1 : ℕ)),
    if_pos (by omega : 1 ≤ (1 : ℕ) ∧ 1 ≤ (3 : ℕ)), Nat.reduceSubDiff]
  rw [secondLayer_south_formula x r0 r1 r2 r3 gamma M hM hbound 3 (by omega) (by omega),
    secondLayer_south_formula x r0 r1 r2 r3 gamma M hM hbound 2 (by omega) (by omega),
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 3 (by omega),
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 2 (by omega)]
  simp only [if_pos (by omega : 1 ≤ (3 : ℕ)),
    if_pos (by omega : 1 ≤ (2 : ℕ)),
    if_pos (by omega : 1 ≤ (2 : ℕ) - 1),
    if_neg (by omega : (3 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 0),
    Nat.reduceSubDiff]
  have hpoly := fourPointRidge_polynomial_identity
    r0 r1 r2 r3 (x 0 0) (x 0 1) (x 0 2) (x 0 3)
  congr 1
  dsimp [fourPointRidgeThirdBias, fourPointRidgeFirstCarrierCoefficient,
    fourPointRidgeSecondCarrierCoefficient]
  have hz0 : zeroExtend x 0 0 = x 0 0 := zeroExtend_of_lt _ (by omega) (by omega)
  have hz1 : zeroExtend x 0 1 = x 0 1 := zeroExtend_of_lt _ (by omega) (by omega)
  have hz2 : zeroExtend x 0 2 = x 0 2 := zeroExtend_of_lt _ (by omega) (by omega)
  have hz3 : zeroExtend x 0 3 = x 0 3 := zeroExtend_of_lt _ (by omega) (by omega)
  rw [hz0, hz1, hz2, hz3]
  dsimp at hpoly
  nlinarith

private theorem fourPointRidgeSeparation_zero_margin
    (r0 r1 r2 r3 : ℝ) :
    2 ≤ 4 * fpT r0 r1 r2 r3 - fpB3 r0 r1 r2 r3 - 3 := by
  dsimp [fpT, fpB3, fourPointRidgeSeparation]
  linarith [le_abs_self (fourPointRidgeBetaThree r0 r1 r2 r3)]

private theorem fourPointRidgeSeparation_succ_margin
    (r0 r1 r2 r3 : ℝ) :
    5 ≤ 4 * fpT r0 r1 r2 r3 - fpB3 r0 r1 r2 r3 := by
  dsimp [fpT, fpB3, fourPointRidgeSeparation]
  linarith [le_abs_self (fourPointRidgeBetaThree r0 r1 r2 r3)]

private theorem fourPointRidgeSecondCarrier_guard
    (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M) :
    24 * M +
        (12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) *
          fourPointRidgeFirstCarrier r0 r1 r2 r3 M + |gamma| + 1 ≤
      fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M := by
  dsimp [fourPointRidgeSecondCarrier]
  have hY : 0 ≤ fourPointRidgeFirstOutputBound r0 r1 r2 r3 M := by
    dsimp [fourPointRidgeFirstOutputBound, fourPointRidgeFirstCarrier]
    have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
    positivity
  have hlead :
      0 ≤ (3 + |fpB2 r0 r1 r2 r3|) *
        fourPointRidgeFirstOutputBound r0 r1 r2 r3 M := by positivity
  linarith

private theorem fourPointRidgeFirstCarrier_pos
    (r0 r1 r2 r3 M : ℝ) (hM : 0 ≤ M) :
    0 < fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
  dsimp [fourPointRidgeFirstCarrier]
  have hn := fourPointRidgeFirstNorm_nonneg r0 r1 r2 r3
  positivity

private theorem fourPoint_input_linear_lower
    (x : Image 1 4) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (a0 a1 a2 a3 : ℝ)
    (ha0 : |a0| ≤ 1) (ha1 : |a1| ≤ 6) (ha2 : |a2| ≤ 11)
    (ha3 : |a3| ≤ 6) :
    -(24 * M) ≤ a0 * x 0 3 + a1 * x 0 2 + a2 * x 0 1 + a3 * x 0 0 := by
  have h0 := hbound 3
  have h1 := hbound 2
  have h2 := hbound 1
  have h3 := hbound 0
  have t0 : -(1 * M) ≤ a0 * x 0 3 := by
    calc
      -(1 * M) ≤ -(|a0| * M) := by nlinarith
      _ ≤ -|a0 * x 0 3| := by
        rw [abs_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h0 (abs_nonneg a0))
      _ ≤ _ := neg_abs_le _
  have t1 : -(6 * M) ≤ a1 * x 0 2 := by
    calc
      -(6 * M) ≤ -(|a1| * M) := by nlinarith
      _ ≤ -|a1 * x 0 2| := by
        rw [abs_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h1 (abs_nonneg a1))
      _ ≤ _ := neg_abs_le _
  have t2 : -(11 * M) ≤ a2 * x 0 1 := by
    calc
      -(11 * M) ≤ -(|a2| * M) := by nlinarith
      _ ≤ -|a2 * x 0 1| := by
        rw [abs_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h2 (abs_nonneg a2))
      _ ≤ _ := neg_abs_le _
  have t3 : -(6 * M) ≤ a3 * x 0 0 := by
    calc
      -(6 * M) ≤ -(|a3| * M) := by nlinarith
      _ ≤ -|a3 * x 0 0| := by
        rw [abs_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h3 (abs_nonneg a3))
      _ ≤ _ := neg_abs_le _
  nlinarith

private theorem fourPoint_north_pre_nonneg
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (q : ℕ) (hq : q < 4) :
    0 ≤
      fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
            (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
            (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
              (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 0 q +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [fullConv_fourPointRidgeThirdKernel_nat]
  simp only [if_neg (by omega : ¬1 ≤ (0 : ℕ)),
    if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ q)), add_zero]
  rw [secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound q hq]
  by_cases hq0 : q = 0
  · subst q
    simp only [if_neg (by omega : ¬1 ≤ (0 : ℕ)), add_zero]
    rw [show zeroExtend x 0 0 = x 0 0 by
      exact zeroExtend_of_lt _ (by omega) (by omega)]
    have hx := hbound 0
    have hxl := neg_abs_le (x 0 0)
    have hB := (fourPointRidgeFirstCarrier_pos r0 r1 r2 r3 M hM).le
    have hmargin := fourPointRidgeSeparation_zero_margin r0 r1 r2 r3
    have hL := fourPointRidgeSecondCarrier_nonneg r0 r1 r2 r3 gamma M hM
    have hmarginL := mul_le_mul_of_nonneg_right hmargin hL
    have hguard := fourPointRidgeSecondCarrier_guard r0 r1 r2 r3 gamma M hM
    have hD := le_abs_self (fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3)
    have hscalar :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) ≤
          1 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3 := by
      linarith
    have hDB :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M ≤
          (1 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
      exact mul_le_mul_of_nonneg_right hscalar hB
    have hg := neg_le_abs gamma
    dsimp [fourPointRidgeThirdBias,
      fourPointRidgeSecondCarrierCoefficient]
    nlinarith
  · have hq1 : 1 ≤ q := by omega
    rw [if_pos hq1,
      secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound (q - 1) (by omega),
      if_neg hq0]
    simp only [if_pos (by omega : 1 ≤ q)]
    have hinput : -(24 * M) ≤
        zeroExtend x 0 q + 3 * zeroExtend x 0 (q - 1) +
          2 * zeroExtend x 0 (q - 2) +
          3 * (zeroExtend x 0 (q - 1) +
            3 * zeroExtend x 0 (q - 2) +
            2 * zeroExtend x 0 (q - 3)) := by
      have hz (k : ℕ) : |zeroExtend x 0 k| ≤ M :=
        abs_zeroExtend_le_fourPoint x M hM hbound 0 k
      have z0 := neg_abs_le (zeroExtend x 0 q)
      have z1 := neg_abs_le (zeroExtend x 0 (q - 1))
      have z2 := neg_abs_le (zeroExtend x 0 (q - 2))
      have z3 := neg_abs_le (zeroExtend x 0 (q - 3))
      nlinarith [hz q, hz (q - 1), hz (q - 2), hz (q - 3)]
    have hB := (fourPointRidgeFirstCarrier_pos r0 r1 r2 r3 M hM).le
    have hmargin := fourPointRidgeSeparation_succ_margin r0 r1 r2 r3
    have hL := fourPointRidgeSecondCarrier_nonneg r0 r1 r2 r3 gamma M hM
    have hmarginL := mul_le_mul_of_nonneg_right hmargin hL
    have hguard := fourPointRidgeSecondCarrier_guard r0 r1 r2 r3 gamma M hM
    have hD := le_abs_self (fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3)
    have hscalar :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) ≤
          12 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3 := by
      linarith
    have hDB :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M ≤
          (12 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
      exact mul_le_mul_of_nonneg_right hscalar hB
    have hscalarSix :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) ≤
          6 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3 := by
      linarith
    have hDBSix :
        -(12 + |fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3|) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M ≤
          (6 - fourPointRidgeFirstCarrierCoefficient r0 r1 r2 r3) *
            fourPointRidgeFirstCarrier r0 r1 r2 r3 M := by
      exact mul_le_mul_of_nonneg_right hscalarSix hB
    have hx0l : -M ≤ x 0 0 := by
      linarith [neg_abs_le (x 0 0), hbound 0]
    have hx1l : -M ≤ x 0 1 := by
      linarith [neg_abs_le (x 0 1), hbound 1]
    have hx2l : -M ≤ x 0 2 := by
      linarith [neg_abs_le (x 0 2), hbound 2]
    have hx3l : -M ≤ x 0 3 := by
      linarith [neg_abs_le (x 0 3), hbound 3]
    have hinputOne : -(24 * M) ≤ x 0 1 + 6 * x 0 0 := by
      nlinarith
    have hinputTwo : -(24 * M) ≤ x 0 2 + 6 * x 0 1 + 11 * x 0 0 := by
      nlinarith
    have hinputThree :
        -(24 * M) ≤ x 0 3 + 6 * x 0 2 + 11 * x 0 1 + 6 * x 0 0 := by
      nlinarith
    have hg := neg_le_abs gamma
    dsimp [fourPointRidgeThirdBias,
      fourPointRidgeSecondCarrierCoefficient]
    interval_cases q
    · norm_num [zeroExtend] at ⊢
      ring_nf at hmarginL hDBSix hinputOne ⊢
      linarith
    · norm_num [zeroExtend] at ⊢
      have hinputTwo' :
          -(24 * M) ≤ x 0 ⟨2, by omega⟩ + 6 * x 0 1 + 11 * x 0 0 := by
        simpa using hinputTwo
      ring_nf at hmarginL hDB hinputTwo' ⊢
      linarith
    · norm_num [zeroExtend] at ⊢
      have hinputThree' :
          -(24 * M) ≤ x 0 ⟨3, by omega⟩ + 6 * x 0 ⟨2, by omega⟩ +
            11 * x 0 1 + 6 * x 0 0 := by
        simpa using hinputThree
      ring_nf at hmarginL hDB hinputThree' ⊢
      linarith

private theorem protectedFourPointRidgeNetwork_north_raw
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (q : ℕ) (hq : q < 4) :
    zeroExtend ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 0 q =
      fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
            (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
            (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
              (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 0 q +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
            (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
            (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
              (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 0 q +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M) =
      fullConv (fourPointRidgeThirdKernel r0 r1 r2 r3)
          (sharedLayerEval (fourPointRidgeSecondKernel r0 r1 r2 r3)
            (fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M)
            (sharedLayerEval (fourPointRidgeFirstKernel r0 r1 r2 r3)
              (fourPointRidgeFirstCarrier r0 r1 r2 r3 M) x)) 0 q +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M
  exact relu_of_nonneg
    (fourPoint_north_pre_nonneg x r0 r1 r2 r3 gamma M hM hbound q hq)

theorem protectedFourPointRidgeNetwork_north_zero
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 0 0 =
      x 0 0 + fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
        fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_north_raw x r0 r1 r2 r3 gamma M hM hbound 0 (by omega),
    fullConv_fourPointRidgeThirdKernel_nat,
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 0 (by omega)]
  simp

theorem protectedFourPointRidgeNetwork_north_one
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 0 1 =
      x 0 1 + 6 * x 0 0 +
        6 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
        4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_north_raw x r0 r1 r2 r3 gamma M hM hbound 1 (by omega),
    fullConv_fourPointRidgeThirdKernel_nat,
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 1 (by omega),
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 0 (by omega)]
  simp
  ring

theorem protectedFourPointRidgeNetwork_north_two
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 0 2 =
      x 0 2 + 6 * x 0 1 + 11 * x 0 0 +
        12 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
        4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_north_raw x r0 r1 r2 r3 gamma M hM hbound 2 (by omega),
    fullConv_fourPointRidgeThirdKernel_nat,
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 2 (by omega),
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 1 (by omega)]
  simp
  ring

theorem protectedFourPointRidgeNetwork_north_three
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    zeroExtend ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) 0 3 =
      x 0 3 + 6 * x 0 2 + 11 * x 0 1 + 6 * x 0 0 +
        12 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
        4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
        fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
  rw [protectedFourPointRidgeNetwork_north_raw x r0 r1 r2 r3 gamma M hM hbound 3 (by omega),
    fullConv_fourPointRidgeThirdKernel_nat,
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 3 (by omega),
    secondLayer_north_formula x r0 r1 r2 r3 gamma M hM hbound 2 (by omega)]
  simp
  ring

/-- Explicit triangular affine decoder for the four northern registers. -/
noncomputable def fourPointRidgeAffineRecovery
    (r0 r1 r2 r3 gamma M : ℝ) (z : Image 4 7) : Image 1 4 :=
  let B := fourPointRidgeFirstCarrier r0 r1 r2 r3 M
  let L := fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M
  let b := fourPointRidgeThirdBias r0 r1 r2 r3 gamma M
  let x0 := z 0 0 - (B + L + b)
  let x1 := z 0 1 - 6 * x0 - (6 * B + 4 * L + b)
  let x2 := z 0 2 - 6 * x1 - 11 * x0 - (12 * B + 4 * L + b)
  let x3 := z 0 3 - 6 * x2 - 11 * x1 - 6 * x0 - (12 * B + 4 * L + b)
  fun _ j ↦ if (j : ℕ) = 0 then x0 else if (j : ℕ) = 1 then x1
    else if (j : ℕ) = 2 then x2 else x3

theorem protectedFourPointRidgeNetwork_affineRecovery
    (x : Image 1 4) (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) :
    fourPointRidgeAffineRecovery r0 r1 r2 r3 gamma M
        ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x) = x := by
  have h0 :
      (protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x 0 0 =
        x 0 0 + fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
          fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
          fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
    simpa using protectedFourPointRidgeNetwork_north_zero
      x r0 r1 r2 r3 gamma M hM hbound
  have h1 :
      (protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x 0 1 =
        x 0 1 + 6 * x 0 0 +
          6 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
          4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
          fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
    simpa using protectedFourPointRidgeNetwork_north_one
      x r0 r1 r2 r3 gamma M hM hbound
  have h2 :
      (protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x 0 2 =
        x 0 2 + 6 * x 0 1 + 11 * x 0 0 +
          12 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
          4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
          fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
    simpa using protectedFourPointRidgeNetwork_north_two
      x r0 r1 r2 r3 gamma M hM hbound
  have h3 :
      (protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval x 0 3 =
        x 0 3 + 6 * x 0 2 + 11 * x 0 1 + 6 * x 0 0 +
          12 * fourPointRidgeFirstCarrier r0 r1 r2 r3 M +
          4 * fourPointRidgeSecondCarrier r0 r1 r2 r3 gamma M +
          fourPointRidgeThirdBias r0 r1 r2 r3 gamma M := by
    simpa using protectedFourPointRidgeNetwork_north_three
      x r0 r1 r2 r3 gamma M hM hbound
  funext i j
  fin_cases i
  fin_cases j <;>
    simp [fourPointRidgeAffineRecovery, h0, h1, h2, h3] <;> ring

theorem protectedFourPointRidgeNetwork_injectiveOn
    {X : Type u} {K : Set X} (F : X → Image 1 4)
    (r0 r1 r2 r3 gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ∀ j, |F x 0 j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedFourPointRidgeNetwork
        r0 r1 r2 r3 gamma M).eval (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  calc
    F x = fourPointRidgeAffineRecovery r0 r1 r2 r3 gamma M
        ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval (F x)) :=
      (protectedFourPointRidgeNetwork_affineRecovery
        (F x) r0 r1 r2 r3 gamma M hM (hbound x hx)).symm
    _ = fourPointRidgeAffineRecovery r0 r1 r2 r3 gamma M
        ((protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M).eval (F y)) :=
      congrArg (fourPointRidgeAffineRecovery r0 r1 r2 r3 gamma M) heval
    _ = F y := protectedFourPointRidgeNetwork_affineRecovery
      (F y) r0 r1 r2 r3 gamma M hM (hbound y hy)

theorem exists_protectedFourPointRidgeNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → Image 1 4) (hF : ContinuousFeatureOn K F)
    (hFinjective : Set.InjOn F K) (r0 r1 r2 r3 gamma : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 4 4 7,
        net.net.depth = 3 ∧
        (∀ x ∈ K,
          zeroExtend (net.eval (F x)) 1 3 =
            relu (r0 * F x 0 0 + r1 * F x 0 1 +
              r2 * F x 0 2 + r3 * F x 0 3 + gamma) ∧
          fourPointRidgeAffineRecovery r0 r1 r2 r3 gamma M
            (net.eval (F x)) = F x) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  refine ⟨M, hM, protectedFourPointRidgeNetwork r0 r1 r2 r3 gamma M,
    protectedFourPointRidgeNetwork_depth r0 r1 r2 r3 gamma M, ?_, ?_⟩
  · intro x hx
    have hxbound : ∀ j, |F x 0 j| ≤ M := fun j ↦ by
      have := hbound x hx 0 j
      simpa using this.le
    exact ⟨protectedFourPointRidgeNetwork_ridge
        (F x) r0 r1 r2 r3 gamma M hM.le hxbound,
      protectedFourPointRidgeNetwork_affineRecovery
        (F x) r0 r1 r2 r3 gamma M hM.le hxbound⟩
  · exact protectedFourPointRidgeNetwork_injectiveOn
      F r0 r1 r2 r3 gamma M hM.le
      (fun x hx j ↦ by
        have := hbound x hx 0 j
        simpa using this.le)
      hFinjective

end

end OneChannelCNNUniversality
