import OneChannelCNNUniversality.SharedBias
import OneChannelCNNUniversality.Register

/-!
# Boundary-generated position signals

Zero extension makes the boundary an exact source of positional information,
even when every hidden bias is spatially shared.  This file records the first
two such signals: a left-edge indicator and a northwest-corner indicator.
-/

namespace OneChannelCNNUniversality

/-- The horizontal first-difference kernel `(1, -1)` in a `2 × 2` window. -/
def horizontalBoundaryKernel : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (-1)

/-- The vertical first-difference kernel `(1, -1)` in a `2 × 2` window. -/
def verticalBoundaryKernel : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (-1)

/-- A zero convolution followed by a nonnegative shared bias is exactly constant. -/
theorem constant_seed {rows cols : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (x : Image rows cols) :
    sharedLayerEval (0 : Kernel 2 2) c x = constantImage _ _ c := by
  funext p q
  simp [sharedLayerEval, layerEval, constantImage, fullConv, hc]

/-- Apply horizontal differencing to a constant rectangle. -/
def horizontalBoundarySignal (rows cols : ℕ) (c : ℝ) :
    Image (rows + 2 - 1) (cols + 2 - 1) :=
  sharedLayerEval horizontalBoundaryKernel 0 (constantImage rows cols c)

/-- The exact positive left edge; it is zero when either input dimension is zero. -/
def expectedLeftBoundary (rows cols : ℕ) (c : ℝ) :
    Image (rows + 2 - 1) (cols + 2 - 1) :=
  fun p q ↦ if (p : ℕ) < rows ∧ 0 < cols ∧ (q : ℕ) = 0 then c else 0

/-- Horizontal differencing and ReLU retain exactly the positive left edge. -/
theorem horizontal_boundary_signal {rows cols : ℕ} {c : ℝ} (hc : 0 < c) :
    horizontalBoundarySignal rows cols c = expectedLeftBoundary rows cols c := by
  funext p q
  unfold horizontalBoundarySignal expectedLeftBoundary sharedLayerEval layerEval
  simp only [constantImage, add_zero]
  unfold horizontalBoundaryKernel
  rw [fullConv_twoTapKernel]
  by_cases hr : (p : ℕ) < rows
  · by_cases hcols : 0 < cols
    · by_cases hq0 : (q : ℕ) = 0
      · simp [horizontalBoundaryKernel, hq0, hr, hcols, constantImage,
          zeroExtend, hc.le]
      · have hq1 : 1 ≤ (q : ℕ) := by omega
        by_cases hq : (q : ℕ) < cols
        · have hqm : (q : ℕ) - 1 < cols := by omega
          simp [horizontalBoundaryKernel, hq0, hq1, hr, hcols, hq, hqm,
            constantImage, zeroExtend]
        · have hqeq : (q : ℕ) = cols := by omega
          have hqm : (q : ℕ) - 1 < cols := by omega
          have hcols1 : 1 ≤ cols := by omega
          have hcolsne : cols ≠ 0 := by omega
          simp [horizontalBoundaryKernel, hq0, hq1, hr, hcols, hq, hqeq, hqm,
            hcols1, hcolsne, constantImage, zeroExtend, hc.le]
    · have hcols0 : cols = 0 := by omega
      simp [horizontalBoundaryKernel, hcols0, constantImage, zeroExtend]
  · have hr' : rows ≤ (p : ℕ) := by omega
    simp [horizontalBoundaryKernel, hr, hr', constantImage, zeroExtend]

/-- Apply vertical differencing to the generated left edge. -/
def cornerSeed (rows cols : ℕ) (c : ℝ) :
    Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
  sharedLayerEval verticalBoundaryKernel 0 (horizontalBoundarySignal rows cols c)

/-- The exact northwest-corner seed; empty input rectangles produce zero. -/
def expectedNorthwestCorner (rows cols : ℕ) (c : ℝ) :
    Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
  fun p q ↦
    if 0 < rows ∧ 0 < cols ∧ (p : ℕ) = 0 ∧ (q : ℕ) = 0 then c else 0

/-- Vertical differencing of the left edge retains exactly its northwest corner. -/
theorem corner_seed_signal {rows cols : ℕ} {c : ℝ} (hc : 0 < c) :
    cornerSeed rows cols c = expectedNorthwestCorner rows cols c := by
  rw [cornerSeed, horizontal_boundary_signal hc]
  funext p q
  unfold expectedNorthwestCorner sharedLayerEval layerEval expectedLeftBoundary
  simp only [constantImage, add_zero]
  unfold verticalBoundaryKernel
  rw [fullConv_twoTapKernel]
  by_cases hrows : 0 < rows
  · by_cases hcols : 0 < cols
    · by_cases hp0 : (p : ℕ) = 0
      · by_cases hq0 : (q : ℕ) = 0
        · simp [verticalBoundaryKernel, hp0, hq0, hrows, hcols, zeroExtend, hc.le]
        · simp [verticalBoundaryKernel, hp0, hq0, hrows, hcols, zeroExtend]
      · have hp1 : 1 ≤ (p : ℕ) := by omega
        by_cases hp : (p : ℕ) < rows
        · have hpm : (p : ℕ) - 1 < rows := by omega
          by_cases hq0 : (q : ℕ) = 0
          · have hpout : (p : ℕ) < rows + 1 := by omega
            have hpmout : (p : ℕ) - 1 < rows + 1 := by omega
            have hqout : (q : ℕ) < cols + 1 := by omega
            simp [hp0, hp1, hp, hpm, hpout, hpmout, hq0, hqout, hrows,
              hcols, zeroExtend]
          · simp [hp0, hp1, hp, hpm, hq0, hrows, hcols, zeroExtend]
        · by_cases hpeq : (p : ℕ) = rows
          · have hpm : (p : ℕ) - 1 < rows := by omega
            by_cases hq0 : (q : ℕ) = 0
            · have hpout : (p : ℕ) < rows + 1 := by omega
              have hpmout : (p : ℕ) - 1 < rows + 1 := by omega
              have hqout : (q : ℕ) < cols + 1 := by omega
              have hrows1 : 1 ≤ rows := by omega
              have hrowsne : rows ≠ 0 := by omega
              simp [hp0, hp1, hp, hpeq, hpm, hpout, hpmout, hq0, hqout,
                hrows, hrows1, hrowsne, hcols, zeroExtend, hc.le]
            · simp [hp0, hp1, hp, hpeq, hpm, hq0, hrows, hcols,
                zeroExtend]
          · have hrange : rows + 1 ≤ (p : ℕ) := by omega
            by_cases hq0 : (q : ℕ) = 0
            · have hpeq' : (p : ℕ) = rows + 1 := by omega
              simp [hp0, hp1, hp, hpeq, hpeq', hrange, hq0, hrows, hcols,
                zeroExtend]
            · simp [hp0, hp1, hp, hpeq, hrange, hq0, hrows, hcols,
                zeroExtend]
    · have hcols0 : cols = 0 := by omega
      simp [verticalBoundaryKernel, hcols0, zeroExtend]
  · have hrows0 : rows = 0 := by omega
    simp [verticalBoundaryKernel, hrows0, zeroExtend]

end OneChannelCNNUniversality
