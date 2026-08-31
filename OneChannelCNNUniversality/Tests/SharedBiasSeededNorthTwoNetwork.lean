import OneChannelCNNUniversality.SharedBiasSeededNorthTwoNetwork

/-! # Regression tests for the seeded northern-two-row network bridge -/

namespace OneChannelCNNUniversality

#check seededNorthTwoState
#check seededZeroBiasBilinearNetwork
#check seededZeroBiasBilinearNetwork_depth
#check exists_seededNorthTwoNetwork_threshold_on_compact

/-- The empty factor block still has exactly the genuine seed layer. -/
example {rows cols : ℕ} (c : ℝ) :
    (seededZeroBiasBilinearNetwork []
      (rows := rows) (cols := cols) c).net.depth = 1 := by
  simp

/-- A one-factor positive horizontal kernel supplies a concrete nonempty
unit-lower carrier regression. -/
example (cols : ℕ) :
    NorthTwoUnitLowerAlong
      [{ a0 := 1, a1 := 1, b0 := 0, b1 := 0 }]
      (constantImage 2 (cols + 1) 2) := by
  constructor
  · intro p hp q
    rw [BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
    simp [constantImage, zeroExtend]
    split_ifs <;> norm_num <;> omega
  · trivial

end OneChannelCNNUniversality
