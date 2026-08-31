import OneChannelCNNUniversality.SharedBiasNorthTwoLinearization

/-!
# Regression tests for northern-two-row linearization
-/

namespace OneChannelCNNUniversality

#check NorthTwoAgree
#check NorthTwoAgree.refl
#check NorthTwoAgree.trans
#check northTwoAgree_sharedLayerEval
#check NorthTwoLinearAlong
#check zeroBiasBilinearNetwork_northTwoAgree_fullConvChain
#check zeroBiasBilinearNetwork_northTwo_eval_eq_fullConvChain

example {cols : ℕ} (x : Image 1 cols) :
    NorthTwoAgree x x := NorthTwoAgree.refl x

example (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (x : Image rows cols) (h : LinearBranchAlong fs x) :
    NorthTwoLinearAlong fs x := by
  exact linearBranchAlong_imp_northTwoLinearAlong fs x h

private def northTwoRegressionFactor : BilinearKernelFactor where
  a0 := 1
  a1 := 0
  b0 := 0
  b1 := 0

private def northTwoRegressionInput : Image 3 1 :=
  fun i _ ↦ if (i : ℕ) = 2 then -1 else 1

/-- A concrete southern negative value is allowed: only the northern two
preactivation rows must be nonnegative. -/
example : NorthTwoLinearAlong [northTwoRegressionFactor]
    northTwoRegressionInput := by
  constructor
  · intro p hp q
    change 0 ≤ fullConv (bilinearKernel 1 0 0 0)
      northTwoRegressionInput p q
    rw [fullConv_bilinearKernel_nat]
    simp only [one_mul, zero_mul, ite_self, add_zero]
    have hp3 : (p : ℕ) < 3 := by omega
    by_cases hq : (q : ℕ) < 1
    · have hp2 : (p : ℕ) ≠ 2 := by omega
      rw [zeroExtend_of_lt _ hp3 hq]
      simp [northTwoRegressionInput, hp2]
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hq)]
  · trivial

/-- The genuine ReLU layer truncates the negative southern value. -/
example :
    (zeroBiasBilinearNetwork [northTwoRegressionFactor]).eval
      northTwoRegressionInput ⟨2, by norm_num [grownSize]⟩
        ⟨0, by norm_num [grownSize]⟩ = 0 := by
  change relu
    (fullConv (bilinearKernel 1 0 0 0) northTwoRegressionInput 2 0 + 0) = 0
  rw [fullConv_bilinearKernel_nat]
  norm_num [northTwoRegressionInput, zeroExtend, relu]

/-- The corresponding formal convolution retains that southern value, so
the preceding regression genuinely exercises a nonlinear ReLU branch. -/
example :
    fullConvChain [northTwoRegressionFactor] northTwoRegressionInput
      ⟨2, by norm_num [grownSize]⟩ ⟨0, by norm_num [grownSize]⟩ = -1 := by
  change fullConv (bilinearKernel 1 0 0 0)
    northTwoRegressionInput 2 0 = -1
  rw [fullConv_bilinearKernel_nat]
  norm_num [northTwoRegressionInput, zeroExtend]

end OneChannelCNNUniversality
