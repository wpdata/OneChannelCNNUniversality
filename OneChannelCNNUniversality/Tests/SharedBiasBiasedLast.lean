import OneChannelCNNUniversality.SharedBiasBiasedLast

/-!
# Regression tests for a heterogeneous chain biased only at its last layer
-/

namespace OneChannelCNNUniversality

#check biasedLastBilinearNetwork
#check biasedLastBilinearNetwork_depth
#check biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
#check biasedLastBilinearNetwork_northTwo_eval_eq_fullConvChain_add_constant

#print axioms biasedLastBilinearNetwork_depth
#print axioms biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
#print axioms biasedLastBilinearNetwork_northTwo_eval_eq_fullConvChain_add_constant

private def biasedLastRegressionFactor : BilinearKernelFactor where
  a0 := 1
  a1 := 0
  b0 := 0
  b1 := 0

private def biasedLastRegressionInput : Image 3 1 :=
  fun i _ ↦ if (i : ℕ) = 2 then -1 else 1

private theorem biasedLastRegressionLinearOne :
    NorthTwoLinearAlong [biasedLastRegressionFactor]
      biasedLastRegressionInput := by
  constructor
  · intro p hp q
    change 0 ≤ fullConv (bilinearKernel 1 0 0 0)
      biasedLastRegressionInput p q
    rw [fullConv_bilinearKernel_nat]
    simp only [one_mul, zero_mul, ite_self, add_zero]
    have hp3 : (p : ℕ) < 3 := by omega
    by_cases hq : (q : ℕ) < 1
    · have hp2 : (p : ℕ) ≠ 2 := by omega
      rw [zeroExtend_of_lt _ hp3 hq]
      simp [biasedLastRegressionInput, hp2]
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hq)]
  · trivial

/-- Single-factor regression: the unique layer receives the requested bias. -/
example :
    (biasedLastBilinearNetwork [biasedLastRegressionFactor] (by simp) 2 3 1).eval
        biasedLastRegressionInput ⟨0, by norm_num [grownSize]⟩
          ⟨0, by norm_num [grownSize]⟩ =
      fullConvChain [biasedLastRegressionFactor] biasedLastRegressionInput
          ⟨0, by norm_num [grownSize]⟩ ⟨0, by norm_num [grownSize]⟩ + 2 := by
  exact biasedLastBilinearNetwork_northTwo_eval_eq_fullConvChain_add_constant
    [biasedLastRegressionFactor] (by simp) 2 biasedLastRegressionInput
      biasedLastRegressionLinearOne (by norm_num) _ _ (by norm_num)

private theorem biasedLastRegressionLinearTwo :
    NorthTwoLinearAlong
      [biasedLastRegressionFactor, biasedLastRegressionFactor]
      biasedLastRegressionInput := by
  refine ⟨biasedLastRegressionLinearOne.1, ?_⟩
  constructor
  · intro p hp q
    change 0 ≤ fullConv (bilinearKernel 1 0 0 0)
      (fullConvImage (bilinearKernel 1 0 0 0) biasedLastRegressionInput) p q
    rw [fullConv_bilinearKernel_nat]
    simp only [one_mul, zero_mul, ite_self, add_zero]
    have hp4 : (p : ℕ) < 3 + 2 - 1 := by omega
    by_cases hq2 : (q : ℕ) < 1 + 2 - 1
    · rw [zeroExtend_of_lt _ hp4 hq2]
      exact biasedLastRegressionLinearOne.1 ⟨p, hp4⟩ hp ⟨q, hq2⟩
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hq2)]
  · trivial

/-- Multi-factor regression: preceding layers have zero bias and only the
last layer contributes the additive constant. -/
example :
    NorthTwoAgree
      ((biasedLastBilinearNetwork
        [biasedLastRegressionFactor, biasedLastRegressionFactor]
        (by simp) 3 3 1).eval biasedLastRegressionInput)
      (fullConvChain
          [biasedLastRegressionFactor, biasedLastRegressionFactor]
          biasedLastRegressionInput + constantImage _ _ 3) := by
  exact biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
    [biasedLastRegressionFactor, biasedLastRegressionFactor] (by simp) 3
      biasedLastRegressionInput biasedLastRegressionLinearTwo (by norm_num)

example :
    (biasedLastBilinearNetwork
      [biasedLastRegressionFactor, biasedLastRegressionFactor]
      (by simp) 3 3 1).net.depth = 2 := by
  simpa using biasedLastBilinearNetwork_depth
    [biasedLastRegressionFactor, biasedLastRegressionFactor]
      (by simp) 3 3 1

end OneChannelCNNUniversality
