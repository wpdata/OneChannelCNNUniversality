import OneChannelCNNUniversality.SharedBiasOneLayerObstruction

/-! # Regression tests for the one-layer shared-bias carrier obstruction -/

namespace OneChannelCNNUniversality

#check twoPointRowInput
#check fullConv_twoPointRowInput_south_left
#check fullConv_twoPointRowInput_south_middle
#check fullConv_twoPointRowInput_south_right
#check slope_eq_zero_of_relu_affine_constant
#check oneLayer_south_constant_kernel_zero
#check oneLayer_south_constant_eq_relu_bias
#check not_oneLayer_south_nonuniform_inputIndependent

#print axioms oneLayer_south_constant_kernel_zero
#print axioms not_oneLayer_south_nonuniform_inputIndependent

/-- A concrete nonuniform carrier requested at the three southern sites. -/
def oneLayerRegressionCarrier : Fin 3 → ℝ :=
  fun q ↦ if q = (1 : Fin 3) then 1 else 0

example (w : Kernel 2 2) (b : ℝ) :
    ¬ ∀ x₀ x₁ q,
      sharedLayerEval w b (twoPointRowInput x₀ x₁)
          (1 : Fin 2) q = oneLayerRegressionCarrier q := by
  intro hconstant
  apply not_oneLayer_south_nonuniform_inputIndependent w b
  refine ⟨oneLayerRegressionCarrier, ?_, hconstant⟩
  exact ⟨(0 : Fin 3), (1 : Fin 3), by simp [oneLayerRegressionCarrier]⟩

end OneChannelCNNUniversality
