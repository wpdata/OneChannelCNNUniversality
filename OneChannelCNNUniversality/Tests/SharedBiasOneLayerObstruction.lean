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
#check oneLayer_south_constant_on_zero_mem_eq_relu_bias
#check not_oneLayer_south_nonuniform_inputIndependent_on_zero_mem
#check twoPointSymmetricBox
#check twoPointSymmetricBox_compact
#check twoPointSymmetricBox_zero_mem
#check not_oneLayer_south_nonuniform_inputIndependent_on_symmetricBox

#print axioms oneLayer_south_constant_kernel_zero
#print axioms not_oneLayer_south_nonuniform_inputIndependent
#print axioms not_oneLayer_south_nonuniform_inputIndependent_on_symmetricBox

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

example (w : Kernel 2 2) (b : ℝ) :
    ¬ ∃ c : Fin 3 → ℝ,
      (∃ q₁ q₂, c q₁ ≠ c q₂) ∧
        ∀ x ∈ twoPointSymmetricBox 1, ∀ q,
          sharedLayerEval w b x (1 : Fin 2) q = c q := by
  exact not_oneLayer_south_nonuniform_inputIndependent_on_symmetricBox
    1 (by norm_num) w b

end OneChannelCNNUniversality
