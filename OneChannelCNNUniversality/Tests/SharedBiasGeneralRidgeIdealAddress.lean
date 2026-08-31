import OneChannelCNNUniversality.SharedBiasGeneralRidgeIdealAddress

/-!
# Regression tests for the ideal boxcar ridge address
-/

namespace OneChannelCNNUniversality

#check generalRidgeNodalProduct_succ
#check generalRidgeNodalProduct_coeff_nonneg
#check generalRidgeNodalProduct_coeff_one_le
#check generalRidgeBoxcar
#check generalRidgeBoxcar_coeff
#check coeff_mul_generalRidgeBoxcar_eq_eval_one
#check generalRidgeIdealActiveSet
#check generalRidgeBlockAddress
#check generalRidgeBlockAddress_eq_coeff_mul_boxcar
#check generalRidgeNegativeBlockAddress_unit_gap
#check generalRidgeIdealAddress
#check generalRidgeIdealAddress_eq_coeff_mul_boxcar
#check generalRidgeIdealAddress_center
#check generalRidgeIdealAddress_unit_gap
#check generalRidgeIdealAddress_unique_max
#check generalRidgeIdealNegativeAddress_unit_gap
#check generalRidgeIdealNegativeAddress_unique_min

open Polynomial

example : generalRidgeNodalProduct 3 = (X + 1) * (X + 2) * (X + 3) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [generalRidgeNodalProduct, hu]
  simp [generalRidgeNodalFactor]
  ring

example : generalRidgeIdealActiveSet 3 3 = Finset.range 4 := by
  native_decide

example : generalRidgeIdealActiveSet 3 2 = Finset.range 3 := by
  native_decide

example : generalRidgeIdealActiveSet 3 4 = {1, 2, 3} := by
  native_decide

example :
    generalRidgeIdealAddress 3 3 = 24 := by
  have hG :
      generalRidgeNodalProduct 3 = (X + 1) * (X + 2) * (X + 3) := by
    have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [generalRidgeNodalProduct, hu]
    simp [generalRidgeNodalFactor]
    ring
  have hExpanded :
      (X + 1 : ℝ[X]) * (X + 2) * (X + 3) =
        X ^ 3 + 6 * X ^ 2 + 11 * X + 6 := by ring
  rw [generalRidgeIdealAddress, generalRidgeIdealActiveSet_center, hG]
  rw [hExpanded]
  norm_num [Finset.sum_range_succ, coeff_X, coeff_one]

end OneChannelCNNUniversality
