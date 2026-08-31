import OneChannelCNNUniversality.SharedBiasGeneralRidgeCarrier

/-!
# Regression tests for the separated arbitrary-width carrier allocation
-/

namespace OneChannelCNNUniversality

open Polynomial

#check generalRidgeLastIndex
#check generalRidgeFirstIndex
#check generalRidgeLastIndex_ne_first
#check generalRidgeCarrierScale
#check generalRidgeCarrierScale_pos
#check generalRidgeSeparatedAllocation
#check generalRidgeSeparatedAllocation_sum
#check generalRidgeSeparatedLastLowerFactor_eval_one
#check generalRidgeSeparatedLastLowerFactor_eval_one_le
#check generalRidgeLastNodalFactor_eval
#check generalRidgeLastNodalFactor_eval_zero
#check generalRidgeLastNodalFactor_eval_ge_depth

/-- The first nontrivial depth uses distinct first and last allocation slots. -/
example (w : Fin 3 → ℝ) :
    generalRidgeSeparatedAllocation (d := 2) (by omega) w 0 =
      w 0 + generalRidgeCarrierScale (d := 2) (by omega) w := by
  rw [show (0 : Fin 2) = generalRidgeFirstIndex (by omega) by rfl]
  exact generalRidgeSeparatedAllocation_zero (d := 2) (by omega) w

example (w : Fin 3 → ℝ) :
    generalRidgeSeparatedAllocation (d := 2) (by omega) w 1 =
      -generalRidgeCarrierScale (d := 2) (by omega) w := by
  rw [show (1 : Fin 2) = generalRidgeLastIndex (by omega) by rfl]
  exact generalRidgeSeparatedAllocation_last (d := 2) (by omega) w

/-- Concrete depth-two allocation still sums to the leading coefficient. -/
example (w : Fin 3 → ℝ) :
    ∑ i : Fin 2, generalRidgeSeparatedAllocation (by omega) w i = w 0 := by
  exact generalRidgeSeparatedAllocation_sum (d := 2) (by omega) w

/-- At depth two the separated last response is at most `-4`. -/
example (w : Fin 3 → ℝ) :
    (generalRidgeLowerFactor w
        (generalRidgeSeparatedAllocation (by omega) w)
        (generalRidgeLastIndex (by omega))).eval 1 ≤ -4 := by
  have h := generalRidgeSeparatedLastLowerFactor_eval_one_le
    (d := 2) (by omega) w
  norm_num at h ⊢
  linarith

/-- The last north factor at depth two is `X + 2`. -/
example (q : ℝ) :
    (generalRidgeNodalFactor (generalRidgeLastIndex (d := 2) (by omega))).eval q =
      q + 2 := by
  simpa using generalRidgeLastNodalFactor_eval (d := 2) (by omega) q

end OneChannelCNNUniversality
