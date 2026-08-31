import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeSeedAddress

/-!
# Regression tests for the full signed-stripe seed address
-/

namespace OneChannelCNNUniversality

#check generalRidgeStripeSeedAddressRowZero
#check generalRidgeStripeSeedAddressRowOne
#check generalRidgeStripeSeedPerturbation
#check generalRidgeStripeSeedBTarget
#check generalRidgeStripeSeedAddressThreshold
#check generalRidgeStripeSeedAddressThreshold_one_le
#check generalRidgeStripeSeedAddress_row_one_gap_of_threshold
#check exists_generalRidgeStripeSeedAddressThreshold
#check generalRidgeStripeSeedAddress_north_lower_bound
#check generalRidgeStripeSeedBTarget_eq_sum

#print axioms generalRidgeStripeSeedAddress_row_one_gap_of_threshold
#print axioms exists_generalRidgeStripeSeedAddressThreshold
#print axioms generalRidgeStripeSeedAddress_north_lower_bound
#print axioms generalRidgeStripeSeedBTarget_eq_sum

/-- Every scale above the explicit threshold gives a unit-gap unique target
minimum throughout row one. -/
example (w : Fin 3 → ℝ) (T : ℝ)
    (hT : generalRidgeStripeSeedAddressThreshold (n := 1) w ≤ T)
    (q : ℕ) (hq : q ≤ 2 * 3) (hne : q ≠ 3) :
    1 ≤ generalRidgeStripeSeedAddressRowOne (n := 1) w T q -
      generalRidgeStripeSeedAddressRowOne (n := 1) w T 3 := by
  exact generalRidgeStripeSeedAddress_row_one_gap_of_threshold
    w T hT q hq hne

/-- The northern address is uniformly bounded below relative to the target
by the negative target perturbation. -/
example (w : Fin 2 → ℝ) (T : ℝ) (hT : 1 ≤ T) (q : ℕ) :
    -generalRidgeStripeSeedBTarget (n := 0) w ≤
      generalRidgeStripeSeedAddressRowZero (n := 0) w T q -
        generalRidgeStripeSeedAddressRowOne (n := 0) w T 2 := by
  exact generalRidgeStripeSeedAddress_north_lower_bound w T hT q

/-- The perturbation at the center is exactly the sum of the original
weights; the appended zero coordinate contributes nothing. -/
example (w : Fin 4 → ℝ) :
    generalRidgeStripeSeedBTarget (n := 2) w = ∑ j, w j := by
  exact generalRidgeStripeSeedBTarget_eq_sum w

end OneChannelCNNUniversality
