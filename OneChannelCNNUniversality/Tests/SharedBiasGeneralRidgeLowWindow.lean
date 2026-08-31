import OneChannelCNNUniversality.SharedBiasGeneralRidgeLowWindow

/-!
# Regression tests for truncated polynomial inversion
-/

namespace OneChannelCNNUniversality

#check generalRidgeLowWindowMultiplier
#check generalRidgeLowWindowMultiplier_natDegree_le
#check generalRidgeLowWindowMultiplier_coeff_mul
#check exists_generalRidgeLowWindowMultiplier

open Polynomial

example (a b c : ℝ) (ha : a ≠ 0) :
    ∃ U : ℝ[X], U.natDegree ≤ 2 ∧
      ∀ j ≤ 2,
        (U * (C a + C b * X)).coeff j =
          (C c + X ^ 2).coeff j := by
  exact exists_generalRidgeLowWindowMultiplier 2
    (C a + C b * X) (C c + X ^ 2) (by simpa using ha)

end OneChannelCNNUniversality
