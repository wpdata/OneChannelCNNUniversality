import OneChannelCNNUniversality.SharedBiasGeneralRidgeAddressPlateau

/-!
# Regression tests for the linear shared-bias address plateau
-/

namespace OneChannelCNNUniversality

#check linearBiasAddressDirection
#check linearBiasAddress
#check linearBiasAddressDirection_eq_eval_one_on_core
#check linearBiasAddress_flat_on_core
#check exists_competing_linearBiasAddress_coordinate
#check linearBiasAddress_core_singleton_at_two_extra_layers

open Polynomial

example (Q : Fin 3 → ℝ[X])
    (hdegree : ∀ k, (Q k).natDegree ≤ 3 - ((k : ℕ) + 1))
    (scale : Fin 3 → ℝ) (b : ℝ) :
    linearBiasAddress 5 3 Q scale b 2 =
      linearBiasAddress 5 3 Q scale b 5 := by
  exact linearBiasAddress_flat_on_core Q hdegree scale b
    (q := 2) (r := 5) (by omega) (by omega) (by omega) (by omega)

example :
    ∃ q' ≠ 4,
      4 - 1 ≤ q' ∧ q' ≤ 5 := by
  simpa using
    (exists_competing_linearBiasAddress_core_coordinate
      (m := 5) (L := 4) (q := 4) (by omega) (by omega) (by omega) (by omega))

/-- The upper endpoint `L=m` still forces a distinct competitor. -/
example :
    ∃ q' ≠ 5,
      5 - 1 ≤ q' ∧ q' ≤ 5 := by
  simpa using
    (exists_competing_linearBiasAddress_core_coordinate
      (m := 5) (L := 5) (q := 5) (by omega) (by omega) (by omega) (by omega))

/-- At `L=m+1`, the former common interval is exactly the singleton `{m}`. -/
example {q : ℕ} (hleft : 5 + 1 - 1 ≤ q) (hright : q ≤ 5) :
    q = 5 := by
  exact linearBiasAddress_core_singleton_at_two_extra_layers hleft hright

end OneChannelCNNUniversality
