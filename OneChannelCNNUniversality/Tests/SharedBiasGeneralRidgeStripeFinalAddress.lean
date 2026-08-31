import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeFinalAddress

/-!
# Regression tests for the final signed-stripe local address
-/

namespace OneChannelCNNUniversality

#check generalRidgeStripeFinalLocalAddress
#check generalRidgeStripeFinalLocalAddress_target
#check generalRidgeStripeFinalLocalAddress_row_zero_gap
#check generalRidgeStripeFinalLocalAddress_row_one_left_gap
#check generalRidgeStripeFinalLocalAddress_row_one_right_gap
#check generalRidgeStripeFinalLocalAddress_row_one_interior

#print axioms generalRidgeStripeFinalLocalAddress_row_zero_gap
#print axioms generalRidgeStripeFinalLocalAddress_row_one_left_gap
#print axioms generalRidgeStripeFinalLocalAddress_row_one_right_gap
#print axioms generalRidgeStripeFinalLocalAddress_row_one_interior

/-- Every northern output column lies at least two above the target in the
local address. -/
example (w : Fin 3 → ℝ) (T : ℝ) (hT : 1 ≤ T) (q : ℕ)
    (hq : q ≤ 2 * 3) :
    2 ≤ generalRidgeStripeFinalLocalAddress (n := 1) w T 0 q -
      generalRidgeStripeFinalLocalAddress (n := 1) w T 1 3 := by
  exact generalRidgeStripeFinalLocalAddress_row_zero_gap w T hT q hq

/-- The two horizontal endpoints of row one also lie at least two above the
target. -/
example (w : Fin 2 → ℝ) (T : ℝ) (hT : 1 ≤ T) :
    2 ≤ generalRidgeStripeFinalLocalAddress (n := 0) w T 1 0 -
      generalRidgeStripeFinalLocalAddress (n := 0) w T 1 2 ∧
    2 ≤ generalRidgeStripeFinalLocalAddress (n := 0) w T 1 (2 * 2) -
      generalRidgeStripeFinalLocalAddress (n := 0) w T 1 2 := by
  exact ⟨generalRidgeStripeFinalLocalAddress_row_one_left_gap w T hT,
    generalRidgeStripeFinalLocalAddress_row_one_right_gap w T hT⟩

/-- Every interior coordinate of row one has the same local address as the
target, so this local direction alone is not a horizontal selector. -/
example (w : Fin 4 → ℝ) (T : ℝ) (q : ℕ)
    (hq0 : 1 ≤ q) (hq1 : q < 2 * 4) :
    generalRidgeStripeFinalLocalAddress (n := 2) w T 1 q =
      generalRidgeStripeFinalLocalAddress (n := 2) w T 1 4 := by
  exact generalRidgeStripeFinalLocalAddress_row_one_interior
    w T q hq0 hq1

end OneChannelCNNUniversality
