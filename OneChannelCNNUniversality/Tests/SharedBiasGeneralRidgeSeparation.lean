import OneChannelCNNUniversality.SharedBiasGeneralRidgeSeparation

/-!
# Regression tests for the final-factor carrier separation
-/

namespace OneChannelCNNUniversality

#check generalRidgeSeparatedLastFactor
#check generalRidgeSeparatedLastFactor_eq
#check generalRidgeSeparatedLastKernel
#check generalRidgeSeparatedLastKernel_eq
#check generalRidgePenultimateIndex
#check generalRidgeFactorPrefix
#check generalRidgeFactorPrefix_length
#check generalRidgeFactorList_split_last_two
#check fullConv_generalRidgeSeparatedLastKernel_target_eq
#check fullConv_generalRidgeSeparatedLastKernel_target_le
#check fullConv_generalRidgeSeparatedLastKernel_north_ge_one
#check generalRidgeSeparatedLastKernel_gap

#print axioms generalRidgeFactorList_split_last_two
#print axioms fullConv_generalRidgeSeparatedLastKernel_target_eq
#print axioms fullConv_generalRidgeSeparatedLastKernel_north_ge_one
#print axioms generalRidgeSeparatedLastKernel_gap

/-- The depth-three list exposes its final two factors in natural order. -/
example (w : Fin 4 → ℝ) (η : Fin 3 → ℝ) :
    generalRidgeFactorList w η =
      generalRidgeFactorPrefix (d := 3) (by omega) w η ++
        [generalRidgeKernelFactor w η
            (generalRidgePenultimateIndex (d := 3) (by omega)),
          generalRidgeKernelFactor w η
            (generalRidgeLastIndex (d := 3) (by omega))] := by
  exact generalRidgeFactorList_split_last_two (n := 1) w η

/-- At the first nontrivial depth, the target carrier response is nonpositive
with a full unit of strict separation. -/
example (w : Fin 3 → ℝ) :
    fullConv
        (generalRidgeSeparatedLastKernel (d := 2) (by omega) w)
        (constantImage 2 4 1) 1 2 ≤ -1 := by
  exact fullConv_generalRidgeSeparatedLastKernel_target_le
    (d := 2) (by omega) w

/-- The exact target formula retains no hidden dependence on the allocation
scale. -/
example (w : Fin 3 → ℝ) :
    fullConv
        (generalRidgeSeparatedLastKernel (d := 2) (by omega) w)
        (constantImage 2 4 1) 1 2 =
      generalRidgeBeta w (generalRidgeLastIndex (d := 2) (by omega)) -
        |generalRidgeBeta w (generalRidgeLastIndex (d := 2) (by omega))| - 1 := by
  exact fullConv_generalRidgeSeparatedLastKernel_target_eq
    (d := 2) (by omega) w

/-- Every northern output coordinate survives with value at least one. -/
example (w : Fin 3 → ℝ) (q : Fin 5) :
    1 ≤ fullConv
      (generalRidgeSeparatedLastKernel (d := 2) (by omega) w)
      (constantImage 2 4 1) 0 q := by
  exact fullConv_generalRidgeSeparatedLastKernel_north_ge_one
    (d := 2) (by omega) w q

/-- Consequently every northern response has a gap of at least two above the
southern target response. -/
example (w : Fin 4 → ℝ) (q : Fin 7) :
    2 ≤
      fullConv
          (generalRidgeSeparatedLastKernel (d := 3) (by omega) w)
          (constantImage 3 6 1) 0 q -
        fullConv
          (generalRidgeSeparatedLastKernel (d := 3) (by omega) w)
          (constantImage 3 6 1) 1 3 := by
  exact generalRidgeSeparatedLastKernel_gap
    (d := 3) (by omega) w q

end OneChannelCNNUniversality
