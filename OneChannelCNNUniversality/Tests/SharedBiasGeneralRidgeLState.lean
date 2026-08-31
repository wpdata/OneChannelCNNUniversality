import OneChannelCNNUniversality.SharedBiasGeneralRidgeLState

namespace OneChannelCNNUniversality

#check generalRidgeLCodeIndex
#check generalRidgeLTerminalIndex
#check generalRidgeLLayout
#check generalRidgeLLayout_code
#check generalRidgeLLayout_terminal
#check generalRidgeLLayout_southeastMonotone
#check generalRidgeLLayout_injective
#check generalRidgeLState
#check generalRidgeNorthPrefix
#check generalRidgeNorthPrefix_injective
#check exists_generalRidgeLState_on_compact

example (n : ℕ) :
    SoutheastMonotoneLayout (generalRidgeLLayout n) :=
  generalRidgeLLayout_southeastMonotone n

example (n : ℕ) :
    Function.Injective (generalRidgeLLayout n) :=
  generalRidgeLLayout_injective n

/-- At the smallest supported network width, the logical state contains the
three northern code sites followed by the southern ridge site. -/
example :
    generalRidgeLLayout 0 (0 : Fin 4) =
        ((0 : Fin 3), (0 : Fin 5)) ∧
      generalRidgeLLayout 0 (1 : Fin 4) =
        ((0 : Fin 3), (1 : Fin 5)) ∧
      generalRidgeLLayout 0 (2 : Fin 4) =
        ((0 : Fin 3), (2 : Fin 5)) ∧
      generalRidgeLLayout 0 (3 : Fin 4) =
        ((1 : Fin 3), (2 : Fin 5)) := by
  decide

example {d : ℕ} (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Function.Injective (generalRidgeNorthPrefix w η) :=
  generalRidgeNorthPrefix_injective w η

#print axioms generalRidgeLLayout_southeastMonotone
#print axioms generalRidgeLLayout_injective
#print axioms generalRidgeNorthPrefix_injective
#print axioms exists_generalRidgeLState_on_compact

end OneChannelCNNUniversality
