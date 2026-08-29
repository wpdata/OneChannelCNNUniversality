import OneChannelCNNUniversality.SharedBiasProtectionObstruction

open OneChannelCNNUniversality

example {X : Type*} {K : Set X} {rows cols : ℕ}
    (V : X → Image rows cols) (targetRow : Fin rows)
    (targetCol : Fin cols)
    (hprotected : PairwiseStrictSoutheastProtectedOn
      K V targetRow targetCol) :
    TargetCoordinateConstantOn K V targetRow targetCol := by
  exact hprotected.targetCoordinate_constant

example {X : Type*} {K : Set X} {rows cols : ℕ}
    (V : X → Image rows cols) (targetRow : Fin rows)
    (targetCol : Fin cols) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hne : V x targetRow targetCol ≠ V y targetRow targetCol) :
    ¬ PairwiseStrictSoutheastProtectedOn K V targetRow targetCol := by
  exact not_pairwiseStrictSoutheastProtectedOn_of_target_ne
    V targetRow targetCol hx hy hne

example {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {targetRow : Fin rows}
    {targetCol : Fin cols}
    (hconstant : TargetCoordinateConstantOn K V targetRow targetCol)
    (θ : ℝ) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    relu (V x targetRow targetCol + θ) =
      relu (V y targetRow targetCol + θ) := by
  exact hconstant.selectedReLU_constant θ hx hy

#check pairwise_appendedSelection_protection_forces_target_constant
#check not_pairwise_appendedSelection_protection_of_target_ne
