import OneChannelCNNUniversality.SharedBiasScheduledRecovery

/-!
# Obstruction to globally protected nontrivial selections

The relative-recovery theorem for one selected ReLU assumes that two feature
images agree at the selected root and may differ only in its southeast
quadrant with that root removed.  Requiring this condition for every pair in
an input family therefore forces the selected coordinate to be constant on
the family.  In particular, a fixed globally protected schedule cannot use
the same root as a nontrivially varying computational register.

This is a limitation of the current recovery invariant, not a
non-universality theorem for the full architecture.  It motivates separating
a protected state copy from a mutable computational copy.
-/

namespace OneChannelCNNUniversality

universe u

/-- Every pair of features in `K` satisfies the root-punctured southeast
protection condition at one fixed target. -/
def PairwiseStrictSoutheastProtectedOn
    {X : Type u} {rows cols : ℕ} (K : Set X)
    (V : X → Image rows cols) (targetRow : Fin rows)
    (targetCol : Fin cols) : Prop :=
  ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
    AgreeOutsideStrictSoutheast (V x) (V y) targetRow targetCol

/-- The selected feature coordinate has the same value for every pair of
parameters in `K`. -/
def TargetCoordinateConstantOn
    {X : Type u} {rows cols : ℕ} (K : Set X)
    (V : X → Image rows cols) (targetRow : Fin rows)
    (targetCol : Fin cols) : Prop :=
  ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
    V x targetRow targetCol = V y targetRow targetCol

/-- Pairwise root-punctured protection forces the target coordinate to be
constant on the protected family. -/
theorem PairwiseStrictSoutheastProtectedOn.targetCoordinate_constant
    {X : Type u} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {targetRow : Fin rows}
    {targetCol : Fin cols}
    (hprotected : PairwiseStrictSoutheastProtectedOn
      K V targetRow targetCol) :
    TargetCoordinateConstantOn K V targetRow targetCol := by
  intro x hx y hy
  have hroot := (hprotected hx hy).2
  simpa [zeroExtend, targetRow.isLt, targetCol.isLt] using hroot

/-- If the target feature takes two different values on `K`, no global
pairwise root-punctured protection proof can exist at that target. -/
theorem not_pairwiseStrictSoutheastProtectedOn_of_target_ne
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (V : X → Image rows cols) (targetRow : Fin rows)
    (targetCol : Fin cols) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hne : V x targetRow targetCol ≠ V y targetRow targetCol) :
    ¬ PairwiseStrictSoutheastProtectedOn K V targetRow targetCol := by
  intro hprotected
  exact hne (hprotected.targetCoordinate_constant hx hy)

/-- Any ReLU threshold applied at a globally protected target is constant on
the input family as well.  Thus such a target cannot be the mutable register
of a nontrivial selected activation. -/
theorem TargetCoordinateConstantOn.selectedReLU_constant
    {X : Type u} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {targetRow : Fin rows}
    {targetCol : Fin cols}
    (hconstant : TargetCoordinateConstantOn K V targetRow targetCol)
    (θ : ℝ) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    relu (V x targetRow targetCol + θ) =
      relu (V y targetRow targetCol + θ) := by
  rw [hconstant hx hy]

/-- Applied to a compiled selector step, a global proof of its local
recovery condition forces the selected successor-feature coordinate to be
constant on the whole compact family. -/
theorem pairwise_appendedSelection_protection_forces_target_constant
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} (F : X → Image inRows inCols)
    (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
    {rowSteps extraColSteps : ℕ}
    {targetRow : Fin (rows + 2 - 1)}
    {targetCol : Fin (cols + 2 - 1)}
    {threshold seed selectorBias : ℝ}
    {selector : SharedBiasNetworkTo 2 2
      (rows + 2 - 1) (cols + 2 - 1)
      (protectedSelectionSize (rows + 2 - 1) rowSteps extraColSteps)
      (protectedSelectionSize (cols + 2 - 1) rowSteps extraColSteps)}
    (selectionSpec : BundledPascalGridSelectionSpec K
      (successorFeature head F) threshold rowSteps extraColSteps
      targetRow targetCol seed selectorBias selector)
    (eval_eq : ∀ x ∈ K,
      (head.appendWithSeed seed selector).eval (F x) =
        selector.eval
          (successorFeature head F x +
            constantImage (rows + 2 - 1) (cols + 2 - 1) seed))
    (hprotected : ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
      (appendedSelectionRecoveryStep F head selectionSpec eval_eq).Protected
        x y) :
    TargetCoordinateConstantOn K (successorFeature head F)
      targetRow targetCol := by
  apply PairwiseStrictSoutheastProtectedOn.targetCoordinate_constant
  intro x hx y hy
  exact hprotected hx hy

/-- Consequently, two distinct target values refute the global pairwise
protection premise for the actual appended-selector recovery step. -/
theorem not_pairwise_appendedSelection_protection_of_target_ne
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} (F : X → Image inRows inCols)
    (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
    {rowSteps extraColSteps : ℕ}
    {targetRow : Fin (rows + 2 - 1)}
    {targetCol : Fin (cols + 2 - 1)}
    {threshold seed selectorBias : ℝ}
    {selector : SharedBiasNetworkTo 2 2
      (rows + 2 - 1) (cols + 2 - 1)
      (protectedSelectionSize (rows + 2 - 1) rowSteps extraColSteps)
      (protectedSelectionSize (cols + 2 - 1) rowSteps extraColSteps)}
    (selectionSpec : BundledPascalGridSelectionSpec K
      (successorFeature head F) threshold rowSteps extraColSteps
      targetRow targetCol seed selectorBias selector)
    (eval_eq : ∀ x ∈ K,
      (head.appendWithSeed seed selector).eval (F x) =
        selector.eval
          (successorFeature head F x +
            constantImage (rows + 2 - 1) (cols + 2 - 1) seed))
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hne : successorFeature head F x targetRow targetCol ≠
      successorFeature head F y targetRow targetCol) :
    ¬ (∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
      (appendedSelectionRecoveryStep F head selectionSpec eval_eq).Protected
        x y) := by
  intro hprotected
  exact hne
    (pairwise_appendedSelection_protection_forces_target_constant
      F head selectionSpec eval_eq hprotected hx hy)

end OneChannelCNNUniversality
