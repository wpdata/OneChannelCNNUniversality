import OneChannelCNNUniversality.SharedBiasFiniteSelection
import OneChannelCNNUniversality.SharedBiasFiniteRecovery

/-!
# Recovery through compiled finite selection schedules

This module connects the finite schedule compiler to the heterogeneous
recovery-chain logic.  One compiled selector block becomes one recovery step
from the preceding network output to the genuinely composed network output.
The exact `appendWithSeed` equation transports output equality to the bundled
selector, and injectivity of the expansive delta bridge then recovers the
preceding output.

The resulting protection predicate remains explicit: a pair must satisfy the
root-punctured southeast condition requested at every scheduled target.
-/

namespace OneChannelCNNUniversality

universe u

/-- A compiled successor selector reflects equality of the genuinely
composed network output back to equality of the preceding network output,
provided the two successor features satisfy the selector's local protection
condition. -/
def appendedSelectionRecoveryStep
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
            constantImage (rows + 2 - 1) (cols + 2 - 1) seed)) :
    RelativeRecoveryStep K (fun x ↦ head.eval (F x))
      (fun x ↦ (head.appendWithSeed seed selector).eval (F x)) where
  Protected := fun x y ↦ AgreeOutsideStrictSoutheast
    (successorFeature head F x) (successorFeature head F y)
    targetRow targetCol
  recover := by
    intro x y hx hy hprotected hcomposed
    have hselector :
        selector.eval
            (successorFeature head F x +
              constantImage (rows + 2 - 1) (cols + 2 - 1) seed) =
          selector.eval
            (successorFeature head F y +
              constantImage (rows + 2 - 1) (cols + 2 - 1) seed) := by
      rw [← eval_eq x hx, ← eval_eq y hy]
      exact hcomposed
    have hsuccessor : successorFeature head F x =
        successorFeature head F y :=
      selectionSpec.injective_on_rootPuncturedSoutheast
        hx hy hprotected hselector
    exact headEval_eq_of_successorFeature_eq head F hsuccessor

namespace CompiledSuccessorSelectionSchedule

/-- Every compiled finite schedule canonically determines a heterogeneous
recovery chain from the head-network feature family to the final composed
network feature family. -/
def recoveryChain
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule) :
    RelativeRecoveryChain K (fun x ↦ head.eval (F x))
      (fun x ↦ compiled.finalNetwork.eval (F x)) :=
  match compiled with
  | .nil _head => .nil _
  | .cons head _rowSteps _extraColSteps _targetRow _targetCol
      _threshold _hrowSteps _hcolSteps _tail _seed _selectorBias
      _selector _hseed _hselectorBias selectionSpec eval_eq compiledTail =>
      .cons (appendedSelectionRecoveryStep F head selectionSpec eval_eq)
        compiledTail.recoveryChain

/-- The recovery chain has exactly one step for every scheduled selector. -/
theorem length_recoveryChain
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule) :
    compiled.recoveryChain.length = schedule.length := by
  induction compiled with
  | nil => rfl
  | cons head rowSteps extraColSteps targetRow targetCol threshold
      hrowSteps hcolSteps tail seed selectorBias selector hseed
      hselectorBias selectionSpec eval_eq compiledTail ih =>
      change compiledTail.recoveryChain.length + 1 = tail.length + 1
      rw [ih]

/-- Equality of final network outputs recovers equality of head-network
outputs whenever every local scheduled protection condition holds. -/
theorem recover_headEval
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hprotected : compiled.recoveryChain.Protected x y)
    (heq : compiled.finalNetwork.eval (F x) =
      compiled.finalNetwork.eval (F y)) :
    head.eval (F x) = head.eval (F y) := by
  exact compiled.recoveryChain.recover hx hy hprotected heq

/-- If the head feature family is injective on the compact set and every pair
in that set satisfies the compiled local protection conditions, then the
single final composed CNN is injective on that set. -/
theorem finalNetwork_injectiveOn
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    (hhead : Set.InjOn (fun x ↦ head.eval (F x)) K)
    (hprotected : ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
      compiled.recoveryChain.Protected x y) :
    Set.InjOn (fun x ↦ compiled.finalNetwork.eval (F x)) K := by
  intro x hx y hy heq
  exact hhead hx hy
    (compiled.recover_headEval hx hy (hprotected hx hy) heq)

end CompiledSuccessorSelectionSchedule

end OneChannelCNNUniversality
