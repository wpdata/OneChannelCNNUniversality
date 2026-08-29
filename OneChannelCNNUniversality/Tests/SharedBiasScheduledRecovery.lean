import OneChannelCNNUniversality.SharedBiasScheduledRecovery

open OneChannelCNNUniversality

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule) :
    RelativeRecoveryChain K (fun x ↦ head.eval (F x))
      (fun x ↦ compiled.finalNetwork.eval (F x)) :=
  compiled.recoveryChain

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule) :
    compiled.recoveryChain.length = schedule.length := by
  exact compiled.length_recoveryChain

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hp : compiled.recoveryChain.Protected x y)
    (heq : compiled.finalNetwork.eval (F x) =
      compiled.finalNetwork.eval (F y)) :
    head.eval (F x) = head.eval (F y) := by
  exact compiled.recover_headEval hx hy hp heq

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    (hhead : Set.InjOn (fun x ↦ head.eval (F x)) K)
    (hprotected : ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K →
      compiled.recoveryChain.Protected x y) :
    Set.InjOn (fun x ↦ compiled.finalNetwork.eval (F x)) K := by
  exact compiled.finalNetwork_injectiveOn hhead hprotected

#check appendedSelectionRecoveryStep
#check CompiledSuccessorSelectionSchedule.recoveryChain
#check CompiledSuccessorSelectionSchedule.finalNetwork_injectiveOn
