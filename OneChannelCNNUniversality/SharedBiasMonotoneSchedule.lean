import OneChannelCNNUniversality.SharedBiasFiniteSelection
import OneChannelCNNUniversality.SharedBiasMonotoneCode

/-!
# Northwest monotone codes through finite compiled schedules

The one-step monotone-code theorem composes through an arbitrary finite
compiled schedule provided every requested selector acts on the northwest
work register.  The proof follows the dependent schedule recursively.  At
each stage the expansive delta bridge transports the current code to the
successor feature, and the genuine `appendWithSeed` block transports it to
the next network output.
-/

namespace OneChannelCNNUniversality

universe u

namespace SuccessorSelectionSchedule

/-- Every selector in the dependent schedule targets the northwest work
register.  The condition is retained explicitly because the general schedule
type also supports arbitrary spatial targets. -/
def NorthwestTargeted {rows cols : ℕ} :
    SuccessorSelectionSchedule rows cols → Prop
  | .nil _ _ => True
  | .cons _ _ targetRow targetCol _ _ _ tail =>
      targetRow.val = 0 ∧ targetCol.val = 0 ∧ tail.NorthwestTargeted

end SuccessorSelectionSchedule

/-- Every protected selector output has at least two columns (and, by the
same calculation, at least two rows).  This supplies the eastern backup
coordinate required by the monotone-code invariant at every later stage. -/
theorem two_le_protectedSelectionSize
    (n rowSteps extraColSteps : ℕ) :
    2 ≤ protectedSelectionSize n rowSteps extraColSteps := by
  have hextra := grownSize_ge_add_steps 2 (n + 2 - 1)
    extraColSteps (by omega)
  have hrows := grownSize_ge_add_steps 2
    (grownSize 2 (n + 2 - 1) extraColSteps) rowSteps (by omega)
  simp only [protectedSelectionSize]
  omega

namespace CompiledSuccessorSelectionSchedule

/-- A northwest monotone code on the current genuine network output is
preserved by every stage of a northwest-targeted compiled schedule. -/
theorem preserves_northwestMonotoneCode
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    (hcols : 2 ≤ cols) (code : X → ℝ)
    (hcode : NorthwestMonotoneCodeOn K
      (fun x ↦ head.eval (F x)) code)
    (htargets : schedule.NorthwestTargeted) :
    NorthwestMonotoneCodeOn K
      (fun x ↦ compiled.finalNetwork.eval (F x)) code := by
  induction compiled generalizing code with
  | nil head =>
      exact hcode
  | cons head rowSteps extraColSteps targetRow targetCol threshold
      hrowSteps hcolSteps tail seed selectorBias selector hseed
      hselectorBias selectionSpec eval_eq compiledTail ih =>
      change targetRow.val = 0 ∧ targetCol.val = 0 ∧
        tail.NorthwestTargeted at htargets
      have htargetRow : targetRow =
          ⟨0, lt_of_le_of_lt (Nat.zero_le targetRow.val)
            targetRow.isLt⟩ :=
        Fin.ext htargets.1
      have htargetCol : targetCol =
          ⟨0, lt_of_le_of_lt (Nat.zero_le targetCol.val)
            targetCol.isLt⟩ :=
        Fin.ext htargets.2.1
      rw [htargetRow, htargetCol] at selectionSpec
      have hsuccessorCode : NorthwestMonotoneCodeOn K
          (successorFeature head F) code := by
        unfold successorFeature
        exact hcode.expansiveIdentity
      have hnextCode : NorthwestMonotoneCodeOn K
          (fun x ↦ (head.appendWithSeed seed selector).eval (F x)) code :=
        head.appendWithSeed_preserves_northwestMonotoneCode
          (by omega) (by omega) selectionSpec hsuccessorCode eval_eq
      exact ih (two_le_protectedSelectionSize _ _ _) code hnextCode
        htargets.2.2

/-- If the current genuine network is injective on `K`, every stage of a
northwest-targeted compiled schedule preserves that injectivity.  The local
recovery premise is supplied by the monotone code rather than the globally
constant target condition used by the older protection-chain theorem. -/
theorem finalNetwork_injectiveOn_of_northwestMonotoneCode
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    (hcols : 2 ≤ cols) (code : X → ℝ)
    (hcode : NorthwestMonotoneCodeOn K
      (fun x ↦ head.eval (F x)) code)
    (hheadInjective : Set.InjOn (fun x ↦ head.eval (F x)) K)
    (htargets : schedule.NorthwestTargeted) :
    Set.InjOn (fun x ↦ compiled.finalNetwork.eval (F x)) K := by
  induction compiled generalizing code with
  | nil head =>
      exact hheadInjective
  | cons head rowSteps extraColSteps targetRow targetCol threshold
      hrowSteps hcolSteps tail seed selectorBias selector hseed
      hselectorBias selectionSpec eval_eq compiledTail ih =>
      change targetRow.val = 0 ∧ targetCol.val = 0 ∧
        tail.NorthwestTargeted at htargets
      have htargetRow : targetRow =
          ⟨0, lt_of_le_of_lt (Nat.zero_le targetRow.val)
            targetRow.isLt⟩ :=
        Fin.ext htargets.1
      have htargetCol : targetCol =
          ⟨0, lt_of_le_of_lt (Nat.zero_le targetCol.val)
            targetCol.isLt⟩ :=
        Fin.ext htargets.2.1
      rw [htargetRow, htargetCol] at selectionSpec
      have hsuccessorCode : NorthwestMonotoneCodeOn K
          (successorFeature head F) code := by
        unfold successorFeature
        exact hcode.expansiveIdentity
      have hnextCode : NorthwestMonotoneCodeOn K
          (fun x ↦ (head.appendWithSeed seed selector).eval (F x)) code :=
        head.appendWithSeed_preserves_northwestMonotoneCode
          (by omega) (by omega) selectionSpec hsuccessorCode eval_eq
      have hnextInjective : Set.InjOn
          (fun x ↦ (head.appendWithSeed seed selector).eval (F x)) K :=
        head.appendWithSeed_injectiveOn_of_northwestMonotoneCode
          (by omega) (by omega) selectionSpec hsuccessorCode
          hheadInjective eval_eq
      exact ih (two_le_protectedSelectionSize _ _ _) code hnextCode
        hnextInjective htargets.2.2

/-- The preservation and injectivity conclusions packaged together for
clients that maintain both certificates while extending a schedule. -/
theorem monotoneCode_and_injectiveOn
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols}
    (compiled : CompiledSuccessorSelectionSchedule K F head schedule)
    (hcols : 2 ≤ cols) (code : X → ℝ)
    (hcode : NorthwestMonotoneCodeOn K
      (fun x ↦ head.eval (F x)) code)
    (hheadInjective : Set.InjOn (fun x ↦ head.eval (F x)) K)
    (htargets : schedule.NorthwestTargeted) :
    NorthwestMonotoneCodeOn K
        (fun x ↦ compiled.finalNetwork.eval (F x)) code ∧
      Set.InjOn (fun x ↦ compiled.finalNetwork.eval (F x)) K := by
  exact ⟨compiled.preserves_northwestMonotoneCode
      hcols code hcode htargets,
    compiled.finalNetwork_injectiveOn_of_northwestMonotoneCode
      hcols code hcode hheadInjective htargets⟩

end CompiledSuccessorSelectionSchedule

/-- End-to-end finite northwest computation from a genuine adjacent-copy
initialization.  Compactness compiles every requested selector into an
internal-seed shared-bias CNN, while the monotone code proves that the final
single network remains injective on `K`. -/
theorem exists_injective_compiledNorthwestSchedule
    {X : Type u} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 0 < cols)
    (F : X → Image rows cols) (hF : ContinuousFeatureOn K F)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFvacant : ∀ x ∈ K, EastNeighborVacant (F x))
    (hFinjective : Set.InjOn F K)
    (schedule : SuccessorSelectionSchedule
      (rows + 2 - 1) (cols + 2 - 1))
    (htargets : schedule.NorthwestTargeted) :
    ∃ compiled : CompiledSuccessorSelectionSchedule K F
        (adjacentCopyLayer (rows := rows) (cols := cols)) schedule,
      NorthwestMonotoneCodeOn K
          (fun x ↦ compiled.finalNetwork.eval (F x))
          (fun x ↦ zeroExtend (F x) 0 0) ∧
        Set.InjOn (fun x ↦ compiled.finalNetwork.eval (F x)) K := by
  let head : SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1) (cols + 2 - 1) := adjacentCopyLayer
  have hdepth : 0 < head.net.depth := by
    simp [head, adjacentCopyLayer, SharedBiasNetworkTo.single,
      SharedBiasNetworkTo.cons, SharedBiasNetworkTo.nil,
      SharedBiasNetwork.depth]
  obtain ⟨compiled⟩ := exists_compiledSuccessorSelectionSchedule
    hK F hF head hdepth schedule
  have hinitialCode : NorthwestMonotoneCodeOn K
      (fun x ↦ head.eval (F x))
      (fun x ↦ zeroExtend (F x) 0 0) := by
    exact northwestMonotoneCodeOn_adjacentCopy hrows hcols F
      hFnonnegative hFvacant
  have hheadInjective : Set.InjOn (fun x ↦ head.eval (F x)) K := by
    intro x hx y hy heval
    apply hFinjective hx hy
    exact adjacentCopyLayer_injective_of_nonnegative
      (hFnonnegative x hx) (hFnonnegative y hy) heval
  refine ⟨compiled, ?_⟩
  exact compiled.monotoneCode_and_injectiveOn (by omega)
    (fun x ↦ zeroExtend (F x) 0 0) hinitialCode hheadInjective htargets

end OneChannelCNNUniversality
