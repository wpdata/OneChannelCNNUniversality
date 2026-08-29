import OneChannelCNNUniversality.SharedBiasSuccessorSelection

/-!
# Compiling finite successor-selection schedules

A schedule records a finite sequence of protected Pascal-selection requests.
Its later targets are indexed by the spatial dimensions produced by all
earlier requests.  Compactness chooses the positive carrier seed and selector
bias at each stage.  The compiled certificate retains those witnesses and
ends in one genuine `SharedBiasNetworkTo` obtained only by network
composition and internal seed layers.
-/

namespace OneChannelCNNUniversality

universe u

/-- A finite dependent schedule of protected selections.  The target of each
later request lives in the successor image generated from the output size of
the preceding selection block. -/
inductive SuccessorSelectionSchedule : ℕ → ℕ → Type
  | nil (rows cols : ℕ) : SuccessorSelectionSchedule rows cols
  | cons {rows cols : ℕ}
      (rowSteps extraColSteps : ℕ)
      (targetRow : Fin (rows + 2 - 1))
      (targetCol : Fin (cols + 2 - 1))
      (threshold : ℝ)
      (hrowSteps : (rows + 2 - 1) - 1 ≤ rowSteps)
      (hcolSteps : (cols + 2 - 1) - 1 ≤ extraColSteps + 1)
      (tail : SuccessorSelectionSchedule
        (protectedSelectionSize (rows + 2 - 1) rowSteps extraColSteps)
        (protectedSelectionSize (cols + 2 - 1) rowSteps extraColSteps)) :
      SuccessorSelectionSchedule rows cols

namespace SuccessorSelectionSchedule

/-- Number of scheduled selector blocks. -/
def length {rows cols : ℕ} : SuccessorSelectionSchedule rows cols → ℕ
  | .nil _ _ => 0
  | .cons _ _ _ _ _ _ _ tail => tail.length + 1

/-- Row dimension of the network after compiling the whole schedule. -/
def finalRows {rows cols : ℕ} : SuccessorSelectionSchedule rows cols → ℕ
  | .nil rows _ => rows
  | .cons _ _ _ _ _ _ _ tail => tail.finalRows

/-- Column dimension of the network after compiling the whole schedule. -/
def finalCols {rows cols : ℕ} : SuccessorSelectionSchedule rows cols → ℕ
  | .nil _ cols => cols
  | .cons _ _ _ _ _ _ _ tail => tail.finalCols

end SuccessorSelectionSchedule

/-- Evidence produced by compiling a finite successor-selection schedule.
Every nonempty stage stores the compactness-generated positive constants,
the protected selector and its exact evaluation equation. -/
inductive CompiledSuccessorSelectionSchedule
    {X : Type u} [TopologicalSpace X] (K : Set X)
    {inRows inCols : ℕ} (F : X → Image inRows inCols) :
    {rows cols : ℕ} →
      (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols) →
      SuccessorSelectionSchedule rows cols → Type (u + 1)
  | nil {rows cols : ℕ}
      (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols) :
      CompiledSuccessorSelectionSchedule K F head
        (.nil rows cols)
  | cons {rows cols : ℕ}
      (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
      (rowSteps extraColSteps : ℕ)
      (targetRow : Fin (rows + 2 - 1))
      (targetCol : Fin (cols + 2 - 1))
      (threshold : ℝ)
      (hrowSteps : (rows + 2 - 1) - 1 ≤ rowSteps)
      (hcolSteps : (cols + 2 - 1) - 1 ≤ extraColSteps + 1)
      (tail : SuccessorSelectionSchedule
        (protectedSelectionSize (rows + 2 - 1) rowSteps extraColSteps)
        (protectedSelectionSize (cols + 2 - 1) rowSteps extraColSteps))
      (seed selectorBias : ℝ)
      (selector : SharedBiasNetworkTo 2 2
        (rows + 2 - 1) (cols + 2 - 1)
        (protectedSelectionSize (rows + 2 - 1) rowSteps extraColSteps)
        (protectedSelectionSize (cols + 2 - 1) rowSteps extraColSteps))
      (hseed : 0 < seed) (hselectorBias : 0 < selectorBias)
      (selectionSpec : BundledPascalGridSelectionSpec K
        (successorFeature head F) threshold rowSteps extraColSteps
        targetRow targetCol seed selectorBias selector)
      (eval_eq : ∀ x ∈ K,
        (head.appendWithSeed seed selector).eval (F x) =
          selector.eval
            (successorFeature head F x +
              constantImage (rows + 2 - 1) (cols + 2 - 1) seed))
      (compiledTail : CompiledSuccessorSelectionSchedule K F
        (head.appendWithSeed seed selector) tail) :
      CompiledSuccessorSelectionSchedule K F head
        (.cons rowSteps extraColSteps targetRow targetCol threshold
          hrowSteps hcolSteps tail)

namespace CompiledSuccessorSelectionSchedule

/-- The single genuine expansive shared-bias CNN obtained at the end of a
compiled schedule. -/
def finalNetwork
    {X : Type u} [TopologicalSpace X] {K : Set X}
    {inRows inCols rows cols : ℕ} {F : X → Image inRows inCols}
    {head : SharedBiasNetworkTo 2 2 inRows inCols rows cols}
    {schedule : SuccessorSelectionSchedule rows cols} :
    CompiledSuccessorSelectionSchedule K F head schedule →
      SharedBiasNetworkTo 2 2 inRows inCols
        schedule.finalRows schedule.finalCols
  | .nil head => head
  | .cons _head _rowSteps _extraColSteps _targetRow _targetCol
      _threshold _hrowSteps _hcolSteps _tail _seed _selectorBias
      _selector _hseed _hselectorBias _selectionSpec _eval_eq compiledTail =>
      compiledTail.finalNetwork

end CompiledSuccessorSelectionSchedule

/-- Every finite successor-selection schedule over a compact input family can
be compiled.  At each induction step compactness supplies new positive
parameters, while `appendWithSeed` keeps the complete construction inside one
shared-bias CNN. -/
theorem exists_compiledSuccessorSelectionSchedule
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {inRows inCols rows cols : ℕ} (F : X → Image inRows inCols)
    (hF : ContinuousFeatureOn K F)
    (head : SharedBiasNetworkTo 2 2 inRows inCols rows cols)
    (hhead : 0 < head.net.depth)
    (schedule : SuccessorSelectionSchedule rows cols) :
    Nonempty (CompiledSuccessorSelectionSchedule K F head schedule) := by
  induction schedule with
  | nil rows cols =>
      exact ⟨.nil head⟩
  | @cons rows cols rowSteps extraColSteps targetRow targetCol threshold
      hrowSteps hcolSteps tail ih =>
      obtain ⟨seed, selectorBias, selector, hseed, hselectorBias,
        selectionSpec, eval_eq⟩ :=
        exists_bundled_pascal_selection_after hK head hhead F hF
          rowSteps extraColSteps targetRow targetCol threshold
          hrowSteps hcolSteps
      have hnext : 0 < (head.appendWithSeed seed selector).net.depth := by
        rw [SharedBiasNetworkTo.depth_appendWithSeed]
        omega
      obtain ⟨compiledTail⟩ := ih
        (head := head.appendWithSeed seed selector) hnext
      exact ⟨.cons head rowSteps extraColSteps targetRow targetCol threshold
        hrowSteps hcolSteps tail seed selectorBias selector hseed
        hselectorBias selectionSpec eval_eq compiledTail⟩

end OneChannelCNNUniversality
