import OneChannelCNNUniversality.SharedBiasFrontier
import OneChannelCNNUniversality.SharedBiasGridScan

/-!
# A lossless horizontal moving-frontier chain

A vacant eastern tail lets repeated zero-bias horizontal accumulation carry
two registers through an arbitrarily long genuine shared-bias CNN.  After
`steps` layers, the work register has moved to column `steps`, the unchanged
backup register has moved to column `steps + 1`, and the remaining eastern
tail is still vacant.  The complete representation remains injective on
nonnegative input families.
-/

namespace OneChannelCNNUniversality

universe u

/-- Every northwest-row coordinate from column two onward is initially
vacant. -/
def EastTailVacant {rows cols : ℕ} (x : Image rows cols) : Prop :=
  ∀ q, 2 ≤ q → zeroExtend x 0 q = 0

/-- The exact work/backup/tail state after a horizontal frontier has advanced
`steps` columns from its source image. -/
def HorizontalFrontierInvariant
    {rows cols outRows outCols : ℕ}
    (source : Image rows cols) (steps : ℕ)
    (state : Image outRows outCols) : Prop :=
  zeroExtend state 0 steps =
      zeroExtend source 0 0 + (steps : ℝ) * zeroExtend source 0 1 ∧
    zeroExtend state 0 (steps + 1) = zeroExtend source 0 1 ∧
    ∀ q, steps + 2 ≤ q → zeroExtend state 0 q = 0

/-- The one-dimensional Pascal recurrence advances the work register while
copying its backup and preserving a vacant tail. -/
theorem iteratePairKernel_frontierInvariant
    (u : ℕ → ℝ) (htail : ∀ q, 2 ≤ q → u q = 0) (steps : ℕ) :
    iteratePairKernel steps u steps = u 0 + (steps : ℝ) * u 1 ∧
      iteratePairKernel steps u (steps + 1) = u 1 ∧
      ∀ q, steps + 2 ≤ q → iteratePairKernel steps u q = 0 := by
  induction steps with
  | zero =>
      constructor
      · simp
      constructor
      · rfl
      · intro q hq
        exact htail q hq
  | succ steps ih =>
      rcases ih with ⟨hwork, hbackup, htailSteps⟩
      constructor
      · rw [iteratePairKernel_succ]
        simp only [predecessor]
        rw [hbackup, hwork]
        push_cast
        ring
      constructor
      · rw [iteratePairKernel_succ]
        simp only [predecessor]
        rw [htailSteps (steps + 2) (by omega), hbackup]
        ring
      · intro q hq
        rw [iteratePairKernel_succ]
        obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := by
          exact ⟨q - 1, by omega⟩
        simp only [predecessor]
        rw [htailSteps (q + 1) (by omega), htailSteps q (by omega)]
        ring

/-- Repeated horizontal full convolution satisfies the moving-frontier
invariant exactly, before ReLU semantics are introduced. -/
theorem iterateHorizontalAccumulation_frontierInvariant
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols)
    (htail : EastTailVacant x) :
    HorizontalFrontierInvariant x steps
      (iterateFullConv horizontalAccumulationKernel steps x) := by
  have hpair := iteratePairKernel_frontierInvariant
    (fun q ↦ zeroExtend x 0 q) htail steps
  unfold HorizontalFrontierInvariant
  constructor
  · rw [← horizontalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_horizontal,
      ← iteratePairKernel_eq_iterate]
    exact hpair.1
  constructor
  · rw [← horizontalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_horizontal,
      ← iteratePairKernel_eq_iterate]
    exact hpair.2.1
  · intro q hq
    rw [← horizontalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_horizontal,
      ← iteratePairKernel_eq_iterate]
    exact hpair.2.2 q hq

/-- The genuine fixed-kernel network implementing `steps` horizontal
frontier advances. -/
def horizontalFrontierNetwork {rows cols : ℕ} (steps : ℕ) :
    SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 rows steps) (grownSize 2 cols steps) :=
  zeroBiasIterations horizontalAccumulationKernel steps

/-- On nonnegative input, every ReLU in the frontier network remains in its
linear branch. -/
theorem horizontalFrontierNetwork_eval_of_nonnegative
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols)
    (hx : ImageNonnegative x) :
    (horizontalFrontierNetwork steps).eval x =
      iterateFullConv horizontalAccumulationKernel steps x := by
  exact zeroBiasIterations_eval_of_nonnegative
    horizontalAccumulationKernel_nonnegative steps x hx

/-- A nonnegative injective input family with a vacant eastern tail remains
injectively encoded after any finite number of genuine frontier advances,
and every output satisfies the exact work/backup/tail invariant. -/
theorem horizontalFrontierNetwork_injectiveOn_and_invariant
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (steps : ℕ) (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFtail : ∀ x ∈ K, EastTailVacant (F x))
    (hFinjective : Set.InjOn F K) :
    Set.InjOn (fun x ↦ (horizontalFrontierNetwork steps).eval (F x)) K ∧
      ∀ x ∈ K,
        HorizontalFrontierInvariant (F x) steps
          ((horizontalFrontierNetwork steps).eval (F x)) := by
  constructor
  · intro x hx y hy heval
    apply hFinjective hx hy
    apply horizontalAccumulationIterations_injective steps
    change iterateFullConv horizontalAccumulationKernel steps (F x) =
      iterateFullConv horizontalAccumulationKernel steps (F y)
    rw [← horizontalFrontierNetwork_eval_of_nonnegative steps (F x)
        (hFnonnegative x hx),
      ← horizontalFrontierNetwork_eval_of_nonnegative steps (F y)
        (hFnonnegative y hy)]
    exact heval
  · intro x hx
    rw [horizontalFrontierNetwork_eval_of_nonnegative steps (F x)
      (hFnonnegative x hx)]
    exact iterateHorizontalAccumulation_frontierInvariant
      steps (F x) (hFtail x hx)

end OneChannelCNNUniversality
