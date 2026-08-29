import OneChannelCNNUniversality.SharedBiasFrontierChain

/-!
# Turning a lossless frontier from east to south

The horizontal moving-frontier chain is followed by genuine zero-bias
vertical accumulation.  For a two-register northwest seed with vacant lower
rows, the work/backup pair reaches an arbitrary southeast frontier coordinate
with its values unchanged during the vertical leg.  Both columns remain
vacant below the new frontier, and the complete CNN stays injective on
nonnegative input families.
-/

namespace OneChannelCNNUniversality

universe u

/-- Every row strictly south of the northwest row is vacant. -/
def SouthRowsVacant {rows cols : ℕ} (x : Image rows cols) : Prop :=
  ∀ p, 1 ≤ p → ∀ q, zeroExtend x p q = 0

/-- A northwest work/backup pair followed by a vacant eastern tail and with
all lower rows vacant. -/
def NorthwestTwoRegisterSeed {rows cols : ℕ} (x : Image rows cols) : Prop :=
  EastTailVacant x ∧ SouthRowsVacant x

/-- Exact state after `colSteps` eastern advances followed by `rowSteps`
southern advances.  The two active columns remain vacant below the frontier. -/
def TwoDimensionalFrontierInvariant
    {rows cols outRows outCols : ℕ}
    (source : Image rows cols) (rowSteps colSteps : ℕ)
    (state : Image outRows outCols) : Prop :=
  zeroExtend state rowSteps colSteps =
      zeroExtend source 0 0 + (colSteps : ℝ) * zeroExtend source 0 1 ∧
    zeroExtend state rowSteps (colSteps + 1) = zeroExtend source 0 1 ∧
    ∀ p, rowSteps + 1 ≤ p →
      zeroExtend state p colSteps = 0 ∧
        zeroExtend state p (colSteps + 1) = 0

/-- A Pascal recurrence applied to the zero sequence remains zero. -/
theorem iteratePairKernel_eq_zero_of_eq_zero
    (u : ℕ → ℝ) (hu : ∀ q, u q = 0) (steps q : ℕ) :
    iteratePairKernel steps u q = 0 := by
  induction steps generalizing q with
  | zero => exact hu q
  | succ steps ih =>
      rw [iteratePairKernel_succ, ih]
      cases q with
      | zero => simp [predecessor]
      | succ q =>
          simp only [predecessor]
          rw [ih]
          ring

/-- Horizontal accumulation never introduces a nonzero value into a row that
was entirely vacant. -/
theorem iterateHorizontalAccumulation_southRowsVacant
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols)
    (hsouth : SouthRowsVacant x) :
    SouthRowsVacant
      (iterateFullConv horizontalAccumulationKernel steps x) := by
  intro p hp q
  rw [← horizontalPairKernel_two_eq_accumulation,
    zeroExtend_iterateFullConv_horizontal,
    ← iteratePairKernel_eq_iterate]
  exact iteratePairKernel_eq_zero_of_eq_zero
    (fun j ↦ zeroExtend x p j) (fun j ↦ hsouth p hp j) steps q

/-- The linear horizontal-then-vertical Pascal transform realizes the exact
two-dimensional frontier turn. -/
theorem iteratePascalGrid_frontierInvariant
    {rows cols : ℕ} (rowSteps colSteps : ℕ) (x : Image rows cols)
    (hseed : NorthwestTwoRegisterSeed x) :
    TwoDimensionalFrontierInvariant x rowSteps colSteps
      (iterateFullConv verticalAccumulationKernel rowSteps
        (iterateFullConv horizontalAccumulationKernel colSteps x)) := by
  let mid := iterateFullConv horizontalAccumulationKernel colSteps x
  have hhorizontal : HorizontalFrontierInvariant x colSteps mid :=
    iterateHorizontalAccumulation_frontierInvariant colSteps x hseed.1
  have hsouthMid : SouthRowsVacant mid :=
    iterateHorizontalAccumulation_southRowsVacant colSteps x hseed.2
  have hvertical (q : ℕ) := iteratePairKernel_frontierInvariant
    (fun p ↦ zeroExtend mid p q)
    (fun p hp ↦ hsouthMid p (by omega) q) rowSteps
  have hfront (q : ℕ) :
      zeroExtend
          (iterateFullConv verticalAccumulationKernel rowSteps mid)
          rowSteps q = zeroExtend mid 0 q := by
    rw [← verticalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_vertical,
      ← iteratePairKernel_eq_iterate]
    rw [(hvertical q).1, hsouthMid 1 (by omega) q]
    ring
  have hnext (q : ℕ) :
      zeroExtend
          (iterateFullConv verticalAccumulationKernel rowSteps mid)
          (rowSteps + 1) q = 0 := by
    rw [← verticalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_vertical,
      ← iteratePairKernel_eq_iterate]
    rw [(hvertical q).2.1, hsouthMid 1 (by omega) q]
  have htail (q p : ℕ) (hp : rowSteps + 2 ≤ p) :
      zeroExtend
          (iterateFullConv verticalAccumulationKernel rowSteps mid) p q = 0 := by
    rw [← verticalPairKernel_two_eq_accumulation,
      zeroExtend_iterateFullConv_vertical,
      ← iteratePairKernel_eq_iterate]
    exact (hvertical q).2.2 p hp
  unfold TwoDimensionalFrontierInvariant
  change
    zeroExtend
        (iterateFullConv verticalAccumulationKernel rowSteps mid)
        rowSteps colSteps = _ ∧ _
  constructor
  · rw [hfront]
    exact hhorizontal.1
  constructor
  · rw [hfront]
    exact hhorizontal.2.1
  · intro p hp
    by_cases heq : p = rowSteps + 1
    · subst p
      exact ⟨hnext colSteps, hnext (colSteps + 1)⟩
    · have hpTail : rowSteps + 2 ≤ p := by omega
      exact ⟨htail colSteps p hpTail,
        htail (colSteps + 1) p hpTail⟩

/-- The genuine shared-bias CNN that first advances east and then turns
south. -/
def twoDimensionalFrontierNetwork {rows cols : ℕ}
    (rowSteps colSteps : ℕ) :
    SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
      (grownSize 2 (grownSize 2 cols colSteps) rowSteps) :=
  zeroBiasPascalGridNetwork rowSteps colSteps

/-- The routed frontier reaches `(rowSteps, colSteps)` in exactly the
Manhattan-distance number of convolution/ReLU layers. -/
theorem twoDimensionalFrontierNetwork_depth
    {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    (twoDimensionalFrontierNetwork (rows := rows) (cols := cols)
      rowSteps colSteps).net.depth = rowSteps + colSteps := by
  exact zeroBiasPascalGridNetwork_depth rowSteps colSteps

/-- On nonnegative input, the genuine two-dimensional frontier network is
exactly its linear Pascal transform. -/
theorem twoDimensionalFrontierNetwork_eval_of_nonnegative
    {rows cols : ℕ} (rowSteps colSteps : ℕ) (x : Image rows cols)
    (hx : ImageNonnegative x) :
    (twoDimensionalFrontierNetwork rowSteps colSteps).eval x =
      iterateFullConv verticalAccumulationKernel rowSteps
        (iterateFullConv horizontalAccumulationKernel colSteps x) := by
  exact zeroBiasPascalGridNetwork_eval_of_nonnegative
    rowSteps colSteps x hx

/-- On any nonnegative injective family of northwest two-register seeds, the
genuine east-then-south CNN remains injective and satisfies the exact turned
frontier invariant. -/
theorem twoDimensionalFrontierNetwork_injectiveOn_and_invariant
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFseed : ∀ x ∈ K, NorthwestTwoRegisterSeed (F x))
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
        (fun x ↦
          (twoDimensionalFrontierNetwork rowSteps colSteps).eval (F x)) K ∧
      ∀ x ∈ K,
        TwoDimensionalFrontierInvariant (F x) rowSteps colSteps
          ((twoDimensionalFrontierNetwork rowSteps colSteps).eval (F x)) := by
  constructor
  · intro x hx y hy heval
    apply hFinjective hx hy
    have hinjective := pascalGridTransform_injective
      (rows := rows) (cols := cols) rowSteps colSteps
    rw [horizontalPairKernel_two_eq_accumulation,
      verticalPairKernel_two_eq_accumulation] at hinjective
    apply hinjective
    change
      iterateFullConv verticalAccumulationKernel rowSteps
          (iterateFullConv horizontalAccumulationKernel colSteps (F x)) =
        iterateFullConv verticalAccumulationKernel rowSteps
          (iterateFullConv horizontalAccumulationKernel colSteps (F y))
    rw [← twoDimensionalFrontierNetwork_eval_of_nonnegative
        rowSteps colSteps (F x) (hFnonnegative x hx),
      ← twoDimensionalFrontierNetwork_eval_of_nonnegative
        rowSteps colSteps (F y) (hFnonnegative y hy)]
    exact heval
  · intro x hx
    rw [twoDimensionalFrontierNetwork_eval_of_nonnegative
      rowSteps colSteps (F x) (hFnonnegative x hx)]
    exact iteratePascalGrid_frontierInvariant
      rowSteps colSteps (F x) (hFseed x hx)

end OneChannelCNNUniversality
