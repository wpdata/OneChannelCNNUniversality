import OneChannelCNNUniversality.SharedBiasChainLayout

/-!
# Protected selection on a monotone row chain

This file connects the combinatorial row-chain layout to the genuine bundled
shared-bias selection network.  Agreement on a chain prefix is exactly the
root-punctured southeast variation invariant required by relative
injectivity.  Consequently, one protected selection block is recoverable
whenever the already-processed prefix is fixed.
-/

namespace OneChannelCNNUniversality

/-- The unique row coordinate of a one-row image. -/
def rowZero : Fin 1 := ⟨0, by omega⟩

/-- Two one-row states agree through the target index, inclusive. -/
def RowPrefixAgree {n : ℕ}
    (x y : Image 1 n) (target : Fin n) : Prop :=
  ∀ j, j ≤ target → x rowZero j = y rowZero j

/-- On a one-row image, prefix agreement is precisely agreement outside the
southeast suffix together with agreement at its root. -/
theorem rowPrefixAgree_iff_agreeOutsideStrictSoutheast
    {n : ℕ} {x y : Image 1 n} {target : Fin n} :
    RowPrefixAgree x y target ↔
      AgreeOutsideStrictSoutheast x y rowZero target := by
  constructor
  · intro hprefix
    constructor
    · intro i j houtside
      by_cases hi : i < 1
      · have hi0 : i = 0 := by omega
        subst i
        by_cases hj : j < n
        · have hjle : j ≤ (target : ℕ) := by
            by_contra hle
            apply houtside
            exact ⟨by omega, by omega⟩
          have hentry := hprefix ⟨j, hj⟩ (by exact_mod_cast hjle)
          simpa [zeroExtend, rowZero, hj] using hentry
        · simp [zeroExtend, hj]
      · simp [zeroExtend, hi]
    · have hentry := hprefix target le_rfl
      simpa [zeroExtend, rowZero, target.isLt] using hentry
  · intro hstrict j hj
    have hentry := hstrict.northwestAgree
      (rowZero : ℕ) le_rfl (j : ℕ) (by exact_mod_cast hj)
    simpa [rowZero] using hentry

/-- Output-typed network used for a protected selection on a one-row chain. -/
abbrev RowChainSelectionNetwork
    (n rowSteps extraColSteps : ℕ) :=
  SharedBiasNetworkTo 2 2 1 n
    (grownSize 2 (grownSize 2 (1 + 2 - 1) extraColSteps) rowSteps + 2 - 1)
    (grownSize 2 (grownSize 2 (n + 2 - 1) extraColSteps) rowSteps + 2 - 1)

/-- The general bundled protected-selection contract specialized to a
one-row chain and its unique row coordinate. -/
def BundledRowChainSelectionSpec
    {X : Type*} {n : ℕ} (K : Set X) (V : X → Image 1 n)
    (θ : ℝ) (rowSteps extraColSteps : ℕ)
    (target : Fin n) (c b : ℝ)
    (net : RowChainSelectionNetwork n rowSteps extraColSteps) : Prop :=
  BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
    rowZero target c b net

/-- A genuine protected shared-bias selection block is relatively injective
on one-row states that agree on the already-processed prefix. -/
theorem BundledRowChainSelectionSpec.injective_of_rowPrefixAgree
    {X : Type*} {K : Set X} {n : ℕ}
    {V : X → Image 1 n} {θ : ℝ} {rowSteps extraColSteps : ℕ}
    {target : Fin n} {c b : ℝ}
    {net : RowChainSelectionNetwork n rowSteps extraColSteps}
    (hspec : BundledRowChainSelectionSpec K V θ rowSteps extraColSteps
      target c b net) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hprefix : RowPrefixAgree (V x) (V y) target)
    (heval : net.eval (V x + constantImage 1 n c) =
      net.eval (V y + constantImage 1 n c)) :
    V x = V y := by
  exact BundledPascalGridSelectionSpec.injective_on_rootPuncturedSoutheast
    hspec hx hy
      (rowPrefixAgree_iff_agreeOutsideStrictSoutheast.mp hprefix) heval

/-- Compactness supplies a genuine bundled selection network on any finite
row chain together with its prefix-relative recovery guarantee. -/
theorem exists_bundled_rowChain_protected_selection
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (V : X → Image 1 n) (hV : ContinuousFeatureOn K V)
    (rowSteps extraColSteps : ℕ) (target : Fin n) (θ : ℝ)
    (hcolSteps : n - 1 ≤ extraColSteps + 1) :
    ∃ c b : ℝ, ∃ net : RowChainSelectionNetwork n rowSteps extraColSteps,
      0 < c ∧ 0 < b ∧ net.net.depth = rowSteps + extraColSteps + 2 ∧
        BundledRowChainSelectionSpec K V θ rowSteps extraColSteps
          target c b net ∧
        ∀ {x y : X}, x ∈ K → y ∈ K →
          RowPrefixAgree (V x) (V y) target →
          net.eval (V x + constantImage 1 n c) =
            net.eval (V y + constantImage 1 n c) →
          V x = V y := by
  obtain ⟨c, b, net, hc, hb, hdepth, hspec⟩ :=
    exists_bundled_pascal_grid_protected_selection hK V hV
      rowSteps extraColSteps rowZero target θ (by omega) hcolSteps
  refine ⟨c, b, net, hc, hb, hdepth, hspec, ?_⟩
  intro x y hx hy hprefix heval
  exact BundledRowChainSelectionSpec.injective_of_rowPrefixAgree
    hspec hx hy hprefix heval

end OneChannelCNNUniversality
