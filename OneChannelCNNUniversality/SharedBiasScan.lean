import OneChannelCNNUniversality.SharedBiasAddress
import OneChannelCNNUniversality.SparseEncoder

/-!
# Monotone scan addresses from repeated positive accumulation

Repeated use of the horizontal two-tap kernel `(1, 1)` produces Pascal
prefix sums on a constant carrier.  With enough steps these values are
strictly increasing across every original row.  Consequently, any chosen
column is the unique lowest address among the still-unprocessed suffix of
that row.
-/

namespace OneChannelCNNUniversality

/-- Prefix sum of one row of Pascal's triangle, regarded as a real number. -/
def pascalPrefix (steps q : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (q + 1), (Nat.choose steps r : ℝ)

/-- One new Pascal coefficient is exposed at each successive coordinate. -/
theorem pascalPrefix_succ_sub (steps q : ℕ) :
    pascalPrefix steps (q + 1) - pascalPrefix steps q =
      (Nat.choose steps (q + 1) : ℝ) := by
  simp [pascalPrefix, Finset.sum_range_succ]

theorem pascalPrefix_monotone (steps : ℕ) : Monotone (pascalPrefix steps) := by
  intro p q hpq
  unfold pascalPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hpq))
    (fun _ _ _ ↦ by positivity)

/-- Before the binomial support is exhausted, every later prefix is at least
one unit above every earlier prefix. -/
theorem pascalPrefix_gap (steps s q : ℕ) (hsq : s < q) (hq : q ≤ steps) :
    1 ≤ pascalPrefix steps q - pascalPrefix steps s := by
  have hsstep : s + 1 ≤ steps := by omega
  have hchooseNat : 0 < Nat.choose steps (s + 1) := Nat.choose_pos hsstep
  have hchoose : (1 : ℝ) ≤ (Nat.choose steps (s + 1) : ℝ) := by
    exact_mod_cast hchooseNat
  have hfirst : 1 ≤ pascalPrefix steps (s + 1) - pascalPrefix steps s := by
    rw [pascalPrefix_succ_sub]
    exact hchoose
  have hmono : pascalPrefix steps (s + 1) ≤ pascalPrefix steps q :=
    pascalPrefix_monotone steps (by omega)
  linarith

/-- The actual constant carrier after repeated horizontal `2 × 2`
accumulation, restricted back to the original rectangle. -/
def protectedHorizontalScanAddress (steps rows cols : ℕ) (c : ℝ) :
    Image rows cols :=
  fun i j ↦ zeroExtend
    (iterateFullConv
      (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
      steps (constantImage rows cols c)) i j

/-- On every original row the repeated carrier is exactly a scaled Pascal
prefix. -/
theorem protectedHorizontalScanAddress_eq {rows cols : ℕ}
    (steps : ℕ) (c : ℝ) (i : Fin rows) (j : Fin cols) :
    protectedHorizontalScanAddress steps rows cols c i j =
      c * pascalPrefix steps j := by
  unfold protectedHorizontalScanAddress
  rw [zeroExtend_iterateFullConv_horizontal
    (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega)]
  rw [← congrFun (iteratePairKernel_eq_iterate steps
    (fun t ↦ zeroExtend (constantImage rows cols c) i t)) j]
  rw [iteratePairKernel_eq_sum_choose]
  have hinside : ∀ t ∈ Finset.range ((j : ℕ) + 1),
      zeroExtend (constantImage rows cols c) i t = c := by
    intro t ht
    have htlt : t < cols := by
      have := Finset.mem_range.mp ht
      omega
    simp [zeroExtend, constantImage, i.isLt, htlt]
  calc
    (∑ t ∈ Finset.range ((j : ℕ) + 1),
        (Nat.choose steps ((j : ℕ) - t) : ℝ) *
          zeroExtend (constantImage rows cols c) i t) =
        ∑ t ∈ Finset.range ((j : ℕ) + 1),
          (Nat.choose steps ((j : ℕ) - t) : ℝ) * c := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hinside t ht]
    _ = c * ∑ t ∈ Finset.range ((j : ℕ) + 1),
          (Nat.choose steps ((j : ℕ) - t) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = c * pascalPrefix steps j := by
      congr 1
      simpa [pascalPrefix] using
        (Finset.sum_range_reflect
          (fun r ↦ (Nat.choose steps r : ℝ)) ((j : ℕ) + 1))

/-- A target column has a carrier gap of at least `c` over every later column
in the protected suffix, provided the number of accumulation steps reaches
that later column. -/
theorem protectedHorizontalScanAddress_suffix_gap {rows cols : ℕ}
    (steps : ℕ) (c : ℝ) (i : Fin rows) (target q : Fin cols)
    (hc : 0 ≤ c) (htq : (target : ℕ) < (q : ℕ))
    (hq : (q : ℕ) ≤ steps) :
    c ≤ protectedHorizontalScanAddress steps rows cols c i q -
      protectedHorizontalScanAddress steps rows cols c i target := by
  rw [protectedHorizontalScanAddress_eq, protectedHorizontalScanAddress_eq]
  have hgap := pascalPrefix_gap steps target q htq hq
  have hscaled := mul_le_mul_of_nonneg_left hgap hc
  nlinarith

/-- The not-yet-processed suffix of one chosen original row. -/
def rowSuffixProtected {rows cols : ℕ} (row : Fin rows) (target : Fin cols) :
    Fin rows → Fin cols → Prop :=
  fun i j ↦ i = row ∧ target ≤ j

theorem protectedHorizontalScanAddress_gap_on {rows cols : ℕ}
    (steps : ℕ) (c : ℝ) (row : Fin rows) (target : Fin cols)
    (hsteps : cols - 1 ≤ steps) (hc : 0 ≤ c) :
    ∀ i j, rowSuffixProtected row target i j →
      (i, j) ≠ (row, target) →
      c ≤ protectedHorizontalScanAddress steps rows cols c i j -
        protectedHorizontalScanAddress steps rows cols c row target := by
  intro i j hp hne
  rcases hp with ⟨hi, hj⟩
  subst i
  have hjne : j ≠ target := by
    intro heq
    subst j
    exact hne rfl
  have htjFin : target < j := lt_of_le_of_ne hj hjne.symm
  have htj : (target : ℕ) < (j : ℕ) := by exact_mod_cast htjFin
  have hjsteps : (j : ℕ) ≤ steps := by
    have hjlt := j.isLt
    omega
  exact protectedHorizontalScanAddress_suffix_gap
    steps c row target j hc htj hjsteps

/-- Compactness scales the Pascal carrier so that one shared scalar bias
selects any requested column, provided only the still-unprocessed suffix of
that row must be preserved. -/
theorem exists_horizontal_suffix_selected_relu
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (steps : ℕ) (row : Fin rows) (target : Fin cols) (θ : ℝ)
    (hsteps : cols - 1 ≤ steps) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i j,
      rowSuffixProtected row target i j →
      relu (signal x i j +
          protectedHorizontalScanAddress steps rows cols c i j +
          (θ - protectedHorizontalScanAddress steps rows cols c row target)) =
        if (i, j) = (row, target) then relu (signal x i j + θ)
        else signal x i j +
          protectedHorizontalScanAddress steps rows cols c i j +
          (θ - protectedHorizontalScanAddress steps rows cols c row target) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal θ
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hselected := sharedBiasSelectiveActivation_on
    (signal x) (protectedHorizontalScanAddress steps rows cols c)
    (rowSuffixProtected row target) (row, target) θ c
    (protectedHorizontalScanAddress_gap_on
      steps c row target hsteps hc.le)
    (fun i j _hp ↦ hbound x hx i j)
  intro i j hp
  exact hselected i j hp

/-- Every finite iteration remains injective because each positive
accumulation layer has an identity base tap and is itself injective. -/
theorem horizontalAccumulationIterations_injective {rows cols : ℕ}
    (steps : ℕ) :
    Function.Injective
      (fun x : Image rows cols ↦
        iterateFullConv horizontalAccumulationKernel steps x) := by
  induction steps generalizing rows cols with
  | zero =>
      intro x y hxy
      exact hxy
  | succ steps ih =>
      intro x y hxy
      apply horizontalAccumulationTransform_injective
      exact ih hxy

end OneChannelCNNUniversality
