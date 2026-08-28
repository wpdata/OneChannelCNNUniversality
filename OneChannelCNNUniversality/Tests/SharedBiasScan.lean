import OneChannelCNNUniversality.SharedBiasScan

open OneChannelCNNUniversality

example (steps q : ℕ) :
    pascalPrefix steps (q + 1) - pascalPrefix steps q =
      (Nat.choose steps (q + 1) : ℝ) := by
  exact pascalPrefix_succ_sub steps q

example (steps s q : ℕ) (hsq : s < q) (hq : q ≤ steps) :
    1 ≤ pascalPrefix steps q - pascalPrefix steps s := by
  exact pascalPrefix_gap steps s q hsq hq

/-- The endpoint `q = steps` remains inside the certified Pascal gap. -/
example : pascalPrefix 3 3 - pascalPrefix 3 2 = 1 := by
  norm_num [pascalPrefix, Finset.sum_range_succ, Nat.choose]

example {rows cols : ℕ} (steps : ℕ) (c : ℝ)
    (i : Fin rows) (j : Fin cols) :
    protectedHorizontalScanAddress steps rows cols c i j =
      c * pascalPrefix steps j := by
  exact protectedHorizontalScanAddress_eq steps c i j

example {rows cols : ℕ} (steps : ℕ) (c : ℝ)
    (i : Fin rows) (target q : Fin cols)
    (hc : 0 ≤ c) (htq : (target : ℕ) < (q : ℕ))
    (hq : (q : ℕ) ≤ steps) :
    c ≤ protectedHorizontalScanAddress steps rows cols c i q -
      protectedHorizontalScanAddress steps rows cols c i target := by
  exact protectedHorizontalScanAddress_suffix_gap steps c i target q hc htq hq

example {rows cols : ℕ} (steps : ℕ) :
    Function.Injective
      (fun x : Image rows cols ↦
        iterateFullConv horizontalAccumulationKernel steps x) := by
  exact horizontalAccumulationIterations_injective steps

/-- Injectivity also covers an empty row dimension. -/
example : Function.Injective
    (fun x : Image 0 3 ↦
      iterateFullConv horizontalAccumulationKernel 4 x) := by
  exact horizontalAccumulationIterations_injective 4

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (signal : X → Image rows cols) (hSignal : ContinuousFeatureOn K signal)
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
  exact exists_horizontal_suffix_selected_relu
    hK signal hSignal steps row target θ hsteps
