import OneChannelCNNUniversality.SharedBiasScan

/-!
# Two-dimensional Pascal scan addresses

Horizontal and vertical positive accumulations turn a constant image into a
separable Pascal-prefix carrier.  The carrier is strictly increasing in each
coordinate throughout the original rectangle.  Thus every chosen register
is the unique minimum of its southeast protected quadrant.
-/

namespace OneChannelCNNUniversality

theorem horizontalPairKernel_two_eq_accumulation :
    horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega) =
      horizontalAccumulationKernel := by
  rfl

theorem verticalPairKernel_two_eq_accumulation :
    verticalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega) =
      verticalAccumulationKernel := by
  rfl

/-- Every finite vertical accumulation remains injective. -/
theorem verticalAccumulationIterations_injective {rows cols : ℕ}
    (steps : ℕ) :
    Function.Injective
      (fun x : Image rows cols ↦
        iterateFullConv verticalAccumulationKernel steps x) := by
  induction steps generalizing rows cols with
  | zero =>
      intro x y hxy
      exact hxy
  | succ steps ih =>
      intro x y hxy
      apply verticalAccumulationTransform_injective
      exact ih hxy

/-- The complete horizontal-then-vertical Pascal transform is injective. -/
theorem pascalGridTransform_injective {rows cols : ℕ}
    (rowSteps colSteps : ℕ) :
    Function.Injective (fun x : Image rows cols ↦
      iterateFullConv
        (verticalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
        rowSteps
        (iterateFullConv
          (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
          colSteps x)) := by
  rw [horizontalPairKernel_two_eq_accumulation,
    verticalPairKernel_two_eq_accumulation]
  intro x y hxy
  apply horizontalAccumulationIterations_injective
  exact verticalAccumulationIterations_injective rowSteps hxy

/-- The actual two-dimensional carrier after horizontal and then vertical
Pascal accumulation, restricted to the original rectangle. -/
def protectedPascalGridAddress
    (rowSteps colSteps rows cols : ℕ) (c : ℝ) : Image rows cols :=
  fun i j ↦ zeroExtend
    (iterateFullConv
      (verticalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
      rowSteps
      (iterateFullConv
        (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
        colSteps (constantImage rows cols c))) i j

/-- The two-dimensional address factors as the product of its row and column
Pascal prefixes. -/
theorem protectedPascalGridAddress_eq {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (c : ℝ) (i : Fin rows) (j : Fin cols) :
    protectedPascalGridAddress rowSteps colSteps rows cols c i j =
      c * pascalPrefix rowSteps i * pascalPrefix colSteps j := by
  unfold protectedPascalGridAddress
  rw [zeroExtend_iterateFullConv_vertical
    (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega)]
  rw [← congrFun (iteratePairKernel_eq_iterate rowSteps
    (fun t ↦ zeroExtend
      (iterateFullConv
        (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
        colSteps (constantImage rows cols c)) t j)) i]
  rw [iteratePairKernel_eq_sum_choose]
  have hinside : ∀ t ∈ Finset.range ((i : ℕ) + 1),
      zeroExtend
        (iterateFullConv
          (horizontalPairKernel (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega))
          colSteps (constantImage rows cols c)) t j =
        c * pascalPrefix colSteps j := by
    intro t ht
    have htlt : t < rows := by
      have := Finset.mem_range.mp ht
      omega
    simpa [protectedHorizontalScanAddress] using
      protectedHorizontalScanAddress_eq colSteps c (⟨t, htlt⟩ : Fin rows) j
  calc
    (∑ t ∈ Finset.range ((i : ℕ) + 1),
        (Nat.choose rowSteps ((i : ℕ) - t) : ℝ) *
          zeroExtend
            (iterateFullConv
              (horizontalPairKernel (show 2 ≤ 2 by omega)
                (show 2 ≤ 2 by omega))
              colSteps (constantImage rows cols c)) t j) =
        ∑ t ∈ Finset.range ((i : ℕ) + 1),
          (Nat.choose rowSteps ((i : ℕ) - t) : ℝ) *
            (c * pascalPrefix colSteps j) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hinside t ht]
    _ = (c * pascalPrefix colSteps j) *
          ∑ t ∈ Finset.range ((i : ℕ) + 1),
            (Nat.choose rowSteps ((i : ℕ) - t) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = (c * pascalPrefix colSteps j) * pascalPrefix rowSteps i := by
      congr 1
      simpa [pascalPrefix] using
        (Finset.sum_range_reflect
          (fun r ↦ (Nat.choose rowSteps r : ℝ)) ((i : ℕ) + 1))
    _ = c * pascalPrefix rowSteps i * pascalPrefix colSteps j := by ring

theorem one_le_pascalPrefix (steps q : ℕ) : 1 ≤ pascalPrefix steps q := by
  have hmono := pascalPrefix_monotone steps (Nat.zero_le q)
  have hzero : pascalPrefix steps 0 = 1 := by simp [pascalPrefix]
  linarith

/-- The southeast quadrant rooted at a chosen original register. -/
def southeastProtected {rows cols : ℕ}
    (targetRow : Fin rows) (targetCol : Fin cols) :
    Fin rows → Fin cols → Prop :=
  fun i j ↦ targetRow ≤ i ∧ targetCol ≤ j

/-- A product of sufficiently long Pascal prefixes has unit gap at the root
of every southeast protected quadrant. -/
theorem pascalPrefix_product_gap
    (rowSteps colSteps r s i j : ℕ)
    (hri : r ≤ i) (hsj : s ≤ j) (hne : (i, j) ≠ (r, s))
    (hi : i ≤ rowSteps) (hj : j ≤ colSteps) :
    1 ≤ pascalPrefix rowSteps i * pascalPrefix colSteps j -
      pascalPrefix rowSteps r * pascalPrefix colSteps s := by
  have hPr : 1 ≤ pascalPrefix rowSteps r := one_le_pascalPrefix _ _
  have hPj : 1 ≤ pascalPrefix colSteps j := one_le_pascalPrefix _ _
  have hcolMono : pascalPrefix colSteps s ≤ pascalPrefix colSteps j :=
    pascalPrefix_monotone colSteps hsj
  by_cases hir : i = r
  · subst i
    have hjs : s < j := by
      have hjne : j ≠ s := by
        intro heq
        subst j
        exact hne rfl
      omega
    have hcolGap := pascalPrefix_gap colSteps s j hjs hj
    have hscaled := mul_le_mul_of_nonneg_left hcolGap (by linarith :
      0 ≤ pascalPrefix rowSteps r)
    nlinarith
  · have hrowStrict : r < i := by omega
    have hrowGap := pascalPrefix_gap rowSteps r i hrowStrict hi
    have hmain : 1 ≤
        (pascalPrefix rowSteps i - pascalPrefix rowSteps r) *
          pascalPrefix colSteps j := by
      simpa only [one_mul] using
        (mul_le_mul hrowGap hPj (by norm_num) (by linarith))
    have hextra : 0 ≤ pascalPrefix rowSteps r *
        (pascalPrefix colSteps j - pascalPrefix colSteps s) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hcolMono)
    nlinarith

/-- The scaled carrier gap on an arbitrary southeast protected quadrant. -/
theorem protectedPascalGridAddress_gap_on {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (c : ℝ)
    (targetRow : Fin rows) (targetCol : Fin cols)
    (hrowSteps : rows - 1 ≤ rowSteps) (hcolSteps : cols - 1 ≤ colSteps)
    (hc : 0 ≤ c) :
    ∀ i j, southeastProtected targetRow targetCol i j →
      (i, j) ≠ (targetRow, targetCol) →
      c ≤ protectedPascalGridAddress rowSteps colSteps rows cols c i j -
        protectedPascalGridAddress rowSteps colSteps rows cols c
          targetRow targetCol := by
  intro i j hp hne
  rw [protectedPascalGridAddress_eq, protectedPascalGridAddress_eq]
  have hiSteps : (i : ℕ) ≤ rowSteps := by
    have := i.isLt
    omega
  have hjSteps : (j : ℕ) ≤ colSteps := by
    have := j.isLt
    omega
  have hproduct := pascalPrefix_product_gap rowSteps colSteps
    targetRow targetCol i j (by exact_mod_cast hp.1) (by exact_mod_cast hp.2)
    (by
      intro heq
      apply hne
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst heq
      · exact congrArg Prod.snd heq)
    hiSteps hjSteps
  have hscaled := mul_le_mul_of_nonneg_left hproduct hc
  nlinarith

/-- Compactness turns the two-dimensional Pascal gap into an exact shared-
bias selected ReLU at any requested target, while keeping its southeast
protected quadrant in the linear branch.  This theorem certifies the final
pointwise activation once the signal-plus-address state is present; it does
not package the preceding accumulation layers as an end-to-end shared-bias
ReLU network. -/
theorem exists_southeast_selected_relu
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (rowSteps colSteps : ℕ) (targetRow : Fin rows) (targetCol : Fin cols)
    (θ : ℝ) (hrowSteps : rows - 1 ≤ rowSteps)
    (hcolSteps : cols - 1 ≤ colSteps) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i j,
      southeastProtected targetRow targetCol i j →
      relu (signal x i j +
          protectedPascalGridAddress rowSteps colSteps rows cols c i j +
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol)) =
        if (i, j) = (targetRow, targetCol) then relu (signal x i j + θ)
        else signal x i j +
          protectedPascalGridAddress rowSteps colSteps rows cols c i j +
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal θ
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hselected := sharedBiasSelectiveActivation_on
    (signal x) (protectedPascalGridAddress rowSteps colSteps rows cols c)
    (southeastProtected targetRow targetCol) (targetRow, targetCol) θ c
    (protectedPascalGridAddress_gap_on rowSteps colSteps c
      targetRow targetCol hrowSteps hcolSteps hc.le)
    (fun i j _hp ↦ hbound x hx i j)
  intro i j hp
  exact hselected i j hp

end OneChannelCNNUniversality
