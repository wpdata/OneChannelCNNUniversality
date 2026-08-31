import OneChannelCNNUniversality.SharedBiasGeneralRidgeSeparation

/-!
# Signed stripe algebra for arbitrary-width ridge factors

This file prepares the algebraic factor schedule used by the protected
two-row stripe construction.  One zero weight is appended to the requested
ridge, and the leading allocation is split between the first and last
factors.  The last lower factor then has two strictly negative taps.

For a nonzero scale `T`, all lower factors before the last one are multiplied
by `-T⁻¹`, while the horizontal part of the last factor is multiplied by
`-T`.  The two signs and reciprocal scales cancel in every term contributing
to vertical degree one.  Consequently the vertical polynomial remains the
requested target, whereas the complete horizontal product becomes

\[
  -T\prod_{i=1}^{d}(X+i).
\]

The coefficientwise scale needed for prefix positivity and the subsequent
compact ReLU compiler are intentionally left to later modules.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-! ## Appending a zero target weight -/

/-- Append one zero coordinate to a natural-order ridge weight vector. -/
def generalRidgeExtendedWeights {d : ℕ} (w : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  Fin.lastCases 0 w

@[simp] theorem generalRidgeExtendedWeights_castSucc {d : ℕ}
    (w : Fin d → ℝ) (i : Fin d) :
    generalRidgeExtendedWeights w i.castSucc = w i := by
  simp [generalRidgeExtendedWeights]

@[simp] theorem generalRidgeExtendedWeights_last {d : ℕ}
    (w : Fin d → ℝ) :
    generalRidgeExtendedWeights w (Fin.last d) = 0 := by
  simp [generalRidgeExtendedWeights]

/-! ## A coefficientwise-negative last lower factor -/

/-- The scale placed negatively in the last allocation slot. -/
noncomputable def generalRidgeStripeSeparationScale {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  |generalRidgeBeta (generalRidgeExtendedWeights w)
      (generalRidgeLastIndex (d := n + 2) (by omega))| + 1

theorem generalRidgeStripeSeparationScale_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    1 ≤ generalRidgeStripeSeparationScale w := by
  unfold generalRidgeStripeSeparationScale
  linarith [abs_nonneg
    (generalRidgeBeta (generalRidgeExtendedWeights w)
      (generalRidgeLastIndex (d := n + 2) (by omega)))]

theorem generalRidgeStripeSeparationScale_pos {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    0 < generalRidgeStripeSeparationScale w :=
  lt_of_lt_of_le zero_lt_one (generalRidgeStripeSeparationScale_one_le w)

/-- Put the required leading weight plus `S` in the first slot, `-S` in the
last slot, and zero in every other slot. -/
noncomputable def generalRidgeStripeAllocation {n : ℕ}
    (w : Fin (n + 2) → ℝ) : Fin (n + 2) → ℝ :=
  let hd : 2 ≤ n + 2 := by omega
  fun i ↦
    if i = generalRidgeFirstIndex hd then
      generalRidgeExtendedWeights w 0 + generalRidgeStripeSeparationScale w
    else if i = generalRidgeLastIndex hd then
      -generalRidgeStripeSeparationScale w
    else 0

@[simp] theorem generalRidgeStripeAllocation_first {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    generalRidgeStripeAllocation w
        (generalRidgeFirstIndex (d := n + 2) (by omega)) =
      generalRidgeExtendedWeights w 0 +
        generalRidgeStripeSeparationScale w := by
  simp [generalRidgeStripeAllocation]

@[simp] theorem generalRidgeStripeAllocation_last {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    generalRidgeStripeAllocation w
        (generalRidgeLastIndex (d := n + 2) (by omega)) =
      -generalRidgeStripeSeparationScale w := by
  simp [generalRidgeStripeAllocation,
    generalRidgeLastIndex_ne_first (d := n + 2) (by omega)]

/-- The signed first/last allocation has the target leading total. -/
theorem generalRidgeStripeAllocation_sum {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    ∑ i : Fin (n + 2), generalRidgeStripeAllocation w i =
      generalRidgeExtendedWeights w 0 := by
  classical
  let hd : 2 ≤ n + 2 := by omega
  calc
    ∑ i : Fin (n + 2), generalRidgeStripeAllocation w i =
        ∑ i : Fin (n + 2),
          ((if i = generalRidgeFirstIndex hd then
              generalRidgeExtendedWeights w 0 +
                generalRidgeStripeSeparationScale w else 0) +
            (if i = generalRidgeLastIndex hd then
              -generalRidgeStripeSeparationScale w else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hfirst : i = generalRidgeFirstIndex hd
        · subst i
          simp [generalRidgeStripeAllocation,
            (generalRidgeLastIndex_ne_first hd).symm]
        · by_cases hlast : i = generalRidgeLastIndex hd
          · simp [generalRidgeStripeAllocation, hlast]
          · simp [generalRidgeStripeAllocation, hfirst, hlast]
    _ = generalRidgeExtendedWeights w 0 := by
      rw [Finset.sum_add_distrib]
      simp

/-! ## Generic factor scalings -/

namespace BilinearKernelFactor

/-- Scale only the lower polynomial `B`. -/
def scaleLower (c : ℝ) (f : BilinearKernelFactor) : BilinearKernelFactor where
  a0 := f.a0
  a1 := f.a1
  b0 := c * f.b0
  b1 := c * f.b1

/-- Scale only the horizontal polynomial `A`. -/
def scaleHorizontal (c : ℝ)
    (f : BilinearKernelFactor) : BilinearKernelFactor where
  a0 := c * f.a0
  a1 := c * f.a1
  b0 := f.b0
  b1 := f.b1

@[simp] theorem scaleLower_A (c : ℝ) (f : BilinearKernelFactor) :
    (scaleLower c f).A = f.A := rfl

@[simp] theorem scaleLower_B (c : ℝ) (f : BilinearKernelFactor) :
    (scaleLower c f).B = C c * f.B := by
  simp [scaleLower, B, linearPolynomial]
  ring

@[simp] theorem scaleHorizontal_A (c : ℝ) (f : BilinearKernelFactor) :
    (scaleHorizontal c f).A = C c * f.A := by
  simp [scaleHorizontal, A, linearPolynomial]
  ring

@[simp] theorem scaleHorizontal_B (c : ℝ) (f : BilinearKernelFactor) :
    (scaleHorizontal c f).B = f.B := rfl

end BilinearKernelFactor

@[simp] theorem horizontalProduct_map_scaleLower (c : ℝ)
    (fs : List BilinearKernelFactor) :
    horizontalProduct (fs.map (BilinearKernelFactor.scaleLower c)) =
      horizontalProduct fs := by
  induction fs with
  | nil => simp [horizontalProduct]
  | cons f fs ih =>
      change
        (BilinearKernelFactor.scaleLower c f).A *
            horizontalProduct
              (fs.map (BilinearKernelFactor.scaleLower c)) =
          f.A * horizontalProduct fs
      rw [BilinearKernelFactor.scaleLower_A, ih]

theorem verticalOne_map_scaleLower (c : ℝ)
    (fs : List BilinearKernelFactor) :
    verticalOne (fs.map (BilinearKernelFactor.scaleLower c)) =
      C c * verticalOne fs := by
  induction fs with
  | nil => simp [verticalOne]
  | cons f fs ih =>
      simp only [List.map_cons, verticalOne,
        BilinearKernelFactor.scaleLower_A,
        BilinearKernelFactor.scaleLower_B,
        horizontalProduct_map_scaleLower, ih]
      ring

@[simp] theorem horizontalProduct_append_single
    (fs : List BilinearKernelFactor) (f : BilinearKernelFactor) :
    horizontalProduct (fs ++ [f]) = horizontalProduct fs * f.A := by
  simp [horizontalProduct]

theorem verticalOne_append_single
    (fs : List BilinearKernelFactor) (f : BilinearKernelFactor) :
    verticalOne (fs ++ [f]) =
      verticalOne fs * f.A + horizontalProduct fs * f.B := by
  induction fs with
  | nil => simp [verticalOne, horizontalProduct]
  | cons g fs ih =>
      simp only [List.cons_append, verticalOne, ih,
        horizontalProduct_append_single]
      simp only [horizontalProduct, List.map_cons, List.prod_cons]
      ring

/-! ## The signed stripe factor list -/

private noncomputable def generalRidgeStripeOriginalPrefix {n : ℕ}
    (w : Fin (n + 2) → ℝ) : List BilinearKernelFactor :=
  let hd : 2 ≤ n + 2 := by omega
  let w' := generalRidgeExtendedWeights w
  let η := generalRidgeStripeAllocation w
  generalRidgeFactorPrefix hd w' η ++
    [generalRidgeKernelFactor w' η (generalRidgePenultimateIndex hd)]

/-- The unscaled last factor of the stripe allocation. -/
noncomputable def generalRidgeStripeLastFactor {n : ℕ}
    (w : Fin (n + 2) → ℝ) : BilinearKernelFactor :=
  generalRidgeKernelFactor (generalRidgeExtendedWeights w)
    (generalRidgeStripeAllocation w)
    (generalRidgeLastIndex (d := n + 2) (by omega))

/-- The complete factor list after reciprocal lower scaling on the proper
prefix and negative horizontal scaling on the last factor. -/
noncomputable def generalRidgeStripeTwistedFactors {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) : List BilinearKernelFactor :=
  (generalRidgeStripeOriginalPrefix w).map
      (BilinearKernelFactor.scaleLower (-T⁻¹)) ++
    [BilinearKernelFactor.scaleHorizontal (-T)
      (generalRidgeStripeLastFactor w)]

/-- The actual final factor in the signed stripe list. -/
noncomputable def generalRidgeStripeTwistedLastFactor {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) : BilinearKernelFactor :=
  BilinearKernelFactor.scaleHorizontal (-T)
    (generalRidgeStripeLastFactor w)

private theorem generalRidgeStripe_factorList_split {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    generalRidgeFactorList (generalRidgeExtendedWeights w)
        (generalRidgeStripeAllocation w) =
      generalRidgeStripeOriginalPrefix w ++
        [generalRidgeStripeLastFactor w] := by
  simpa [generalRidgeStripeOriginalPrefix, generalRidgeStripeLastFactor,
    List.append_assoc] using
    (generalRidgeFactorList_split_last_two (n := n)
      (generalRidgeExtendedWeights w) (generalRidgeStripeAllocation w))

/-- Twisting changes the complete horizontal product by exactly `-T`. -/
theorem generalRidgeStripeTwistedFactors_horizontalProduct {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    horizontalProduct (generalRidgeStripeTwistedFactors w T) =
      C (-T) * generalRidgeNodalProduct (n + 2) := by
  rw [generalRidgeStripeTwistedFactors,
    horizontalProduct_append_single, horizontalProduct_map_scaleLower,
    BilinearKernelFactor.scaleHorizontal_A]
  rw [← mul_assoc]
  rw [mul_comm (horizontalProduct (generalRidgeStripeOriginalPrefix w))]
  rw [mul_assoc]
  congr 1
  rw [← horizontalProduct_append_single]
  rw [← generalRidgeStripe_factorList_split]
  exact generalRidgeFactorList_horizontalProduct _ _

private theorem generalRidgeStripe_original_verticalOne {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    verticalOne
        (generalRidgeFactorList (generalRidgeExtendedWeights w)
          (generalRidgeStripeAllocation w)) =
      generalRidgeTargetPolynomial (generalRidgeExtendedWeights w) := by
  rw [← bivariateProduct_coeff_one,
    generalRidgeFactorList_bivariateProduct]
  exact generalRidgeBiProduct_vertical_one
    (generalRidgeExtendedWeights w) (generalRidgeStripeAllocation w)
    (generalRidgeStripeAllocation_sum w)

/-- The reciprocal/sign twist preserves the complete vertical-degree-one
target polynomial. -/
theorem generalRidgeStripeTwistedFactors_verticalOne {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0) :
    verticalOne (generalRidgeStripeTwistedFactors w T) =
      generalRidgeTargetPolynomial (generalRidgeExtendedWeights w) := by
  rw [generalRidgeStripeTwistedFactors, verticalOne_append_single,
    verticalOne_map_scaleLower, horizontalProduct_map_scaleLower,
    BilinearKernelFactor.scaleHorizontal_A,
    BilinearKernelFactor.scaleHorizontal_B]
  have hscale : C (-T⁻¹) * C (-T) = (1 : ℝ[X]) := by
    rw [← map_mul]
    simp [hT]
  have hfirst :
      C (-T⁻¹) * verticalOne (generalRidgeStripeOriginalPrefix w) *
          (C (-T) * (generalRidgeStripeLastFactor w).A) =
        verticalOne (generalRidgeStripeOriginalPrefix w) *
          (generalRidgeStripeLastFactor w).A := by
    calc
      _ = (C (-T⁻¹) * C (-T)) *
          (verticalOne (generalRidgeStripeOriginalPrefix w) *
            (generalRidgeStripeLastFactor w).A) := by ring
      _ = _ := by rw [hscale, one_mul]
  rw [hfirst]
  rw [← verticalOne_append_single]
  rw [← generalRidgeStripe_factorList_split]
  exact generalRidgeStripe_original_verticalOne w

/-! ## Exact and signed final taps -/

/-- Closed form of all four taps in the final twisted factor. -/
theorem generalRidgeStripeTwistedLastFactor_taps {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    let β := generalRidgeBeta (generalRidgeExtendedWeights w)
      (generalRidgeLastIndex (d := n + 2) (by omega))
    let S := generalRidgeStripeSeparationScale w
    let f := generalRidgeStripeTwistedLastFactor w T
    f.a0 = -T * (n + 2 : ℝ) ∧
      f.a1 = -T ∧
      f.b0 = β - S * (n + 2 : ℝ) ∧
      f.b1 = -S := by
  dsimp only
  unfold generalRidgeStripeTwistedLastFactor
  unfold BilinearKernelFactor.scaleHorizontal
  unfold generalRidgeStripeLastFactor
  unfold generalRidgeKernelFactor
  dsimp
  rw [generalRidgeStripeAllocation_last]
  constructor
  · congr 1
    norm_num [Nat.cast_add]
    ring
  constructor
  · ring
  constructor
  · push_cast
    ring
  · rfl

/-- If `T ≥ 1`, every tap of the final twisted factor is at most `-1`. -/
theorem generalRidgeStripeTwistedLastFactor_taps_le_neg_one {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T) :
    let f := generalRidgeStripeTwistedLastFactor w T
    f.a0 ≤ -1 ∧ f.a1 ≤ -1 ∧ f.b0 ≤ -1 ∧ f.b1 ≤ -1 := by
  dsimp only
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    generalRidgeStripeTwistedLastFactor_taps w T
  rw [ha0, ha1, hb0, hb1]
  let β := generalRidgeBeta (generalRidgeExtendedWeights w)
    (generalRidgeLastIndex (d := n + 2) (by omega))
  have hβ : β ≤ |β| := le_abs_self β
  have hS : generalRidgeStripeSeparationScale w = |β| + 1 := rfl
  have hn : (2 : ℝ) ≤ n + 2 := by exact_mod_cast (show 2 ≤ n + 2 by omega)
  rw [hS]
  constructor
  · nlinarith
  constructor
  · linarith
  constructor <;> nlinarith [abs_nonneg β]

end OneChannelCNNUniversality
