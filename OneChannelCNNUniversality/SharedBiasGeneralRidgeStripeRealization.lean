import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAddress
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripePrefix
import OneChannelCNNUniversality.SharedBiasHeterogeneousCarrier
import OneChannelCNNUniversality.SharedBiasGridNetwork

/-!
# Realization bridges for the signed stripe

The signed-stripe address modules describe two fixed spatial directions by
polynomial coefficients and by natural-coordinate convolution formulas.  This
file identifies those descriptions with the actual heterogeneous formal
convolution chain.  It also packages the variable part of the chain as an
image of the final stripe dimensions and proves that its protected target is
the requested linear form.

The equalities are stated through `zeroExtend` whenever a dependent output
dimension would otherwise require a transport cast.  Thus they remain exact
at every natural coordinate, including coordinates outside the finite output
rectangle.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial Set

/-! ## Factor-list decomposition and dimensions -/

/-- The complete twisted schedule is its public proper block followed by its
public final factor. -/
theorem generalRidgeStripeTwistedFactors_eq_proper_append_last {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeTwistedFactors w T =
      generalRidgeStripeTwistedProperFactors w T ++
        [generalRidgeStripeTwistedLastFactor w T] := by
  let hd : 2 ≤ n + 2 := by omega
  let w' := generalRidgeExtendedWeights w
  let η := generalRidgeStripeAllocation w
  let c := BilinearKernelFactor.scaleLower (-T⁻¹)
  let penultimate :=
    generalRidgeKernelFactor w' η (generalRidgePenultimateIndex hd)
  let last := generalRidgeStripeLastFactor w
  have hsplit :
      generalRidgeFactorList w' η =
        generalRidgeFactorPrefix hd w' η ++ [penultimate, last] := by
    simpa [penultimate, last, generalRidgeStripeLastFactor] using
      (generalRidgeFactorList_split_last_two (n := n) w' η)
  have htake :
      (generalRidgeFactorList w' η).take (n + 1) =
        generalRidgeFactorPrefix hd w' η ++ [penultimate] := by
    rw [hsplit, List.take_append]
    have hlength : (generalRidgeFactorPrefix hd w' η).length = n := by
      simp
    rw [List.take_of_length_le (by omega), hlength]
    simp
  change
    (generalRidgeFactorPrefix hd w' η ++ [penultimate]).map c ++
          [BilinearKernelFactor.scaleHorizontal (-T) last] =
      ((generalRidgeFactorList w' η).take (n + 1)).map c ++
          [BilinearKernelFactor.scaleHorizontal (-T) last]
  rw [htake]

@[simp] theorem generalRidgeStripeTwistedFactors_length {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    (generalRidgeStripeTwistedFactors w T).length = n + 2 := by
  rw [generalRidgeStripeTwistedFactors_eq_proper_append_last]
  simp

/-- With a `2 × 2` kernel, each formal convolution layer adds one row and
one column. -/
private theorem stripe_grownSize_two_eq_add (start steps : ℕ) :
    grownSize 2 start steps = start + steps := by
  induction steps generalizing start with
  | zero => simp [grownSize]
  | succ steps ih =>
      rw [grownSize, ih]
      omega

/-! ## The complete identity-seed address -/

/-- Either northern row of the unit seed is the width-`n+3` boxcar. -/
private theorem rowPolynomial_constantOneStripe (n p : ℕ) (hp : p < 2) :
    rowPolynomial (constantImage 2 (n + 3) 1) p =
      generalRidgeBoxcar (n + 2) := by
  ext q
  rw [rowPolynomial_coeff, generalRidgeBoxcar_coeff]
  by_cases hq : q < n + 3
  · have hq' : q ≤ n + 2 := by omega
    simp [zeroExtend, constantImage, hp, hq, hq']
  · have hq' : ¬q ≤ n + 2 := by omega
    simp [zeroExtend, hp, hq, hq']

/-- Exact northern polynomial transported from the unit identity seed. -/
theorem generalRidgeStripeSeed_fullConvChain_row_zero {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (constantImage 2 (n + 3) 1)) 0 =
      horizontalProduct (generalRidgeStripeTwistedFactors w T) *
        generalRidgeBoxcar (n + 2) := by
  rw [rowPolynomial_fullConvChain_zero,
    rowPolynomial_constantOneStripe n 0 (by omega)]

/-- Exact first-southern polynomial transported from the unit identity
seed. -/
theorem generalRidgeStripeSeed_fullConvChain_row_one {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    rowPolynomial
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (constantImage 2 (n + 3) 1)) 1 =
      (horizontalProduct (generalRidgeStripeTwistedFactors w T) +
          verticalOne (generalRidgeStripeTwistedFactors w T)) *
        generalRidgeBoxcar (n + 2) := by
  rw [rowPolynomial_fullConvChain_one,
    rowPolynomial_constantOneStripe n 1 (by omega),
    rowPolynomial_constantOneStripe n 0 (by omega)]
  ring

/-- On both protected rows, the algebraic seed-address image is exactly the
unit identity seed propagated through the complete formal convolution chain.
The `zeroExtend` form removes all dependent output-size casts. -/
theorem generalRidgeStripeSeedAddressImage_eq_fullConvChain_north {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (p : ℕ) (hp : p ≤ 1) (q : ℕ) :
    zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (constantImage 2 (n + 3) 1)) p q =
      zeroExtend (generalRidgeStripeSeedAddressImage w T) p q := by
  have hrows : grownSize 2 2
      (generalRidgeStripeTwistedFactors w T).length = n + 4 := by
    simp [stripe_grownSize_two_eq_add]
    omega
  have hcols : grownSize 2 (n + 3)
      (generalRidgeStripeTwistedFactors w T).length =
        2 * (n + 2) + 1 := by
    simp [stripe_grownSize_two_eq_add]
    omega
  by_cases hq : q < 2 * (n + 2) + 1
  · have hp_cases : p = 0 ∨ p = 1 := by omega
    rcases hp_cases with rfl | rfl
    · rw [← rowPolynomial_coeff,
        generalRidgeStripeSeed_fullConvChain_row_zero]
      simp [zeroExtend, hq,
        generalRidgeStripeSeedAddressImage,
        generalRidgeStripeSeedAddressRowZero]
    · rw [← rowPolynomial_coeff,
        generalRidgeStripeSeed_fullConvChain_row_one]
      simp [zeroExtend, hq,
        generalRidgeStripeSeedAddressImage,
        generalRidgeStripeSeedAddressRowOne]
  · have hqout : 2 * (n + 2) + 1 ≤ q := Nat.le_of_not_gt hq
    have hqoutChain : grownSize 2 (n + 3)
        (generalRidgeStripeTwistedFactors w T).length ≤ q := by
      rw [hcols]
      exact hqout
    rw [zeroExtend_col_outside _ hqoutChain,
      zeroExtend_col_outside _ hqout]

/-! ## The last-factor local address -/

/-- On the protected northern rows, the embedded local address is literally
the convolution of the predecessor unit constant image by the public final
twisted factor. -/
theorem generalRidgeStripeFinalLocalAddressImage_eq_fullConv_north {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (p : Fin (n + 4)) (hp : (p : ℕ) ≤ 1)
    (q : Fin (2 * (n + 2) + 1)) :
    fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
        (constantImage (n + 3) (2 * (n + 2)) 1) p q =
      generalRidgeStripeFinalLocalAddressImage w T p q := by
  rw [generalRidgeStripeFinalLocalAddressImage_north w T p hp q]
  rfl

/-! ## Variable signal and the exact protected target -/

/-- Pure variable state produced by the northwest identity seed, before any
constant carrier is added. -/
noncomputable def generalRidgeStripeVariableSeed {n : ℕ}
    (x : Image 1 (n + 2)) : Image 2 (n + 3) :=
  fullConvImage expansiveIdentityKernel x

/-- The variable part of the complete signed-stripe chain, repackaged at the
explicit final stripe dimensions by coordinatewise zero extension. -/
noncomputable def generalRidgeStripeVariableSignal {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (x : Image 1 (n + 2)) :
    Image (n + 4) (2 * (n + 2) + 1) :=
  fun p q ↦ zeroExtend
    (fullConvChain (generalRidgeStripeTwistedFactors w T)
      (generalRidgeStripeVariableSeed x)) p q

/-- Coordinatewise continuity of the variable signed-stripe signal on any
input family for which the original feature map is coordinatewise
continuous. -/
theorem continuousFeatureOn_generalRidgeStripeVariableSignal
    {X : Type*} [TopologicalSpace X] {K : Set X} {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (F : X → Image 1 (n + 2)) (hF : ContinuousFeatureOn K F) :
    ContinuousFeatureOn K
      (fun x ↦ generalRidgeStripeVariableSignal w T (F x)) := by
  have hseed : ContinuousFeatureOn K
      (fun x ↦ generalRidgeStripeVariableSeed (F x)) := by
    intro p q
    exact continuousFeatureOn_fullConv hF expansiveIdentityKernel p q
  have hchain := continuousFeatureOn_fullConvChain
    (generalRidgeStripeTwistedFactors w T)
    (fun x ↦ generalRidgeStripeVariableSeed (F x)) hseed
  intro p q
  simpa [generalRidgeStripeVariableSignal] using
    (continuousFeatureOn_zeroExtend hchain (p : ℕ) (q : ℕ))

/-- Append a zero column to the original variable input while keeping a
single row.  It is used only to invoke the existing natural-target theorem. -/
private noncomputable def generalRidgeStripeExtendedInput {n : ℕ}
    (x : Image 1 (n + 2)) : Image 1 (n + 3) :=
  fun _ q ↦ zeroExtend x 0 q

private theorem generalRidgeStripeVariableSeed_row_zero {n : ℕ}
    (x : Image 1 (n + 2)) :
    rowPolynomial (generalRidgeStripeVariableSeed x) 0 =
      rowPolynomial (generalRidgeStripeExtendedInput x) 0 := by
  ext q
  rw [rowPolynomial_coeff, rowPolynomial_coeff]
  change zeroExtend (fullConvImage expansiveIdentityKernel x) 0 q =
    zeroExtend (generalRidgeStripeExtendedInput x) 0 q
  rw [zeroExtend_fullConvImage, fullConv_expansiveIdentityKernel_nat]
  by_cases hq : q < n + 3
  · rw [zeroExtend_of_lt _ (by omega) hq]
    rfl
  · rw [zeroExtend_col_outside _ (by omega),
      zeroExtend_col_outside _ (Nat.le_of_not_gt hq)]

private theorem generalRidgeStripeVariableSeed_row_one {n : ℕ}
    (x : Image 1 (n + 2)) :
      rowPolynomial (generalRidgeStripeVariableSeed x) 1 = 0 := by
  ext q
  rw [rowPolynomial_coeff]
  change zeroExtend (fullConvImage expansiveIdentityKernel x) 1 q = 0
  rw [zeroExtend_fullConvImage, fullConv_expansiveIdentityKernel_nat]
  simp [zeroExtend]

private theorem generalRidgeStripeExtendedInput_row_one {n : ℕ}
    (x : Image 1 (n + 2)) :
    rowPolynomial (generalRidgeStripeExtendedInput x) 1 = 0 := by
  ext q
  simp [rowPolynomial_coeff]

/-- The protected target `(1,n+2)` of the pure variable stripe signal is
exactly the requested natural-order dot product. -/
theorem generalRidgeStripeVariableSignal_target {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0)
    (x : Image 1 (n + 2)) :
    generalRidgeStripeVariableSignal w T x
        (generalRidgeStripeTarget n).1
        (generalRidgeStripeTarget n).2 =
      ∑ j, w j * x 0 j := by
  let w' := generalRidgeExtendedWeights w
  let η := generalRidgeStripeAllocation w
  let fs := generalRidgeStripeTwistedFactors w T
  let seed := generalRidgeStripeVariableSeed x
  let x' := generalRidgeStripeExtendedInput x
  have hη : ∑ i, η i = w' 0 := by
    exact generalRidgeStripeAllocation_sum w
  have htwisted : verticalOne fs = generalRidgeTargetPolynomial w' := by
    exact generalRidgeStripeTwistedFactors_verticalOne w T hT
  have horiginal :
      verticalOne (generalRidgeFactorList w' η) =
        generalRidgeTargetPolynomial w' := by
    rw [← bivariateProduct_coeff_one,
      generalRidgeFactorList_bivariateProduct]
    exact generalRidgeBiProduct_vertical_one w' η hη
  have hsame :
      zeroExtend (fullConvChain fs seed) 1 (n + 2) =
        zeroExtend (generalRidgeFullConv w' η x') 1 (n + 2) := by
    rw [← rowPolynomial_coeff, ← rowPolynomial_coeff,
      rowPolynomial_fullConvChain_one, generalRidgeFullConv,
      rowPolynomial_fullConvChain_one,
      generalRidgeStripeVariableSeed_row_one,
      generalRidgeStripeExtendedInput_row_one,
      generalRidgeStripeVariableSeed_row_zero, htwisted, horiginal]
    simp [x']
  calc
    generalRidgeStripeVariableSignal w T x
          (generalRidgeStripeTarget n).1
          (generalRidgeStripeTarget n).2 =
        zeroExtend (fullConvChain fs seed) 1 (n + 2) := by
      rfl
    _ = zeroExtend (generalRidgeFullConv w' η x') 1 (n + 2) := hsame
    _ = ∑ j : Fin (n + 3), w' j * x' 0 j :=
      generalRidgeFullConv_target w' η hη x'
    _ = ∑ j : Fin (n + 2), w j * x 0 j := by
      rw [Fin.sum_univ_castSucc]
      simp [w', x', generalRidgeStripeExtendedInput,
        zeroExtend]

end OneChannelCNNUniversality
