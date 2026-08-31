import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeNetwork
import OneChannelCNNUniversality.SharedBiasGeneralRidgeRecovery

/-!
# Recovery from the genuine signed-stripe ridge network

The completed ridge block does not merely expose one nonlinear ridge value.
Its northern output row is an affine translate of a faithful linear encoding
of the original input row.  This module proves that encoding injective and
upgrades the compact existence theorem with injectivity of the genuine
network output on every compact injective input family.
-/

namespace OneChannelCNNUniversality

open Polynomial Set

private theorem stripeRecovery_fullConvChain_add
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (x y : Image rows cols) :
    fullConvChain fs (x + y) =
      fullConvChain fs x + fullConvChain fs y := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (x + y)) = _
      rw [fullConvImage_add, ih]
      rfl

private theorem stripeRecovery_fullConvChain_smul
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (a : ℝ) (x : Image rows cols) :
    fullConvChain fs (a • x) = a • fullConvChain fs x := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (a • x)) = _
      rw [fullConvImage_smul, ih]
      rfl

/-- The complete northern row of the variable signed-stripe signal. -/
noncomputable def generalRidgeStripeVariableNorthRow {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (x : Image 1 (n + 2)) :
    Fin (2 * (n + 2) + 1) → ℝ :=
  fun q ↦ generalRidgeStripeVariableSignal w T x 0 q

@[simp] theorem generalRidgeStripeVariableNorthRow_apply {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (x : Image 1 (n + 2))
    (q : Fin (2 * (n + 2) + 1)) :
    generalRidgeStripeVariableNorthRow w T x q =
      generalRidgeStripeVariableSignal w T x 0 q := rfl

/-- The expansive identity seed preserves the entire generating polynomial
of the original northern input row; the newly created eastern fringe is
zero. -/
theorem generalRidgeStripeVariableSeed_row_zero_eq_input {n : ℕ}
    (x : Image 1 (n + 2)) :
    rowPolynomial (generalRidgeStripeVariableSeed x) 0 =
      rowPolynomial x 0 := by
  ext q
  rw [rowPolynomial_coeff, rowPolynomial_coeff]
  change zeroExtend (fullConvImage expansiveIdentityKernel x) 0 q =
    zeroExtend x 0 q
  rw [zeroExtend_fullConvImage, fullConv_expansiveIdentityKernel_nat]

/-- For nonzero reciprocal scale, equality of complete variable northern
rows forces equality of the original inputs. -/
theorem generalRidgeStripeVariableNorthRow_injective {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0) :
    Function.Injective (generalRidgeStripeVariableNorthRow w T) := by
  intro x y hxy
  have hpoly :
      rowPolynomial
          (fullConvChain (generalRidgeStripeTwistedFactors w T)
            (generalRidgeStripeVariableSeed x)) 0 =
        rowPolynomial
          (fullConvChain (generalRidgeStripeTwistedFactors w T)
            (generalRidgeStripeVariableSeed y)) 0 := by
    ext q
    rw [rowPolynomial_coeff, rowPolynomial_coeff]
    by_cases hq : q < 2 * (n + 2) + 1
    · have hcoord := congrFun hxy ⟨q, hq⟩
      exact hcoord
    · have hout : grownSize 2 (n + 3)
          (generalRidgeStripeTwistedFactors w T).length ≤ q := by
        have := Nat.le_of_not_gt hq
        simp [grownSize_two_eq_add]
        omega
      rw [zeroExtend_col_outside _ hout,
        zeroExtend_col_outside _ hout]
  rw [rowPolynomial_fullConvChain_zero,
    rowPolynomial_fullConvChain_zero,
    generalRidgeStripeTwistedFactors_horizontalProduct] at hpoly
  have hfactor :
      Polynomial.C (-T) * generalRidgeNodalProduct (n + 2) ≠ 0 := by
    apply mul_ne_zero
    · simp [hT]
    · exact (generalRidgeNodalProduct_monic (n + 2)).ne_zero
  have hseed :
      rowPolynomial (generalRidgeStripeVariableSeed x) 0 =
        rowPolynomial (generalRidgeStripeVariableSeed y) 0 :=
    mul_left_cancel₀ hfactor hpoly
  rw [generalRidgeStripeVariableSeed_row_zero_eq_input,
    generalRidgeStripeVariableSeed_row_zero_eq_input] at hseed
  exact rowPolynomial_zero_injective (n + 2) hseed

/-- The variable northern stripe is a finite-dimensional linear encoding of
the original row. -/
noncomputable def generalRidgeStripeVariableNorthLinearMap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    Image 1 (n + 2) →ₗ[ℝ] (Fin (2 * (n + 2) + 1) → ℝ) where
  toFun := generalRidgeStripeVariableNorthRow w T
  map_add' x y := by
    funext q
    change zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (generalRidgeStripeVariableSeed (x + y))) 0 q = _
    change zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (fullConvImage expansiveIdentityKernel (x + y))) 0 q = _
    rw [fullConvImage_add, stripeRecovery_fullConvChain_add,
      zeroExtend_add]
    rfl
  map_smul' a x := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    change zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T)
          (fullConvImage expansiveIdentityKernel (a • x))) 0 q = _
    rw [fullConvImage_smul, stripeRecovery_fullConvChain_smul,
      zeroExtend_smul]
    rfl

theorem generalRidgeStripeVariableNorthLinearMap_injective {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0) :
    Function.Injective (generalRidgeStripeVariableNorthLinearMap w T) :=
  generalRidgeStripeVariableNorthRow_injective w T hT

/-- A chosen linear decoder for the northern stripe code. -/
noncomputable def generalRidgeStripeVariableNorthLeftInverse {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    (Fin (2 * (n + 2) + 1) → ℝ) →ₗ[ℝ] Image 1 (n + 2) :=
  (generalRidgeStripeVariableNorthLinearMap w T).leftInverse

/-- The chosen decoder recovers every input exactly whenever `T ≠ 0`. -/
theorem generalRidgeStripeVariableNorthLeftInverse_apply {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : T ≠ 0)
    (x : Image 1 (n + 2)) :
    generalRidgeStripeVariableNorthLeftInverse w T
        (generalRidgeStripeVariableNorthLinearMap w T x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr
    (generalRidgeStripeVariableNorthLinearMap_injective w T hT)

/-- Compact exact-ridge construction strengthened with injectivity of the
complete genuine network state whenever the supplied feature family is
injective. -/
theorem exists_injective_generalRidgeStripeNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (w : Fin (n + 2) → ℝ) (theta : ℝ) :
    ∃ T c t : ℝ,
      1 ≤ T ∧ 0 < c ∧ 0 < t ∧
      (generalRidgeStripeNetwork w T c t theta).net.depth = n + 3 ∧
      (∀ x ∈ K, ∀ (p : Fin (n + 4))
        (q : Fin (2 * (n + 2) + 1)), (p : ℕ) ≤ 1 →
        (generalRidgeStripeNetwork w T c t theta).eval (F x) p q =
          if (p, q) = generalRidgeStripeTarget n then
            relu (∑ j, w j * F x 0 j + theta)
          else
            twoCarrierPreactivation
              (generalRidgeStripeVariableSignal w T (F x))
              (generalRidgeStripeSeedAddressImage w T)
              (generalRidgeStripeFinalLocalAddressImage w T)
              (generalRidgeStripeTarget n) theta c t p q) ∧
      Set.InjOn
        (fun x ↦ (generalRidgeStripeNetwork w T c t theta).eval (F x)) K := by
  obtain ⟨T, c, t, hT, hc, ht, hdepth, hbehavior⟩ :=
    exists_generalRidgeStripeNetwork_on_compact hK F hF w theta
  refine ⟨T, c, t, hT, hc, ht, hdepth, hbehavior, ?_⟩
  intro x hx y hy heval
  apply hFinjective hx hy
  apply generalRidgeStripeVariableNorthRow_injective w T
    (ne_of_gt (zero_lt_one.trans_le hT))
  funext q
  let p0 : Fin (n + 4) := ⟨0, by omega⟩
  have hp0 : (p0 : ℕ) ≤ 1 := by simp [p0]
  have hne : (p0, q) ≠ generalRidgeStripeTarget n := by
    intro heq
    have hrow := congrArg (fun z ↦ (z.1 : ℕ)) heq
    simp [p0, generalRidgeStripeTarget] at hrow
  have hxrow := hbehavior x hx p0 q hp0
  have hyrow := hbehavior y hy p0 q hp0
  rw [if_neg hne] at hxrow hyrow
  have heqrow := congrFun (congrFun heval p0) q
  change (generalRidgeStripeNetwork w T c t theta).eval (F x) p0 q =
    (generalRidgeStripeNetwork w T c t theta).eval (F y) p0 q at heqrow
  rw [hxrow, hyrow] at heqrow
  change generalRidgeStripeVariableSignal w T (F x) p0 q =
    generalRidgeStripeVariableSignal w T (F y) p0 q
  simp only [twoCarrierPreactivation] at heqrow
  linarith

end OneChannelCNNUniversality
