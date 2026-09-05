import OneChannelCNNUniversality.SharedBiasCompensatedCarrier

/-!
# Affinely compensated compact carriers

A shared scalar bias can carry two logically different terms.  A fixed term
belongs to the transported signal, while a second term, multiplied by one
large common scale, belongs to the positive carrier.  Separating these terms
lets later constructions insert independent affine offsets without scaling
them together with the carrier used to linearize the intermediate ReLUs.

This file proves the compact bridge for that two-scale invariant.  If every
formal carrier preactivation is at least one in the northern two rows, then a
single sufficiently large scale makes the genuine ReLU network agree there
with the affine signal recursion plus the scaled carrier recursion.
-/

namespace OneChannelCNNUniversality

open Set

/-- One bilinear convolution step with a fixed signal bias and a carrier bias
that is multiplied by the common scale. -/
structure AffineCompensatedBilinearStep where
  factor : BilinearKernelFactor
  signalBias : ℝ
  carrierBias : ℝ

/-- The affine signal recursion.  Its biases are not multiplied by the
carrier scale. -/
def affineCompensatedVariableChain :
    (steps : List AffineCompensatedBilinearStep) →
      {rows cols : ℕ} → Image rows cols →
        Image (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], _, _, signal => signal
  | step :: steps, _, _, signal =>
      affineCompensatedVariableChain steps
        (fullConvImage step.factor.kernel signal +
          constantImage _ _ step.signalBias)

/-- The carrier recursion.  Only these bias coefficients are multiplied by
the common network scale. -/
def affineCompensatedCarrierChain :
    (steps : List AffineCompensatedBilinearStep) →
      {rows cols : ℕ} → Image rows cols →
        Image (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], _, _, carrier => carrier
  | step :: steps, _, _, carrier =>
      affineCompensatedCarrierChain steps
        (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.carrierBias)

/-- The genuine network with actual layer bias
`signalBias + scale * carrierBias`. -/
def affineCompensatedBilinearNetwork :
    (steps : List AffineCompensatedBilinearStep) →
      {rows cols : ℕ} → ℝ →
        SharedBiasNetworkTo 2 2 rows cols
          (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], rows, cols, _ => SharedBiasNetworkTo.nil rows cols 2 2
  | step :: steps, _, _, scale =>
      SharedBiasNetworkTo.cons step.factor.kernel
        (step.signalBias + scale * step.carrierBias)
        (affineCompensatedBilinearNetwork steps scale)

@[simp] theorem affineCompensatedBilinearNetwork_depth
    (steps : List AffineCompensatedBilinearStep)
    {rows cols : ℕ} (scale : ℝ) :
    (affineCompensatedBilinearNetwork steps
      (rows := rows) (cols := cols) scale).net.depth = steps.length := by
  induction steps generalizing rows cols with
  | nil => rfl
  | cons step steps ih =>
      change (affineCompensatedBilinearNetwork steps
        (rows := rows + 2 - 1) (cols := cols + 2 - 1)
        scale).net.depth + 1 = steps.length + 1
      rw [ih]

/-- Every scaled-carrier preactivation is at least one in the northern two
rows.  Fixed signal biases deliberately do not occur in this certificate. -/
def AffineNorthTwoCompensatedUnitLowerAlong :
    (steps : List AffineCompensatedBilinearStep) →
      {rows cols : ℕ} → Image rows cols → Prop
  | [], _, _, _ => True
  | step :: steps, rows, cols, carrier =>
      (∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
        ∀ q : Fin (cols + 2 - 1),
          1 ≤ fullConv step.factor.kernel carrier p q +
            step.carrierBias) ∧
      AffineNorthTwoCompensatedUnitLowerAlong steps
        (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.carrierBias)

/-- The carrier certificate for a concatenated affine-compensated chain
splits into the head certificate and the transported tail certificate. -/
theorem affineNorthTwoCompensatedUnitLowerAlong_append_iff
    (head tail : List AffineCompensatedBilinearStep)
    {rows cols : ℕ} (carrier : Image rows cols) :
    AffineNorthTwoCompensatedUnitLowerAlong (head ++ tail) carrier ↔
      AffineNorthTwoCompensatedUnitLowerAlong head carrier ∧
        AffineNorthTwoCompensatedUnitLowerAlong tail
          (affineCompensatedCarrierChain head carrier) := by
  induction head generalizing rows cols carrier with
  | nil =>
      change AffineNorthTwoCompensatedUnitLowerAlong tail carrier ↔
        True ∧ AffineNorthTwoCompensatedUnitLowerAlong tail carrier
      tauto
  | cons step head ih =>
      simp only [List.cons_append,
        AffineNorthTwoCompensatedUnitLowerAlong,
        affineCompensatedCarrierChain]
      rw [ih]
      tauto

private theorem northTwoAgree_affineCompensated_first
    {rows cols : ℕ} (step : AffineCompensatedBilinearStep)
    (signal carrier : Image rows cols) (scale bound : ℝ)
    (hscale : 0 ≤ scale) (hboundScale : bound ≤ scale)
    (hsignal : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1),
        |fullConv step.factor.kernel signal p q + step.signalBias| < bound)
    (hcarrier : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1),
        1 ≤ fullConv step.factor.kernel carrier p q +
          step.carrierBias) :
    NorthTwoAgree
      (sharedLayerEval step.factor.kernel
        (step.signalBias + scale * step.carrierBias)
        (signal + scale • carrier))
      ((fullConvImage step.factor.kernel signal +
          constantImage _ _ step.signalBias) +
        scale • (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.carrierBias)) := by
  intro p hp q
  by_cases hprow : p < rows + 2 - 1
  · by_cases hqcol : q < cols + 2 - 1
    · let p' : Fin (rows + 2 - 1) := ⟨p, hprow⟩
      let q' : Fin (cols + 2 - 1) := ⟨q, hqcol⟩
      rw [zeroExtend_of_lt _ hprow hqcol,
        zeroExtend_of_lt _ hprow hqcol]
      change relu
          (fullConv step.factor.kernel (signal + scale • carrier) p' q' +
            (step.signalBias + scale * step.carrierBias)) =
        (fullConv step.factor.kernel signal p' q' + step.signalBias) +
          scale * (fullConv step.factor.kernel carrier p' q' +
            step.carrierBias)
      rw [fullConv_add]
      have hsmul :
          fullConv step.factor.kernel (scale • carrier) p' q' =
            scale * fullConv step.factor.kernel carrier p' q' := by
        have h := congrFun
          (congrFun
            (fullConvImage_smul step.factor.kernel scale carrier) p') q'
        exact h
      rw [hsmul, relu_of_nonneg]
      · ring
      · have hvar := hsignal p' hp q'
        have hcar := hcarrier p' hp q'
        have hneg :
            -bound < fullConv step.factor.kernel signal p' q' +
              step.signalBias := neg_lt_of_abs_lt hvar
        have hscaled :
            scale ≤ scale *
              (fullConv step.factor.kernel carrier p' q' +
                step.carrierBias) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcar hscale
        linarith
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol),
        zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol)]
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hprow),
      zeroExtend_row_outside _ (Nat.le_of_not_gt hprow)]

/-- Compact genuine-network bridge for affine signal compensation and a
separately scaled positive carrier.  The admissible scale interval is upward
closed. -/
theorem exists_affineCompensatedNorthTwoNetwork_scale_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (steps : List AffineCompensatedBilinearStep)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hsignal : ContinuousFeatureOn K signal) (carrier : Image rows cols)
    (hcarrier :
      AffineNorthTwoCompensatedUnitLowerAlong steps carrier) :
    ∃ scale₀ : ℝ, 0 ≤ scale₀ ∧
      ∀ scale : ℝ, scale₀ ≤ scale → ∀ x ∈ K,
        ∀ p, p ≤ 1 → ∀ q,
          zeroExtend
              ((affineCompensatedBilinearNetwork steps scale).eval
                (signal x + scale • carrier)) p q =
            zeroExtend (affineCompensatedVariableChain steps (signal x)) p q +
              scale * zeroExtend
                (affineCompensatedCarrierChain steps carrier) p q := by
  induction steps generalizing rows cols signal carrier with
  | nil =>
      refine ⟨0, le_rfl, ?_⟩
      intro scale hscale x hx p hp q
      change zeroExtend
          ((SharedBiasNetworkTo.nil rows cols 2 2).eval
            (signal x + scale • carrier)) p q =
        zeroExtend (signal x) p q + scale * zeroExtend carrier p q
      rw [SharedBiasNetworkTo.eval_nil, zeroExtend_add, zeroExtend_smul]
  | cons step steps ih =>
      rcases hcarrier with ⟨hfirstCarrier, htailCarrier⟩
      let nextSignal : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ fullConvImage step.factor.kernel (signal x) +
          constantImage _ _ step.signalBias
      let nextCarrier : Image (rows + 2 - 1) (cols + 2 - 1) :=
        fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.carrierBias
      have hnextSignal : ContinuousFeatureOn K nextSignal := by
        intro p q
        exact (continuousFeatureOn_fullConv hsignal step.factor.kernel p q).add
          continuousOn_const
      obtain ⟨bound, hboundPos, hbound⟩ :=
        exists_uniform_feature_margin hK nextSignal hnextSignal 0
      obtain ⟨tailScale, htailScale, htail⟩ :=
        ih nextSignal hnextSignal nextCarrier htailCarrier
      refine ⟨max bound tailScale, ?_, ?_⟩
      · exact hboundPos.le.trans (le_max_left _ _)
      intro scale hscale x hx
      have hboundScale : bound ≤ scale :=
        (le_max_left bound tailScale).trans hscale
      have htailScale' : tailScale ≤ scale :=
        (le_max_right bound tailScale).trans hscale
      have hscaleNonneg : 0 ≤ scale := htailScale.trans htailScale'
      let actualFirst : Image (rows + 2 - 1) (cols + 2 - 1) :=
        sharedLayerEval step.factor.kernel
          (step.signalBias + scale * step.carrierBias)
          (signal x + scale • carrier)
      let formalFirst : Image (rows + 2 - 1) (cols + 2 - 1) :=
        nextSignal x + scale • nextCarrier
      have hfirstAgree : NorthTwoAgree actualFirst formalFirst := by
        apply northTwoAgree_affineCompensated_first step (signal x) carrier
          scale bound hscaleNonneg hboundScale
        · intro p hp q
          have hb := hbound x hx p q
          dsimp [nextSignal] at hb
          simp only [add_zero] at hb
          exact hb
        · exact hfirstCarrier
      have htransport : NorthTwoAgree
          ((affineCompensatedBilinearNetwork steps scale).eval actualFirst)
          ((affineCompensatedBilinearNetwork steps scale).eval formalFirst) :=
        northTwoAgree_sharedBiasNetworkTo_eval
          (affineCompensatedBilinearNetwork steps scale) hfirstAgree
      have hformal := htail scale htailScale' x hx
      intro p hp q
      have htransportCoord := htransport p hp q
      have hformalCoord := hformal p hp q
      calc
        zeroExtend
            ((affineCompensatedBilinearNetwork (step :: steps) scale).eval
              (signal x + scale • carrier)) p q =
            zeroExtend
              ((affineCompensatedBilinearNetwork steps scale).eval
                actualFirst) p q := by rfl
        _ = zeroExtend
              ((affineCompensatedBilinearNetwork steps scale).eval
                formalFirst) p q := htransportCoord
        _ = zeroExtend
              (affineCompensatedVariableChain steps (nextSignal x)) p q +
            scale * zeroExtend
              (affineCompensatedCarrierChain steps nextCarrier) p q :=
          hformalCoord
        _ = zeroExtend
              (affineCompensatedVariableChain (step :: steps)
                (signal x)) p q +
            scale * zeroExtend
              (affineCompensatedCarrierChain (step :: steps) carrier) p q := by
          rfl

end OneChannelCNNUniversality
