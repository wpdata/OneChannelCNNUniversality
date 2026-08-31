import OneChannelCNNUniversality.SharedBiasNorthTwoCarrier

/-!
# Layerwise compensated compact carriers

A sign-changing factor chain need not transport one positive zero-bias
carrier.  It can instead add a prescribed shared scalar after each
convolution.  This file formalizes that more flexible invariant.

A compensated step consists of a bilinear kernel factor and one scalar
carrier bias.  If the resulting carrier preactivation is at least one in
the northern two rows at every step, compactness supplies one common scale.
At every larger scale, the genuine shared-bias ReLU network agrees on those
rows with the pure variable convolution chain plus the scaled compensated
carrier chain.
-/

namespace OneChannelCNNUniversality

open Set

/-- One bilinear factor together with its prescribed carrier-bias
coefficient.  At network scale `s`, the actual shared bias is `s * bias`. -/
structure CompensatedBilinearStep where
  factor : BilinearKernelFactor
  bias : ℝ

/-- Pure variable convolution recursion associated with the compensated
steps.  Bias coefficients do not affect this signal component. -/
def compensatedVariableChain : (steps : List CompensatedBilinearStep) →
    {rows cols : ℕ} → Image rows cols →
      Image (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], _, _, signal => signal
  | step :: steps, _, _, signal =>
      compensatedVariableChain steps
        (fullConvImage step.factor.kernel signal)

/-- Formal carrier recursion with one broadcast scalar added after every
convolution. -/
def compensatedCarrierChain : (steps : List CompensatedBilinearStep) →
    {rows cols : ℕ} → Image rows cols →
      Image (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], _, _, carrier => carrier
  | step :: steps, _, _, carrier =>
      compensatedCarrierChain steps
        (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.bias)

/-- Genuine network whose step biases are all multiplied by one common
nonnegative scale. -/
def compensatedBilinearNetwork : (steps : List CompensatedBilinearStep) →
    {rows cols : ℕ} → ℝ →
      SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 rows steps.length) (grownSize 2 cols steps.length)
  | [], rows, cols, _ => SharedBiasNetworkTo.nil rows cols 2 2
  | step :: steps, _, _, s =>
      SharedBiasNetworkTo.cons step.factor.kernel (s * step.bias)
        (compensatedBilinearNetwork steps s)

@[simp] theorem compensatedBilinearNetwork_depth
    (steps : List CompensatedBilinearStep) {rows cols : ℕ} (s : ℝ) :
    (compensatedBilinearNetwork steps
      (rows := rows) (cols := cols) s).net.depth = steps.length := by
  induction steps generalizing rows cols with
  | nil => rfl
  | cons step steps ih =>
      change (compensatedBilinearNetwork steps
        (rows := rows + 2 - 1) (cols := cols + 2 - 1) s).net.depth + 1 =
          steps.length + 1
      rw [ih]

/-- Every compensated carrier preactivation is at least one throughout the
northern two rows. -/
def NorthTwoCompensatedUnitLowerAlong :
    (steps : List CompensatedBilinearStep) →
      {rows cols : ℕ} → Image rows cols → Prop
  | [], _, _, _ => True
  | step :: steps, rows, cols, carrier =>
      (∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
        ∀ q : Fin (cols + 2 - 1),
          1 ≤ fullConv step.factor.kernel carrier p q + step.bias) ∧
      NorthTwoCompensatedUnitLowerAlong steps
        (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.bias)

private theorem northTwoAgree_compensated_first
    {rows cols : ℕ} (step : CompensatedBilinearStep)
    (V carrier : Image rows cols) (s M : ℝ)
    (hs : 0 ≤ s) (hMs : M ≤ s)
    (hvariable : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1),
        |fullConv step.factor.kernel V p q| < M)
    (hcarrier : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1),
        1 ≤ fullConv step.factor.kernel carrier p q + step.bias) :
    NorthTwoAgree
      (sharedLayerEval step.factor.kernel (s * step.bias)
        (V + s • carrier))
      (fullConvImage step.factor.kernel V +
        s • (fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.bias)) := by
  intro p hp q
  by_cases hprow : p < rows + 2 - 1
  · by_cases hqcol : q < cols + 2 - 1
    · let p' : Fin (rows + 2 - 1) := ⟨p, hprow⟩
      let q' : Fin (cols + 2 - 1) := ⟨q, hqcol⟩
      rw [zeroExtend_of_lt _ hprow hqcol,
        zeroExtend_of_lt _ hprow hqcol]
      change relu
          (fullConv step.factor.kernel (V + s • carrier) p' q' +
            s * step.bias) =
        fullConv step.factor.kernel V p' q' +
          s * (fullConv step.factor.kernel carrier p' q' + step.bias)
      rw [fullConv_add]
      have hsmul :
          fullConv step.factor.kernel (s • carrier) p' q' =
            s * fullConv step.factor.kernel carrier p' q' := by
        have h := congrFun
          (congrFun
            (fullConvImage_smul step.factor.kernel s carrier) p') q'
        exact h
      rw [hsmul, relu_of_nonneg]
      · ring
      · have hvar := hvariable p' hp q'
        have hcar := hcarrier p' hp q'
        have hneg : -M < fullConv step.factor.kernel V p' q' :=
          neg_lt_of_abs_lt hvar
        have hscaled :
            s ≤ s *
              (fullConv step.factor.kernel carrier p' q' + step.bias) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcar hs
        linarith
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol),
        zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol)]
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hprow),
      zeroExtend_row_outside _ (Nat.le_of_not_gt hprow)]

/-- Compact genuine-network bridge for a layerwise compensated carrier.
The conclusion is upward closed in the common scale. -/
theorem exists_compensatedNorthTwoNetwork_scale_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (steps : List CompensatedBilinearStep)
    {rows cols : ℕ} (V : X → Image rows cols)
    (hV : ContinuousFeatureOn K V) (carrier : Image rows cols)
    (hcarrier : NorthTwoCompensatedUnitLowerAlong steps carrier) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s : ℝ, s₀ ≤ s → ∀ x ∈ K,
      ∀ p, p ≤ 1 → ∀ q,
        zeroExtend
            ((compensatedBilinearNetwork steps s).eval
              (V x + s • carrier)) p q =
          zeroExtend (compensatedVariableChain steps (V x)) p q +
            s * zeroExtend (compensatedCarrierChain steps carrier) p q := by
  induction steps generalizing rows cols V carrier with
  | nil =>
      refine ⟨0, le_rfl, ?_⟩
      intro s hs x hx p hp q
      change zeroExtend
          ((SharedBiasNetworkTo.nil rows cols 2 2).eval
            (V x + s • carrier)) p q =
        zeroExtend (V x) p q + s * zeroExtend carrier p q
      rw [SharedBiasNetworkTo.eval_nil, zeroExtend_add, zeroExtend_smul]
  | cons step steps ih =>
      rcases hcarrier with ⟨hfirstCarrier, htailCarrier⟩
      let nextV : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ fullConvImage step.factor.kernel (V x)
      let nextCarrier : Image (rows + 2 - 1) (cols + 2 - 1) :=
        fullConvImage step.factor.kernel carrier +
          constantImage _ _ step.bias
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV step.factor.kernel p q
      obtain ⟨M, hMpos, hMbound⟩ :=
        exists_uniform_feature_margin hK nextV hnextV 0
      obtain ⟨tailScale, htailScale, htail⟩ :=
        ih nextV hnextV nextCarrier htailCarrier
      refine ⟨max M tailScale, ?_, ?_⟩
      · exact hMpos.le.trans (le_max_left _ _)
      intro s hs x hx
      have hMs : M ≤ s := (le_max_left M tailScale).trans hs
      have htails : tailScale ≤ s :=
        (le_max_right M tailScale).trans hs
      have hsnonneg : 0 ≤ s := htailScale.trans htails
      let actualFirst : Image (rows + 2 - 1) (cols + 2 - 1) :=
        sharedLayerEval step.factor.kernel (s * step.bias)
          (V x + s • carrier)
      let formalFirst : Image (rows + 2 - 1) (cols + 2 - 1) :=
        nextV x + s • nextCarrier
      have hfirstAgree : NorthTwoAgree actualFirst formalFirst := by
        apply northTwoAgree_compensated_first step (V x) carrier s M
            hsnonneg hMs
        · intro p hp q
          simpa [nextV, fullConvImage] using hMbound x hx p q
        · exact hfirstCarrier
      have htransport : NorthTwoAgree
          ((compensatedBilinearNetwork steps s).eval actualFirst)
          ((compensatedBilinearNetwork steps s).eval formalFirst) :=
        northTwoAgree_sharedBiasNetworkTo_eval
          (compensatedBilinearNetwork steps s) hfirstAgree
      have hformal := htail s htails x hx
      intro p hp q
      have htransportCoord := htransport p hp q
      have hformalCoord := hformal p hp q
      calc
        zeroExtend
            ((compensatedBilinearNetwork (step :: steps) s).eval
              (V x + s • carrier)) p q =
            zeroExtend
              ((compensatedBilinearNetwork steps s).eval actualFirst) p q := by
                rfl
        _ = zeroExtend
              ((compensatedBilinearNetwork steps s).eval formalFirst) p q :=
            htransportCoord
        _ = zeroExtend (compensatedVariableChain steps (nextV x)) p q +
              s * zeroExtend
                (compensatedCarrierChain steps nextCarrier) p q :=
            hformalCoord
        _ = zeroExtend
              (compensatedVariableChain (step :: steps) (V x)) p q +
              s * zeroExtend
                (compensatedCarrierChain (step :: steps) carrier) p q := by
            rfl

end OneChannelCNNUniversality
