import OneChannelCNNUniversality.SharedBiasParallelStripeAffinePacking
import OneChannelCNNUniversality.SharedBiasMultiTargetSelection

/-!
# A genuine compact two-ridge shared-bias network block

This module joins the corrected three-layer proper carrier, the fourth packed
factor, and simultaneous target selection.  The outcome is one genuine
depth-four expansive `2 × 2`, one-channel, spatially shared-bias ReLU network.
When evaluated on the explicit carrier-loaded affine embedding of a compact
family of width-two inputs, its two packed target coordinates compute two
independently shifted affine ReLU ridges, up to the common positive packing
factor `ε`.
-/

namespace OneChannelCNNUniversality

open Set

/-- The two packed output sites. -/
def parallelStripePackedTargets (p : Fin 6) (q : Fin 7) : Prop :=
  (p : ℕ) = 1 ∧ ((q : ℕ) = 2 ∨ (q : ℕ) = 4)

/-- The targets together with their separating middle site. -/
def parallelStripePackedProtect (p : Fin 6) (q : Fin 7) : Prop :=
  (p : ℕ) = 1 ∧
    ((q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 4)

instance parallelStripePackedTargetsDecidable :
    ∀ p q, Decidable (parallelStripePackedTargets p q) := by
  intro p q
  unfold parallelStripePackedTargets
  infer_instance

/-- Final image-level carrier after the fourth packed convolution. -/
noncomputable def parallelStripePackedFinalCarrierImage
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : Image 6 7 :=
  fullConvImage (parallelStripePackedFactorThree ε w).kernel
    (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
      (parallelStripeCorrectedCarrier ε w))

/-- Common carrier baseline at the first target. -/
noncomputable def parallelStripePackedFinalBase
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) : ℝ :=
  parallelStripePackedFinalCarrierImage ε w 1 2

/-- The genuine four-layer network.  Its first three biases are the scaled
compensating biases; the last bias subtracts the common target baseline. -/
noncomputable def parallelStripePackedAffineNetwork
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (s : ℝ) :
    SharedBiasNetworkTo 2 2 2 3 6 7 :=
  (compensatedBilinearNetwork
      (parallelStripePackedProperSteps ε w) (rows := 2) (cols := 3) s).append
    (SharedBiasNetworkTo.single
      (parallelStripePackedFactorThree ε w).kernel
      (-s * parallelStripePackedFinalBase ε w))

@[simp] theorem parallelStripePackedAffineNetwork_depth
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) (s : ℝ) :
    (parallelStripePackedAffineNetwork ε w s).net.depth = 4 := by
  simp [parallelStripePackedAffineNetwork,
    parallelStripePackedProperSteps, SharedBiasNetworkTo.single,
    SharedBiasNetworkTo.nil, SharedBiasNetworkTo.cons, SharedBiasNetwork.depth]

private theorem parallelStripePackedFinalCarrier_targets
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ) :
    ∀ p q, parallelStripePackedTargets p q →
      parallelStripePackedFinalCarrierImage ε w p q =
        parallelStripePackedFinalBase ε w := by
  intro p q hpq
  rcases hpq with ⟨hp, hq⟩
  fin_cases p
  · norm_num at hp
  · rcases hq with hq | hq
    · fin_cases q <;> simp_all [parallelStripePackedFinalBase]
    · fin_cases q <;> try norm_num at hq
      have hraw :
          zeroExtend (parallelStripePackedFinalCarrierImage ε w) 1 4 =
            zeroExtend (parallelStripePackedFinalCarrierImage ε w) 1 2 := by
        exact (parallelStripeCorrectedFinalImage_common_targets ε w).symm
      simpa [parallelStripePackedFinalBase, zeroExtend] using hraw
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp

private theorem parallelStripePackedFinalCarrier_gap
    (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (hgap : 1 < (parallelStripeCorrectedFinalCarrier ε w).coeff 3 -
      (parallelStripeCorrectedFinalCarrier ε w).coeff 2) :
    ∀ p q, parallelStripePackedProtect p q →
      ¬ parallelStripePackedTargets p q →
      1 ≤ parallelStripePackedFinalCarrierImage ε w p q -
        parallelStripePackedFinalBase ε w := by
  intro p q hpq hnot
  rcases hpq with ⟨hp, hq⟩
  have hq3 : (q : ℕ) = 3 := by
    rcases hq with hq2 | hq3 | hq4
    · exact False.elim (hnot ⟨hp, Or.inl hq2⟩)
    · exact hq3
    · exact False.elim (hnot ⟨hp, Or.inr hq4⟩)
  fin_cases p
  · norm_num at hp
  · fin_cases q <;> try norm_num at hq3
    change 1 ≤ zeroExtend (parallelStripePackedFinalCarrierImage ε w) 1 3 -
      zeroExtend (parallelStripePackedFinalCarrierImage ε w) 1 2
    rw [← rowPolynomial_coeff, ← rowPolynomial_coeff]
    change 1 ≤
      (rowPolynomial
        (fullConvImage (parallelStripePackedFactorThree ε w).kernel
          (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
            (parallelStripeCorrectedCarrier ε w))) 1).coeff 3 -
      (rowPolynomial
        (fullConvImage (parallelStripePackedFactorThree ε w).kernel
          (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
            (parallelStripeCorrectedCarrier ε w))) 1).coeff 2
    rw [parallelStripeCorrectedFinalCarrier_rowPolynomial]
    exact hgap.le
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp

private theorem continuousFeatureOn_parallelStripePackedFinalVariable
    (K : Set (Image 1 2)) (ε : ℝ) (w : Fin 2 → Fin 2 → ℝ)
    (θ : Fin 2 → ℝ) :
    ContinuousFeatureOn K
      (fun x ↦ parallelStripePackedFinalVariable ε w
        (parallelStripeAffineSeed ε θ x)) := by
  change ContinuousFeatureOn K
    (fun x ↦ fullConvChain (parallelStripePackedFactorList ε w)
      (parallelStripeAffineSeed ε θ x))
  exact continuousFeatureOn_fullConvChain
    (parallelStripePackedFactorList ε w)
    (parallelStripeAffineSeed ε θ)
    (continuousFeatureOn_parallelStripeAffineSeed K ε θ)

private theorem relu_mul_of_pos (ε z : ℝ) (hε : 0 < ε) :
    relu (ε * z) = ε * relu z := by
  by_cases hz : 0 ≤ z
  · rw [relu_of_nonneg hz, relu_of_nonneg (mul_nonneg hε.le hz)]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    rw [relu_of_nonpos hz', relu_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hε.le hz')]
    ring

/-- **Exact compact two-affine-ridge block with a nonnegative input state.**

For every compact set of width-two inputs and every pair of affine ridge
parameters, there are positive scales `ε` and `s` such that one genuine
depth-four expansive shared-bias ReLU network, evaluated on the explicitly
carrier-loaded affine input state, returns the two ridge ReLUs at the packed
target sites, multiplied by the same positive `ε`.  The carrier-loaded state
is coordinatewise nonnegative throughout the compact input family. -/
theorem exists_parallelStripePackedAffineNetwork_nonnegative_input_on_compact
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    ∃ ε s : ℝ, 0 < ε ∧ 0 < s ∧
      (parallelStripePackedAffineNetwork ε w s).net.depth = 4 ∧
      (∀ x ∈ K, ImageNonnegative
        (parallelStripeAffineSeed ε θ x +
          s • parallelStripeCorrectedCarrier ε w)) ∧
      ∀ x ∈ K,
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeAffineSeed ε θ x +
              s • parallelStripeCorrectedCarrier ε w) 1 2 =
          ε * relu (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) ∧
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeAffineSeed ε θ x +
              s • parallelStripeCorrectedCarrier ε w) 1 4 =
          ε * relu (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  classical
  rcases exists_parallelStripeCorrected_unitLower_gap_and_inputPositive w with
    ⟨ε, hε, hinputCarrier, hcarrier, hgap⟩
  let V : Image 1 2 → Image 2 3 := parallelStripeAffineSeed ε θ
  have hV : ContinuousFeatureOn K V :=
    continuousFeatureOn_parallelStripeAffineSeed K ε θ
  rcases exists_uniform_feature_margin hK V hV 0 with
    ⟨input₀, hinput₀, hinputBound⟩
  rcases exists_compensatedNorthTwoNetwork_scale_on_compact
      hK (parallelStripePackedProperSteps ε w) V hV
      (parallelStripeCorrectedCarrier ε w) hcarrier with
    ⟨proper₀, hproper₀, hproper⟩
  let signal : Image 1 2 → Image 6 7 := fun x ↦
    parallelStripePackedFinalVariable ε w (V x)
  let carrier := parallelStripePackedFinalCarrierImage ε w
  let base := parallelStripePackedFinalBase ε w
  have hsignal : ContinuousFeatureOn K signal :=
    continuousFeatureOn_parallelStripePackedFinalVariable K ε w θ
  have htargets : ∀ p q, parallelStripePackedTargets p q →
      carrier p q = base :=
    parallelStripePackedFinalCarrier_targets ε w
  have hprotected : ∀ p q, parallelStripePackedProtect p q →
      ¬ parallelStripePackedTargets p q → 1 ≤ carrier p q - base :=
    parallelStripePackedFinalCarrier_gap ε w hgap
  rcases exists_multiTargetSelectiveActivation_threshold_on
      hK signal hsignal carrier base parallelStripePackedTargets
      parallelStripePackedProtect 0 htargets hprotected with
    ⟨select₀, hselect₀, hselect⟩
  let s := max proper₀ (max select₀ input₀)
  have hproperS : proper₀ ≤ s := le_max_left _ _
  have hselectS : select₀ ≤ s :=
    (le_max_left select₀ input₀).trans (le_max_right proper₀ _)
  have hinputS : input₀ ≤ s :=
    (le_max_right select₀ input₀).trans (le_max_right proper₀ _)
  have hs : 0 < s := hselect₀.trans_le hselectS
  have hloadedNonnegative : ∀ x ∈ K, ImageNonnegative
      (parallelStripeAffineSeed ε θ x +
        s • parallelStripeCorrectedCarrier ε w) := by
    intro x hx p q
    have hvariableAbs : |V x p q| < input₀ := by
      simpa using hinputBound x hx p q
    have hvariableLower : -input₀ < V x p q :=
      neg_lt_of_abs_lt hvariableAbs
    have hscaledCarrier : s ≤
        s * parallelStripeCorrectedCarrier ε w p q := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (hinputCarrier p q) hs.le
    change 0 ≤ V x p q + s * parallelStripeCorrectedCarrier ε w p q
    linarith
  refine ⟨ε, s, hε, hs, parallelStripePackedAffineNetwork_depth ε w s,
    hloadedNonnegative, ?_⟩
  intro x hx
  have hproperAt := hproper s hproperS x hx
  let actual : Image 5 6 :=
    (compensatedBilinearNetwork (parallelStripePackedProperSteps ε w) s).eval
      (V x + s • parallelStripeCorrectedCarrier ε w)
  let formal : Image 5 6 := compensatedVariableChain
      (parallelStripePackedProperSteps ε w) (V x) +
    s • compensatedCarrierChain (parallelStripePackedProperSteps ε w)
      (parallelStripeCorrectedCarrier ε w)
  have hagree : NorthTwoAgree actual formal := by
    intro p hp q
    change zeroExtend actual p q = zeroExtend
      (compensatedVariableChain (parallelStripePackedProperSteps ε w) (V x) +
        s • compensatedCarrierChain (parallelStripePackedProperSteps ε w)
          (parallelStripeCorrectedCarrier ε w)) p q
    rw [zeroExtend_add, zeroExtend_smul]
    exact hproperAt p hp q
  have hfinalAgree := northTwoAgree_sharedLayerEval
    (parallelStripePackedFactorThree ε w).kernel (-s * base) hagree
  have hformalSelect : ∀ p q, parallelStripePackedProtect p q →
      sharedLayerEval (parallelStripePackedFactorThree ε w).kernel
          (-s * base) formal p q =
        if parallelStripePackedTargets p q then relu (signal x p q)
        else multiTargetPreactivation (signal x) carrier base 0 s p q := by
    intro p q hpq
    have hslt := hselect s hselectS x hx p q hpq
    dsimp [formal]
    change relu
      (fullConv (parallelStripePackedFactorThree ε w).kernel
          (compensatedVariableChain (parallelStripePackedProperSteps ε w) (V x) +
            s • compensatedCarrierChain (parallelStripePackedProperSteps ε w)
              (parallelStripeCorrectedCarrier ε w)) p q +
        (-s * base)) = _
    rw [fullConv_add]
    have hsmul := congrFun
      (congrFun (fullConvImage_smul
        (parallelStripePackedFactorThree ε w).kernel s
        (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
          (parallelStripeCorrectedCarrier ε w))) p) q
    change fullConv (parallelStripePackedFactorThree ε w).kernel
      (s • compensatedCarrierChain (parallelStripePackedProperSteps ε w)
        (parallelStripeCorrectedCarrier ε w)) p q =
      s * fullConv (parallelStripePackedFactorThree ε w).kernel
        (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
          (parallelStripeCorrectedCarrier ε w)) p q at hsmul
    rw [hsmul]
    have hslt' :
        relu (multiTargetPreactivation (signal x) carrier base 0 s p q) =
          if parallelStripePackedTargets p q then relu (signal x p q)
          else multiTargetPreactivation (signal x) carrier base 0 s p q := by
      simpa only [add_zero] using hslt
    have hpre :
        fullConv (parallelStripePackedFactorThree ε w).kernel
              (compensatedVariableChain (parallelStripePackedProperSteps ε w) (V x)) p q +
            s * fullConv (parallelStripePackedFactorThree ε w).kernel
              (compensatedCarrierChain (parallelStripePackedProperSteps ε w)
                (parallelStripeCorrectedCarrier ε w)) p q +
            (-s * base) =
          multiTargetPreactivation (signal x) carrier base 0 s p q := by
      simp [multiTargetPreactivation, signal, carrier, base,
        parallelStripePackedFinalVariable, parallelStripePackedFinalCarrierImage,
        fullConvImage]
      ac_rfl
    exact (congrArg relu hpre).trans hslt'
  have hactualProtected : ∀ p q, parallelStripePackedProtect p q →
      (parallelStripePackedAffineNetwork ε w s).eval
          (V x + s • parallelStripeCorrectedCarrier ε w) p q =
        if parallelStripePackedTargets p q then relu (signal x p q)
        else multiTargetPreactivation (signal x) carrier base 0 s p q := by
    intro p q hpq
    rw [parallelStripePackedAffineNetwork,
      SharedBiasNetworkTo.eval_append]
    change sharedLayerEval (parallelStripePackedFactorThree ε w).kernel
      (-s * base) actual p q = _
    have heqZero := hfinalAgree (p : ℕ) (by
      rcases hpq with ⟨hp, _⟩
      omega) (q : ℕ)
    have heq :
        sharedLayerEval (parallelStripePackedFactorThree ε w).kernel
            (-s * base) actual p q =
          sharedLayerEval (parallelStripePackedFactorThree ε w).kernel
            (-s * base) formal p q := by
      simpa [zeroExtend] using heqZero
    exact heq.trans (hformalSelect p q hpq)
  constructor
  · have hout := hactualProtected (1 : Fin 6) (2 : Fin 7) (by
      simp [parallelStripePackedProtect])
    rw [if_pos (by simp [parallelStripePackedTargets])] at hout
    rw [hout]
    change relu
      (parallelStripePackedFinalVariable ε w
        (parallelStripeAffineSeed ε θ x) 1 2) = _
    rw [parallelStripePackedFinalVariable_affine_target_zero]
    exact relu_mul_of_pos ε _ hε
  · have hout := hactualProtected (1 : Fin 6) (4 : Fin 7) (by
      simp [parallelStripePackedProtect])
    rw [if_pos (by simp [parallelStripePackedTargets])] at hout
    rw [hout]
    change relu
      (parallelStripePackedFinalVariable ε w
        (parallelStripeAffineSeed ε θ x) 1 4) = _
    rw [parallelStripePackedFinalVariable_affine_target_one]
    exact relu_mul_of_pos ε _ hε

/-- Compatibility form of the compact two-affine-ridge theorem, obtained by
forgetting the strengthened input-state nonnegativity certificate. -/
theorem exists_parallelStripePackedAffineNetwork_on_compact
    {K : Set (Image 1 2)} (hK : IsCompact K)
    (w : Fin 2 → Fin 2 → ℝ) (θ : Fin 2 → ℝ) :
    ∃ ε s : ℝ, 0 < ε ∧ 0 < s ∧
      (parallelStripePackedAffineNetwork ε w s).net.depth = 4 ∧
      ∀ x ∈ K,
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeAffineSeed ε θ x +
              s • parallelStripeCorrectedCarrier ε w) 1 2 =
          ε * relu (w 0 0 * x 0 0 + w 0 1 * x 0 1 + θ 0) ∧
        (parallelStripePackedAffineNetwork ε w s).eval
            (parallelStripeAffineSeed ε θ x +
              s • parallelStripeCorrectedCarrier ε w) 1 4 =
          ε * relu (w 1 0 * x 0 0 + w 1 1 * x 0 1 + θ 1) := by
  rcases exists_parallelStripePackedAffineNetwork_nonnegative_input_on_compact
      hK w θ with ⟨ε, s, hε, hs, hdepth, _hnonnegative, htargets⟩
  exact ⟨ε, s, hε, hs, hdepth, htargets⟩

end OneChannelCNNUniversality
