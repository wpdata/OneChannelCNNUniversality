import OneChannelCNNUniversality.SharedBiasNorthTwoLinearization
import OneChannelCNNUniversality.SharedBiasHeterogeneousCarrier
import OneChannelCNNUniversality.SharedBiasGridNetwork
import OneChannelCNNUniversality.SharedBiasRecovery
import OneChannelCNNUniversality.SharedBiasSeedTransport

/-!
# Compact domination by a northern-two-row carrier

This module turns a quantitative positive carrier certificate into the exact
linearity hypothesis required by `SharedBiasNorthTwoLinearization`.  The
carrier must contribute at least one at every northern-two-row preactivation
of every prefix.  Compactness then supplies one scale that dominates the
entire variable signal family at all such sites simultaneously.

The result is independent of the ridge factorization.  A later module only
has to prove that its explicit stripe carrier satisfies
`NorthTwoUnitLowerAlong`.
-/

namespace OneChannelCNNUniversality

open Set

/-- For an arbitrary signed compact input family, every sufficiently large
identity-seed bias exposes the exact affine state `identity convolution + c`.
The threshold is upward closed, which lets a later carrier argument enlarge
the same seed without redoing the first-layer proof. -/
theorem exists_sharedBiasSeed_threshold_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) :
    ∃ b : ℝ, 0 < b ∧ ∀ c : ℝ, b ≤ c → ∀ x ∈ K,
      (sharedBiasSeedLayer c).eval (F x) =
        fullConvImage expansiveIdentityKernel (F x) +
          constantImage (rows + 2 - 1) (cols + 2 - 1) c := by
  obtain ⟨b, hb, hlinear⟩ :=
    exists_shared_bias_linearization hK F hF expansiveIdentityKernel
  refine ⟨b, hb, ?_⟩
  intro c hbc x hx
  funext p q
  have hbase : 0 ≤ fullConv expansiveIdentityKernel (F x) p q + b := by
    calc
      0 ≤ sharedLayerEval expansiveIdentityKernel b (F x) p q :=
        sharedLayerEval_nonnegative expansiveIdentityKernel b (F x) p q
      _ = fullConv expansiveIdentityKernel (F x) p q + b :=
        hlinear x hx p q
  change relu (fullConv expansiveIdentityKernel (F x) p q + c) =
    fullConv expansiveIdentityKernel (F x) p q + c
  apply relu_of_nonneg
  linarith

/-- A formal carrier contributes at least one at every preactivation in rows
zero and one, recursively along a heterogeneous bilinear-kernel chain. -/
def NorthTwoUnitLowerAlong : (fs : List BilinearKernelFactor) →
    {rows cols : ℕ} → Image rows cols → Prop
  | [], _, _, _ => True
  | f :: fs, rows, cols, carrier =>
      (∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
        ∀ q : Fin (cols + 2 - 1),
          1 ≤ fullConv f.kernel carrier p q) ∧
      NorthTwoUnitLowerAlong fs (fullConvImage f.kernel carrier)

/-- A carrier certificate for a concatenated factor list splits into the
certificate for the head and the certificate for the transported carrier
along the tail. -/
theorem northTwoUnitLowerAlong_append_iff
    (fs gs : List BilinearKernelFactor) {rows cols : ℕ}
    (carrier : Image rows cols) :
    NorthTwoUnitLowerAlong (fs ++ gs) carrier ↔
      NorthTwoUnitLowerAlong fs carrier ∧
        NorthTwoUnitLowerAlong gs (fullConvChain fs carrier) := by
  induction fs generalizing rows cols carrier with
  | nil =>
      change NorthTwoUnitLowerAlong gs carrier ↔
        True ∧ NorthTwoUnitLowerAlong gs carrier
      tauto
  | cons f fs ih =>
      simp only [List.cons_append, NorthTwoUnitLowerAlong, fullConvChain]
      rw [ih]
      tauto

/-- A unit-lower carrier can be scaled to keep an arbitrary continuous
compact signal family in the linear ReLU branch throughout the northern two
rows of every prefix. -/
theorem exists_northTwoLinearAlong_add_smul_of_unitLower
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (fs : List BilinearKernelFactor)
    {rows cols : ℕ} (V : X → Image rows cols)
    (hV : ContinuousFeatureOn K V) (carrier : Image rows cols)
    (hcarrier : NorthTwoUnitLowerAlong fs carrier) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧
      ∀ s : ℝ, s₀ ≤ s → ∀ x ∈ K,
        NorthTwoLinearAlong fs (V x + s • carrier) := by
  induction fs generalizing rows cols V carrier with
  | nil =>
      exact ⟨0, le_rfl, by intros; trivial⟩
  | cons f fs ih =>
      rcases hcarrier with ⟨hfirstCarrier, htailCarrier⟩
      let nextV : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ fullConvImage f.kernel (V x)
      let nextCarrier : Image (rows + 2 - 1) (cols + 2 - 1) :=
        fullConvImage f.kernel carrier
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV f.kernel p q
      obtain ⟨M, hMpos, hMbound⟩ :=
        exists_uniform_feature_margin hK nextV hnextV 0
      obtain ⟨tailScale, htailScale, htail⟩ :=
        ih nextV hnextV nextCarrier htailCarrier
      refine ⟨max M tailScale, ?_, ?_⟩
      · exact hMpos.le.trans (le_max_left _ _)
      intro s hs x hx
      have hMs : M ≤ s := le_trans (le_max_left _ _) hs
      have htails : tailScale ≤ s := le_trans (le_max_right _ _) hs
      have hsnonneg : 0 ≤ s := htailScale.trans htails
      constructor
      · intro p hp q
        have hvariable :
            |fullConv f.kernel (V x) p q| < M := by
          simpa [nextV, fullConvImage] using hMbound x hx p q
        have hscaled :
            s ≤ s * fullConv f.kernel carrier p q := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hfirstCarrier p hp q) hsnonneg
        have hsmul :
            fullConv f.kernel (s • carrier) p q =
              s * fullConv f.kernel carrier p q := by
          have h := congrFun
            (congrFun (fullConvImage_smul f.kernel s carrier) p) q
          exact h
        rw [fullConv_add, hsmul]
        have hnegative : -M < fullConv f.kernel (V x) p q := by
          exact neg_lt_of_abs_lt hvariable
        linarith
      · have htail := htail s htails x hx
        simpa [nextV, nextCarrier, fullConvImage_add,
          fullConvImage_smul] using htail

end OneChannelCNNUniversality
