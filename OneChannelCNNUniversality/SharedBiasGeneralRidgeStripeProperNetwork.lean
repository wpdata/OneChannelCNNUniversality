import OneChannelCNNUniversality.SharedBiasBiasedLast
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeCarrier
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeSeedAddress
import OneChannelCNNUniversality.SharedBiasSeededNorthTwoNetwork

/-!
# The genuine proper signed-stripe network

This module realizes the proper part of the signed stripe by a genuine
one-channel expansive shared-bias ReLU network.  An identity seed layer with
bias `c` is followed by all `n+1` proper twisted factors.  Only the last
proper factor receives the additional shared bias `t`; every earlier proper
factor has bias zero.

The reciprocal scale is chosen above both independent algebraic thresholds:
the northern-two-row carrier threshold for every proper prefix and the
complete seed-address threshold used by the final selector.  Compactness then
gives one upward-closed seed threshold.  For every larger seed and every
nonnegative last-proper-layer bias, the genuine network agrees on its northern
two rows with the formal proper convolution plus the constant `t`.
-/

namespace OneChannelCNNUniversality

open Set

private def stripeReindexImage
    {rows cols rows' cols' : ℕ} (hrows : rows = rows')
    (hcols : cols = cols') (x : Image rows cols) : Image rows' cols' :=
  fun p q ↦ x (Fin.cast hrows.symm p) (Fin.cast hcols.symm q)

private theorem zeroExtend_stripeReindexImage
    {rows cols rows' cols' : ℕ} (hrows : rows = rows')
    (hcols : cols = cols') (x : Image rows cols) (p q : ℕ) :
    zeroExtend (stripeReindexImage hrows hcols x) p q =
      zeroExtend x p q := by
  subst rows'
  subst cols'
  rfl

private def stripeReindexSharedBiasNetworkTo
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols) :
    SharedBiasNetworkTo kRows kCols inRows inCols outRows' outCols' :=
  ⟨net.net, net.rows_eq.trans hrows, net.cols_eq.trans hcols⟩

private theorem zeroExtend_stripeReindexSharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) (p q : ℕ) :
    zeroExtend
        ((stripeReindexSharedBiasNetworkTo hrows hcols net).eval x) p q =
      zeroExtend (net.eval x) p q := by
  subst outRows'
  subst outCols'
  rfl

/-- The proper signed-stripe factor block is nonempty, including at `n=0`. -/
theorem generalRidgeStripeTwistedProperFactors_ne_nil {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    generalRidgeStripeTwistedProperFactors w T ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp at hlength

/-- Before output-dimension normalization, the genuine network is the seed
layer followed by a factor block biased only at its last layer. -/
noncomputable def generalRidgeStripeProperRawNetwork {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    SharedBiasNetworkTo 2 2 1 (n + 2)
      (grownSize 2 2
        (generalRidgeStripeTwistedProperFactors w T).length)
      (grownSize 2 (n + 3)
        (generalRidgeStripeTwistedProperFactors w T).length) :=
  (sharedBiasSeedLayer c).append
    (biasedLastBilinearNetwork
      (generalRidgeStripeTwistedProperFactors w T)
      (generalRidgeStripeTwistedProperFactors_ne_nil w T) t 2 (n + 3))

/-- The genuine proper signed-stripe network, with its output dimensions
normalized to `(n+3) × (2*(n+2))`. -/
noncomputable def generalRidgeStripeProperNetwork {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    SharedBiasNetworkTo 2 2 1 (n + 2) (n + 3) (2 * (n + 2)) :=
  stripeReindexSharedBiasNetworkTo
    (by simp [grownSize_two_eq_add]; omega)
    (by simp [grownSize_two_eq_add]; omega)
    (generalRidgeStripeProperRawNetwork w T c t)

/-- Reindexing the public network does not alter any zero-extended output
coordinate. -/
theorem zeroExtend_generalRidgeStripeProperNetwork_eval {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ)
    (x : Image 1 (n + 2)) (p q : ℕ) :
    zeroExtend ((generalRidgeStripeProperNetwork w T c t).eval x) p q =
      zeroExtend ((generalRidgeStripeProperRawNetwork w T c t).eval x) p q := by
  exact zeroExtend_stripeReindexSharedBiasNetworkTo_eval _ _ _ x p q

/-- The proper network has the seed layer plus exactly `n+1` proper factor
layers. -/
@[simp] theorem generalRidgeStripeProperNetwork_depth {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    (generalRidgeStripeProperNetwork w T c t).net.depth = n + 2 := by
  change (generalRidgeStripeProperRawNetwork w T c t).net.depth = n + 2
  rw [generalRidgeStripeProperRawNetwork,
    SharedBiasNetworkTo.depth_append]
  have htail := biasedLastBilinearNetwork_depth
    (generalRidgeStripeTwistedProperFactors w T)
    (generalRidgeStripeTwistedProperFactors_ne_nil w T) t 2 (n + 3)
  change 1 +
      (biasedLastBilinearNetwork
        (generalRidgeStripeTwistedProperFactors w T)
        (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t 2 (n + 3)).net.depth = n + 2
  rw [htail]
  simp
  omega

/-- The exactly sized formal proper state: formal convolution through the
proper factors, followed by addition of the last proper-layer bias. -/
noncomputable def generalRidgeStripeProperFormalState {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T t : ℝ)
    (seeded : Image 2 (n + 3)) : Image (n + 3) (2 * (n + 2)) :=
  stripeReindexImage
    (by simp [grownSize_two_eq_add]; omega)
    (by simp [grownSize_two_eq_add]; omega)
    (fullConvChain (generalRidgeStripeTwistedProperFactors w T) seeded +
      constantImage
        (grownSize 2 2
          (generalRidgeStripeTwistedProperFactors w T).length)
        (grownSize 2 (n + 3)
          (generalRidgeStripeTwistedProperFactors w T).length) t)

/-- The normalized formal state is coordinatewise the formal proper chain
plus the constant `t`, after zero extension. -/
theorem zeroExtend_generalRidgeStripeProperFormalState {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T t : ℝ)
    (seeded : Image 2 (n + 3)) (p q : ℕ) :
    zeroExtend (generalRidgeStripeProperFormalState w T t seeded) p q =
      zeroExtend
        (fullConvChain (generalRidgeStripeTwistedProperFactors w T) seeded +
          constantImage
            (grownSize 2 2
              (generalRidgeStripeTwistedProperFactors w T).length)
            (grownSize 2 (n + 3)
              (generalRidgeStripeTwistedProperFactors w T).length) t) p q := by
  exact zeroExtend_stripeReindexImage _ _ _ p q

/-- Exact northern-two-row behavior once the seed layer is exact and the
formal proper factor chain stays in ReLU's linear branch there. -/
theorem generalRidgeStripeProperNetwork_northTwoAgree_formalState
    {n : ℕ} (w : Fin (n + 2) → ℝ) (T c t : ℝ)
    (x : Image 1 (n + 2)) (seeded : Image 2 (n + 3))
    (hseed : (sharedBiasSeedLayer c).eval x = seeded)
    (hlinear : NorthTwoLinearAlong
      (generalRidgeStripeTwistedProperFactors w T) seeded)
    (ht : 0 ≤ t) :
    NorthTwoAgree
      ((generalRidgeStripeProperNetwork w T c t).eval x)
      (generalRidgeStripeProperFormalState w T t seeded) := by
  let fs := generalRidgeStripeTwistedProperFactors w T
  have hraw : NorthTwoAgree
      ((biasedLastBilinearNetwork fs
        (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t 2 (n + 3)).eval seeded)
      (fullConvChain fs seeded +
        constantImage (grownSize 2 2 fs.length)
          (grownSize 2 (n + 3) fs.length) t) :=
    biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
      fs (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t seeded hlinear ht
  intro p hp q
  rw [zeroExtend_generalRidgeStripeProperNetwork_eval,
    zeroExtend_generalRidgeStripeProperFormalState]
  change zeroExtend
      (((sharedBiasSeedLayer c).append
        (biasedLastBilinearNetwork fs
          (generalRidgeStripeTwistedProperFactors_ne_nil w T)
          t 2 (n + 3))).eval x) p q = _
  rw [SharedBiasNetworkTo.eval_append, hseed]
  exact hraw p hp q

/-- One explicit reciprocal scale that simultaneously dominates the proper
carrier threshold and the complete seed-address threshold. -/
noncomputable def generalRidgeStripeJointScaleThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  max (generalRidgeStripeCarrierThreshold w)
    (generalRidgeStripeSeedAddressThreshold w)

theorem generalRidgeStripeJointScaleThreshold_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    1 ≤ generalRidgeStripeJointScaleThreshold w := by
  exact (generalRidgeStripeCarrierThreshold_one_le w).trans
    (le_max_left _ _)

/-- Every scale above the joint threshold supplies both the unit-lower
proper carrier and the complete row-one unit-gap seed address. -/
theorem generalRidgeStripeJointScaleThreshold_spec {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeJointScaleThreshold w ≤ T) :
    NorthTwoUnitLowerAlong
        (generalRidgeStripeTwistedProperFactors w T)
        (constantImage 2 (n + 3) 2) ∧
      ∀ q : ℕ, q ≤ 2 * (n + 2) → q ≠ n + 2 →
        1 ≤ generalRidgeStripeSeedAddressRowOne w T q -
          generalRidgeStripeSeedAddressRowOne w T (n + 2) := by
  constructor
  · exact generalRidgeStripeTwistedProperFactors_unitLower_of_large
      w T ((le_max_left _ _).trans hT)
  · intro q hq hne
    exact generalRidgeStripeSeedAddress_row_one_gap_of_threshold
      w T ((le_max_right _ _).trans hT) q hq hne

/-- Existential interface for choosing one reciprocal scale with both
properties. -/
theorem exists_generalRidgeStripeJointScale {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧
      NorthTwoUnitLowerAlong
          (generalRidgeStripeTwistedProperFactors w T)
          (constantImage 2 (n + 3) 2) ∧
        ∀ q : ℕ, q ≤ 2 * (n + 2) → q ≠ n + 2 →
          1 ≤ generalRidgeStripeSeedAddressRowOne w T q -
            generalRidgeStripeSeedAddressRowOne w T (n + 2) := by
  refine ⟨generalRidgeStripeJointScaleThreshold w,
    generalRidgeStripeJointScaleThreshold_one_le w, ?_⟩
  exact generalRidgeStripeJointScaleThreshold_spec w _ le_rfl

/-- For a fixed scale above the joint threshold, compactness supplies one
upward-closed seed threshold.  Every larger seed and every nonnegative
last-proper-layer bias have the advertised exact northern-two-row behavior. -/
theorem exists_generalRidgeStripeProperNetwork_threshold_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F) (w : Fin (n + 2) → ℝ)
    (T : ℝ) (hT : generalRidgeStripeJointScaleThreshold w ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, C ≤ c → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
        (sharedBiasSeedLayer c).eval (F x) =
            seededNorthTwoState F c x ∧
          NorthTwoLinearAlong
            (generalRidgeStripeTwistedProperFactors w T)
            (seededNorthTwoState F c x) ∧
          NorthTwoAgree
            ((generalRidgeStripeProperNetwork w T c t).eval (F x))
            (generalRidgeStripeProperFormalState w T t
              (seededNorthTwoState F c x)) := by
  have hcarrier := (generalRidgeStripeJointScaleThreshold_spec w T hT).1
  obtain ⟨C, hC, hbehavior⟩ :=
    exists_seededNorthTwoNetwork_threshold_on_compact
      hK F hF (generalRidgeStripeTwistedProperFactors w T) hcarrier
  refine ⟨C, hC, ?_⟩
  intro c hCc t ht x hx
  obtain ⟨hseed, hlinear, -⟩ := hbehavior c hCc x hx
  exact ⟨hseed, hlinear,
    generalRidgeStripeProperNetwork_northTwoAgree_formalState
      w T c t (F x) (seededNorthTwoState F c x) hseed hlinear ht⟩

/-- Fully bundled compact interface: the explicit joint scale and a compact
seed threshold produce a depth-`n+2` genuine proper network for every
`c ≥ C` and `t ≥ 0`. -/
theorem exists_generalRidgeStripeProperNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F) (w : Fin (n + 2) → ℝ) :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧
      NorthTwoUnitLowerAlong
          (generalRidgeStripeTwistedProperFactors w T)
          (constantImage 2 (n + 3) 2) ∧
      (∀ q : ℕ, q ≤ 2 * (n + 2) → q ≠ n + 2 →
        1 ≤ generalRidgeStripeSeedAddressRowOne w T q -
          generalRidgeStripeSeedAddressRowOne w T (n + 2)) ∧
      ∀ c : ℝ, C ≤ c → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
        (sharedBiasSeedLayer c).eval (F x) =
            seededNorthTwoState F c x ∧
          NorthTwoLinearAlong
            (generalRidgeStripeTwistedProperFactors w T)
            (seededNorthTwoState F c x) ∧
          NorthTwoAgree
            ((generalRidgeStripeProperNetwork w T c t).eval (F x))
            (generalRidgeStripeProperFormalState w T t
              (seededNorthTwoState F c x)) := by
  let T := generalRidgeStripeJointScaleThreshold w
  have hT : generalRidgeStripeJointScaleThreshold w ≤ T := le_rfl
  have hspec := generalRidgeStripeJointScaleThreshold_spec w T hT
  obtain ⟨C, hC, hbehavior⟩ :=
    exists_generalRidgeStripeProperNetwork_threshold_on_compact
      hK F hF w T hT
  exact ⟨T, C, generalRidgeStripeJointScaleThreshold_one_le w, hC,
    hspec.1, hspec.2, hbehavior⟩

end OneChannelCNNUniversality
