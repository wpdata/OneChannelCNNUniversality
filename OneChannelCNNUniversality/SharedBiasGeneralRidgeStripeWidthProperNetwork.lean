import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeProperNetwork
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeWidthCarrier

/-!
# Genuine signed-stripe networks with independent input width

The factor depth and the input width play different roles in parallel ridge
packing.  If `w : Fin (n+2) → ℝ`, the proper signed-stripe block has `n+1`
factors, whereas the input may have any width `m`.  This module removes the
earlier specialization `m = n+2` at the genuine shared-bias ReLU-network
level.

An identity seed layer maps a `1 × m` input to a `2 × (m+1)` state.  It is
followed by the `n+1` proper twisted factors, with an optional nonnegative
bias only on the last proper layer.  The output therefore has dimensions

\[
  (n+3)\times(m+n+2),
\]

and the total depth is exactly `n+2`.  On compact input families, the
independent-width carrier theorem supplies one seed threshold above which
the genuine network agrees with the formal convolution chain on its northern
two rows.
-/

namespace OneChannelCNNUniversality

open Set

private def widthStripeReindexImage
    {rows cols rows' cols' : ℕ} (hrows : rows = rows')
    (hcols : cols = cols') (x : Image rows cols) : Image rows' cols' :=
  fun p q ↦ x (Fin.cast hrows.symm p) (Fin.cast hcols.symm q)

private theorem zeroExtend_widthStripeReindexImage
    {rows cols rows' cols' : ℕ} (hrows : rows = rows')
    (hcols : cols = cols') (x : Image rows cols) (p q : ℕ) :
    zeroExtend (widthStripeReindexImage hrows hcols x) p q =
      zeroExtend x p q := by
  subst rows'
  subst cols'
  rfl

private def widthStripeReindexSharedBiasNetworkTo
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols) :
    SharedBiasNetworkTo kRows kCols inRows inCols outRows' outCols' :=
  ⟨net.net, net.rows_eq.trans hrows, net.cols_eq.trans hcols⟩

private theorem zeroExtend_widthStripeReindexSharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) (p q : ℕ) :
    zeroExtend
        ((widthStripeReindexSharedBiasNetworkTo hrows hcols net).eval x) p q =
      zeroExtend (net.eval x) p q := by
  subst outRows'
  subst outCols'
  rfl

/-- Before dimension normalization, the independent-width genuine network
is the seed layer followed by the proper factor block, biased only at its
last layer. -/
noncomputable def generalRidgeStripeWidthProperRawNetwork {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    SharedBiasNetworkTo 2 2 1 m
      (grownSize 2 2
        (generalRidgeStripeTwistedProperFactors w T).length)
      (grownSize 2 (m + 1)
        (generalRidgeStripeTwistedProperFactors w T).length) :=
  (sharedBiasSeedLayer c).append
    (biasedLastBilinearNetwork
      (generalRidgeStripeTwistedProperFactors w T)
      (generalRidgeStripeTwistedProperFactors_ne_nil w T) t 2 (m + 1))

/-- A genuine one-channel expansive shared-bias ReLU network with arbitrary
input width `m`, proper-factor depth `n+1`, and normalized output dimensions
`(n+3) × (m+n+2)`. -/
noncomputable def generalRidgeStripeWidthProperNetwork {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    SharedBiasNetworkTo 2 2 1 m (n + 3) (m + n + 2) :=
  widthStripeReindexSharedBiasNetworkTo
    (by simp [grownSize_two_eq_add]; omega)
    (by simp [grownSize_two_eq_add]; omega)
    (generalRidgeStripeWidthProperRawNetwork w T c t)

/-- Reindexing the public independent-width network preserves every
zero-extended output coordinate. -/
theorem zeroExtend_generalRidgeStripeWidthProperNetwork_eval {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ)
    (x : Image 1 m) (p q : ℕ) :
    zeroExtend
        ((generalRidgeStripeWidthProperNetwork w T c t).eval x) p q =
      zeroExtend
        ((generalRidgeStripeWidthProperRawNetwork w T c t).eval x) p q := by
  exact zeroExtend_widthStripeReindexSharedBiasNetworkTo_eval _ _ _ x p q

/-- The independent-width proper network has one seed layer and exactly
`n+1` proper factor layers. -/
@[simp] theorem generalRidgeStripeWidthProperNetwork_depth {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t : ℝ) :
    (generalRidgeStripeWidthProperNetwork
      (m := m) w T c t).net.depth = n + 2 := by
  change (generalRidgeStripeWidthProperRawNetwork
    (m := m) w T c t).net.depth = n + 2
  rw [generalRidgeStripeWidthProperRawNetwork,
    SharedBiasNetworkTo.depth_append]
  have htail := biasedLastBilinearNetwork_depth
    (generalRidgeStripeTwistedProperFactors w T)
    (generalRidgeStripeTwistedProperFactors_ne_nil w T) t 2 (m + 1)
  change 1 +
      (biasedLastBilinearNetwork
        (generalRidgeStripeTwistedProperFactors w T)
        (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t 2 (m + 1)).net.depth = n + 2
  rw [htail]
  simp
  omega

/-- The normalized independent-width formal state: proper convolution of
the seeded state followed by addition of the last proper-layer bias. -/
noncomputable def generalRidgeStripeWidthProperFormalState {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T t : ℝ)
    (seeded : Image 2 (m + 1)) : Image (n + 3) (m + n + 2) :=
  widthStripeReindexImage
    (by simp [grownSize_two_eq_add]; omega)
    (by simp [grownSize_two_eq_add]; omega)
    (fullConvChain (generalRidgeStripeTwistedProperFactors w T) seeded +
      constantImage
        (grownSize 2 2
          (generalRidgeStripeTwistedProperFactors w T).length)
        (grownSize 2 (m + 1)
          (generalRidgeStripeTwistedProperFactors w T).length) t)

/-- Coordinate form of the independent-width formal state. -/
theorem zeroExtend_generalRidgeStripeWidthProperFormalState {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T t : ℝ)
    (seeded : Image 2 (m + 1)) (p q : ℕ) :
    zeroExtend
        (generalRidgeStripeWidthProperFormalState w T t seeded) p q =
      zeroExtend
        (fullConvChain (generalRidgeStripeTwistedProperFactors w T) seeded +
          constantImage
            (grownSize 2 2
              (generalRidgeStripeTwistedProperFactors w T).length)
            (grownSize 2 (m + 1)
              (generalRidgeStripeTwistedProperFactors w T).length) t) p q := by
  exact zeroExtend_widthStripeReindexImage _ _ _ p q

/-- Exact northern-two-row behavior once the seed is exact and the formal
proper chain stays in ReLU's linear branch there. -/
theorem generalRidgeStripeWidthProperNetwork_northTwoAgree_formalState
    {n m : ℕ} (w : Fin (n + 2) → ℝ) (T c t : ℝ)
    (x : Image 1 m) (seeded : Image 2 (m + 1))
    (hseed : (sharedBiasSeedLayer c).eval x = seeded)
    (hlinear : NorthTwoLinearAlong
      (generalRidgeStripeTwistedProperFactors w T) seeded)
    (ht : 0 ≤ t) :
    NorthTwoAgree
      ((generalRidgeStripeWidthProperNetwork w T c t).eval x)
      (generalRidgeStripeWidthProperFormalState w T t seeded) := by
  let fs := generalRidgeStripeTwistedProperFactors w T
  have hraw : NorthTwoAgree
      ((biasedLastBilinearNetwork fs
        (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t 2 (m + 1)).eval seeded)
      (fullConvChain fs seeded +
        constantImage (grownSize 2 2 fs.length)
          (grownSize 2 (m + 1) fs.length) t) :=
    biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
      fs (generalRidgeStripeTwistedProperFactors_ne_nil w T)
        t seeded hlinear ht
  intro p hp q
  rw [zeroExtend_generalRidgeStripeWidthProperNetwork_eval,
    zeroExtend_generalRidgeStripeWidthProperFormalState]
  change zeroExtend
      (((sharedBiasSeedLayer c).append
        (biasedLastBilinearNetwork fs
          (generalRidgeStripeTwistedProperFactors_ne_nil w T)
          t 2 (m + 1))).eval x) p q = _
  rw [SharedBiasNetworkTo.eval_append, hseed]
  exact hraw p hp q

/-- The explicit reciprocal-scale threshold needed by the arbitrary-width
proper network. -/
noncomputable def generalRidgeStripeWidthProperScaleThreshold {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) : ℝ :=
  generalRidgeStripeWidthCarrierThreshold w m

theorem generalRidgeStripeWidthProperScaleThreshold_one_le {n : ℕ}
    (w : Fin (n + 2) → ℝ) (m : ℕ) :
    1 ≤ generalRidgeStripeWidthProperScaleThreshold w m := by
  exact generalRidgeStripeWidthCarrierThreshold_one_le w m

/-- Every scale above the explicit threshold gives the unit-lower carrier
needed for arbitrary-width genuine linearization. -/
theorem generalRidgeStripeWidthProperScaleThreshold_spec {n m : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeWidthProperScaleThreshold w m ≤ T) :
    NorthTwoUnitLowerAlong
      (generalRidgeStripeTwistedProperFactors w T)
      (constantImage 2 (m + 1) 2) := by
  exact generalRidgeStripeTwistedProperFactors_unitLower_width_of_large
    w T hT

/-- At a fixed sufficiently large scale, compactness supplies one
upward-closed seed threshold for the arbitrary-width genuine network. -/
theorem exists_generalRidgeStripeWidthProperNetwork_threshold_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n m : ℕ} (F : X → Image 1 m)
    (hF : ContinuousFeatureOn K F) (w : Fin (n + 2) → ℝ)
    (T : ℝ) (hT : generalRidgeStripeWidthProperScaleThreshold w m ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, C ≤ c → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
        (sharedBiasSeedLayer c).eval (F x) =
            seededNorthTwoState F c x ∧
          NorthTwoLinearAlong
            (generalRidgeStripeTwistedProperFactors w T)
            (seededNorthTwoState F c x) ∧
          NorthTwoAgree
            ((generalRidgeStripeWidthProperNetwork w T c t).eval (F x))
            (generalRidgeStripeWidthProperFormalState w T t
              (seededNorthTwoState F c x)) := by
  have hcarrier := generalRidgeStripeWidthProperScaleThreshold_spec
    w T hT
  obtain ⟨C, hC, hbehavior⟩ :=
    exists_seededNorthTwoNetwork_threshold_on_compact
      hK F hF (generalRidgeStripeTwistedProperFactors w T) hcarrier
  refine ⟨C, hC, ?_⟩
  intro c hCc t ht x hx
  obtain ⟨hseed, hlinear, -⟩ := hbehavior c hCc x hx
  exact ⟨hseed, hlinear,
    generalRidgeStripeWidthProperNetwork_northTwoAgree_formalState
      w T c t (F x) (seededNorthTwoState F c x)
      hseed hlinear ht⟩

/-- Bundled compact interface: one explicit scale and one compact seed
threshold yield an exact genuine arbitrary-width proper network for every
larger seed and every nonnegative last-layer bias. -/
theorem exists_generalRidgeStripeWidthProperNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n m : ℕ} (F : X → Image 1 m)
    (hF : ContinuousFeatureOn K F) (w : Fin (n + 2) → ℝ) :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧
      NorthTwoUnitLowerAlong
        (generalRidgeStripeTwistedProperFactors w T)
        (constantImage 2 (m + 1) 2) ∧
      ∀ c : ℝ, C ≤ c → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
        (sharedBiasSeedLayer c).eval (F x) =
            seededNorthTwoState F c x ∧
          NorthTwoLinearAlong
            (generalRidgeStripeTwistedProperFactors w T)
            (seededNorthTwoState F c x) ∧
          NorthTwoAgree
            ((generalRidgeStripeWidthProperNetwork w T c t).eval (F x))
            (generalRidgeStripeWidthProperFormalState w T t
              (seededNorthTwoState F c x)) := by
  let T := generalRidgeStripeWidthProperScaleThreshold w m
  have hT : generalRidgeStripeWidthProperScaleThreshold w m ≤ T := le_rfl
  have hcarrier := generalRidgeStripeWidthProperScaleThreshold_spec w T hT
  obtain ⟨C, hC, hbehavior⟩ :=
    exists_generalRidgeStripeWidthProperNetwork_threshold_on_compact
      hK F hF w T hT
  exact ⟨T, C, generalRidgeStripeWidthProperScaleThreshold_one_le w m,
    hC, hcarrier, hbehavior⟩

end OneChannelCNNUniversality
