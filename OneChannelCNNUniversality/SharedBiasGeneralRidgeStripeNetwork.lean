import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeProperNetwork
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeRealization
import OneChannelCNNUniversality.SharedBiasTwoCarrierSelection

/-!
# A genuine signed-stripe shared-bias ridge network

This module joins the proper-prefix linearization, the two realized carrier
addresses, and the compact two-carrier selector.  The result is a genuine
one-channel expansive `2 × 2` shared-bias ReLU network of depth `n+3` for an
input of width `n+2`.  Its protected target computes one arbitrary affine
ReLU ridge exactly, while every other coordinate in the northern two rows
remains in the linear branch of the final ReLU.
-/

namespace OneChannelCNNUniversality

open Set

private theorem stripe_fullConvChain_add
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (x y : Image rows cols) :
    fullConvChain fs (x + y) =
      fullConvChain fs x + fullConvChain fs y := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (x + y)) = _
      rw [fullConvImage_add]
      exact ih _ _

private theorem stripe_fullConvChain_smul
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (a : ℝ) (x : Image rows cols) :
    fullConvChain fs (a • x) = a • fullConvChain fs x := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (a • x)) = _
      rw [fullConvImage_smul]
      exact ih _

private theorem fullConv_eq_of_zeroExtend_eq
    {kRows kCols rows cols rows' cols' : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols)
    (y : Image rows' cols') (p q : ℕ)
    (hxy : ∀ i j, zeroExtend x i j = zeroExtend y i j) :
    fullConv w x p q = fullConv w y p q := by
  unfold fullConv
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · rw [hxy]
  · rfl

private theorem stripe_fullConv_smul
    {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (a : ℝ) (x : Image rows cols)
    (p q : ℕ) :
    fullConv w (a • x) p q = a * fullConv w x p q := by
  unfold fullConv
  simp only [zeroExtend_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- Scalar shared bias used by the final factor, normalized so that its
target preactivation is the variable signal plus `theta`. -/
noncomputable def generalRidgeStripeFinalBias {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t theta : ℝ) : ℝ :=
  theta - c * generalRidgeStripeSeedAddressImage w T
      (generalRidgeStripeTarget n).1 (generalRidgeStripeTarget n).2 -
    t * generalRidgeStripeFinalLocalAddressImage w T
      (generalRidgeStripeTarget n).1 (generalRidgeStripeTarget n).2

private def stripeFinalReindexNetworkTo
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols) :
    SharedBiasNetworkTo kRows kCols inRows inCols outRows' outCols' :=
  ⟨net.net, net.rows_eq.trans hrows, net.cols_eq.trans hcols⟩

private theorem zeroExtend_stripeFinalReindexNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) (p q : ℕ) :
    zeroExtend ((stripeFinalReindexNetworkTo hrows hcols net).eval x) p q =
      zeroExtend (net.eval x) p q := by
  subst outRows'
  subst outCols'
  rfl

/-- The complete genuine signed-stripe network: a seed layer, all proper
factors with a bias only at the last proper layer, and the final twisted
factor with its target-normalizing shared bias. -/
noncomputable def generalRidgeStripeNetwork {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t theta : ℝ) :
    SharedBiasNetworkTo 2 2 1 (n + 2)
      (n + 4) (2 * (n + 2) + 1) :=
  stripeFinalReindexNetworkTo (by omega) (by omega)
    ((generalRidgeStripeProperNetwork w T c t).append
      (SharedBiasNetworkTo.single
        (generalRidgeStripeTwistedLastFactor w T).kernel
        (generalRidgeStripeFinalBias w T c t theta)))

@[simp] theorem generalRidgeStripeNetwork_depth {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t theta : ℝ) :
    (generalRidgeStripeNetwork w T c t theta).net.depth = n + 3 := by
  change (((generalRidgeStripeProperNetwork w T c t).append
      (SharedBiasNetworkTo.single
        (generalRidgeStripeTwistedLastFactor w T).kernel
        (generalRidgeStripeFinalBias w T c t theta))).net.depth) = n + 3
  rw [SharedBiasNetworkTo.depth_append,
    generalRidgeStripeProperNetwork_depth]
  change n + 2 + 1 = n + 3
  omega

/-- The explicit final output agrees at every zero-extended coordinate with
the unreindexed append construction. -/
theorem zeroExtend_generalRidgeStripeNetwork_eval {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t theta : ℝ)
    (x : Image 1 (n + 2)) (p q : ℕ) :
    zeroExtend ((generalRidgeStripeNetwork w T c t theta).eval x) p q =
      zeroExtend (sharedLayerEval
          (generalRidgeStripeTwistedLastFactor w T).kernel
          (generalRidgeStripeFinalBias w T c t theta)
          ((generalRidgeStripeProperNetwork w T c t).eval x)) p q := by
  rw [generalRidgeStripeNetwork]
  rw [zeroExtend_stripeFinalReindexNetworkTo_eval]
  rw [SharedBiasNetworkTo.eval_append, SharedBiasNetworkTo.eval_single]

/-- Exact scalar decomposition of the ideal final preactivation on the
protected northern two rows. -/
theorem generalRidgeStripeFormalFinal_preactivation {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T c t theta : ℝ)
    (x : Image 1 (n + 2))
    (p : Fin (n + 4)) (hp : (p : ℕ) ≤ 1)
    (q : Fin (2 * (n + 2) + 1)) :
    fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
        (generalRidgeStripeProperFormalState w T t
          (generalRidgeStripeVariableSeed x +
            constantImage 2 (n + 3) c)) p q +
        generalRidgeStripeFinalBias w T c t theta =
      twoCarrierPreactivation
        (generalRidgeStripeVariableSignal w T x)
        (generalRidgeStripeSeedAddressImage w T)
        (generalRidgeStripeFinalLocalAddressImage w T)
        (generalRidgeStripeTarget n) theta c t p q := by
  let fs := generalRidgeStripeTwistedProperFactors w T
  let last := generalRidgeStripeTwistedLastFactor w T
  let variableSeed := generalRidgeStripeVariableSeed x
  let unitSeed : Image 2 (n + 3) := constantImage 2 (n + 3) 1
  let properVariable := fullConvChain fs variableSeed
  let properSeed := fullConvChain fs unitSeed
  let localCarrier : Image (grownSize 2 2 fs.length)
      (grownSize 2 (n + 3) fs.length) :=
    constantImage (grownSize 2 2 fs.length)
      (grownSize 2 (n + 3) fs.length) 1
  have hconstant : constantImage 2 (n + 3) c = c • unitSeed := by
    funext i j
    simp [unitSeed, constantImage]
  have hlocalConstant :
      constantImage (grownSize 2 2 fs.length)
          (grownSize 2 (n + 3) fs.length) t =
        t • localCarrier := by
    funext i j
    simp [localCarrier, constantImage]
  have hproper : ∀ i j,
      zeroExtend
          (generalRidgeStripeProperFormalState w T t
            (variableSeed + constantImage 2 (n + 3) c)) i j =
        zeroExtend (properVariable + c • properSeed + t • localCarrier) i j := by
    intro i j
    rw [zeroExtend_generalRidgeStripeProperFormalState]
    rw [hconstant, hlocalConstant, stripe_fullConvChain_add,
      stripe_fullConvChain_smul]
  have hconv := fullConv_eq_of_zeroExtend_eq last.kernel
    (generalRidgeStripeProperFormalState w T t
      (variableSeed + constantImage 2 (n + 3) c))
    (properVariable + c • properSeed + t • localCarrier) p q hproper
  rw [hconv, fullConv_add, fullConv_add]
  have hproperSeedFinal :
      fullConv last.kernel properSeed p q =
        generalRidgeStripeSeedAddressImage w T p q := by
    have happend := zeroExtend_fullConvChain_append fs [last] unitSeed p q
    rw [← generalRidgeStripeTwistedFactors_eq_proper_append_last] at happend
    change zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T) unitSeed) p q =
      zeroExtend (fullConvImage last.kernel properSeed) p q at happend
    have haddress :=
      generalRidgeStripeSeedAddressImage_eq_fullConvChain_north
        w T p hp q
    have hleft : p < n + 4 := p.isLt
    have hright : q < 2 * (n + 2) + 1 := q.isLt
    have hproperLeft :
        (p : ℕ) < grownSize 2 2 fs.length + 2 - 1 := by
      simp [fs, grownSize_two_eq_add]
      omega
    have hproperRight :
        (q : ℕ) < grownSize 2 (n + 3) fs.length + 2 - 1 := by
      simp [fs, grownSize_two_eq_add]
      omega
    have hpLe : (p : ℕ) ≤ 2 + fs.length := by
      simpa [grownSize_two_eq_add] using hproperLeft
    have hqLe : (q : ℕ) ≤ n + 3 + fs.length := by
      simpa [grownSize_two_eq_add] using hproperRight
    simpa [zeroExtend, hleft, hright, hproperLeft, hproperRight,
      hpLe, hqLe, fullConvImage] using happend.symm.trans haddress
  have hproperVariableFinal :
      fullConv last.kernel properVariable p q =
        generalRidgeStripeVariableSignal w T x p q := by
    have happend := zeroExtend_fullConvChain_append fs [last] variableSeed p q
    rw [← generalRidgeStripeTwistedFactors_eq_proper_append_last] at happend
    change zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors w T) variableSeed) p q =
      zeroExtend (fullConvImage last.kernel properVariable) p q at happend
    have hleft : p < n + 4 := p.isLt
    have hright : q < 2 * (n + 2) + 1 := q.isLt
    have hproperLeft :
        (p : ℕ) < grownSize 2 2 fs.length + 2 - 1 := by
      simp [fs, grownSize_two_eq_add]
      omega
    have hproperRight :
        (q : ℕ) < grownSize 2 (n + 3) fs.length + 2 - 1 := by
      simp [fs, grownSize_two_eq_add]
      omega
    have hpLe : (p : ℕ) ≤ 2 + fs.length := by
      simpa [grownSize_two_eq_add] using hproperLeft
    have hqLe : (q : ℕ) ≤ n + 3 + fs.length := by
      simpa [grownSize_two_eq_add] using hproperRight
    simpa [generalRidgeStripeVariableSignal, zeroExtend,
      hleft, hright, hproperLeft, hproperRight, hpLe, hqLe, fullConvImage]
      using happend.symm
  have hlocalFinal :
      fullConv last.kernel localCarrier p q =
        generalRidgeStripeFinalLocalAddressImage w T p q := by
    let explicitUnit : Image (n + 3) (2 * (n + 2)) :=
      constantImage (n + 3) (2 * (n + 2)) 1
    have hlocalEq : ∀ i j,
        zeroExtend localCarrier i j = zeroExtend explicitUnit i j := by
      intro i j
      have hrows : grownSize 2 2 fs.length = n + 3 := by
        simp [fs, grownSize_two_eq_add]
        omega
      have hcols : grownSize 2 (n + 3) fs.length = 2 * (n + 2) := by
        simp [fs, grownSize_two_eq_add]
        omega
      by_cases hi : i < grownSize 2 2 fs.length
      · have hi' : i < n + 3 := by simpa [hrows] using hi
        have hiRaw : i < 2 + fs.length := by
          simpa [grownSize_two_eq_add] using hi
        by_cases hj : j < grownSize 2 (n + 3) fs.length
        · have hj' : j < 2 * (n + 2) := by simpa [hcols] using hj
          have hjRaw : j < n + 3 + fs.length := by
            simpa [grownSize_two_eq_add] using hj
          simp [zeroExtend, hi', hj', hiRaw, hjRaw, localCarrier,
            explicitUnit, constantImage]
        · have hj' : ¬ j < 2 * (n + 2) := by simpa [hcols] using hj
          have hjRaw : ¬ j < n + 3 + fs.length := by
            simpa [grownSize_two_eq_add] using hj
          simp [zeroExtend, hi', hj', hiRaw, hjRaw]
      · have hi' : ¬ i < n + 3 := by simpa [hrows] using hi
        have hiRaw : ¬ i < 2 + fs.length := by
          simpa [grownSize_two_eq_add] using hi
        simp [zeroExtend, hi', hiRaw]
    rw [fullConv_eq_of_zeroExtend_eq last.kernel
      localCarrier explicitUnit p q hlocalEq]
    exact generalRidgeStripeFinalLocalAddressImage_eq_fullConv_north
      w T p hp q
  have hseedSmul :
      fullConv last.kernel (c • properSeed) p q =
        c * fullConv last.kernel properSeed p q := by
    exact stripe_fullConv_smul last.kernel c properSeed p q
  have hlocalSmul :
      fullConv last.kernel (t • localCarrier) p q =
        t * fullConv last.kernel localCarrier p q := by
    exact stripe_fullConv_smul last.kernel t localCarrier p q
  rw [hseedSmul, hlocalSmul, hproperVariableFinal,
    hproperSeedFinal, hlocalFinal]
  simp [twoCarrierPreactivation, generalRidgeStripeFinalBias]

/-- **Exact genuine arbitrary-width ridge block on a compact set.**

For every continuous family of one-row inputs, every affine functional
`x ↦ ∑ j, w j * x 0 j + theta`, and every compact parameter set, there
are positive scales `T`, `c`, and `t` such that the explicit one-channel
expansive shared-bias `2 × 2` ReLU network has depth `n+3` and computes the
requested affine ReLU exactly at its protected target.  More strongly, the
same formula identifies every coordinate in the northern two output rows:
the target is the ridge ReLU, while every other protected coordinate remains
on the linear branch of the last ReLU and equals its two-carrier
preactivation. -/
theorem exists_generalRidgeStripeNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 2))
    (hF : ContinuousFeatureOn K F)
    (w : Fin (n + 2) → ℝ) (theta : ℝ) :
    ∃ T c t : ℝ,
      1 ≤ T ∧ 0 < c ∧ 0 < t ∧
      (generalRidgeStripeNetwork w T c t theta).net.depth = n + 3 ∧
      ∀ x ∈ K, ∀ (p : Fin (n + 4))
        (q : Fin (2 * (n + 2) + 1)), (p : ℕ) ≤ 1 →
        (generalRidgeStripeNetwork w T c t theta).eval (F x) p q =
          if (p, q) = generalRidgeStripeTarget n then
            relu (∑ j, w j * F x 0 j + theta)
          else
            twoCarrierPreactivation
              (generalRidgeStripeVariableSignal w T (F x))
              (generalRidgeStripeSeedAddressImage w T)
              (generalRidgeStripeFinalLocalAddressImage w T)
              (generalRidgeStripeTarget n) theta c t p q := by
  let T := generalRidgeStripeJointScaleThreshold w
  have hT : generalRidgeStripeJointScaleThreshold w ≤ T := le_rfl
  have hTone : 1 ≤ T := generalRidgeStripeJointScaleThreshold_one_le w
  obtain ⟨C, hC, hproper⟩ :=
    exists_generalRidgeStripeProperNetwork_threshold_on_compact
      hK F hF w T hT
  let signal : X → Image (n + 4) (2 * (n + 2) + 1) :=
    fun x ↦ generalRidgeStripeVariableSignal w T (F x)
  have hsignal : ContinuousFeatureOn K signal :=
    continuousFeatureOn_generalRidgeStripeVariableSignal w T F hF
  have hgap : ∀ (p : Fin (n + 4))
      (q : Fin (2 * (n + 2) + 1)), (p : ℕ) ≤ 1 →
      (p, q) ≠ generalRidgeStripeTarget n →
      (1 ≤ generalRidgeStripeSeedAddressImage w T p q -
            generalRidgeStripeSeedAddressImage w T
              (generalRidgeStripeTarget n).1
              (generalRidgeStripeTarget n).2 ∧
          0 ≤ generalRidgeStripeFinalLocalAddressImage w T p q -
            generalRidgeStripeFinalLocalAddressImage w T
              (generalRidgeStripeTarget n).1
              (generalRidgeStripeTarget n).2) ∨
        (-generalRidgeStripeSeedBTarget w ≤
            generalRidgeStripeSeedAddressImage w T p q -
              generalRidgeStripeSeedAddressImage w T
                (generalRidgeStripeTarget n).1
                (generalRidgeStripeTarget n).2 ∧
          2 ≤ generalRidgeStripeFinalLocalAddressImage w T p q -
            generalRidgeStripeFinalLocalAddressImage w T
              (generalRidgeStripeTarget n).1
              (generalRidgeStripeTarget n).2) := by
    intro p q hp hne
    exact generalRidgeStripeTwoCarrier_gap w T
      ((le_max_right _ _).trans hT) p q hp hne
  obtain ⟨c, t, hCc, hc, ht, hselect⟩ :=
    exists_twoCarrierSelectiveActivation_on_with_seed_lower_bound
      hK signal hsignal
      (generalRidgeStripeSeedAddressImage w T)
      (generalRidgeStripeFinalLocalAddressImage w T)
      (fun p _ ↦ (p : ℕ) ≤ 1)
      (generalRidgeStripeTarget n) theta
      (generalRidgeStripeSeedBTarget w) C hgap
  refine ⟨T, c, t, hTone, hc, ht,
    generalRidgeStripeNetwork_depth w T c t theta, ?_⟩
  intro x hx p q hp
  obtain ⟨hseed, _hlinear, hproperAgree⟩ :=
    hproper c hCc t ht.le x hx
  have hseeded : seededNorthTwoState F c x =
      generalRidgeStripeVariableSeed (F x) +
        constantImage 2 (n + 3) c := by
    rfl
  rw [hseeded] at hproperAgree
  have hactual :
      (generalRidgeStripeNetwork w T c t theta).eval (F x) p q =
        sharedLayerEval
          (generalRidgeStripeTwistedLastFactor w T).kernel
          (generalRidgeStripeFinalBias w T c t theta)
          ((generalRidgeStripeProperNetwork w T c t).eval (F x)) p q := by
    have hz := zeroExtend_generalRidgeStripeNetwork_eval
      w T c t theta (F x) p q
    simpa using hz
  rw [hactual]
  have hfinalAgree := northTwoAgree_sharedLayerEval
    (generalRidgeStripeTwistedLastFactor w T).kernel
    (generalRidgeStripeFinalBias w T c t theta) hproperAgree
  have hformal :
      sharedLayerEval
          (generalRidgeStripeTwistedLastFactor w T).kernel
          (generalRidgeStripeFinalBias w T c t theta)
          ((generalRidgeStripeProperNetwork w T c t).eval (F x)) p q =
        sharedLayerEval
          (generalRidgeStripeTwistedLastFactor w T).kernel
          (generalRidgeStripeFinalBias w T c t theta)
          (generalRidgeStripeProperFormalState w T t
            (generalRidgeStripeVariableSeed (F x) +
              constantImage 2 (n + 3) c)) p q := by
    have hz := hfinalAgree p hp q
    simpa using hz
  rw [hformal]
  change relu
      (fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
          (generalRidgeStripeProperFormalState w T t
            (generalRidgeStripeVariableSeed (F x) +
              constantImage 2 (n + 3) c)) p q +
        generalRidgeStripeFinalBias w T c t theta) = _
  rw [generalRidgeStripeFormalFinal_preactivation w T c t theta
    (F x) p hp q]
  rw [hselect x hx p q hp]
  by_cases heq : (p, q) = generalRidgeStripeTarget n
  · rw [if_pos heq, if_pos heq]
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    change relu
      (generalRidgeStripeVariableSignal w T (F x)
        (generalRidgeStripeTarget n).1
        (generalRidgeStripeTarget n).2 + theta) = _
    rw [generalRidgeStripeVariableSignal_target w T]
    exact ne_of_gt (zero_lt_one.trans_le hTone)
  · rw [if_neg heq, if_neg heq]

end OneChannelCNNUniversality
