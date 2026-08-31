import OneChannelCNNUniversality.SharedBiasCarrier
import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution
import OneChannelCNNUniversality.SharedBiasSelection

/-!
# Compact carriers for heterogeneous kernel chains

The arbitrary-width ridge factorization uses a different `2 × 2` kernel at
each depth.  This file upgrades the one-layer compact linearization theorem
to such a heterogeneous list.  On a compact input family, a genuine
one-channel shared-bias ReLU network transports the formal convolutional
signal exactly; every scalar-bias contribution is collected in one fixed
spatial carrier.

This theorem deliberately stops before the terminal ridge gate.  Its carrier
is fixed across the compact family but is not yet required to have the
north-versus-target separation needed to protect a final ReLU readout.
-/

namespace OneChannelCNNUniversality

open Set

/-- Formal heterogeneous convolution preserves coordinatewise continuity on
the compact parameter set. -/
theorem continuousFeatureOn_fullConvChain
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) :
    ContinuousFeatureOn K (fun x ↦ fullConvChain fs (V x)) := by
  induction fs generalizing rows cols V with
  | nil =>
      exact hV
  | cons f fs ih =>
      apply ih (fun x ↦ fullConvImage f.kernel (V x))
      intro p q
      exact continuousFeatureOn_fullConv hV f.kernel p q

/-- Concatenating factor lists means executing the left convolution chain
first and the right convolution chain second. -/
theorem fullConvChain_append
    (fs gs : List BilinearKernelFactor) {rows cols : ℕ}
    (x : Image rows cols) :
    HEq (fullConvChain (fs ++ gs) x)
      (fullConvChain gs (fullConvChain fs x)) := by
  induction fs generalizing rows cols with
  | nil => exact HEq.rfl
  | cons f fs ih =>
      change HEq
        (fullConvChain (fs ++ gs) (fullConvImage f.kernel x))
        (fullConvChain gs (fullConvChain fs (fullConvImage f.kernel x)))
      exact ih (fullConvImage f.kernel x)

/-- Coordinatewise zero extension removes the dependent output-size cast in
the append law. -/
theorem zeroExtend_fullConvChain_append
    (fs gs : List BilinearKernelFactor) {rows cols : ℕ}
    (x : Image rows cols) (p q : ℕ) :
    zeroExtend (fullConvChain (fs ++ gs) x) p q =
      zeroExtend (fullConvChain gs (fullConvChain fs x)) p q := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change zeroExtend
          (fullConvChain (fs ++ gs) (fullConvImage f.kernel x)) p q =
        zeroExtend
          (fullConvChain gs
            (fullConvChain fs (fullConvImage f.kernel x))) p q
      exact ih (fullConvImage f.kernel x)

/-- Protected-coordinate form of compact selection from a unit-gap address.
Only the designated coordinates must have an address gap; no claim is made
about the remaining expansive fringe. -/
theorem exists_sharedBias_select_from_unit_address_on
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal) (address : Image rows cols)
    (protect : Fin rows → Fin cols → Prop)
    (target : Fin rows × Fin cols) (theta : ℝ)
    (haddress : ∀ p q, protect p q → (p, q) ≠ target →
      1 ≤ address p q - address target.1 target.2) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ x ∈ K, ∀ p q, protect p q →
      relu
          (signal x p q + scale * address p q +
            (theta - scale * address target.1 target.2)) =
        if (p, q) = target then relu (signal x p q + theta)
        else
          signal x p q + scale * address p q +
            (theta - scale * address target.1 target.2) := by
  obtain ⟨scale, hscale, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  refine ⟨scale, hscale, ?_⟩
  intro x hx
  apply sharedBiasSelectiveActivation_on
      (signal x) (fun p q ↦ scale * address p q)
      protect target theta scale
  · intro p q hpq hne
    have hunit := haddress p q hpq hne
    have hscaled := mul_le_mul_of_nonneg_left hunit hscale.le
    linarith
  · intro p q _hpq
    exact hbound x hx p q

/-- Once a compact family is linearized by a positive scalar bias, every
additional nonnegative scalar `t` remains in ReLU's linear branch and appears
as the constant output image `t`.  This exposes a tunable carrier direction
for the later separating layer. -/
theorem exists_shared_bias_carrier_layer_with_boost
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) (w : Kernel kRows kCols) :
    ∃ (b : ℝ)
      (carrier : Image (rows + kRows - 1) (cols + kCols - 1)),
      0 < b ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
          sharedLayerEval w (b + t) (F x) =
            fullConvImage w (V x) + carrier +
              constantImage (rows + kRows - 1) (cols + kCols - 1) t := by
  have hF : ContinuousFeatureOn K F := by
    intro i j
    apply ((hV i j).add continuousOn_const).congr
    intro x hx
    have h := congrFun (congrFun (hdecomp x hx) i) j
    simpa using h
  obtain ⟨b, hb, hlinear⟩ := exists_shared_bias_linearization hK F hF w
  let carrier : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ fullConv w known p q + b
  refine ⟨b, carrier, hb, ?_⟩
  intro t ht x hx
  funext p q
  have hbase : 0 ≤ fullConv w (F x) p q + b := by
    calc
      0 ≤ sharedLayerEval w b (F x) p q := by
        change 0 ≤ max _ 0
        exact le_max_right _ _
      _ = fullConv w (F x) p q + b := hlinear x hx p q
  change relu (fullConv w (F x) p q + (b + t)) =
    fullConv w (V x) p q + carrier p q + t
  rw [relu_of_nonneg]
  · rw [hdecomp x hx, fullConv_add]
    simp only [carrier]
    ring
  · linarith

/-- Every finite heterogeneous bilinear-kernel chain has an exact genuine
shared-bias realization on a compact signal family, up to one fixed spatial
carrier independent of the input parameter. -/
theorem exists_shared_bias_bilinear_carrier
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 rows fs.length) (grownSize 2 cols fs.length))
      (carrier : Image (grownSize 2 rows fs.length)
        (grownSize 2 cols fs.length)),
      net.net.depth = fs.length ∧
        ∀ x ∈ K,
          net.eval (F x) = fullConvChain fs (V x) + carrier := by
  induction fs generalizing rows cols F V known with
  | nil =>
      exact ⟨SharedBiasNetworkTo.nil rows cols 2 2, known, rfl, hdecomp⟩
  | cons f fs ih =>
      obtain ⟨b, nextCarrier, _hb, hfirst⟩ :=
        exists_shared_bias_carrier_layer hK F V known hdecomp hV f.kernel
      let nextF : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ sharedLayerEval f.kernel b (F x)
      let nextV : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ fullConvImage f.kernel (V x)
      have hnextDecomp :
          ∀ x ∈ K, nextF x = nextV x + nextCarrier := by
        intro x hx
        simpa [nextF, nextV] using hfirst x hx
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV f.kernel p q
      obtain ⟨tail, finalCarrier, htailDepth, htail⟩ :=
        ih nextF nextV nextCarrier hnextDecomp hnextV
      refine ⟨SharedBiasNetworkTo.cons f.kernel b tail, finalCarrier, ?_, ?_⟩
      · change tail.net.depth + 1 = fs.length + 1
        rw [htailDepth]
      intro x hx
      rw [SharedBiasNetworkTo.eval_cons]
      exact htail x hx

/-- A heterogeneous prefix followed by one selected terminal kernel admits a
tunable last prefix bias.  Increasing that bias by `t ≥ 0` adds exactly the
constant image `t` after the selected kernel, without changing the formal
convolutional signal. -/
theorem exists_shared_bias_bilinear_prefix_with_terminal_boost
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (init : List BilinearKernelFactor) (last : BilinearKernelFactor)
    {rows cols : ℕ} (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : ℝ → SharedBiasNetworkTo 2 2 rows cols
          (grownSize 2 rows init.length + 2 - 1)
          (grownSize 2 cols init.length + 2 - 1))
      (b : ℝ)
      (carrier : Image (grownSize 2 rows init.length + 2 - 1)
        (grownSize 2 cols init.length + 2 - 1)),
      0 < b ∧
        (∀ t : ℝ, (net t).net.depth = init.length + 1) ∧
          ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
            (net t).eval (F x) =
              fullConvImage last.kernel (fullConvChain init (V x)) +
                carrier +
                  constantImage (grownSize 2 rows init.length + 2 - 1)
                    (grownSize 2 cols init.length + 2 - 1) t := by
  obtain ⟨head, prefixCarrier, hheadDepth, hhead⟩ :=
    exists_shared_bias_bilinear_carrier hK init F V known hdecomp hV
  let nextF : X → Image (grownSize 2 rows init.length)
      (grownSize 2 cols init.length) :=
    fun x ↦ head.eval (F x)
  let nextV : X → Image (grownSize 2 rows init.length)
      (grownSize 2 cols init.length) :=
    fun x ↦ fullConvChain init (V x)
  have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + prefixCarrier := by
    intro x hx
    simpa [nextF, nextV] using hhead x hx
  have hnextV : ContinuousFeatureOn K nextV := by
    exact continuousFeatureOn_fullConvChain init V hV
  obtain ⟨b, carrier, hb, hboost⟩ :=
    exists_shared_bias_carrier_layer_with_boost hK nextF nextV
      prefixCarrier hnextDecomp hnextV last.kernel
  let net : ℝ → SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 rows init.length + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1) :=
    fun t ↦ head.append (SharedBiasNetworkTo.single last.kernel (b + t))
  refine ⟨net, b, carrier, hb, ?_, ?_⟩
  · intro t
    change (head.append
      (SharedBiasNetworkTo.single last.kernel (b + t))).net.depth = _
    rw [SharedBiasNetworkTo.depth_append, hheadDepth]
    rfl
  intro t ht x hx
  change (head.append
      (SharedBiasNetworkTo.single last.kernel (b + t))).eval (F x) = _
  rw [SharedBiasNetworkTo.eval_append, SharedBiasNetworkTo.eval_single]
  exact hboost t ht x hx

end OneChannelCNNUniversality
