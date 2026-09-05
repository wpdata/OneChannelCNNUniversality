import OneChannelCNNUniversality.SharedBiasCarrierDepthOptimality
import OneChannelCNNUniversality.SharedBiasTwoStageRecovery

/-!
# Non-destructive generation of a nonuniform boundary carrier

The pure depth-two carrier initializer erases its input.  On a compact input
family this file gives a lossless alternative.  A first delta-kernel layer is
uniformly linearized by a positive shared bias.  A second horizontal
first-difference layer is uniformly linearized by another positive shared
bias.  Its output is the sum of an injective transform of the input and a
fixed, spatially nonuniform boundary carrier.
-/

namespace OneChannelCNNUniversality

/-- A nonzero constant seed makes the horizontal shared carrier spatially
nonuniform: its left boundary differs from its first interior column. -/
theorem horizontalSharedCarrier_nonuniform
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 1 < cols)
    {c b : ℝ} (hc : c ≠ 0) :
    SpatiallyNonuniform (horizontalSharedCarrier rows cols c b) := by
  let i : Fin rows := ⟨0, hrows⟩
  let j : Fin cols := ⟨1, hcols⟩
  refine ⟨⟨i, by omega⟩, ⟨0, by omega⟩,
    ⟨i, by omega⟩, ⟨j, by omega⟩, ?_⟩
  rw [horizontalSharedCarrier_left c b i (by omega),
    horizontalSharedCarrier_interior c b i j (by norm_num [j])]
  intro heq
  apply hc
  linarith

/-- The variable part transported by the two layers: northwest-delta
embedding followed by horizontal first differencing. -/
def nondestructiveBoundaryTransform {rows cols : ℕ} (x : Image rows cols) :
    Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
  fullConvImage horizontalBoundaryKernel
    (fullConvImage expansiveIdentityKernel x)

/-- The transported variable signal retains all input information. -/
theorem nondestructiveBoundaryTransform_injective {rows cols : ℕ} :
    Function.Injective
      (nondestructiveBoundaryTransform : Image rows cols →
        Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1)) := by
  exact horizontalBoundaryTransform_injective.comp
    fullConvImage_expansiveIdentityKernel_injective

/-- On every compact input family of positive width, two genuine expansive
`2 × 2` one-channel shared-bias ReLU layers generate a fixed nonuniform
boundary carrier without losing the input.  The theorem returns the exact
signal/carrier decomposition, exact depth, and injectivity of the actual
network evaluation on the compact domain. -/
theorem exists_depthTwo_nondestructive_nonuniform_carrier_on_compact
    {rows cols : ℕ} (K : Set (Image rows cols))
    (hK : IsCompact K) (hcols : 0 < cols) :
    ∃ (net : SharedBiasNetworkTo 2 2 rows cols
          ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1))
      (c b : ℝ)
      (carrier : Image ((rows + 2 - 1) + 2 - 1)
        ((cols + 2 - 1) + 2 - 1)),
      0 < c ∧ 0 < b ∧ net.net.depth = 2 ∧
        carrier = horizontalSharedCarrier
          (rows + 2 - 1) (cols + 2 - 1) c b ∧
        SpatiallyNonuniform carrier ∧
        (∀ x ∈ K,
          net.eval x = nondestructiveBoundaryTransform x + carrier) ∧
        Set.InjOn (fun x ↦ net.eval x) K := by
  obtain ⟨c, hc, hfirstPointwise⟩ :=
    exists_shared_bias_linearization hK (fun x ↦ x)
      (continuousFeatureOn_identity K) expansiveIdentityKernel
  have hfirst : ∀ x ∈ K,
      sharedLayerEval expansiveIdentityKernel c x =
        fullConvImage expansiveIdentityKernel x +
          constantImage (rows + 2 - 1) (cols + 2 - 1) c := by
    intro x hx
    funext p q
    change sharedLayerEval expansiveIdentityKernel c x p q =
      fullConv expansiveIdentityKernel x p q + c
    exact hfirstPointwise x hx p q
  let variablePart : Image rows cols →
      Image (rows + 2 - 1) (cols + 2 - 1) :=
    fun x ↦ fullConvImage expansiveIdentityKernel x
  have hvariablePart : ContinuousFeatureOn K variablePart := by
    intro p q
    exact continuousFeatureOn_fullConv (continuousFeatureOn_identity K)
      expansiveIdentityKernel p q
  obtain ⟨b, hb, hsecond⟩ :=
    exists_horizontal_shared_carrier_layer hK variablePart hvariablePart c
  let carrier : Image ((rows + 2 - 1) + 2 - 1)
      ((cols + 2 - 1) + 2 - 1) :=
    horizontalSharedCarrier (rows + 2 - 1) (cols + 2 - 1) c b
  let net : SharedBiasNetworkTo 2 2 rows cols
      ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
    SharedBiasNetworkTo.cons expansiveIdentityKernel c
      (SharedBiasNetworkTo.single horizontalBoundaryKernel b)
  have heval : ∀ x ∈ K,
      net.eval x = nondestructiveBoundaryTransform x + carrier := by
    intro x hx
    change sharedLayerEval horizontalBoundaryKernel b
      (sharedLayerEval expansiveIdentityKernel c x) = _
    rw [hfirst x hx]
    simpa [variablePart, carrier, nondestructiveBoundaryTransform] using
      hsecond x hx
  have hcarrier : SpatiallyNonuniform carrier := by
    exact horizontalSharedCarrier_nonuniform (by omega) (by omega) hc.ne'
  refine ⟨net, c, b, carrier, hc, hb, rfl, rfl, hcarrier, heval, ?_⟩
  intro x hx y hy hxy
  change net.eval x = net.eval y at hxy
  rw [heval x hx, heval y hy] at hxy
  apply nondestructiveBoundaryTransform_injective
  exact add_right_cancel hxy

end OneChannelCNNUniversality
