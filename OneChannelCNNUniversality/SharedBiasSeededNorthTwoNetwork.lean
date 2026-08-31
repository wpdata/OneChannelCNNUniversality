import OneChannelCNNUniversality.SharedBiasNorthTwoCarrier

/-!
# A genuine seeded network with northern-two-row linearity

This module packages the compact threshold argument used by the signed
stripe construction.  A genuine identity seed layer creates a constant
image of scale `c`.  If the constant image of value two is a unit-lower
carrier for a following heterogeneous factor list, then every sufficiently
large `c` keeps all northern-two-row preactivations of that list in ReLU's
linear branch.

The factor network is genuine and has zero shared bias at every factor
layer.  The conclusion identifies its actual northern two rows with the
formal convolution chain; no claim is made about rows farther south.
-/

namespace OneChannelCNNUniversality

open Set

/-- Identity convolution plus the constant state produced by a linear seed
layer. -/
noncomputable def seededNorthTwoState
    {X : Type*} {rows cols : ℕ} (F : X → Image rows cols)
    (c : ℝ) (x : X) : Image (rows + 2 - 1) (cols + 2 - 1) :=
  fullConvImage expansiveIdentityKernel (F x) +
    constantImage (rows + 2 - 1) (cols + 2 - 1) c

/-- A genuine seed layer followed by the zero-bias network associated with
a heterogeneous bilinear-factor list. -/
def seededZeroBiasBilinearNetwork (fs : List BilinearKernelFactor)
    {rows cols : ℕ} (c : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 (rows + 2 - 1) fs.length)
      (grownSize 2 (cols + 2 - 1) fs.length) :=
  (sharedBiasSeedLayer c).append (zeroBiasBilinearNetwork fs)

@[simp] theorem seededZeroBiasBilinearNetwork_depth
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (c : ℝ) :
    (seededZeroBiasBilinearNetwork fs (rows := rows) (cols := cols) c).net.depth =
      1 + fs.length := by
  rw [seededZeroBiasBilinearNetwork, SharedBiasNetworkTo.depth_append]
  change 1 + (zeroBiasBilinearNetwork fs).net.depth = 1 + fs.length
  have hzero : ∀ r s,
      (zeroBiasBilinearNetwork fs (rows := r) (cols := s)).net.depth =
        fs.length := by
    induction fs with
    | nil => intro r s; rfl
    | cons f fs ih =>
        intro r s
        change (zeroBiasBilinearNetwork fs
          (rows := r + 2 - 1) (cols := s + 2 - 1)).net.depth + 1 =
            fs.length + 1
        rw [ih]
  rw [hzero]

/-- A unit-lower constant carrier yields one upward-closed seed threshold
for both the genuine seed layer and all northern-two-row preactivations of
the following factor list. -/
theorem exists_seededNorthTwoNetwork_threshold_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (fs : List BilinearKernelFactor)
    (hcarrier : NorthTwoUnitLowerAlong fs
      (constantImage (rows + 2 - 1) (cols + 2 - 1) 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, C ≤ c → ∀ x ∈ K,
      (sharedBiasSeedLayer c).eval (F x) =
          seededNorthTwoState F c x ∧
        NorthTwoLinearAlong fs (seededNorthTwoState F c x) ∧
        NorthTwoAgree
          ((seededZeroBiasBilinearNetwork fs c).eval (F x))
          (fullConvChain fs (seededNorthTwoState F c x)) := by
  obtain ⟨b, hb, hseed⟩ :=
    exists_sharedBiasSeed_threshold_on_compact hK F hF
  let V : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
    fun x ↦ fullConvImage expansiveIdentityKernel (F x)
  have hV : ContinuousFeatureOn K V := by
    intro p q
    exact continuousFeatureOn_fullConv hF expansiveIdentityKernel p q
  obtain ⟨s₀, hs₀, hlinear⟩ :=
    exists_northTwoLinearAlong_add_smul_of_unitLower hK fs V hV
      (constantImage (rows + 2 - 1) (cols + 2 - 1) 2) hcarrier
  let C : ℝ := max b (2 * s₀)
  have hC : 0 < C := hb.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro c hCc x hx
  have hbc : b ≤ c := (le_max_left b (2 * s₀)).trans hCc
  have hscale : s₀ ≤ c / 2 := by
    have htwo : 2 * s₀ ≤ c := (le_max_right b (2 * s₀)).trans hCc
    linarith
  have hstate :
      seededNorthTwoState F c x =
        V x + (c / 2) •
          constantImage (rows + 2 - 1) (cols + 2 - 1) 2 := by
    funext p q
    change fullConv expansiveIdentityKernel (F x) p q + c =
      fullConv expansiveIdentityKernel (F x) p q + (c / 2) * 2
    ring
  have hlin := hlinear (c / 2) hscale x hx
  rw [← hstate] at hlin
  have hseedExact := hseed c hbc x hx
  refine ⟨hseedExact, hlin, ?_⟩
  rw [seededZeroBiasBilinearNetwork,
    SharedBiasNetworkTo.eval_append, hseedExact]
  exact zeroBiasBilinearNetwork_northTwoAgree_fullConvChain
    fs (seededNorthTwoState F c x) hlin

end OneChannelCNNUniversality
