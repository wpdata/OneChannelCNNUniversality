import OneChannelCNNUniversality.SharedBiasFrontierRoute

/-!
# Order-sensitive affine frontier routes

Pure horizontal and vertical full convolutions commute.  Direction-dependent
nonnegative shared scalar biases add affine carriers that do not commute with
the opposite convolution.  This module compiles such biased routes to genuine
one-channel shared-ReLU CNNs, proves exact evaluation and injectivity on the
nonnegative cone, and exhibits a machine-checked `east; south` versus
`south; east` output gap.
-/

namespace OneChannelCNNUniversality

universe u

namespace FrontierDirection

/-- Select the shared scalar bias associated with one direction. -/
def bias : FrontierDirection → ℝ → ℝ → ℝ
  | .east, eastBias, _ => eastBias
  | .south, _, southBias => southBias

theorem bias_nonnegative (direction : FrontierDirection)
    {eastBias southBias : ℝ} (heast : 0 ≤ eastBias)
    (hsouth : 0 ≤ southBias) :
    0 ≤ direction.bias eastBias southBias := by
  cases direction with
  | east => exact heast
  | south => exact hsouth

end FrontierDirection

/-- A nonnegative convolution followed by a nonnegative shared bias is an
exact affine map because ReLU stays in its linear branch. -/
theorem sharedLayerEval_of_nonnegative_bias
    {kRows kCols rows cols : ℕ} {w : Kernel kRows kCols}
    {x : Image rows cols} {bias : ℝ}
    (hw : KernelNonnegative w) (hx : ImageNonnegative x)
    (hbias : 0 ≤ bias) :
    sharedLayerEval w bias x =
      fullConvImage w x +
        constantImage (rows + kRows - 1) (cols + kCols - 1) bias := by
  funext p q
  change relu (fullConv w x p q + bias) = fullConv w x p q + bias
  exact relu_of_nonneg
    (add_nonneg (fullConv_nonnegative hw hx p q) hbias)

/-- Linear convolution plus the direction's shared affine carrier. -/
def affineFrontierStep {rows cols : ℕ}
    (direction : FrontierDirection) (bias : ℝ) (x : Image rows cols) :
    Image (rows + 2 - 1) (cols + 2 - 1) :=
  fullConvImage direction.kernel x +
    constantImage (rows + 2 - 1) (cols + 2 - 1) bias

theorem zeroExtend_affineFrontierStep_of_lt
    {rows cols : ℕ} (direction : FrontierDirection) (bias : ℝ)
    (x : Image rows cols) (p q : ℕ)
    (hp : p < rows + 2 - 1) (hq : q < cols + 2 - 1) :
    zeroExtend (affineFrontierStep direction bias x) p q =
      fullConv direction.kernel x p q + bias := by
  rw [affineFrontierStep, zeroExtend_add, zeroExtend_fullConvImage,
    zeroExtend_of_lt _ hp hq]
  rfl

/-- A nonnegative affine frontier step remains nonnegative. -/
theorem affineFrontierStep_nonnegative
    {rows cols : ℕ} (direction : FrontierDirection) (bias : ℝ)
    {x : Image rows cols} (hx : ImageNonnegative x) (hbias : 0 ≤ bias) :
    ImageNonnegative (affineFrontierStep direction bias x) := by
  intro p q
  exact add_nonneg
    (fullConv_nonnegative direction.kernel_nonnegative hx p q) hbias

/-- Adding a common shared carrier after an injective direction kernel does
not lose information. -/
theorem affineFrontierStep_injective
    {rows cols : ℕ} (direction : FrontierDirection) (bias : ℝ) :
    Function.Injective
      (fun x : Image rows cols ↦ affineFrontierStep direction bias x) := by
  intro x y hxy
  apply direction.fullConvImage_kernel_injective
  funext p q
  have hentry := congrFun (congrFun hxy p) q
  change fullConv direction.kernel x p q + bias =
    fullConv direction.kernel y p q + bias at hentry
  exact add_right_cancel hentry

/-- Execute a direction list with fixed direction-dependent shared biases. -/
def applyBiasedFrontierRoute :
    (route : List FrontierDirection) → (eastBias southBias : ℝ) →
      {rows cols : ℕ} → Image rows cols →
        Image (grownSize 2 rows route.length) (grownSize 2 cols route.length)
  | [], _, _, _, _, x => x
  | direction :: route, eastBias, southBias, _, _, x =>
      applyBiasedFrontierRoute route eastBias southBias
        (affineFrontierStep direction
          (direction.bias eastBias southBias) x)

/-- Compile a biased direction list to a genuine shared-ReLU network. -/
def biasedFrontierRouteNetwork :
    (route : List FrontierDirection) → (eastBias southBias : ℝ) →
      {rows cols : ℕ} →
        SharedBiasNetworkTo 2 2 rows cols
          (grownSize 2 rows route.length) (grownSize 2 cols route.length)
  | [], _, _, _, _ => SharedBiasNetworkTo.nil _ _ 2 2
  | direction :: route, eastBias, southBias, _, _ =>
      SharedBiasNetworkTo.cons direction.kernel
        (direction.bias eastBias southBias)
        (biasedFrontierRouteNetwork route eastBias southBias)

/-- The affine route program is injective for every finite direction list
and every pair of shared biases. -/
theorem applyBiasedFrontierRoute_injective
    (route : List FrontierDirection) (eastBias southBias : ℝ)
    {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦
        applyBiasedFrontierRoute route eastBias southBias x) := by
  induction route generalizing rows cols with
  | nil =>
      intro x y hxy
      exact hxy
  | cons direction route ih =>
      intro x y hxy
      apply affineFrontierStep_injective direction
        (direction.bias eastBias southBias)
      exact ih hxy

/-- One network layer is generated for every direction. -/
theorem biasedFrontierRouteNetwork_depth
    (route : List FrontierDirection) (eastBias southBias : ℝ)
    {rows cols : ℕ} :
    (biasedFrontierRouteNetwork (rows := rows) (cols := cols)
      route eastBias southBias).net.depth = route.length := by
  induction route generalizing rows cols with
  | nil => rfl
  | cons direction route ih =>
      change
        (biasedFrontierRouteNetwork
          (rows := rows + 2 - 1) (cols := cols + 2 - 1)
          route eastBias southBias).net.depth + 1 = route.length + 1
      rw [ih]

/-- On nonnegative input with nonnegative direction biases, the genuine ReLU
network is exactly the affine route program. -/
theorem biasedFrontierRouteNetwork_eval_of_nonnegative
    (route : List FrontierDirection) (eastBias southBias : ℝ)
    {rows cols : ℕ} (x : Image rows cols) (hx : ImageNonnegative x)
    (heast : 0 ≤ eastBias) (hsouth : 0 ≤ southBias) :
    (biasedFrontierRouteNetwork route eastBias southBias).eval x =
      applyBiasedFrontierRoute route eastBias southBias x := by
  induction route generalizing rows cols with
  | nil => exact SharedBiasNetworkTo.eval_nil x
  | cons direction route ih =>
      have hbias := direction.bias_nonnegative heast hsouth
      rw [biasedFrontierRouteNetwork, SharedBiasNetworkTo.eval_cons,
        applyBiasedFrontierRoute,
        sharedLayerEval_of_nonnegative_bias
          direction.kernel_nonnegative hx hbias]
      exact ih
        (affineFrontierStep direction
          (direction.bias eastBias southBias) x)
        (affineFrontierStep_nonnegative direction
          (direction.bias eastBias southBias) hx hbias)

/-- A nonnegative injective input family remains injectively represented by
every biased route network. -/
theorem biasedFrontierRouteNetwork_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (route : List FrontierDirection) (eastBias southBias : ℝ)
    (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (heast : 0 ≤ eastBias) (hsouth : 0 ≤ southBias)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦
        (biasedFrontierRouteNetwork route eastBias southBias).eval (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  apply applyBiasedFrontierRoute_injective route eastBias southBias
  change
    applyBiasedFrontierRoute route eastBias southBias (F x) =
      applyBiasedFrontierRoute route eastBias southBias (F y)
  rw [← biasedFrontierRouteNetwork_eval_of_nonnegative
      route eastBias southBias (F x) (hFnonnegative x hx) heast hsouth,
    ← biasedFrontierRouteNetwork_eval_of_nonnegative
      route eastBias southBias (F y) (hFnonnegative y hy) heast hsouth]
  exact heval

/-- Common linear contribution to the order-sensitive two-step calculation. -/
def eastSouthLinearCore {rows cols : ℕ} (x : Image rows cols) : ℝ :=
  fullConv verticalAccumulationKernel
    (fullConvImage horizontalAccumulationKernel x) 1 1

/-- Exact affine value after an east step followed by a south step. -/
theorem eastSouthBiasedRoute_one_one
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (x : Image rows cols) (eastBias southBias : ℝ) :
    zeroExtend
        (applyBiasedFrontierRoute [.east, .south]
          eastBias southBias x) 1 1 =
      eastSouthLinearCore x + 2 * eastBias + southBias := by
  have houter := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.south southBias
    (affineFrontierStep .east eastBias x) 1 1 (by omega) (by omega)
  have hinner11 := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.east eastBias x 1 1 (by omega) (by omega)
  have hinner01 := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.east eastBias x 0 1 (by omega) (by omega)
  simp only [FrontierDirection.kernel] at houter hinner11 hinner01
  change zeroExtend
      (affineFrontierStep .south southBias
        (affineFrontierStep .east eastBias x)) 1 1 = _
  rw [houter, fullConv_verticalAccumulationKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (1 : ℕ)), Nat.reduceSubDiff]
  rw [hinner11, hinner01]
  unfold eastSouthLinearCore
  rw [fullConv_verticalAccumulationKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (1 : ℕ)), Nat.reduceSubDiff,
    zeroExtend_fullConvImage]
  ring

/-- Exact affine value after a south step followed by an east step. -/
theorem southEastBiasedRoute_one_one
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (x : Image rows cols) (eastBias southBias : ℝ) :
    zeroExtend
        (applyBiasedFrontierRoute [.south, .east]
          eastBias southBias x) 1 1 =
      eastSouthLinearCore x + eastBias + 2 * southBias := by
  have houter := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.east eastBias
    (affineFrontierStep .south southBias x) 1 1 (by omega) (by omega)
  have hinner11 := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.south southBias x 1 1 (by omega) (by omega)
  have hinner10 := zeroExtend_affineFrontierStep_of_lt
    FrontierDirection.south southBias x 1 0 (by omega) (by omega)
  simp only [FrontierDirection.kernel] at houter hinner11 hinner10
  have hlinear :
      fullConv horizontalAccumulationKernel
          (fullConvImage verticalAccumulationKernel x) 1 1 =
        eastSouthLinearCore x := by
    calc
      fullConv horizontalAccumulationKernel
          (fullConvImage verticalAccumulationKernel x) 1 1 =
          zeroExtend
            (fullConvImage horizontalAccumulationKernel
              (fullConvImage verticalAccumulationKernel x)) 1 1 := by
            rw [zeroExtend_fullConvImage]
      _ = zeroExtend
            (fullConvImage verticalAccumulationKernel
              (fullConvImage horizontalAccumulationKernel x)) 1 1 := by
            rw [fullConvImage_horizontal_vertical_commute]
      _ = eastSouthLinearCore x := by
            simp only [zeroExtend_fullConvImage, eastSouthLinearCore]
  have hlinearExpanded :
      fullConv verticalAccumulationKernel x 1 1 +
          fullConv verticalAccumulationKernel x 1 0 =
        eastSouthLinearCore x := by
    rw [← hlinear, fullConv_horizontalAccumulationKernel_nat]
    simp only [if_pos (by omega : 1 ≤ (1 : ℕ)), Nat.reduceSubDiff,
      zeroExtend_fullConvImage]
  change zeroExtend
      (affineFrontierStep .east eastBias
        (affineFrontierStep .south southBias x)) 1 1 = _
  rw [houter, fullConv_horizontalAccumulationKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (1 : ℕ)), Nat.reduceSubDiff]
  rw [hinner11, hinner10]
  linear_combination hlinearExpanded

/-- Swapping the two directions changes coordinate `(1,1)` by exactly the
difference of their shared biases. -/
theorem eastSouth_sub_southEast
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (x : Image rows cols) (eastBias southBias : ℝ) :
    zeroExtend
          (applyBiasedFrontierRoute [.east, .south]
            eastBias southBias x) 1 1 -
        zeroExtend
          (applyBiasedFrontierRoute [.south, .east]
            eastBias southBias x) 1 1 =
      eastBias - southBias := by
  rw [eastSouthBiasedRoute_one_one hrows hcols,
    southEastBiasedRoute_one_one hrows hcols]
  ring

/-- With distinct nonnegative direction biases, the two genuine shared-ReLU
CNNs for `east; south` and `south; east` are different on every nonnegative
input of positive rectangular size. -/
theorem biasedFrontierRouteNetwork_order_sensitive
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (x : Image rows cols) (hx : ImageNonnegative x)
    {eastBias southBias : ℝ} (heast : 0 ≤ eastBias)
    (hsouth : 0 ≤ southBias) (hne : eastBias ≠ southBias) :
    (biasedFrontierRouteNetwork [.east, .south]
        eastBias southBias).eval x ≠
      (biasedFrontierRouteNetwork [.south, .east]
        eastBias southBias).eval x := by
  intro heq
  have hcoordinate := congrArg (fun z ↦ zeroExtend z 1 1) heq
  have hgap := eastSouth_sub_southEast
    hrows hcols x eastBias southBias
  rw [← biasedFrontierRouteNetwork_eval_of_nonnegative
      [.east, .south] eastBias southBias x hx heast hsouth,
    ← biasedFrontierRouteNetwork_eval_of_nonnegative
      [.south, .east] eastBias southBias x hx heast hsouth]
    at hgap
  rw [hcoordinate, sub_self] at hgap
  exact hne (sub_eq_zero.mp hgap.symm)

end OneChannelCNNUniversality
