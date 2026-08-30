import OneChannelCNNUniversality.SharedBiasFrontierTurn

/-!
# Arbitrary finite east/south frontier routes

Every direction in a finite route is compiled to one genuine zero-bias
shared-ReLU convolutional layer.  Horizontal and vertical Pascal
accumulation commute as zero-extended full convolutions, so an arbitrarily
interleaved route has the same final linear state as the canonical route with
all eastern steps followed by all southern steps.  This turns the preceding
single-turn certificate into a repeated-turn certificate while retaining
exact depth and injectivity.
-/

namespace OneChannelCNNUniversality

universe u

/-- One monotone direction of a southeast-moving computation frontier. -/
inductive FrontierDirection where
  | east
  | south
  deriving DecidableEq, Repr

namespace FrontierDirection

/-- The genuine `2 × 2` Pascal kernel used by one route step. -/
def kernel : FrontierDirection → Kernel 2 2
  | .east => horizontalAccumulationKernel
  | .south => verticalAccumulationKernel

theorem kernel_nonnegative (direction : FrontierDirection) :
    KernelNonnegative direction.kernel := by
  cases direction with
  | east => exact horizontalAccumulationKernel_nonnegative
  | south => exact verticalAccumulationKernel_nonnegative

/-- Each allowed route step is injective before ReLU. -/
theorem fullConvImage_kernel_injective (direction : FrontierDirection)
    {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage direction.kernel x) := by
  cases direction with
  | east => exact horizontalAccumulationTransform_injective
  | south => exact verticalAccumulationTransform_injective

end FrontierDirection

/-- Number of eastern steps in a finite route. -/
def eastStepCount : List FrontierDirection → ℕ
  | [] => 0
  | .east :: route => eastStepCount route + 1
  | .south :: route => eastStepCount route

/-- Number of southern steps in a finite route. -/
def southStepCount : List FrontierDirection → ℕ
  | [] => 0
  | .east :: route => southStepCount route
  | .south :: route => southStepCount route + 1

theorem eastStepCount_add_southStepCount (route : List FrontierDirection) :
    eastStepCount route + southStepCount route = route.length := by
  induction route with
  | nil => rfl
  | cons direction route ih =>
      cases direction <;>
        simp only [eastStepCount, southStepCount, List.length_cons] <;> omega

/-- Execute a route as a finite sequence of linear full convolutions. -/
def applyFrontierRoute :
    (route : List FrontierDirection) → {rows cols : ℕ} → Image rows cols →
      Image (grownSize 2 rows route.length) (grownSize 2 cols route.length)
  | [], _, _, x => x
  | direction :: route, _, _, x =>
      applyFrontierRoute route (fullConvImage direction.kernel x)

/-- Compile every direction to one genuine zero-bias shared-ReLU layer. -/
def frontierRouteNetwork :
    (route : List FrontierDirection) → {rows cols : ℕ} →
      SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 rows route.length) (grownSize 2 cols route.length)
  | [], _, _ => SharedBiasNetworkTo.nil _ _ 2 2
  | direction :: route, _, _ =>
      SharedBiasNetworkTo.cons direction.kernel 0
        (frontierRouteNetwork route)

/-- Two finite images with possibly different declared rectangles represent
the same zero-extended array. -/
def ZeroExtensionEq {rows₁ cols₁ rows₂ cols₂ : ℕ}
    (x : Image rows₁ cols₁) (y : Image rows₂ cols₂) : Prop :=
  ∀ p q, zeroExtend x p q = zeroExtend y p q

theorem ZeroExtensionEq.refl {rows cols : ℕ} (x : Image rows cols) :
    ZeroExtensionEq x x := by
  intro p q
  rfl

theorem ZeroExtensionEq.trans
    {rows₁ cols₁ rows₂ cols₂ rows₃ cols₃ : ℕ}
    {x : Image rows₁ cols₁} {y : Image rows₂ cols₂}
    {z : Image rows₃ cols₃}
    (hxy : ZeroExtensionEq x y) (hyz : ZeroExtensionEq y z) :
    ZeroExtensionEq x z := by
  intro p q
  exact (hxy p q).trans (hyz p q)

theorem ZeroExtensionEq.fullConvImage
    {kRows kCols rows₁ cols₁ rows₂ cols₂ : ℕ}
    (w : Kernel kRows kCols) {x : Image rows₁ cols₁}
    {y : Image rows₂ cols₂} (hxy : ZeroExtensionEq x y) :
    ZeroExtensionEq (fullConvImage w x) (fullConvImage w y) := by
  intro p q
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage]
  unfold fullConv
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hab : (a : ℕ) ≤ p ∧ (b : ℕ) ≤ q
  · simp only [if_pos hab]
    rw [hxy]
  · simp [hab]

theorem ZeroExtensionEq.iterateFullConv
    {kRows kCols rows₁ cols₁ rows₂ cols₂ : ℕ}
    (w : Kernel kRows kCols) (steps : ℕ)
    {x : Image rows₁ cols₁} {y : Image rows₂ cols₂}
    (hxy : ZeroExtensionEq x y) :
    ZeroExtensionEq (iterateFullConv w steps x)
      (iterateFullConv w steps y) := by
  induction steps generalizing rows₁ cols₁ rows₂ cols₂ with
  | zero => exact hxy
  | succ steps ih =>
      exact ih (ZeroExtensionEq.fullConvImage w hxy)

/-- One horizontal and one vertical Pascal convolution commute exactly. -/
theorem fullConvImage_horizontal_vertical_commute
    {rows cols : ℕ} (x : Image rows cols) :
    fullConvImage horizontalAccumulationKernel
        (fullConvImage verticalAccumulationKernel x) =
      fullConvImage verticalAccumulationKernel
        (fullConvImage horizontalAccumulationKernel x) := by
  funext p q
  change
    fullConv horizontalAccumulationKernel
        (fullConvImage verticalAccumulationKernel x) p q =
      fullConv verticalAccumulationKernel
        (fullConvImage horizontalAccumulationKernel x) p q
  rw [fullConv_horizontalAccumulationKernel_nat,
    fullConv_verticalAccumulationKernel_nat]
  simp only [zeroExtend_fullConvImage]
  by_cases hp : 1 ≤ (p : ℕ)
  · by_cases hq : 1 ≤ (q : ℕ)
    · simp [fullConv_horizontalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat, hp, hq]
      ring
    · simp [fullConv_horizontalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat, hp, hq]
  · by_cases hq : 1 ≤ (q : ℕ)
    · simp [fullConv_horizontalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat, hp, hq]
    · simp [fullConv_horizontalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat, hp, hq]

/-- Any horizontal block commutes past one vertical step as a zero-extended
array. -/
theorem iterateHorizontal_fullConvVertical_commute
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols) :
    ZeroExtensionEq
      (iterateFullConv horizontalAccumulationKernel steps
        (fullConvImage verticalAccumulationKernel x))
      (fullConvImage verticalAccumulationKernel
        (iterateFullConv horizontalAccumulationKernel steps x)) := by
  induction steps generalizing rows cols with
  | zero => exact ZeroExtensionEq.refl _
  | succ steps ih =>
      apply ZeroExtensionEq.trans
        (ZeroExtensionEq.iterateFullConv horizontalAccumulationKernel steps
          (by
            intro p q
            rw [fullConvImage_horizontal_vertical_commute x]))
      exact ih (fullConvImage horizontalAccumulationKernel x)

/-- An arbitrary interleaving of east and south steps equals the canonical
Pascal grid transform with the same directional step counts, after zero
extension. -/
theorem applyFrontierRoute_eq_pascalGrid
    (route : List FrontierDirection) {rows cols : ℕ} (x : Image rows cols) :
    ZeroExtensionEq (applyFrontierRoute route x)
      (iterateFullConv verticalAccumulationKernel (southStepCount route)
        (iterateFullConv horizontalAccumulationKernel (eastStepCount route) x)) := by
  induction route generalizing rows cols with
  | nil => exact ZeroExtensionEq.refl x
  | cons direction route ih =>
      cases direction with
      | east =>
          exact ih (fullConvImage horizontalAccumulationKernel x)
      | south =>
          apply ZeroExtensionEq.trans
            (ih (fullConvImage verticalAccumulationKernel x))
          exact ZeroExtensionEq.iterateFullConv verticalAccumulationKernel
            (southStepCount route)
            (iterateHorizontal_fullConvVertical_commute
              (eastStepCount route) x)

/-- The linear route program loses no information for any direction list. -/
theorem applyFrontierRoute_injective
    (route : List FrontierDirection) {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ applyFrontierRoute route x) := by
  induction route generalizing rows cols with
  | nil =>
      intro x y hxy
      exact hxy
  | cons direction route ih =>
      intro x y hxy
      apply direction.fullConvImage_kernel_injective
      exact ih hxy

/-- A route has exactly one genuine convolution/ReLU layer per direction. -/
theorem frontierRouteNetwork_depth
    (route : List FrontierDirection) {rows cols : ℕ} :
    (frontierRouteNetwork (rows := rows) (cols := cols) route).net.depth =
      route.length := by
  induction route generalizing rows cols with
  | nil => rfl
  | cons direction route ih =>
      change
        (frontierRouteNetwork
          (rows := rows + 2 - 1) (cols := cols + 2 - 1)
          route).net.depth + 1 = route.length + 1
      rw [ih]

/-- On nonnegative input, the compiled route network evaluates exactly to
the corresponding linear route program. -/
theorem frontierRouteNetwork_eval_of_nonnegative
    (route : List FrontierDirection) {rows cols : ℕ} (x : Image rows cols)
    (hx : ImageNonnegative x) :
    (frontierRouteNetwork route).eval x = applyFrontierRoute route x := by
  induction route generalizing rows cols with
  | nil => exact SharedBiasNetworkTo.eval_nil x
  | cons direction route ih =>
      rw [frontierRouteNetwork, SharedBiasNetworkTo.eval_cons,
        applyFrontierRoute,
        sharedLayerEval_zero_of_nonnegative direction.kernel_nonnegative hx]
      exact ih (fullConvImage direction.kernel x)
        (fullConvImage_nonnegative direction.kernel_nonnegative hx)

/-- Every route preserves the exact terminal work/backup formula inherited
from the canonical east-then-south Pascal route. -/
theorem applyFrontierRoute_frontierInvariant
    (route : List FrontierDirection) {rows cols : ℕ} (x : Image rows cols)
    (hseed : NorthwestTwoRegisterSeed x) :
    TwoDimensionalFrontierInvariant x (southStepCount route)
      (eastStepCount route) (applyFrontierRoute route x) := by
  have hcanonical := iteratePascalGrid_frontierInvariant
    (southStepCount route) (eastStepCount route) x hseed
  have hroute := applyFrontierRoute_eq_pascalGrid route x
  unfold TwoDimensionalFrontierInvariant at hcanonical ⊢
  constructor
  · rw [hroute]
    exact hcanonical.1
  constructor
  · rw [hroute]
    exact hcanonical.2.1
  · intro p hp
    rw [hroute, hroute]
    exact hcanonical.2.2 p hp

/-- On a nonnegative injective family of vacant northwest two-register
seeds, every finite repeated-turn route is a genuine injective shared-bias
CNN and satisfies the exact terminal frontier invariant. -/
theorem frontierRouteNetwork_injectiveOn_and_invariant
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (route : List FrontierDirection) (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFseed : ∀ x ∈ K, NorthwestTwoRegisterSeed (F x))
    (hFinjective : Set.InjOn F K) :
    Set.InjOn (fun x ↦ (frontierRouteNetwork route).eval (F x)) K ∧
      ∀ x ∈ K,
        TwoDimensionalFrontierInvariant (F x) (southStepCount route)
          (eastStepCount route)
          ((frontierRouteNetwork route).eval (F x)) := by
  constructor
  · intro x hx y hy heval
    apply hFinjective hx hy
    apply applyFrontierRoute_injective route
    change applyFrontierRoute route (F x) = applyFrontierRoute route (F y)
    rw [← frontierRouteNetwork_eval_of_nonnegative route (F x)
        (hFnonnegative x hx),
      ← frontierRouteNetwork_eval_of_nonnegative route (F y)
        (hFnonnegative y hy)]
    exact heval
  · intro x hx
    rw [frontierRouteNetwork_eval_of_nonnegative route (F x)
      (hFnonnegative x hx)]
    exact applyFrontierRoute_frontierInvariant route (F x) (hFseed x hx)

end OneChannelCNNUniversality
