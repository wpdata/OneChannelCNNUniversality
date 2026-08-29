import OneChannelCNNUniversality.SharedBiasAdjacentCopy
import OneChannelCNNUniversality.SharedBiasCausality

/-!
# Causal obstruction and a moving computation frontier

Expansive convolution is northwest causal, so no later layer can move an
eastern or southern register back into the northwest output.  This module
derives a reusable non-realizability criterion from the existing causality
theorem, then records the first positive alternative: move the work site one
step east.  A genuine horizontal-accumulation layer computes a two-register
affine ReLU at that eastern frontier and, at zero threshold on nonnegative
states, remains injective.
-/

namespace OneChannelCNNUniversality

universe u

/-- Equal northwest input roots force equal northwest outputs for every
finite explicitly typed expansive shared-bias CNN. -/
theorem northwestOutput_eq_of_inputRoot_eq
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols
      inRows inCols outRows outCols)
    {x y : Image inRows inCols}
    (hroot : zeroExtend x 0 0 = zeroExtend y 0 0) :
    zeroExtend (net.eval x) 0 0 = zeroExtend (net.eval y) 0 0 := by
  have hxy : NorthwestAgree x y 0 0 := by
    intro i hi j hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    simpa [hi0, hj0] using hroot
  exact northwestAgree_sharedBiasNetworkTo_eval net hxy 0 le_rfl 0 le_rfl

/-- A scalar target is realized at the northwest output throughout `K`. -/
def NorthwestRealizesOn
    {X : Type u} {rows cols kRows kCols : ℕ}
    (K : Set X) (F : X → Image rows cols) (target : X → ℝ)
    (net : SharedBiasNetwork kRows kCols rows cols) : Prop :=
  ∀ x ∈ K, zeroExtend (net.eval (F x)) 0 0 = target x

/-- Any northwest-realized target is constant on each fiber of the input
northwest-root coordinate. -/
theorem NorthwestRealizesOn.eq_of_inputRoot_eq
    {X : Type u} {K : Set X} {rows cols kRows kCols : ℕ}
    {F : X → Image rows cols} {target : X → ℝ}
    {net : SharedBiasNetwork kRows kCols rows cols}
    (hrealizes : NorthwestRealizesOn K F target net)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hroot : zeroExtend (F x) 0 0 = zeroExtend (F y) 0 0) :
    target x = target y := by
  rw [← hrealizes x hx, ← hrealizes y hy]
  have hxy : NorthwestAgree (F x) (F y) 0 0 := by
    intro i hi j hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    simpa [hi0, hj0] using hroot
  exact northwestAgree_sharedBiasNetwork_eval net hxy 0 le_rfl 0 le_rfl

/-- If two inputs have the same northwest root but a desired scalar target
distinguishes them, no finite expansive shared-bias CNN can realize that
target at its northwest output.  Kernel size and network depth are arbitrary. -/
theorem not_exists_northwestRealization_of_root_eq_target_ne
    {X : Type u} {K : Set X} {rows cols kRows kCols : ℕ}
    (F : X → Image rows cols) (target : X → ℝ)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hroot : zeroExtend (F x) 0 0 = zeroExtend (F y) 0 0)
    (htarget : target x ≠ target y) :
    ¬ ∃ net : SharedBiasNetwork kRows kCols rows cols,
      NorthwestRealizesOn K F target net := by
  rintro ⟨net, hrealizes⟩
  exact htarget (hrealizes.eq_of_inputRoot_eq hx hy hroot)

/-- One genuine shared-bias layer whose eastern frontier combines the two
northwest input registers before applying a scalar threshold. -/
def eastFrontierLayer {rows cols : ℕ} (θ : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1) (cols + 2 - 1) :=
  SharedBiasNetworkTo.single horizontalAccumulationKernel θ

/-- Exact two-register affine-ReLU computation at the eastern frontier. -/
theorem eastFrontierLayer_east_eval
    {rows cols : ℕ} (hcols : 0 < cols) (θ : ℝ)
    (x : Image rows cols) :
    zeroExtend ((eastFrontierLayer (rows := rows) (cols := cols) θ).eval x)
        0 1 =
      relu (zeroExtend x 0 0 + zeroExtend x 0 1 + θ) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu (fullConv horizontalAccumulationKernel x 0 1 + θ) = _
  rw [fullConv_horizontalAccumulationKernel_nat]
  simp only [if_pos le_rfl, Nat.reduceSubDiff]
  congr 1
  ring

/-- At zero threshold on a nonnegative family, the eastern-frontier addition
is performed without losing any state: the complete output map remains
injective while coordinate `(0,1)` equals the sum of the two input roots. -/
theorem eastFrontierLayer_injectiveOn_and_east_add
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (hcols : 0 < cols) (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
        (fun x ↦ (eastFrontierLayer (rows := rows) (cols := cols) 0).eval
          (F x)) K ∧
      ∀ x ∈ K,
        zeroExtend
            ((eastFrontierLayer (rows := rows) (cols := cols) 0).eval
              (F x)) 0 1 =
          zeroExtend (F x) 0 0 + zeroExtend (F x) 0 1 := by
  constructor
  · intro x hx y hy heval
    apply hFinjective hx hy
    exact adjacentCopyLayer_injective_of_nonnegative
      (hFnonnegative x hx) (hFnonnegative y hy) heval
  · intro x hx
    rw [eastFrontierLayer_east_eval hcols]
    have hsum : 0 ≤ zeroExtend (F x) 0 0 + zeroExtend (F x) 0 1 :=
      add_nonneg (zeroExtend_nonnegative (hFnonnegative x hx) 0 0)
        (zeroExtend_nonnegative (hFnonnegative x hx) 0 1)
    simp [relu, hsum]

end OneChannelCNNUniversality
