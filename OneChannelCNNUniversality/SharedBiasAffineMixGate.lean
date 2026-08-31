import OneChannelCNNUniversality.SharedBiasGridGate
import OneChannelCNNUniversality.SharedBiasCarrier

/-!
# A signed affine mixing gate for adjacent registers

A horizontal two-tap convolution forms `x[i,j] + λ * x[i,j-1]`.  On a
compact feature family one shared bias can keep the first ReLU in its linear
branch, even when `λ` is negative.  Two protected layers then apply a signed
affine ReLU to the mixed register while the complete feature image remains
injective.
-/

namespace OneChannelCNNUniversality

universe u

/-- Identity at the current register plus an arbitrary signed multiple of its
western predecessor. -/
def horizontalWeightedKernel (weight : ℝ) : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) weight

/-- Natural-coordinate formula for the signed horizontal mixing kernel. -/
theorem fullConv_horizontalWeightedKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (weight : ℝ) (p q : ℕ) :
    fullConv (horizontalWeightedKernel weight) x p q =
      zeroExtend x p q +
        if 1 ≤ q then weight * zeroExtend x p (q - 1) else 0 := by
  unfold horizontalWeightedKernel
  rw [fullConv_twoTapKernel]
  simp

private theorem horizontalWeightedTransform_zero
    {rows n : ℕ} (x : Image rows (n + 1)) (weight : ℝ) (i : Fin rows) :
    fullConv (horizontalWeightedKernel weight) x i 0 = x i 0 := by
  rw [fullConv_horizontalWeightedKernel_nat]
  simp [zeroExtend, i.isLt]

private theorem horizontalWeightedTransform_succ
    {rows n : ℕ} (x : Image rows (n + 1)) (weight : ℝ)
    (i : Fin rows) (j : Fin n) :
    fullConv (horizontalWeightedKernel weight) x i ((j : ℕ) + 1) =
      x i j.succ + weight * x i j.castSucc := by
  rw [fullConv_horizontalWeightedKernel_nat]
  have hsucc : (j : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (j : ℕ) + 1 := by omega
  simp [zeroExtend, i.isLt, hsucc, hone]
  congr 1

/-- The signed horizontal transform is injective for every real coefficient.
The first column is unchanged and later columns are recovered from west to
east. -/
theorem fullConvImage_horizontalWeightedKernel_injective
    {rows cols : ℕ} (weight : ℝ) :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage (horizontalWeightedKernel weight) x) := by
  intro x y hxy
  by_cases hcols : cols = 0
  · subst cols
    funext i j
    exact Fin.elim0 j
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcols
    funext i j
    induction j using Fin.induction with
    | zero =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv (horizontalWeightedKernel weight) x i 0 =
          fullConv (horizontalWeightedKernel weight) y i 0 at hentry
        simpa only [horizontalWeightedTransform_zero] using hentry
    | succ j ih =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨(j : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv (horizontalWeightedKernel weight) x i ((j : ℕ) + 1) =
          fullConv (horizontalWeightedKernel weight) y i ((j : ℕ) + 1) at hentry
        rw [horizontalWeightedTransform_succ,
          horizontalWeightedTransform_succ] at hentry
        rw [ih] at hentry
        linarith

/-- The genuine first layer used to form the signed adjacent-register mix. -/
def weightedMixLayer {rows cols : ℕ} (weight b : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols (rows + 2 - 1) (cols + 2 - 1) :=
  SharedBiasNetworkTo.single (horizontalWeightedKernel weight) b

/-- Append a protected signed ReLU gate to the linearized mixing layer.  The
offset is corrected by `-a*b`, cancelling the first layer's carrier. -/
def weightedMixGateNetwork {rows cols : ℕ} (weight b a c M : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1 + 2) (cols + 2 - 1 + 2) :=
  (weightedMixLayer (rows := rows) (cols := cols) weight b).append
    (protectedGridGateNetwork
      (rows := rows + 2 - 1) (cols := cols + 2 - 1)
      a (c - a * b) M)

/-- The signed mixing gate has exactly three hidden layers. -/
theorem weightedMixGateNetwork_depth {rows cols : ℕ} (weight b a c M : ℝ) :
    (weightedMixGateNetwork (rows := rows) (cols := cols)
      weight b a c M).net.depth = 3 := by
  rw [weightedMixGateNetwork, SharedBiasNetworkTo.depth_append,
    protectedGridGateNetwork_depth]
  rfl

/-- Exact value at the first mixed northern-row register. -/
theorem weightedMixGateNetwork_gate
    {rows cols : ℕ} (x : Image rows cols) (weight b a c M : ℝ)
    (hcols : 0 < cols)
    (hlinear : ∀ p q,
      (weightedMixLayer (rows := rows) (cols := cols) weight b).eval x p q =
        fullConv (horizontalWeightedKernel weight) x p q + b)
    (hM : 0 ≤ M)
    (hbound : ∀ i j,
      |(weightedMixLayer weight b).eval x i j| ≤ M) :
    zeroExtend
        ((weightedMixGateNetwork weight b a c M).eval x) 0 1 =
      relu (a * (zeroExtend x 0 1 + weight * zeroExtend x 0 0) + c) := by
  rw [weightedMixGateNetwork, SharedBiasNetworkTo.eval_append]
  have hgate := protectedGridGateNetwork_gate
    ((weightedMixLayer weight b).eval x) a (c - a * b) M hM hbound
    (⟨1, by omega⟩ : Fin (cols + 2 - 1))
  rw [hgate]
  rw [zeroExtend_of_lt _ (by omega) (by omega), hlinear]
  rw [fullConv_horizontalWeightedKernel_nat]
  simp
  congr 1
  ring

/-- Exact linearization of the mixing layer makes it injective on an
injectively parameterized family. -/
theorem weightedMixLayer_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (weight b : ℝ)
    (hlinear : ∀ x ∈ K, ∀ p q,
      (weightedMixLayer weight b).eval (F x) p q =
        fullConv (horizontalWeightedKernel weight) (F x) p q + b)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn (fun x ↦ (weightedMixLayer weight b).eval (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  apply fullConvImage_horizontalWeightedKernel_injective weight
  funext p q
  have hentry := congrFun (congrFun heval p) q
  change (weightedMixLayer weight b).eval (F x) p q =
    (weightedMixLayer weight b).eval (F y) p q at hentry
  rw [hlinear x hx p q, hlinear y hy p q] at hentry
  change fullConv (horizontalWeightedKernel weight) (F x) p q =
    fullConv (horizontalWeightedKernel weight) (F y) p q
  exact add_right_cancel hentry

/-- If the intermediate mixed image is uniformly bounded, the complete
three-layer representation remains injective. -/
theorem weightedMixGateNetwork_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (weight b a c M : ℝ)
    (hlinear : ∀ x ∈ K, ∀ p q,
      (weightedMixLayer weight b).eval (F x) p q =
        fullConv (horizontalWeightedKernel weight) (F x) p q + b)
    (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ∀ i j,
      |(weightedMixLayer weight b).eval (F x) i j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (weightedMixGateNetwork weight b a c M).eval (F x)) K := by
  let G : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
    fun x ↦ (weightedMixLayer weight b).eval (F x)
  have hGinjective : Set.InjOn G K := by
    exact weightedMixLayer_injectiveOn F weight b hlinear hFinjective
  have hprotected : Set.InjOn
      (fun x ↦ (protectedGridGateNetwork
        (rows := rows + 2 - 1) (cols := cols + 2 - 1)
        a (c - a * b) M).eval (G x)) K := by
    exact protectedGridGateNetwork_injectiveOn
      G a (c - a * b) M hM hbound hGinjective
  simpa [weightedMixGateNetwork, SharedBiasNetworkTo.eval_append, G] using
    hprotected

/-- On every compact continuous injective feature family with a nonempty
register row, compactness chooses both carrier constants.  The resulting
depth-three network computes one arbitrary signed affine adjacent-register
ReLU exactly and keeps the full representation injective. -/
theorem exists_weightedMixGateNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (hcols : 1 < cols) (weight a c : ℝ) :
    ∃ b : ℝ, 0 < b ∧
      ∃ M : ℝ, 0 < M ∧
        ∃ net : SharedBiasNetworkTo 2 2 rows cols
            (rows + 2 - 1 + 2) (cols + 2 - 1 + 2),
          net.net.depth = 3 ∧
          (∀ x ∈ K,
            zeroExtend (net.eval (F x)) 0 1 =
              relu (a * (zeroExtend (F x) 0 1 +
                weight * zeroExtend (F x) 0 0) + c)) ∧
          Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨b, hb, hlinear⟩ :=
    exists_shared_bias_linearization hK F hF (horizontalWeightedKernel weight)
  let mix : SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1) (cols + 2 - 1) :=
    weightedMixLayer weight b
  let G : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
    fun x ↦ mix.eval (F x)
  have hG : ContinuousFeatureOn K G := by
    exact mix.continuousFeatureOn_eval F hF
  have hGinjective : Set.InjOn G K := by
    exact weightedMixLayer_injectiveOn F weight b
      (fun x hx p q ↦ by
        rw [weightedMixLayer, SharedBiasNetworkTo.eval_single]
        exact hlinear x hx p q)
      hFinjective
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK G hG 0
  refine ⟨b, hb, M, hM,
    weightedMixGateNetwork weight b a c M,
    weightedMixGateNetwork_depth weight b a c M, ?_, ?_⟩
  · intro x hx
    exact weightedMixGateNetwork_gate
      (F x) weight b a c M hcols.le
      (fun p q ↦ by
        rw [weightedMixLayer, SharedBiasNetworkTo.eval_single]
        exact hlinear x hx p q)
      hM.le
      (fun i j ↦ by
        have := hbound x hx i j
        simpa [G, mix] using this.le)
  · exact weightedMixGateNetwork_injectiveOn
      F weight b a c M
      (fun x hx p q ↦ by
        rw [weightedMixLayer, SharedBiasNetworkTo.eval_single]
        exact hlinear x hx p q)
      hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa [G, mix] using this.le)
      hFinjective

end OneChannelCNNUniversality
