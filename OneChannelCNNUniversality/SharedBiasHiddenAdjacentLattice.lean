import OneChannelCNNUniversality.SharedBiasAdjacentRidge
import OneChannelCNNUniversality.LatticeCompiler

/-!
# Encoded adjacent lattice nodes in a genuine hidden state

For a compact one-row feature family, two protected layers first compute
the adjacent difference ridge and retain an affine southeast copy of the
input.  One further injective, compactly linearized convolution combines the
ridge with that copy.  The resulting internal coordinates are

\[
  \max(x_{j-1},x_j)+\Delta
  \quad\text{and}\quad
  \min(x_{j-1},x_j)+\Delta,
\]

for one known positive carrier shift `Δ`.  Unlike a terminal affine readout,
these values occur in the output image of a genuine one-channel shared-bias
CNN, and the complete output representation remains injective.

The shifted form is intentional: it lets the last ReLU stay in its linear
branch at every spatial coordinate, so no information is destroyed.  A later
affine preactivation or terminal affine readout can subtract the known scalar
shift.
-/

namespace OneChannelCNNUniversality

universe u

/-- Identity at the current site plus a signed multiple of its northern
predecessor. -/
def verticalWeightedKernel (weight : ℝ) : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) weight

/-- Identity at the current site plus a signed multiple of its northwest
predecessor. -/
def diagonalWeightedKernel (weight : ℝ) : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) weight

/-- Natural-coordinate formula for the vertical weighted kernel. -/
theorem fullConv_verticalWeightedKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (weight : ℝ) (p q : ℕ) :
    fullConv (verticalWeightedKernel weight) x p q =
      zeroExtend x p q +
        if 1 ≤ p then weight * zeroExtend x (p - 1) q else 0 := by
  unfold verticalWeightedKernel
  rw [fullConv_twoTapKernel]
  simp

/-- Natural-coordinate formula for the diagonal weighted kernel. -/
theorem fullConv_diagonalWeightedKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (weight : ℝ) (p q : ℕ) :
    fullConv (diagonalWeightedKernel weight) x p q =
      zeroExtend x p q +
        if 1 ≤ p ∧ 1 ≤ q then
          weight * zeroExtend x (p - 1) (q - 1)
        else 0 := by
  unfold diagonalWeightedKernel
  rw [fullConv_twoTapKernel]
  simp

private theorem verticalWeightedTransform_zero
    {n cols : ℕ} (x : Image (n + 1) cols) (weight : ℝ) (j : Fin cols) :
    fullConv (verticalWeightedKernel weight) x 0 j = x 0 j := by
  rw [fullConv_verticalWeightedKernel_nat]
  simp [zeroExtend, j.isLt]

private theorem verticalWeightedTransform_succ
    {n cols : ℕ} (x : Image (n + 1) cols) (weight : ℝ)
    (i : Fin n) (j : Fin cols) :
    fullConv (verticalWeightedKernel weight) x ((i : ℕ) + 1) j =
      x i.succ j + weight * x i.castSucc j := by
  rw [fullConv_verticalWeightedKernel_nat]
  have hsucc : (i : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (i : ℕ) + 1 := by omega
  simp [zeroExtend, j.isLt, hsucc, hone]
  congr 1

/-- The vertical weighted transform is injective for every real weight. -/
theorem fullConvImage_verticalWeightedKernel_injective
    {rows cols : ℕ} (weight : ℝ) :
    Function.Injective
      (fun x : Image rows cols ↦
        fullConvImage (verticalWeightedKernel weight) x) := by
  intro x y hxy
  by_cases hrows : rows = 0
  · subst rows
    funext i j
    exact Fin.elim0 i
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrows
    funext i j
    induction i using Fin.induction with
    | zero =>
        have hentry := congrFun (congrFun hxy
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv (verticalWeightedKernel weight) x 0 j =
          fullConv (verticalWeightedKernel weight) y 0 j at hentry
        simpa only [verticalWeightedTransform_zero] using hentry
    | succ i ih =>
        have hentry := congrFun (congrFun hxy
          (⟨(i : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv (verticalWeightedKernel weight) x ((i : ℕ) + 1) j =
          fullConv (verticalWeightedKernel weight) y ((i : ℕ) + 1) j at hentry
        rw [verticalWeightedTransform_succ,
          verticalWeightedTransform_succ, ih] at hentry
        linarith

private theorem diagonalWeightedTransform_zero
    {n cols : ℕ} (x : Image (n + 1) cols) (weight : ℝ) (j : Fin cols) :
    fullConv (diagonalWeightedKernel weight) x 0 j = x 0 j := by
  rw [fullConv_diagonalWeightedKernel_nat]
  simp [zeroExtend, j.isLt]

private theorem diagonalWeightedTransform_succ
    {n cols : ℕ} (x : Image (n + 1) cols) (weight : ℝ)
    (i : Fin n) (j : Fin cols) :
    fullConv (diagonalWeightedKernel weight) x ((i : ℕ) + 1) j =
      x i.succ j +
        if 1 ≤ (j : ℕ) then
          weight * zeroExtend x i ((j : ℕ) - 1)
        else 0 := by
  rw [fullConv_diagonalWeightedKernel_nat]
  have hsucc : (i : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (i : ℕ) + 1 := by omega
  simp only [hone, true_and]
  rw [zeroExtend_of_lt _ hsucc j.isLt]
  congr 1

/-- The diagonal weighted transform is injective for every real weight. -/
theorem fullConvImage_diagonalWeightedKernel_injective
    {rows cols : ℕ} (weight : ℝ) :
    Function.Injective
      (fun x : Image rows cols ↦
        fullConvImage (diagonalWeightedKernel weight) x) := by
  intro x y hxy
  by_cases hrows : rows = 0
  · subst rows
    funext i j
    exact Fin.elim0 i
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrows
    apply funext
    intro i
    induction i using Fin.induction with
    | zero =>
        funext j
        have hentry := congrFun (congrFun hxy
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv (diagonalWeightedKernel weight) x 0 j =
          fullConv (diagonalWeightedKernel weight) y 0 j at hentry
        simpa only [diagonalWeightedTransform_zero] using hentry
    | succ i ih =>
        funext j
        have hentry := congrFun (congrFun hxy
          (⟨(i : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv (diagonalWeightedKernel weight) x ((i : ℕ) + 1) j =
          fullConv (diagonalWeightedKernel weight) y ((i : ℕ) + 1) j at hentry
        rw [diagonalWeightedTransform_succ,
          diagonalWeightedTransform_succ] at hentry
        by_cases hj : 1 ≤ (j : ℕ)
        · simp only [hj, if_true] at hentry
          have hprev : zeroExtend x i ((j : ℕ) - 1) =
              zeroExtend y i ((j : ℕ) - 1) := by
            by_cases hq : (j : ℕ) - 1 < cols
            · rw [zeroExtend_of_lt x (by omega) hq,
                zeroExtend_of_lt y (by omega) hq]
              exact congrFun ih ⟨(j : ℕ) - 1, hq⟩
            · rw [zeroExtend_col_outside x (Nat.le_of_not_gt hq),
                zeroExtend_col_outside y (Nat.le_of_not_gt hq)]
          rw [hprev] at hentry
          linarith
        · simpa [hj] using hentry

/-- Three-layer hidden-state block for adjacent maxima. -/
def encodedAdjacentMaxNetwork {cols : ℕ} (M b : ℝ) :
    SharedBiasNetworkTo 2 2 1 cols 4 (cols + 3) :=
  (protectedAdjacentRidgeNetwork
      (rows := 1) (cols := cols) (-1) 1 0 M).append
    (SharedBiasNetworkTo.single (verticalWeightedKernel 1) b)

/-- Three-layer hidden-state block for adjacent minima. -/
def encodedAdjacentMinNetwork {cols : ℕ} (M b : ℝ) :
    SharedBiasNetworkTo 2 2 1 cols 4 (cols + 3) :=
  (protectedAdjacentRidgeNetwork
      (rows := 1) (cols := cols) (-1) 1 0 M).append
    (SharedBiasNetworkTo.single (diagonalWeightedKernel (-1)) b)

@[simp] theorem encodedAdjacentMaxNetwork_depth {cols : ℕ} (M b : ℝ) :
    (encodedAdjacentMaxNetwork (cols := cols) M b).net.depth = 3 := by
  rw [encodedAdjacentMaxNetwork, SharedBiasNetworkTo.depth_append,
    protectedAdjacentRidgeNetwork_depth]
  rfl

@[simp] theorem encodedAdjacentMinNetwork_depth {cols : ℕ} (M b : ℝ) :
    (encodedAdjacentMinNetwork (cols := cols) M b).net.depth = 3 := by
  rw [encodedAdjacentMinNetwork, SharedBiasNetworkTo.depth_append,
    protectedAdjacentRidgeNetwork_depth]
  rfl

private theorem linearized_layer_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (kernel : Kernel 2 2) (b : ℝ)
    (hlinear : ∀ x ∈ K, ∀ p q,
      sharedLayerEval kernel b (F x) p q =
        fullConv kernel (F x) p q + b)
    (hconv : Function.Injective
      (fun z : Image rows cols ↦ fullConvImage kernel z))
    (hFinjective : Set.InjOn F K) :
    Set.InjOn (fun x ↦ sharedLayerEval kernel b (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  apply hconv
  funext p q
  have hentry := congrFun (congrFun heval p) q
  change sharedLayerEval kernel b (F x) p q =
    sharedLayerEval kernel b (F y) p q at hentry
  rw [hlinear x hx p q, hlinear y hy p q] at hentry
  change fullConv kernel (F x) p q = fullConv kernel (F y) p q
  exact add_right_cancel hentry

/-- On a compact continuous injective one-row feature family, a genuine
depth-three shared-bias CNN stores every adjacent maximum, up to one known
positive carrier shift, in its hidden image and preserves injectivity. -/
theorem exists_encodedAdjacentMaxNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {cols : ℕ} (F : X → Image 1 cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 cols 4 (cols + 3),
        net.net.depth = 3 ∧
        (∀ x ∈ K, ∀ j : Fin cols, 1 ≤ (j : ℕ) →
          zeroExtend (net.eval (F x)) 1 j =
            max (zeroExtend (F x) 0 ((j : ℕ) - 1))
              (zeroExtend (F x) 0 j) + Δ) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  let first : SharedBiasNetworkTo 2 2 1 cols 3 (cols + 2) :=
    protectedAdjacentRidgeNetwork (-1) 1 0 M
  let G : X → Image 3 (cols + 2) := fun x ↦ first.eval (F x)
  have hG : ContinuousFeatureOn K G := first.continuousFeatureOn_eval F hF
  have hfirstInjective : Set.InjOn G K := by
    exact protectedAdjacentRidgeNetwork_injectiveOn
      F (-1) 1 0 M hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      hFinjective
  obtain ⟨b, hb, hlinear⟩ :=
    exists_shared_bias_linearization hK G hG (verticalWeightedKernel 1)
  let Δ := protectedAdjacentRidgeCarrier (-1) 1 0 M + b
  let net := encodedAdjacentMaxNetwork (cols := cols) M b
  have hnetInjective : Set.InjOn (fun x ↦ net.eval (F x)) K := by
    change Set.InjOn
      (fun x ↦ sharedLayerEval (verticalWeightedKernel 1) b (G x)) K
    exact linearized_layer_injectiveOn G (verticalWeightedKernel 1) b
      hlinear (fullConvImage_verticalWeightedKernel_injective 1)
      hfirstInjective
  refine ⟨Δ, ?_, net, encodedAdjacentMaxNetwork_depth M b, ?_,
    hnetInjective⟩
  · dsimp [Δ, protectedAdjacentRidgeCarrier]
    norm_num
    linarith
  · intro x hx j hj
    dsimp only [net]
    rw [zeroExtend_of_lt _ (by omega) (by omega)]
    rw [encodedAdjacentMaxNetwork, SharedBiasNetworkTo.eval_append]
    change sharedLayerEval (verticalWeightedKernel 1) b (G x)
        (⟨1, by omega⟩ : Fin 4) (⟨j, by omega⟩ : Fin (cols + 3)) = _
    rw [hlinear x hx]
    rw [fullConv_verticalWeightedKernel_nat]
    simp only [if_pos (by omega : 1 ≤ (1 : ℕ)), one_mul]
    have hgate := protectedAdjacentRidgeNetwork_gate
      (F x) (-1) 1 0 M hM.le
      (fun i q ↦ by
        have := hbound x hx i q
        simpa using this.le)
      j hj
    let west : Fin cols := ⟨(j : ℕ) - 1, by omega⟩
    have hbackup := protectedAdjacentRidgeNetwork_backup
      (F x) (-1) 1 0 M hM.le
      (fun i q ↦ by
        have := hbound x hx i q
        simpa using this.le)
      (0 : Fin 1) west
    have hwestSucc : (west : ℕ) + 1 = (j : ℕ) := by
      dsimp [west]
      omega
    rw [hwestSucc] at hbackup
    have hGbackup :
        zeroExtend (G x) 1 j =
          F x 0 west +
            protectedAdjacentRidgeCarrier (-1) 1 0 M := by
      simpa [G, first, adjacentRidgeBackupCode, west, zeroExtend] using hbackup
    have hwest : F x 0 west =
        zeroExtend (F x) 0 ((j : ℕ) - 1) := by
      rw [zeroExtend_of_lt _ (by omega) (by omega)]
      rfl
    have hGgate : zeroExtend (G x) 0 j =
        relu (-zeroExtend (F x) 0 ((j : ℕ) - 1) +
          zeroExtend (F x) 0 j) := by
      simpa [G, first] using hgate
    have hcurrent : F x 0 j = zeroExtend (F x) 0 j := by
      exact (zeroExtend_inside (F x) (0 : Fin 1) j).symm
    rw [hGbackup, hwest]
    norm_num
    rw [hGgate]
    have hmax :
        zeroExtend (F x) 0 ((j : ℕ) - 1) +
            relu (-zeroExtend (F x) 0 ((j : ℕ) - 1) +
              zeroExtend (F x) 0 j) =
          max (zeroExtend (F x) 0 ((j : ℕ) - 1))
            (zeroExtend (F x) 0 j) := by
      have h := add_relu_sub_eq_max
        (zeroExtend (F x) 0 j)
        (zeroExtend (F x) 0 ((j : ℕ) - 1))
      rw [max_comm] at h
      have harg :
          -zeroExtend (F x) 0 ((j : ℕ) - 1) +
              zeroExtend (F x) 0 j =
            zeroExtend (F x) 0 j -
              zeroExtend (F x) 0 ((j : ℕ) - 1) := by ring
      rw [harg]
      exact h
    simp only [relu_eq_max] at hmax
    dsimp [Δ]
    rw [hcurrent]
    linarith

/-- On the same class of feature families, a genuine depth-three shared-bias
CNN stores every adjacent minimum, up to a known positive carrier shift, and
preserves the complete input information. -/
theorem exists_encodedAdjacentMinNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {cols : ℕ} (F : X → Image 1 cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 cols 4 (cols + 3),
        net.net.depth = 3 ∧
        (∀ x ∈ K, ∀ j : Fin cols, 1 ≤ (j : ℕ) →
          zeroExtend (net.eval (F x)) 1 ((j : ℕ) + 1) =
            min (zeroExtend (F x) 0 ((j : ℕ) - 1))
              (zeroExtend (F x) 0 j) + Δ) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  let first : SharedBiasNetworkTo 2 2 1 cols 3 (cols + 2) :=
    protectedAdjacentRidgeNetwork (-1) 1 0 M
  let G : X → Image 3 (cols + 2) := fun x ↦ first.eval (F x)
  have hG : ContinuousFeatureOn K G := first.continuousFeatureOn_eval F hF
  have hfirstInjective : Set.InjOn G K := by
    exact protectedAdjacentRidgeNetwork_injectiveOn
      F (-1) 1 0 M hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      hFinjective
  obtain ⟨b, hb, hlinear⟩ :=
    exists_shared_bias_linearization hK G hG (diagonalWeightedKernel (-1))
  let Δ := protectedAdjacentRidgeCarrier (-1) 1 0 M + b
  let net := encodedAdjacentMinNetwork (cols := cols) M b
  have hnetInjective : Set.InjOn (fun x ↦ net.eval (F x)) K := by
    change Set.InjOn
      (fun x ↦ sharedLayerEval (diagonalWeightedKernel (-1)) b (G x)) K
    exact linearized_layer_injectiveOn G (diagonalWeightedKernel (-1)) b
      hlinear (fullConvImage_diagonalWeightedKernel_injective (-1))
      hfirstInjective
  refine ⟨Δ, ?_, net, encodedAdjacentMinNetwork_depth M b, ?_,
    hnetInjective⟩
  · dsimp [Δ, protectedAdjacentRidgeCarrier]
    norm_num
    linarith
  · intro x hx j hj
    dsimp only [net]
    rw [zeroExtend_of_lt _ (by omega) (by omega)]
    rw [encodedAdjacentMinNetwork, SharedBiasNetworkTo.eval_append]
    change sharedLayerEval (diagonalWeightedKernel (-1)) b (G x)
        (⟨1, by omega⟩ : Fin 4)
        (⟨(j : ℕ) + 1, by omega⟩ : Fin (cols + 3)) = _
    rw [hlinear x hx]
    rw [fullConv_diagonalWeightedKernel_nat]
    simp only [if_pos (by omega : 1 ≤ (1 : ℕ) ∧
      1 ≤ (j : ℕ) + 1), neg_one_mul]
    have hgate := protectedAdjacentRidgeNetwork_gate
      (F x) (-1) 1 0 M hM.le
      (fun i q ↦ by
        have := hbound x hx i q
        simpa using this.le)
      j hj
    have hbackup := protectedAdjacentRidgeNetwork_backup
      (F x) (-1) 1 0 M hM.le
      (fun i q ↦ by
        have := hbound x hx i q
        simpa using this.le)
      (0 : Fin 1) j
    have hGbackup :
        zeroExtend (G x) 1 ((j : ℕ) + 1) =
          zeroExtend (F x) 0 j +
            protectedAdjacentRidgeCarrier (-1) 1 0 M := by
      simpa [G, first, adjacentRidgeBackupCode, zeroExtend] using hbackup
    have hGgate : zeroExtend (G x) 0 j =
        relu (-zeroExtend (F x) 0 ((j : ℕ) - 1) +
          zeroExtend (F x) 0 j) := by
      simpa [G, first] using hgate
    have hcurrent : F x 0 j = zeroExtend (F x) 0 j := by
      exact (zeroExtend_inside (F x) (0 : Fin 1) j).symm
    rw [hGbackup]
    norm_num
    rw [hGgate]
    have hmin :
        zeroExtend (F x) 0 j -
            relu (-zeroExtend (F x) 0 ((j : ℕ) - 1) +
              zeroExtend (F x) 0 j) =
          min (zeroExtend (F x) 0 ((j : ℕ) - 1))
            (zeroExtend (F x) 0 j) := by
      have h := sub_relu_sub_eq_min
        (zeroExtend (F x) 0 j)
        (zeroExtend (F x) 0 ((j : ℕ) - 1))
      rw [min_comm] at h
      have harg :
          -zeroExtend (F x) 0 ((j : ℕ) - 1) +
              zeroExtend (F x) 0 j =
            zeroExtend (F x) 0 j -
              zeroExtend (F x) 0 ((j : ℕ) - 1) := by ring
      rw [harg]
      exact h
    simp only [relu_eq_max] at hmin
    dsimp [Δ]
    rw [hcurrent]
    linarith

end OneChannelCNNUniversality
