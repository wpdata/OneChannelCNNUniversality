import OneChannelCNNUniversality.SharedBiasGridGate

/-!
# A protected adjacent-register ridge gate

Two genuine shared-bias layers compute an arbitrary signed affine ReLU of
each adjacent pair on the northern row.  A southeast-shifted triangular code
of the complete input survives below the gate row, so the full representation
remains injective.  The construction combines the mixing and protected-gate
steps in depth two.
-/

namespace OneChannelCNNUniversality

universe u

/-- The northern taps form `alpha * west + beta * current`; the southeast tap
copies an input coordinate into the shifted triangular backup. -/
def protectedAdjacentRidgeKernel (alpha beta : ℝ) : Kernel 2 2 :=
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) beta i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) alpha i j +
        deltaKernel (1 : Fin 2) (1 : Fin 2) 1 i j)

/-- Natural-coordinate formula for the protected adjacent-ridge kernel. -/
theorem fullConv_protectedAdjacentRidgeKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (alpha beta : ℝ) (p q : ℕ) :
    fullConv (protectedAdjacentRidgeKernel alpha beta) x p q =
      beta * zeroExtend x p q +
        (if 1 ≤ q then alpha * zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then zeroExtend x (p - 1) (q - 1) else 0) := by
  unfold protectedAdjacentRidgeKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_deltaKernel]
  simp
  ring_nf

/-- One uniform carrier that linearizes the seed layer and every shifted
triangular backup coordinate on an `M`-bounded input. -/
def protectedAdjacentRidgeCarrier (alpha beta gamma M : ℝ) : ℝ :=
  (1 + |alpha| + |beta|) * M + |gamma|

/-- The protected output rectangle, shifted one step southeast.  Rows are
decoded from south to north, since both extra terms use the next input row. -/
def adjacentRidgeBackupCode {rows cols : ℕ} (alpha beta C : ℝ)
    (x : Image rows cols) : Image rows cols :=
  fun i j ↦ x i j + alpha * zeroExtend x (i + 1) j +
    beta * zeroExtend x (i + 1) (j + 1) + C

/-- Two genuine expansive shared-bias layers. -/
def protectedAdjacentRidgeNetwork {rows cols : ℕ}
    (alpha beta gamma M : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2) :=
  let B := protectedAdjacentRidgeCarrier alpha beta gamma M
  SharedBiasNetworkTo.cons expansiveIdentityKernel B
    (SharedBiasNetworkTo.single (protectedAdjacentRidgeKernel alpha beta)
      (gamma - (alpha + beta) * B))

theorem protectedAdjacentRidgeNetwork_depth {rows cols : ℕ}
    (alpha beta gamma M : ℝ) :
    (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
      alpha beta gamma M).net.depth = 2 := by
  rfl

private theorem abs_zeroExtend_le_adjacentRidge_bound
    {rows cols : ℕ} (x : Image rows cols) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) (p q : ℕ) :
    |zeroExtend x p q| ≤ M := by
  by_cases hp : p < rows
  · by_cases hq : q < cols
    · simpa [zeroExtend, hp, hq] using hbound ⟨p, hp⟩ ⟨q, hq⟩
    · simp [zeroExtend, hp, hq, hM]
  · simp [zeroExtend, hp, hM]

private theorem protectedAdjacentRidge_seed
    {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (p q : ℕ) (hp : p ≤ rows) (hq : q ≤ cols) :
    zeroExtend
        (sharedLayerEval expansiveIdentityKernel
          (protectedAdjacentRidgeCarrier alpha beta gamma M) x) p q =
      zeroExtend x p q + protectedAdjacentRidgeCarrier alpha beta gamma M := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv expansiveIdentityKernel x p q +
        protectedAdjacentRidgeCarrier alpha beta gamma M) = _
  rw [fullConv_expansiveIdentityKernel_nat, relu_of_nonneg]
  have hxabs := abs_zeroExtend_le_adjacentRidge_bound x M hM hbound p q
  have hxlower := neg_abs_le (zeroExtend x p q)
  have hscale : 0 ≤ (|alpha| + |beta|) * M :=
    mul_nonneg (add_nonneg (abs_nonneg alpha) (abs_nonneg beta)) hM
  have hcarrier : M ≤ protectedAdjacentRidgeCarrier alpha beta gamma M := by
    dsimp [protectedAdjacentRidgeCarrier]
    nlinarith [abs_nonneg gamma]
  linarith

/-- Every nonwestern northern coordinate computes the requested arbitrary
two-register ridge. -/
theorem protectedAdjacentRidgeNetwork_gate
    {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) 0 j =
      relu (alpha * zeroExtend x 0 ((j : ℕ) - 1) +
        beta * zeroExtend x 0 j + gamma) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAdjacentRidgeKernel alpha beta)
          (sharedLayerEval expansiveIdentityKernel
            (protectedAdjacentRidgeCarrier alpha beta gamma M) x) 0 j +
        (gamma - (alpha + beta) *
          protectedAdjacentRidgeCarrier alpha beta gamma M)) = _
  rw [fullConv_protectedAdjacentRidgeKernel_nat]
  rw [if_pos hj, if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ (j : ℕ)))]
  simp only [add_zero]
  rw [protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      0 j (Nat.zero_le rows) (by omega),
    protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      0 ((j : ℕ) - 1) (Nat.zero_le rows) (by omega)]
  congr 1
  ring

/-- At the first eastern expansion coordinate, the missing current input
removes the `beta` term.  This is the moving-frontier form of the gate. -/
theorem protectedAdjacentRidgeNetwork_east_fringe
    {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hcols : 0 < cols) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) 0 cols =
      relu (alpha * zeroExtend x 0 (cols - 1) + gamma) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAdjacentRidgeKernel alpha beta)
          (sharedLayerEval expansiveIdentityKernel
            (protectedAdjacentRidgeCarrier alpha beta gamma M) x) 0 cols +
        (gamma - (alpha + beta) *
          protectedAdjacentRidgeCarrier alpha beta gamma M)) = _
  rw [fullConv_protectedAdjacentRidgeKernel_nat]
  rw [if_pos (by omega : 1 ≤ cols),
    if_neg (by omega : ¬(1 ≤ (0 : ℕ) ∧ 1 ≤ cols))]
  simp only [add_zero]
  rw [protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      0 cols (Nat.zero_le rows) le_rfl,
    protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      0 (cols - 1) (Nat.zero_le rows) (by omega),
    zeroExtend_col_outside x le_rfl]
  congr 1
  ring

/-- Every original input coordinate survives one step southeast in a code
that is triangular in the row direction. -/
theorem protectedAdjacentRidgeNetwork_backup
    {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (i : Fin rows) (j : Fin cols) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x)
          (i + 1) (j + 1) =
      adjacentRidgeBackupCode alpha beta
        (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma) x i j := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAdjacentRidgeKernel alpha beta)
          (sharedLayerEval expansiveIdentityKernel
            (protectedAdjacentRidgeCarrier alpha beta gamma M) x)
          (i + 1) (j + 1) +
        (gamma - (alpha + beta) *
          protectedAdjacentRidgeCarrier alpha beta gamma M)) = _
  rw [fullConv_protectedAdjacentRidgeKernel_nat]
  simp only [if_pos (by omega : 1 ≤ (j : ℕ) + 1),
    if_pos (by omega : 1 ≤ (i : ℕ) + 1 ∧ 1 ≤ (j : ℕ) + 1),
    Nat.reduceSubDiff]
  rw [protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      (i + 1) (j + 1) (by omega) (by omega),
    protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      (i + 1) j (by omega) (by omega),
    protectedAdjacentRidge_seed x alpha beta gamma M hM hbound
      i j (by omega) (by omega)]
  have hpre :
      beta * (zeroExtend x (i + 1) (j + 1) +
          protectedAdjacentRidgeCarrier alpha beta gamma M) +
        alpha * (zeroExtend x (i + 1) j +
          protectedAdjacentRidgeCarrier alpha beta gamma M) +
        (zeroExtend x i j +
          protectedAdjacentRidgeCarrier alpha beta gamma M) +
        (gamma - (alpha + beta) *
          protectedAdjacentRidgeCarrier alpha beta gamma M) =
      x i j + alpha * zeroExtend x (i + 1) j +
        beta * zeroExtend x (i + 1) (j + 1) +
        (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma) := by
    rw [zeroExtend_inside]
    ring
  rw [hpre, relu_of_nonneg]
  · rfl
  · have hx := hbound i j
    have hxlower := neg_abs_le (x i j)
    have hnext := abs_zeroExtend_le_adjacentRidge_bound
      x M hM hbound (i + 1) j
    have hdiag := abs_zeroExtend_le_adjacentRidge_bound
      x M hM hbound (i + 1) (j + 1)
    have halower : -(|alpha| * M) ≤ alpha * zeroExtend x (i + 1) j := by
      calc
        -(|alpha| * M) ≤ -|alpha * zeroExtend x (i + 1) j| := by
          rw [abs_mul]
          exact neg_le_neg
            (mul_le_mul_of_nonneg_left hnext (abs_nonneg alpha))
        _ ≤ alpha * zeroExtend x (i + 1) j := neg_abs_le _
    have hblower : -(|beta| * M) ≤
        beta * zeroExtend x (i + 1) (j + 1) := by
      calc
        -(|beta| * M) ≤ -|beta * zeroExtend x (i + 1) (j + 1)| := by
          rw [abs_mul]
          exact neg_le_neg
            (mul_le_mul_of_nonneg_left hdiag (abs_nonneg beta))
        _ ≤ beta * zeroExtend x (i + 1) (j + 1) := neg_abs_le _
    have hcarrierExpand :
        (1 + |alpha| + |beta|) * M =
          M + |alpha| * M + |beta| * M := by ring
    dsimp [protectedAdjacentRidgeCarrier]
    rw [hcarrierExpand]
    linarith [neg_le_abs gamma]

/-- The shifted backup code is injective for all real ridge coefficients and
offsets. -/
theorem adjacentRidgeBackupCode_injective {rows cols : ℕ}
    (alpha beta C : ℝ) :
    Function.Injective
      (adjacentRidgeBackupCode (rows := rows) (cols := cols) alpha beta C) := by
  intro x y hxy
  have hcode (k q : ℕ) (hk : k < rows) (hq : q < cols) :
      zeroExtend x k q + alpha * zeroExtend x (k + 1) q +
          beta * zeroExtend x (k + 1) (q + 1) + C =
        zeroExtend y k q + alpha * zeroExtend y (k + 1) q +
          beta * zeroExtend y (k + 1) (q + 1) + C := by
    have hentry := congrFun (congrFun hxy ⟨k, hk⟩) ⟨q, hq⟩
    simpa [adjacentRidgeBackupCode, zeroExtend_of_lt _ hk hq] using hentry
  have hsuffix : ∀ k : ℕ, k ≤ rows →
      ∀ t : ℕ, k ≤ t → t < rows → ∀ q : ℕ,
        zeroExtend x t q = zeroExtend y t q := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
        intro t ht hlt q
        omega
    | of_succ k hk ih =>
        intro t hkt ht q
        by_cases htk : t = k
        · subst t
          by_cases hq : q < cols
          · have heq := hcode k q hk hq
            have hnext : zeroExtend x (k + 1) q =
                zeroExtend y (k + 1) q := by
              by_cases hnextRows : k + 1 < rows
              · exact ih (k + 1) le_rfl hnextRows q
              · have hout : rows ≤ k + 1 := Nat.le_of_not_gt hnextRows
                rw [zeroExtend_row_outside x hout,
                  zeroExtend_row_outside y hout]
            have hdiag : zeroExtend x (k + 1) (q + 1) =
                zeroExtend y (k + 1) (q + 1) := by
              by_cases hnextRows : k + 1 < rows
              · exact ih (k + 1) le_rfl hnextRows (q + 1)
              · have hout : rows ≤ k + 1 := Nat.le_of_not_gt hnextRows
                rw [zeroExtend_row_outside x hout,
                  zeroExtend_row_outside y hout]
            rw [hnext, hdiag] at heq
            linarith
          · have hout : cols ≤ q := Nat.le_of_not_gt hq
            rw [zeroExtend_col_outside x hout, zeroExtend_col_outside y hout]
        · exact ih t (by omega) ht q
  funext i j
  have hij := hsuffix 0 (Nat.zero_le rows) i (Nat.zero_le i) i.isLt j
  simpa using hij

/-- The complete two-layer representation is injective on every uniformly
bounded injective image family. -/
theorem protectedAdjacentRidgeNetwork_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ K, ∀ i j, |F x i j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedAdjacentRidgeNetwork alpha beta gamma M).eval (F x))
      K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  apply adjacentRidgeBackupCode_injective alpha beta
    (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma)
  funext i j
  rw [← protectedAdjacentRidgeNetwork_backup
      (F x) alpha beta gamma M hM (hbound x hx) i j,
    ← protectedAdjacentRidgeNetwork_backup
      (F y) alpha beta gamma M hM (hbound y hy) i j]
  exact congrArg (fun z ↦ zeroExtend z (i + 1) (j + 1)) heval

/-- Compactness supplies one uniform carrier.  The resulting depth-two
network computes every nonwestern northern adjacent ridge, exposes the exact
shifted backup code, and preserves injectivity. -/
theorem exists_protectedAdjacentRidgeNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (alpha beta gamma : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2),
        net.net.depth = 2 ∧
        (∀ x ∈ K,
          (∀ j : Fin cols, 1 ≤ (j : ℕ) →
            zeroExtend (net.eval (F x)) 0 j =
              relu (alpha * zeroExtend (F x) 0 ((j : ℕ) - 1) +
                beta * zeroExtend (F x) 0 j + gamma)) ∧
          ∀ i : Fin rows, ∀ j : Fin cols,
            zeroExtend (net.eval (F x)) (i + 1) (j + 1) =
              adjacentRidgeBackupCode alpha beta
                (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma)
                (F x) i j) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  refine ⟨M, hM, protectedAdjacentRidgeNetwork alpha beta gamma M,
    protectedAdjacentRidgeNetwork_depth alpha beta gamma M, ?_, ?_⟩
  · intro x hx
    have hxbound : ∀ i j, |F x i j| ≤ M := fun i j ↦ by
      have := hbound x hx i j
      simpa using this.le
    exact ⟨fun j hj ↦ protectedAdjacentRidgeNetwork_gate
        (F x) alpha beta gamma M hM.le hxbound j hj,
      fun i j ↦ protectedAdjacentRidgeNetwork_backup
        (F x) alpha beta gamma M hM.le hxbound i j⟩
  · exact protectedAdjacentRidgeNetwork_injectiveOn
      F alpha beta gamma M hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      hFinjective

end OneChannelCNNUniversality
