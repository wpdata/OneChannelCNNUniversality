import OneChannelCNNUniversality.SharedBiasRowGate

/-!
# A protected shared-bias gate on the top row of an arbitrary image

The one-row signed gate extends to inputs of arbitrary finite height.  Its
northern output row contains the requested pointwise signed ReLU gates.  The
remaining relevant rows form a south-triangular code: starting at the bottom,
each input row is recovered exactly from one output row and the already
recovered successor row.  Thus the gate does not destroy the full image.
-/

namespace OneChannelCNNUniversality

universe u

/-- One carrier bound that simultaneously linearizes the identity seed and
all protected south-triangular backup rows. -/
def protectedGridGateCarrier (a c M : ℝ) : ℝ :=
  (1 + |a|) * M + |c|

/-- The protected rows exposed by the second layer, reindexed to the original
image.  This code is triangular when rows are read from south to north. -/
def southTriangularCode {rows cols : ℕ} (a C : ℝ)
    (x : Image rows cols) : Image rows cols :=
  fun i j ↦ x i j + a * zeroExtend x (i + 1) j + C

/-- One step of the exact south-to-north decoder.  At the final row the
zero extension makes the successor term vanish; every earlier row then uses
the successor that has already been decoded. -/
theorem southTriangularCode_recover {rows cols : ℕ}
    (x : Image rows cols) (a C : ℝ) (i : Fin rows) (j : Fin cols) :
    southTriangularCode a C x i j - C -
        a * zeroExtend x (i + 1) j = x i j := by
  simp [southTriangularCode]

/-- Two genuine shared-bias layers.  The northern row computes the gates;
the rows immediately below it contain the triangular backup code. -/
def protectedGridGateNetwork {rows cols : ℕ} (a c M : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2) :=
  let B := protectedGridGateCarrier a c M
  SharedBiasNetworkTo.cons expansiveIdentityKernel B
    (SharedBiasNetworkTo.single (protectedRowGateKernel a) (c - a * B))

theorem protectedGridGateNetwork_depth {rows cols : ℕ} (a c M : ℝ) :
    (protectedGridGateNetwork (rows := rows) (cols := cols) a c M).net.depth =
      2 := by
  rfl

private theorem abs_zeroExtend_le_grid_bound
    {rows cols : ℕ} (x : Image rows cols) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) (p : ℕ) (j : Fin cols) :
    |zeroExtend x p j| ≤ M := by
  by_cases hp : p < rows
  · rw [zeroExtend_of_lt _ hp j.isLt]
    exact hbound ⟨p, hp⟩ j
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hp)]
    simpa using hM

private theorem protectedGridGate_seed
    {rows cols : ℕ} (x : Image rows cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) (p : ℕ) (hp : p ≤ rows)
    (j : Fin cols) :
    zeroExtend
        (sharedLayerEval expansiveIdentityKernel
          (protectedGridGateCarrier a c M) x) p j =
      zeroExtend x p j + protectedGridGateCarrier a c M := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv expansiveIdentityKernel x p j +
        protectedGridGateCarrier a c M) = _
  rw [fullConv_expansiveIdentityKernel_nat, relu_of_nonneg]
  have hxabs := abs_zeroExtend_le_grid_bound x M hM hbound p j
  have hxlower := neg_abs_le (zeroExtend x p j)
  have haM : 0 ≤ |a| * M := mul_nonneg (abs_nonneg a) hM
  have hcarrier : M ≤ protectedGridGateCarrier a c M := by
    dsimp [protectedGridGateCarrier]
    nlinarith [abs_nonneg c]
  linarith

/-- Every coordinate of the northern output row computes the requested
signed affine ReLU of the corresponding northern input coordinate. -/
theorem protectedGridGateNetwork_gate
    {rows cols : ℕ} (x : Image rows cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) (j : Fin cols) :
    zeroExtend
        ((protectedGridGateNetwork (rows := rows) (cols := cols)
          a c M).eval x) 0 j =
      relu (a * zeroExtend x 0 j + c) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel
            (protectedGridGateCarrier a c M) x) 0 j +
        (c - a * protectedGridGateCarrier a c M)) = _
  have hconv :
      fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel
            (protectedGridGateCarrier a c M) x) 0 j =
        a * zeroExtend
          (sharedLayerEval expansiveIdentityKernel
            (protectedGridGateCarrier a c M) x) 0 j := by
    rw [protectedRowGateKernel, fullConv_twoTapKernel]
    simp
  rw [hconv, protectedGridGate_seed x a c M hM hbound 0
    (Nat.zero_le rows) j]
  congr 1
  ring

/-- Each row below the gate row is one exact triangular backup equation.
The last equation has a zero successor and starts the south-to-north decoder. -/
theorem protectedGridGateNetwork_backup
    {rows cols : ℕ} (x : Image rows cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) (i : Fin rows) (j : Fin cols) :
    zeroExtend
        ((protectedGridGateNetwork (rows := rows) (cols := cols)
          a c M).eval x) (i + 1) j =
      southTriangularCode a (protectedGridGateCarrier a c M + c) x i j := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel
            (protectedGridGateCarrier a c M) x) (i + 1) j +
        (c - a * protectedGridGateCarrier a c M)) = _
  have hconv :
      fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel
            (protectedGridGateCarrier a c M) x) (i + 1) j =
        zeroExtend
            (sharedLayerEval expansiveIdentityKernel
              (protectedGridGateCarrier a c M) x) i j +
          a * zeroExtend
            (sharedLayerEval expansiveIdentityKernel
              (protectedGridGateCarrier a c M) x) (i + 1) j := by
    rw [protectedRowGateKernel, fullConv_twoTapKernel]
    simp
  rw [hconv,
    protectedGridGate_seed x a c M hM hbound i
      (Nat.le_of_lt i.isLt) j,
    protectedGridGate_seed x a c M hM hbound (i + 1)
      (Nat.succ_le_of_lt i.isLt) j]
  have hpre :
      zeroExtend x i j + protectedGridGateCarrier a c M +
          a * (zeroExtend x (i + 1) j + protectedGridGateCarrier a c M) +
          (c - a * protectedGridGateCarrier a c M) =
        zeroExtend x i j + a * zeroExtend x (i + 1) j +
          (protectedGridGateCarrier a c M + c) := by
    ring
  rw [hpre, relu_of_nonneg]
  · simp [southTriangularCode]
  · have hxi := abs_zeroExtend_le_grid_bound x M hM hbound i j
    have hxilower := neg_abs_le (zeroExtend x i j)
    have hxnext := abs_zeroExtend_le_grid_bound x M hM hbound (i + 1) j
    have hanext :
        -(|a| * M) ≤ a * zeroExtend x (i + 1) j := by
      calc
        -(|a| * M) ≤ -|a * zeroExtend x (i + 1) j| := by
          rw [abs_mul]
          exact neg_le_neg
            (mul_le_mul_of_nonneg_left hxnext (abs_nonneg a))
        _ ≤ a * zeroExtend x (i + 1) j := neg_abs_le _
    have hc : 0 ≤ |c| + c := by
      linarith [neg_le_abs c]
    have hcarrierExpand : (1 + |a|) * M = M + |a| * M := by
      ring
    dsimp [protectedGridGateCarrier]
    rw [hcarrierExpand]
    linarith

/-- The south-triangular backup code is injective for every real coefficient
`a` and offset `C`.  The proof solves rows backward from the zero boundary. -/
theorem southTriangularCode_injective {rows cols : ℕ} (a C : ℝ) :
    Function.Injective
      (southTriangularCode (rows := rows) (cols := cols) a C) := by
  intro x y hxy
  funext i j
  have hcode (k : ℕ) (hk : k < rows) :
      zeroExtend x k j + a * zeroExtend x (k + 1) j + C =
        zeroExtend y k j + a * zeroExtend y (k + 1) j + C := by
    have hentry := congrFun (congrFun hxy ⟨k, hk⟩) j
    simpa [southTriangularCode, zeroExtend_of_lt _ hk j.isLt] using hentry
  have hsuffix : ∀ k : ℕ, k ≤ rows →
      ∀ t : ℕ, k ≤ t → t < rows →
        zeroExtend x t j = zeroExtend y t j := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
        intro t hrows hlt
        omega
    | of_succ k hk ih =>
        intro t hkt ht
        by_cases htk : t = k
        · subst t
          have heq := hcode k hk
          have hnext :
              zeroExtend x (k + 1) j = zeroExtend y (k + 1) j := by
            by_cases hnextRows : k + 1 < rows
            · exact ih (k + 1) le_rfl hnextRows
            · have hout : rows ≤ k + 1 := Nat.le_of_not_gt hnextRows
              rw [zeroExtend_row_outside x hout,
                zeroExtend_row_outside y hout]
          rw [hnext] at heq
          linarith
        · exact ih t (by omega) ht
  have hi := hsuffix 0 (Nat.zero_le rows) i (Nat.zero_le i) i.isLt
  simpa using hi

/-- The full two-layer representation remains injective on every uniformly
bounded injective image family. -/
theorem protectedGridGateNetwork_injectiveOn
    {X : Type u} {K : Set X} {rows cols : ℕ}
    (F : X → Image rows cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ∀ i j, |F x i j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedGridGateNetwork (rows := rows) (cols := cols)
        a c M).eval (F x)) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  apply southTriangularCode_injective a
    (protectedGridGateCarrier a c M + c)
  funext i j
  rw [← protectedGridGateNetwork_backup
      (F x) a c M hM (hbound x hx) i j,
    ← protectedGridGateNetwork_backup
      (F y) a c M hM (hbound y hy) i j]
  exact congrArg (fun z ↦ zeroExtend z (i + 1) j) heval

/-- Compactness chooses one carrier for a continuous finite image family.
The resulting depth-two network gates the whole northern row, exposes an
exact triangular backup of every input row, and preserves injectivity. -/
theorem exists_protectedGridGateNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (a c : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2),
        net.net.depth = 2 ∧
        (∀ x ∈ K,
          (∀ j : Fin cols,
            zeroExtend (net.eval (F x)) 0 j =
              relu (a * zeroExtend (F x) 0 j + c)) ∧
          ∀ i : Fin rows, ∀ j : Fin cols,
            zeroExtend (net.eval (F x)) (i + 1) j =
              southTriangularCode a
                (protectedGridGateCarrier a c M + c) (F x) i j) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_feature_margin hK F hF 0
  refine ⟨M, hM, protectedGridGateNetwork a c M,
    protectedGridGateNetwork_depth a c M, ?_, ?_⟩
  · intro x hx
    have hxbound : ∀ i j, |F x i j| ≤ M := fun i j ↦ by
      have := hbound x hx i j
      simpa using this.le
    exact ⟨fun j ↦ protectedGridGateNetwork_gate
        (F x) a c M hM.le hxbound j,
      fun i j ↦ protectedGridGateNetwork_backup
        (F x) a c M hM.le hxbound i j⟩
  · exact protectedGridGateNetwork_injectiveOn
      F a c M hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      hFinjective

end OneChannelCNNUniversality
