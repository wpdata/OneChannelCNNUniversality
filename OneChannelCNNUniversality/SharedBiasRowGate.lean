import OneChannelCNNUniversality.SharedBiasSignedGate

/-!
# A protected signed ReLU gate for an entire register row

The scalar gate extends to every finite one-row state.  The first genuine
shared-bias layer embeds the row with a uniform positive carrier.  The second
layer applies `relu (a * x + c)` pointwise along its northern boundary while
its next row is an affine copy of the complete input.  Subtracting one known
constant therefore recovers every register exactly.
-/

namespace OneChannelCNNUniversality

universe u

/-- A vertical two-tap kernel.  Its northern tap has arbitrary signed weight
`a`; its southern tap copies the predecessor with coefficient one. -/
def protectedRowGateKernel (a : ℝ) : Kernel 2 2 :=
  twoTapKernel (1 : Fin 2) (0 : Fin 2)
    (0 : Fin 2) (0 : Fin 2) a

/-- Two genuine shared-bias layers acting on a finite register row.  Set
`B = M + |c|`.  The first layer is the expansive identity with bias `B`;
the second uses bias `c - aB`, so the carrier cancels on the northern gate
row but leaves the recoverable row equal to `x + B + c`. -/
def protectedRowGateNetwork {cols : ℕ} (a c M : ℝ) :
    SharedBiasNetworkTo 2 2 1 cols 3 (cols + 2) :=
  SharedBiasNetworkTo.cons expansiveIdentityKernel (M + |c|)
    (SharedBiasNetworkTo.single (protectedRowGateKernel a)
      (c - a * (M + |c|)))

theorem protectedRowGateNetwork_depth {cols : ℕ} (a c M : ℝ) :
    (protectedRowGateNetwork (cols := cols) a c M).net.depth = 2 := by
  rfl

private theorem protectedRowGate_seed_top
    {cols : ℕ} (x : Image 1 cols) (c M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (j : Fin cols) :
    zeroExtend
        (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 0 j =
      x 0 j + (M + |c|) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu (fullConv expansiveIdentityKernel x 0 j + (M + |c|)) = _
  have hconv : fullConv expansiveIdentityKernel x 0 j = x 0 j := by
    simpa using fullConv_expansiveIdentityKernel_original
      x (0 : Fin 1) j
  rw [hconv, relu_of_nonneg]
  have hxlower := neg_abs_le (x 0 j)
  have hxbound := hbound j
  linarith [abs_nonneg c]

private theorem protectedRowGate_seed_south
    {cols : ℕ} (x : Image 1 cols) (c M : ℝ) (hM : 0 ≤ M)
    (j : Fin cols) :
    zeroExtend
        (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 1 j =
      M + |c| := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu (fullConv expansiveIdentityKernel x 1 j + (M + |c|)) = _
  rw [fullConv_expansiveIdentityKernel_nat,
    zeroExtend_row_outside _ (by omega)]
  simpa using relu_of_nonneg (add_nonneg hM (abs_nonneg c))

/-- Every northern output register computes the requested signed affine
ReLU with the same coefficients `a,c`. -/
theorem protectedRowGateNetwork_gate
    {cols : ℕ} (x : Image 1 cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (j : Fin cols) :
    zeroExtend ((protectedRowGateNetwork (cols := cols) a c M).eval x)
        0 j = relu (a * x 0 j + c) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 0 j +
        (c - a * (M + |c|))) = _
  have hconv :
      fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 0 j =
        a * zeroExtend
          (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 0 j := by
    rw [protectedRowGateKernel, fullConv_twoTapKernel]
    simp
  rw [hconv]
  rw [protectedRowGate_seed_top x c M hM hbound j]
  congr 1
  ring

/-- The row immediately below the gates retains every signed input register
up to one known additive constant. -/
theorem protectedRowGateNetwork_recover
    {cols : ℕ} (x : Image 1 cols) (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |x 0 j| ≤ M) (j : Fin cols) :
    zeroExtend ((protectedRowGateNetwork (cols := cols) a c M).eval x)
        1 j - (M + |c| + c) = x 0 j := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 1 j +
        (c - a * (M + |c|))) - (M + |c| + c) = _
  have hconv :
      fullConv (protectedRowGateKernel a)
          (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 1 j =
        zeroExtend
            (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 0 j +
          a * zeroExtend
            (sharedLayerEval expansiveIdentityKernel (M + |c|) x) 1 j := by
    rw [protectedRowGateKernel, fullConv_twoTapKernel]
    simp
  rw [hconv]
  rw [protectedRowGate_seed_top x c M hM hbound j,
    protectedRowGate_seed_south x c M hM j]
  have hpre :
      x 0 j + (M + |c|) + a * (M + |c|) +
          (c - a * (M + |c|)) = x 0 j + (M + |c|) + c := by
    ring
  rw [hpre, relu_of_nonneg]
  · ring
  · have hxlower := neg_abs_le (x 0 j)
    have hxbound := hbound j
    linarith [neg_le_abs c]

/-- Because the complete input row has an exact coordinate decoder, the
two-layer nonlinear representation is injective on every uniformly bounded
injective family. -/
theorem protectedRowGateNetwork_injectiveOn
    {X : Type u} {K : Set X} {cols : ℕ} (F : X → Image 1 cols)
    (a c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K, ∀ j, |F x 0 j| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedRowGateNetwork (cols := cols) a c M).eval (F x))
      K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  funext i j
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rw [← protectedRowGateNetwork_recover
      (F x) a c M hM (hbound x hx) j,
    ← protectedRowGateNetwork_recover
      (F y) a c M hM (hbound y hy) j]
  exact congrArg
    (fun z ↦ zeroExtend z 1 j - (M + |c| + c)) heval

/-- Compactness supplies one carrier margin for every coordinate in a
continuous finite row family.  The resulting depth-two network computes all
pointwise signed gates, decodes the full input row, and preserves injectivity. -/
theorem exists_protectedRowGateNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {cols : ℕ} (F : X → Image 1 cols) (hF : ContinuousFeatureOn K F)
    (hFinjective : Set.InjOn F K) (a c : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 cols 3 (cols + 2),
        net.net.depth = 2 ∧
        (∀ x ∈ K, ∀ j : Fin cols,
          zeroExtend (net.eval (F x)) 0 j = relu (a * F x 0 j + c) ∧
            zeroExtend (net.eval (F x)) 1 j - (M + |c| + c) =
              F x 0 j) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_feature_margin hK F hF 0
  refine ⟨M, hM, protectedRowGateNetwork a c M,
    protectedRowGateNetwork_depth a c M, ?_, ?_⟩
  · intro x hx j
    have hxbound : |F x 0 j| ≤ M := by
      have := hbound x hx 0 j
      simpa using this.le
    exact ⟨protectedRowGateNetwork_gate
        (F x) a c M hM.le (fun j ↦ by
          have := hbound x hx 0 j
          simpa using this.le) j,
      protectedRowGateNetwork_recover
        (F x) a c M hM.le (fun j ↦ by
          have := hbound x hx 0 j
          simpa using this.le) j⟩
  · exact protectedRowGateNetwork_injectiveOn F a c M hM.le
      (fun x hx j ↦ by
        have := hbound x hx 0 j
        simpa using this.le)
      hFinjective

end OneChannelCNNUniversality
