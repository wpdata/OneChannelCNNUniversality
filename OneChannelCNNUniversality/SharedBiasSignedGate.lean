import OneChannelCNNUniversality.SharedBiasFrontierAffineRoute

/-!
# A protected signed affine ReLU gate

This module gives the first input-dependent signed gate for the strict
shared-scalar-bias model.  On a bounded scalar input, one genuine layer
creates two redundant nonnegative codes `B + x` and `B - x`.  A second
genuine layer uses one shared scalar bias to compute `relu (a * x + c)` at
one boundary coordinate while retaining two coordinates whose difference
recovers `x` exactly.
-/

namespace OneChannelCNNUniversality

universe u

/-- Regard one real number as a `1 × 1` input image. -/
def scalarImage (x : ℝ) : Image 1 1 := fun _ _ ↦ x

/-- Four signed copies of a scalar: the left column has coefficient `+1`
and the right column coefficient `-1`, in both rows. -/
def signedPairKernel : Kernel 2 2 :=
  fun _ q ↦ if (q : ℕ) = 0 then 1 else -1

/-- The top row combines `B+x` and `B-x` into `a*x`; the lower-left tap
copies the redundant pair to the southern boundary. -/
noncomputable def protectedAffineGateKernel (a : ℝ) : Kernel 2 2 :=
  fun p q ↦
    if (p : ℕ) = 0 then
      if (q : ℕ) = 0 then -(a / 2) else a / 2
    else
      if (q : ℕ) = 0 then 1 else 0

/-- Two genuine `2 × 2`, one-channel, shared-bias ReLU layers.  The first
bias is large enough to linearize the signed encoding on `|x| ≤ M`; the
second layer's unique scalar bias is the desired affine offset `c`. -/
noncomputable def protectedSignedGateNetwork (a c M : ℝ) :
    SharedBiasNetworkTo 2 2 1 1 3 3 :=
  SharedBiasNetworkTo.cons signedPairKernel (M + |c|)
    (SharedBiasNetworkTo.single (protectedAffineGateKernel a) c)

theorem protectedSignedGateNetwork_depth (a c M : ℝ) :
    (protectedSignedGateNetwork a c M).net.depth = 2 := by
  rfl

private theorem signedPairLayer_value
    (x B : ℝ) (p q : Fin 2) :
    sharedLayerEval signedPairKernel B (scalarImage x) p q =
      relu ((if (q : ℕ) = 0 then x else -x) + B) := by
  fin_cases p <;> fin_cases q <;>
    simp [sharedLayerEval, layerEval, fullConv, signedPairKernel,
      scalarImage, constantImage]

private theorem signedPairLayer_linear
    (x c M : ℝ) (_hM : 0 ≤ M) (hx : |x| ≤ M)
    (p q : Fin 2) :
    sharedLayerEval signedPairKernel (M + |c|) (scalarImage x) p q =
      (if (q : ℕ) = 0 then x else -x) + (M + |c|) := by
  rw [signedPairLayer_value]
  apply relu_of_nonneg
  have hxle : x ≤ M := le_trans (le_abs_self x) hx
  have hnegxle : -x ≤ M := le_trans (neg_le_abs x) hx
  split_ifs <;> linarith [abs_nonneg c]

/-- The northern interior coordinate is the requested signed affine ReLU. -/
theorem protectedSignedGateNetwork_gate
    (a c M : ℝ) (hM : 0 ≤ M) (x : ℝ) (hx : |x| ≤ M) :
    zeroExtend
        ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 0 1 =
      relu (a * x + c) := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAffineGateKernel a)
          (sharedLayerEval signedPairKernel (M + |c|) (scalarImage x))
          0 1 + c) = _
  simp only [fullConv]
  simp [protectedAffineGateKernel,
    signedPairLayer_linear x c M hM hx]
  congr 1
  ring

/-- The first southern code remains affine and nonnegative. -/
theorem protectedSignedGateNetwork_code_left
    (a c M : ℝ) (hM : 0 ≤ M) (x : ℝ) (hx : |x| ≤ M) :
    zeroExtend
        ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 0 =
      M + |c| + x + c := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAffineGateKernel a)
          (sharedLayerEval signedPairKernel (M + |c|) (scalarImage x))
          2 0 + c) = _
  have hpre :
      fullConv (protectedAffineGateKernel a)
          (sharedLayerEval signedPairKernel (M + |c|) (scalarImage x))
          2 0 + c = M + |c| + x + c := by
    simp [fullConv, protectedAffineGateKernel,
      signedPairLayer_linear x c M hM hx]
    ring
  rw [hpre, relu_of_nonneg]
  have hxle : -M ≤ x := by
    have := neg_abs_le x
    linarith
  linarith [neg_le_abs c]

/-- The second southern code remains affine and nonnegative. -/
theorem protectedSignedGateNetwork_code_right
    (a c M : ℝ) (hM : 0 ≤ M) (x : ℝ) (hx : |x| ≤ M) :
    zeroExtend
        ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 1 =
      M + |c| - x + c := by
  rw [zeroExtend_of_lt _ (by omega) (by omega)]
  change relu
      (fullConv (protectedAffineGateKernel a)
          (sharedLayerEval signedPairKernel (M + |c|) (scalarImage x))
          2 1 + c) = _
  have hpre :
      fullConv (protectedAffineGateKernel a)
          (sharedLayerEval signedPairKernel (M + |c|) (scalarImage x))
          2 1 + c = M + |c| - x + c := by
    simp [fullConv, protectedAffineGateKernel,
      signedPairLayer_linear x c M hM hx]
    ring
  rw [hpre, relu_of_nonneg]
  have hxle : x ≤ M := le_trans (le_abs_self x) hx
  linarith [neg_le_abs c]

/-- The two protected southern coordinates recover the signed input exactly. -/
theorem protectedSignedGateNetwork_recover
    (a c M : ℝ) (hM : 0 ≤ M) (x : ℝ) (hx : |x| ≤ M) :
    (zeroExtend
          ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 0 -
        zeroExtend
          ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 1) /
        2 = x := by
  rw [protectedSignedGateNetwork_code_left a c M hM x hx,
    protectedSignedGateNetwork_code_right a c M hM x hx]
  ring

/-- The complete two-layer representation is injective on every bounded
scalar family, even though one coordinate has undergone the selected ReLU. -/
theorem protectedSignedGateNetwork_injectiveOn
    {X : Type u} {K : Set X} (F : X → ℝ) (a c M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ K, |F x| ≤ M)
    (hFinjective : Set.InjOn F K) :
    Set.InjOn
      (fun x ↦ (protectedSignedGateNetwork a c M).eval
        (scalarImage (F x))) K := by
  intro x hx y hy heval
  apply hFinjective hx hy
  rw [← protectedSignedGateNetwork_recover a c M hM (F x) (hbound x hx),
    ← protectedSignedGateNetwork_recover a c M hM (F y) (hbound y hy)]
  exact congrArg
    (fun z ↦ (zeroExtend z 2 0 - zeroExtend z 2 1) / 2) heval

/-- Compactness automatically supplies one encoding margin for a whole
continuous scalar family.  The resulting depth-two genuine shared-bias CNN
simultaneously computes the requested signed affine ReLU, retains an exact
linear decoder for the input, and is injective whenever the incoming scalar
representation is injective. -/
theorem exists_protectedSignedGateNetwork_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (F : X → ℝ) (hF : ContinuousOn F K) (hFinjective : Set.InjOn F K)
    (a c : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 1 1 3 3,
        net.net.depth = 2 ∧
        (∀ x ∈ K,
          zeroExtend (net.eval (scalarImage (F x))) 0 1 =
              relu (a * F x + c) ∧
            (zeroExtend (net.eval (scalarImage (F x))) 2 0 -
                zeroExtend (net.eval (scalarImage (F x))) 2 1) / 2 = F x) ∧
        Set.InjOn (fun x ↦ net.eval (scalarImage (F x))) K := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_abs_bound hK F hF
  refine ⟨M, hM, protectedSignedGateNetwork a c M,
    protectedSignedGateNetwork_depth a c M, ?_, ?_⟩
  · intro x hx
    have hxbound : |F x| ≤ M := (hbound x hx).le
    exact ⟨protectedSignedGateNetwork_gate a c M hM.le (F x) hxbound,
      protectedSignedGateNetwork_recover a c M hM.le (F x) hxbound⟩
  · exact protectedSignedGateNetwork_injectiveOn
      F a c M hM.le (fun x hx ↦ (hbound x hx).le) hFinjective

end OneChannelCNNUniversality
