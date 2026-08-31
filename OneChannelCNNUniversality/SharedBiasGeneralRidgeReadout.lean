import OneChannelCNNUniversality.SharedBiasGeneralRidgeNetwork
import OneChannelCNNUniversality.SharedBiasAdjacentLattice

/-!
# Terminal min/max readouts for arbitrary-width shared-bias ridge networks

The protected general-ridge network exposes two complementary pieces of
information: its northern row is a fixed affine translate of an injective
linear encoding of the whole input, while its southern target is one chosen
affine ReLU ridge.  A linear left inverse of the northern encoding therefore
recovers every input affine functional by an ordinary finite affine readout.

Given

\[
 A(x)=\sum_j a_jx_j+\alpha,
 \qquad
 B(x)=\sum_j b_jx_j+\beta,
\]

we choose the terminal ridge to be

\[
 \mathrm{ReLU}(A(x)-B(x)).
\]

Combining that coordinate with recovered affine values gives

\[
 \min(A,B)=A-\mathrm{ReLU}(A-B),\qquad
 \max(A,B)=B+\mathrm{ReLU}(A-B).
\]

This is terminal-readout expressivity.  The selected left inverse and
generally nonlocal affine readout are not convolutional hidden layers, so this
result does not compile iterated lattice expressions back into the hidden
state.
-/

namespace OneChannelCNNUniversality

private theorem readout_fullConvImage_add
    {kRows kCols rows cols : ℕ} (kernel : Kernel kRows kCols)
    (x y : Image rows cols) :
    fullConvImage kernel (x + y) =
      fullConvImage kernel x + fullConvImage kernel y := by
  funext p q
  exact fullConv_add kernel x y p q

private theorem readout_fullConvChain_add
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (x y : Image rows cols) :
    fullConvChain fs (x + y) =
      fullConvChain fs x + fullConvChain fs y := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (x + y)) = _
      rw [readout_fullConvImage_add, ih]
      rfl

private theorem readout_fullConvChain_smul
    (fs : List BilinearKernelFactor) {rows cols : ℕ}
    (c : ℝ) (x : Image rows cols) :
    fullConvChain fs (c • x) = c • fullConvChain fs x := by
  induction fs generalizing rows cols with
  | nil => rfl
  | cons f fs ih =>
      change fullConvChain fs (fullConvImage f.kernel (c • x)) = _
      rw [fullConvImage_smul, ih]
      rfl

/-- The pure complete northern row, normalized to its explicit width
`2d+1`, as a linear map of the input row. -/
noncomputable def generalRidgeNormalizedNorthLinearMap {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Image 1 (d + 1) →ₗ[ℝ] (Fin (2 * d + 1) → ℝ) where
  toFun x q := zeroExtend (generalRidgeFullConv w η x) 0 q
  map_add' x y := by
    funext q
    rw [generalRidgeFullConv, readout_fullConvChain_add]
    exact zeroExtend_add _ _ 0 q
  map_smul' c x := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [generalRidgeFullConv, readout_fullConvChain_smul,
      zeroExtend_smul]
    rfl

/-- The normalized northern linear encoding is injective for every ridge
weight vector and every lower-factor allocation. -/
theorem generalRidgeNormalizedNorthLinearMap_injective {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Function.Injective (generalRidgeNormalizedNorthLinearMap w η) := by
  intro x y hxy
  apply generalRidgeFullConv_north_eq_imp_eq w η
  intro q
  have hcols : grownSize 2 (d + 1) d = 2 * d + 1 := by
    rw [grownSize_two_eq_add]
    omega
  let q' : Fin (2 * d + 1) := Fin.cast hcols q
  have hq := congrFun hxy q'
  change zeroExtend (generalRidgeFullConv w η x) 0 q' =
    zeroExtend (generalRidgeFullConv w η y) 0 q' at hq
  simpa [generalRidgeFullConvNorthRow_apply, q'] using hq

/-- A chosen linear left inverse of the normalized northern encoding. -/
noncomputable def generalRidgeNormalizedNorthLeftInverse {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    (Fin (2 * d + 1) → ℝ) →ₗ[ℝ] Image 1 (d + 1) :=
  (generalRidgeNormalizedNorthLinearMap w η).leftInverse

/-- The chosen northern inverse recovers every input row exactly. -/
theorem generalRidgeNormalizedNorthLeftInverse_apply {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) :
    generalRidgeNormalizedNorthLeftInverse w η
        (generalRidgeNormalizedNorthLinearMap w η x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr
    (generalRidgeNormalizedNorthLinearMap_injective w η)

/-- Linear part of an arbitrary affine functional on a one-row input. -/
def generalRidgeAffineInputLinearMap {d : ℕ}
    (a : Fin (d + 1) → ℝ) : Image 1 (d + 1) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, a j * x 0 j
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- Projection of a full normalized output image onto its northern row. -/
def generalRidgeNorthProjection (d : ℕ) :
    Image (d + 1) (2 * d + 1) →ₗ[ℝ] (Fin (2 * d + 1) → ℝ) where
  toFun z q := z ⟨0, by omega⟩ q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear functional on the full network output that recovers an arbitrary
input linear functional from the northern row. -/
noncomputable def generalRidgeAffineRecoveryLinearMap {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) :
    Image (d + 1) (2 * d + 1) →ₗ[ℝ] ℝ :=
  (generalRidgeAffineInputLinearMap a).comp
    ((generalRidgeNormalizedNorthLeftInverse w η).comp
      (generalRidgeNorthProjection d))

/-- Finite ordinary output weights for recovery of an input affine
functional. -/
noncomputable def generalRidgeAffineReadoutWeight {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) : Image (d + 1) (2 * d + 1) :=
  linearReadoutWeights (generalRidgeAffineRecoveryLinearMap w η a)

/-- Constant correction for the fixed northern carrier offset. -/
noncomputable def generalRidgeAffineReadoutConstant {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) (alpha : ℝ)
    (offset : Image (d + 1) (2 * d + 1)) : ℝ :=
  alpha - generalRidgeAffineInputLinearMap a
    (generalRidgeNormalizedNorthLeftInverse w η
      (generalRidgeNorthProjection d offset))

/-- Any output whose northern row is the pure encoding plus a fixed offset
admits an exact finite affine readout for every input affine functional. -/
theorem generalRidgeAffineReadout_spec {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) (alpha : ℝ)
    (offset z : Image (d + 1) (2 * d + 1))
    (x : Image 1 (d + 1))
    (hnorth : ∀ q : Fin (2 * d + 1),
      z ⟨0, by omega⟩ q =
        generalRidgeNormalizedNorthLinearMap w η x q +
          offset ⟨0, by omega⟩ q) :
    (∑ p, ∑ q, generalRidgeAffineReadoutWeight w η a p q * z p q) +
        generalRidgeAffineReadoutConstant w η a alpha offset =
      (∑ j, a j * x 0 j) + alpha := by
  rw [generalRidgeAffineReadoutWeight, linearReadoutWeights_apply]
  have hprojection :
      generalRidgeNorthProjection d z =
        generalRidgeNormalizedNorthLinearMap w η x +
          generalRidgeNorthProjection d offset := by
    funext q
    exact hnorth q
  change generalRidgeAffineInputLinearMap a
      (generalRidgeNormalizedNorthLeftInverse w η
        (generalRidgeNorthProjection d z)) +
      (alpha - generalRidgeAffineInputLinearMap a
        (generalRidgeNormalizedNorthLeftInverse w η
          (generalRidgeNorthProjection d offset))) = _
  rw [hprojection, map_add, generalRidgeNormalizedNorthLeftInverse_apply,
    map_add]
  change
    ((∑ j, a j * x 0 j) +
        generalRidgeAffineInputLinearMap a
          (generalRidgeNormalizedNorthLeftInverse w η
            (generalRidgeNorthProjection d offset))) +
      (alpha - generalRidgeAffineInputLinearMap a
        (generalRidgeNormalizedNorthLeftInverse w η
          (generalRidgeNorthProjection d offset))) = _
  ring

/-- Linear functional extracting the protected southern ridge coordinate. -/
def generalRidgeTargetLinearMap {d : ℕ} (hd : 2 ≤ d) :
    Image (d + 1) (2 * d + 1) →ₗ[ℝ] ℝ where
  toFun z := z ⟨1, by omega⟩ ⟨d, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear part of the terminal minimum readout. -/
noncomputable def generalRidgeMinLinearMap {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) :
    Image (d + 1) (2 * d + 1) →ₗ[ℝ] ℝ :=
  generalRidgeAffineRecoveryLinearMap w η a -
    generalRidgeTargetLinearMap hd

/-- Linear part of the terminal maximum readout. -/
noncomputable def generalRidgeMaxLinearMap {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (b : Fin (d + 1) → ℝ) :
    Image (d + 1) (2 * d + 1) →ₗ[ℝ] ℝ :=
  generalRidgeAffineRecoveryLinearMap w η b +
    generalRidgeTargetLinearMap hd

/-- Ordinary finite weights for the terminal minimum readout. -/
noncomputable def generalRidgeMinReadoutWeight {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (a : Fin (d + 1) → ℝ) : Image (d + 1) (2 * d + 1) :=
  linearReadoutWeights (generalRidgeMinLinearMap hd w η a)

/-- Ordinary finite weights for the terminal maximum readout. -/
noncomputable def generalRidgeMaxReadoutWeight {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (b : Fin (d + 1) → ℝ) : Image (d + 1) (2 * d + 1) :=
  linearReadoutWeights (generalRidgeMaxLinearMap hd w η b)

/-- On a compact continuous feature family, one genuine arbitrary-width
shared-bias network has ordinary affine readouts exactly realizing the
minimum and maximum of any two prescribed input affine functions. -/
theorem exists_generalRidgeMinMaxReadouts_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 3))
    (hF : ContinuousFeatureOn K F)
    (a : Fin (n + 3) → ℝ) (alpha : ℝ)
    (b : Fin (n + 3) → ℝ) (beta : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 (n + 3)
          (n + 3) (2 * (n + 2) + 1)),
      net.net.depth = n + 2 ∧
        ∃ minWeight maxWeight : Image (n + 3) (2 * (n + 2) + 1),
          ∃ minConstant maxConstant : ℝ,
            (∀ x ∈ K,
              (∑ p, ∑ q, minWeight p q * net.eval (F x) p q) +
                  minConstant =
                min ((∑ j, a j * F x 0 j) + alpha)
                  ((∑ j, b j * F x 0 j) + beta)) ∧
            (∀ x ∈ K,
              (∑ p, ∑ q, maxWeight p q * net.eval (F x) p q) +
                  maxConstant =
                max ((∑ j, a j * F x 0 j) + alpha)
                  ((∑ j, b j * F x 0 j) + beta)) := by
  let d := n + 2
  let hd : 2 ≤ d := by omega
  let w : Fin (n + 3) → ℝ := fun j ↦ a j - b j
  let gamma : ℝ := alpha - beta
  let η : Fin d → ℝ := generalRidgeSeparatedAllocation hd w
  obtain ⟨net, offset, hdepth, hbehavior⟩ :=
    exists_protectedGeneralRidgeNetwork_behavior_on_compact
      (n := n) hK F hF w gamma
  let minWeight : Image (n + 3) (2 * (n + 2) + 1) :=
    generalRidgeMinReadoutWeight hd w η a
  let maxWeight : Image (n + 3) (2 * (n + 2) + 1) :=
    generalRidgeMaxReadoutWeight hd w η b
  let minConstant : ℝ :=
    generalRidgeAffineReadoutConstant w η a alpha offset
  let maxConstant : ℝ :=
    generalRidgeAffineReadoutConstant w η b beta offset
  refine ⟨net, hdepth, minWeight, maxWeight, minConstant, maxConstant,
    ?_, ?_⟩
  · intro x hx
    let z := net.eval (F x)
    have hnorth : ∀ q : Fin (2 * d + 1),
        z ⟨0, by omega⟩ q =
          generalRidgeNormalizedNorthLinearMap w η (F x) q +
            offset ⟨0, by omega⟩ q := by
      intro q
      have hq := (hbehavior x hx).2 q
      simpa [z, d, generalRidgeNormalizedNorthLinearMap, zeroExtend,
        q.isLt] using hq
    have hrecover := generalRidgeAffineReadout_spec
      w η a alpha offset z (F x) hnorth
    have hrecover' :
        generalRidgeAffineRecoveryLinearMap w η a z + minConstant =
          (∑ j, a j * F x 0 j) + alpha := by
      simpa [generalRidgeAffineReadoutWeight, minConstant,
        linearReadoutWeights_apply] using hrecover
    have htarget : generalRidgeTargetLinearMap hd z =
        relu (((∑ j, a j * F x 0 j) + alpha) -
          ((∑ j, b j * F x 0 j) + beta)) := by
      have ht := (hbehavior x hx).1
      have harg :
          (∑ j : Fin (n + 3), w j * F x 0 j) + gamma =
            ((∑ j, a j * F x 0 j) + alpha) -
              ((∑ j, b j * F x 0 j) + beta) := by
        simp_rw [w, sub_mul]
        rw [Finset.sum_sub_distrib]
        simp [gamma]
        ring
      rw [harg] at ht
      simpa [z, d, generalRidgeTargetLinearMap, zeroExtend] using ht
    change
      (∑ p, ∑ q, generalRidgeMinReadoutWeight hd w η a p q * z p q) +
          minConstant = _
    rw [generalRidgeMinReadoutWeight, linearReadoutWeights_apply]
    simp only [generalRidgeMinLinearMap, LinearMap.sub_apply]
    calc
      generalRidgeAffineRecoveryLinearMap w η a z -
            generalRidgeTargetLinearMap hd z + minConstant =
          (generalRidgeAffineRecoveryLinearMap w η a z + minConstant) -
            generalRidgeTargetLinearMap hd z := by ring
      _ = ((∑ j, a j * F x 0 j) + alpha) -
          relu (((∑ j, a j * F x 0 j) + alpha) -
            ((∑ j, b j * F x 0 j) + beta)) := by
        rw [hrecover', htarget]
      _ = min ((∑ j, a j * F x 0 j) + alpha)
          ((∑ j, b j * F x 0 j) + beta) :=
        sub_relu_sub_eq_min _ _
  · intro x hx
    let z := net.eval (F x)
    have hnorth : ∀ q : Fin (2 * d + 1),
        z ⟨0, by omega⟩ q =
          generalRidgeNormalizedNorthLinearMap w η (F x) q +
            offset ⟨0, by omega⟩ q := by
      intro q
      have hq := (hbehavior x hx).2 q
      simpa [z, d, generalRidgeNormalizedNorthLinearMap, zeroExtend,
        q.isLt] using hq
    have hrecover := generalRidgeAffineReadout_spec
      w η b beta offset z (F x) hnorth
    have hrecover' :
        generalRidgeAffineRecoveryLinearMap w η b z + maxConstant =
          (∑ j, b j * F x 0 j) + beta := by
      simpa [generalRidgeAffineReadoutWeight, maxConstant,
        linearReadoutWeights_apply] using hrecover
    have htarget : generalRidgeTargetLinearMap hd z =
        relu (((∑ j, a j * F x 0 j) + alpha) -
          ((∑ j, b j * F x 0 j) + beta)) := by
      have ht := (hbehavior x hx).1
      have harg :
          (∑ j : Fin (n + 3), w j * F x 0 j) + gamma =
            ((∑ j, a j * F x 0 j) + alpha) -
              ((∑ j, b j * F x 0 j) + beta) := by
        simp_rw [w, sub_mul]
        rw [Finset.sum_sub_distrib]
        simp [gamma]
        ring
      rw [harg] at ht
      simpa [z, d, generalRidgeTargetLinearMap, zeroExtend] using ht
    change
      (∑ p, ∑ q, generalRidgeMaxReadoutWeight hd w η b p q * z p q) +
          maxConstant = _
    rw [generalRidgeMaxReadoutWeight, linearReadoutWeights_apply]
    simp only [generalRidgeMaxLinearMap, LinearMap.add_apply]
    calc
      generalRidgeAffineRecoveryLinearMap w η b z +
            generalRidgeTargetLinearMap hd z + maxConstant =
          (generalRidgeAffineRecoveryLinearMap w η b z + maxConstant) +
            generalRidgeTargetLinearMap hd z := by ring
      _ = ((∑ j, b j * F x 0 j) + beta) +
          relu (((∑ j, a j * F x 0 j) + alpha) -
            ((∑ j, b j * F x 0 j) + beta)) := by
        rw [hrecover', htarget]
      _ = max ((∑ j, a j * F x 0 j) + alpha)
          ((∑ j, b j * F x 0 j) + beta) :=
        add_relu_sub_eq_max _ _

end OneChannelCNNUniversality
