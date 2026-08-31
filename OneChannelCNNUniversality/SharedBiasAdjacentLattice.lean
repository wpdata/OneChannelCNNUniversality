import OneChannelCNNUniversality.SharedBiasAdjacentRidge
import OneChannelCNNUniversality.SharedBiasRecovery
import OneChannelCNNUniversality.LatticeCompiler

/-!
# Affine recovery and terminal adjacent lattice readouts

The southeast backup exposed by `protectedAdjacentRidgeNetwork` is an
injective affine triangular transform of the complete input image.  Its
linear part therefore has a linear left inverse.  Composing that inverse with
the southeast-block projection gives ordinary finite affine readouts for
every original input coordinate.

For the ridge coefficients `alpha = 1`, `beta = -1`, and `gamma = 0`, the
northern gate is `relu (west - current)`.  One affine readout recovers the
current input and adds this gate, while another recovers the western input
and subtracts it.  The same genuine depth-two shared-bias network therefore
realizes both adjacent `max` and adjacent `min`, with different final affine
readouts, and retains its injective complete feature representation.

This is a terminal-readout theorem.  The chosen affine inverse is not a
causal convolutional layer and hence does not by itself compile nested
`min`/`max` expressions back into the northern hidden row.
-/

namespace OneChannelCNNUniversality

universe u

/-- The linear part of the south-triangular adjacent-ridge backup. -/
def adjacentRidgeBackupLinearMap {rows cols : ℕ} (alpha beta : ℝ) :
    Image rows cols →ₗ[ℝ] Image rows cols where
  toFun := adjacentRidgeBackupCode alpha beta 0
  map_add' x y := by
    funext i j
    simp only [adjacentRidgeBackupCode, Pi.add_apply, zeroExtend_add]
    ring
  map_smul' a x := by
    funext i j
    simp only [adjacentRidgeBackupCode, Pi.smul_apply, smul_eq_mul,
      zeroExtend_smul, RingHom.id_apply]
    ring

@[simp] theorem adjacentRidgeBackupLinearMap_apply
    {rows cols : ℕ} (alpha beta : ℝ) (x : Image rows cols)
    (i : Fin rows) (j : Fin cols) :
    adjacentRidgeBackupLinearMap alpha beta x i j =
      x i j + alpha * zeroExtend x (i + 1) j +
        beta * zeroExtend x (i + 1) (j + 1) := by
  simp [adjacentRidgeBackupLinearMap, adjacentRidgeBackupCode]

/-- The backup linear map is injective for arbitrary coefficients. -/
theorem adjacentRidgeBackupLinearMap_injective
    {rows cols : ℕ} (alpha beta : ℝ) :
    Function.Injective
      (adjacentRidgeBackupLinearMap (rows := rows) (cols := cols)
        alpha beta) := by
  exact adjacentRidgeBackupCode_injective alpha beta 0

/-- A chosen linear left inverse of the triangular backup linear map. -/
noncomputable def adjacentRidgeBackupLeftInverse
    {rows cols : ℕ} (alpha beta : ℝ) :
    Image rows cols →ₗ[ℝ] Image rows cols :=
  (adjacentRidgeBackupLinearMap (rows := rows) (cols := cols)
    alpha beta).leftInverse

/-- The chosen inverse exactly recovers every input image. -/
theorem adjacentRidgeBackupLeftInverse_apply
    {rows cols : ℕ} (alpha beta : ℝ) (x : Image rows cols) :
    adjacentRidgeBackupLeftInverse alpha beta
        (adjacentRidgeBackupLinearMap alpha beta x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr
    (adjacentRidgeBackupLinearMap_injective alpha beta)

/-- The affine backup is its linear part plus one constant image. -/
theorem adjacentRidgeBackupCode_eq_linear_add_constant
    {rows cols : ℕ} (alpha beta C : ℝ) (x : Image rows cols) :
    adjacentRidgeBackupCode alpha beta C x =
      adjacentRidgeBackupLinearMap alpha beta x +
        constantImage rows cols C := by
  funext i j
  simp [adjacentRidgeBackupCode, adjacentRidgeBackupLinearMap,
    constantImage]

/-- Extract the southeast-shifted backup rectangle from a depth-two output. -/
def adjacentRidgeBackupProjection (rows cols : ℕ) :
    Image (rows + 2) (cols + 2) →ₗ[ℝ] Image rows cols where
  toFun z i j := z ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear recovery of the whole original image from the shifted output
backup, before correcting the known affine carrier. -/
noncomputable def adjacentRidgeRecoveryLinearMap
    {rows cols : ℕ} (alpha beta : ℝ) :
    Image (rows + 2) (cols + 2) →ₗ[ℝ] Image rows cols :=
  (adjacentRidgeBackupLeftInverse alpha beta).comp
    (adjacentRidgeBackupProjection rows cols)

/-- The linear functional that recovers one input coordinate, before its
known affine carrier correction. -/
noncomputable def adjacentRidgeCoordinateLinearMap
    {rows cols : ℕ} (alpha beta : ℝ)
    (i : Fin rows) (j : Fin cols) :
    Image (rows + 2) (cols + 2) →ₗ[ℝ] ℝ :=
  (LinearMap.proj j ∘ₗ LinearMap.proj i).comp
    (adjacentRidgeRecoveryLinearMap alpha beta)

/-- Finite output weights for recovery of one original coordinate. -/
noncomputable def adjacentRidgeCoordinateReadoutWeight
    {rows cols : ℕ} (alpha beta : ℝ)
    (i : Fin rows) (j : Fin cols) : Image (rows + 2) (cols + 2) :=
  linearReadoutWeights
    (adjacentRidgeCoordinateLinearMap alpha beta i j)

/-- Constant correction for recovery from the affine backup with offset
`C`. -/
noncomputable def adjacentRidgeCoordinateReadoutConstant
    {rows cols : ℕ} (alpha beta C : ℝ)
    (i : Fin rows) (j : Fin cols) : ℝ :=
  -adjacentRidgeBackupLeftInverse alpha beta
      (constantImage rows cols C) i j

/-- At the map level, a protected network output recovers the input plus the
known image contributed by the affine backup carrier. -/
theorem adjacentRidgeRecoveryLinearMap_protected_eval
    {rows cols : ℕ} (x : Image rows cols)
    (alpha beta gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M) :
    adjacentRidgeRecoveryLinearMap alpha beta
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) =
      x + adjacentRidgeBackupLeftInverse alpha beta
        (constantImage rows cols
          (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma)) := by
  let C := protectedAdjacentRidgeCarrier alpha beta gamma M + gamma
  have hprojection :
      adjacentRidgeBackupProjection rows cols
          ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) =
        adjacentRidgeBackupCode alpha beta C x := by
    funext i j
    simp only [adjacentRidgeBackupProjection, LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [← protectedAdjacentRidgeNetwork_backup
      x alpha beta gamma M hM hbound i j]
    rw [zeroExtend_of_lt _ (by omega) (by omega)]
  simp only [adjacentRidgeRecoveryLinearMap, LinearMap.comp_apply]
  rw [hprojection]
  rw [adjacentRidgeBackupCode_eq_linear_add_constant]
  rw [map_add, adjacentRidgeBackupLeftInverse_apply]

/-- Every original coordinate is recovered by an ordinary finite affine
readout of the genuine depth-two network output. -/
theorem protectedAdjacentRidgeNetwork_realize_coordinate
    {rows cols : ℕ} (x : Image rows cols)
    (alpha beta gamma M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M)
    (i : Fin rows) (j : Fin cols) :
    (∑ p, ∑ q,
        adjacentRidgeCoordinateReadoutWeight alpha beta i j p q *
          (protectedAdjacentRidgeNetwork alpha beta gamma M).eval x p q) +
        adjacentRidgeCoordinateReadoutConstant alpha beta
          (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma) i j =
      x i j := by
  rw [adjacentRidgeCoordinateReadoutWeight, linearReadoutWeights_apply]
  change
    adjacentRidgeRecoveryLinearMap alpha beta
          ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) i j -
        adjacentRidgeBackupLeftInverse alpha beta
          (constantImage rows cols
            (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma)) i j =
      x i j
  rw [adjacentRidgeRecoveryLinearMap_protected_eval
    x alpha beta gamma M hM hbound]
  simp

private def outputCoordinateLinearMap
    {rows cols : ℕ} (i : Fin rows) (j : Fin cols) :
    Image rows cols →ₗ[ℝ] ℝ :=
  LinearMap.proj j ∘ₗ LinearMap.proj i

/-- Linear part of the terminal adjacent-min readout. -/
noncomputable def protectedAdjacentMinLinearMap
    {rows cols : ℕ} (hrows : 0 < rows)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    Image (rows + 2) (cols + 2) →ₗ[ℝ] ℝ :=
  adjacentRidgeCoordinateLinearMap (1 : ℝ) (-1 : ℝ)
      (⟨0, hrows⟩ : Fin rows) (⟨(j : ℕ) - 1, by omega⟩ : Fin cols) -
    outputCoordinateLinearMap
      (⟨0, by omega⟩ : Fin (rows + 2))
      (⟨j, by omega⟩ : Fin (cols + 2))

/-- Linear part of the terminal adjacent-max readout. -/
noncomputable def protectedAdjacentMaxLinearMap
    {rows cols : ℕ} (hrows : 0 < rows) (j : Fin cols) :
    Image (rows + 2) (cols + 2) →ₗ[ℝ] ℝ :=
  adjacentRidgeCoordinateLinearMap (1 : ℝ) (-1 : ℝ)
      (⟨0, hrows⟩ : Fin rows) j +
    outputCoordinateLinearMap
      (⟨0, by omega⟩ : Fin (rows + 2))
      (⟨j, by omega⟩ : Fin (cols + 2))

/-- Ordinary finite weights for the adjacent-min terminal readout. -/
noncomputable def protectedAdjacentMinReadoutWeight
    {rows cols : ℕ} (hrows : 0 < rows)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    Image (rows + 2) (cols + 2) :=
  linearReadoutWeights (protectedAdjacentMinLinearMap hrows j hj)

/-- Constant term for the adjacent-min terminal readout. -/
noncomputable def protectedAdjacentMinReadoutConstant
    {rows cols : ℕ} (M : ℝ) (hrows : 0 < rows)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) : ℝ :=
  adjacentRidgeCoordinateReadoutConstant (1 : ℝ) (-1 : ℝ)
    (protectedAdjacentRidgeCarrier 1 (-1) 0 M)
    (⟨0, hrows⟩ : Fin rows) (⟨(j : ℕ) - 1, by omega⟩ : Fin cols)

/-- Ordinary finite weights for the adjacent-max terminal readout. -/
noncomputable def protectedAdjacentMaxReadoutWeight
    {rows cols : ℕ} (hrows : 0 < rows) (j : Fin cols) :
    Image (rows + 2) (cols + 2) :=
  linearReadoutWeights (protectedAdjacentMaxLinearMap hrows j)

/-- Constant term for the adjacent-max terminal readout. -/
noncomputable def protectedAdjacentMaxReadoutConstant
    {rows cols : ℕ} (M : ℝ) (hrows : 0 < rows) (j : Fin cols) : ℝ :=
  adjacentRidgeCoordinateReadoutConstant (1 : ℝ) (-1 : ℝ)
    (protectedAdjacentRidgeCarrier 1 (-1) 0 M)
    (⟨0, hrows⟩ : Fin rows) j

/-- The depth-two adjacent-difference network followed by the min readout is
exact on every bounded input image. -/
theorem protectedAdjacentRidgeNetwork_realize_adjacent_min
    {rows cols : ℕ} (x : Image rows cols) (M : ℝ)
    (hrows : 0 < rows) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    (∑ p, ∑ q,
        protectedAdjacentMinReadoutWeight hrows j hj p q *
          (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
            1 (-1) 0 M).eval x p q) +
        protectedAdjacentMinReadoutConstant M hrows j hj =
      min (zeroExtend x 0 ((j : ℕ) - 1)) (zeroExtend x 0 j) := by
  rw [protectedAdjacentMinReadoutWeight, linearReadoutWeights_apply]
  simp only [protectedAdjacentMinLinearMap, LinearMap.sub_apply,
    adjacentRidgeCoordinateLinearMap, LinearMap.comp_apply,
    outputCoordinateLinearMap, LinearMap.proj_apply,
    protectedAdjacentMinReadoutConstant,
    adjacentRidgeCoordinateReadoutConstant]
  have houtput :
      (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
          1 (-1) 0 M).eval x
          (⟨0, by omega⟩ : Fin (rows + 2))
          (⟨j, by omega⟩ : Fin (cols + 2)) =
        zeroExtend ((protectedAdjacentRidgeNetwork 1 (-1) 0 M).eval x)
          0 j := by
    rw [zeroExtend_of_lt _ (by omega) (by omega)]
  rw [houtput]
  rw [adjacentRidgeRecoveryLinearMap_protected_eval
      x 1 (-1) 0 M hM hbound,
    protectedAdjacentRidgeNetwork_gate x 1 (-1) 0 M hM hbound j hj]
  simp only [Pi.add_apply]
  have hwest :
      x (⟨0, hrows⟩ : Fin rows)
          (⟨(j : ℕ) - 1, by omega⟩ : Fin cols) =
        zeroExtend x 0 ((j : ℕ) - 1) := by
    rw [zeroExtend_of_lt _ hrows (by omega)]
  rw [hwest]
  have hgate :
      relu
          (1 * zeroExtend x 0 ((j : ℕ) - 1) +
            -1 * zeroExtend x 0 j + 0) =
        relu (zeroExtend x 0 ((j : ℕ) - 1) - zeroExtend x 0 j) := by
    congr 1
    ring
  rw [hgate]
  ring_nf
  exact sub_relu_sub_eq_min
    (zeroExtend x 0 ((j : ℕ) - 1)) (zeroExtend x 0 j)

/-- The same depth-two hidden network followed by the max readout is exact
on every bounded input image. -/
theorem protectedAdjacentRidgeNetwork_realize_adjacent_max
    {rows cols : ℕ} (x : Image rows cols) (M : ℝ)
    (hrows : 0 < rows) (hM : 0 ≤ M)
    (hbound : ∀ i j, |x i j| ≤ M)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    (∑ p, ∑ q,
        protectedAdjacentMaxReadoutWeight hrows j p q *
          (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
            1 (-1) 0 M).eval x p q) +
        protectedAdjacentMaxReadoutConstant M hrows j =
      max (zeroExtend x 0 ((j : ℕ) - 1)) (zeroExtend x 0 j) := by
  rw [protectedAdjacentMaxReadoutWeight, linearReadoutWeights_apply]
  simp only [protectedAdjacentMaxLinearMap, LinearMap.add_apply,
    adjacentRidgeCoordinateLinearMap, LinearMap.comp_apply,
    outputCoordinateLinearMap, LinearMap.proj_apply,
    protectedAdjacentMaxReadoutConstant,
    adjacentRidgeCoordinateReadoutConstant]
  have houtput :
      (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
          1 (-1) 0 M).eval x
          (⟨0, by omega⟩ : Fin (rows + 2))
          (⟨j, by omega⟩ : Fin (cols + 2)) =
        zeroExtend ((protectedAdjacentRidgeNetwork 1 (-1) 0 M).eval x)
          0 j := by
    rw [zeroExtend_of_lt _ (by omega) (by omega)]
  rw [houtput]
  rw [adjacentRidgeRecoveryLinearMap_protected_eval
      x 1 (-1) 0 M hM hbound,
    protectedAdjacentRidgeNetwork_gate x 1 (-1) 0 M hM hbound j hj]
  simp only [Pi.add_apply]
  have hcurrent :
      x (⟨0, hrows⟩ : Fin rows) j = zeroExtend x 0 j := by
    rw [zeroExtend_of_lt _ hrows j.isLt]
  rw [hcurrent]
  have hgate :
      relu
          (1 * zeroExtend x 0 ((j : ℕ) - 1) +
            -1 * zeroExtend x 0 j + 0) =
        relu (zeroExtend x 0 ((j : ℕ) - 1) - zeroExtend x 0 j) := by
    congr 1
    ring
  rw [hgate]
  ring_nf
  simpa [sub_eq_add_neg, add_comm] using add_relu_sub_eq_max
    (zeroExtend x 0 ((j : ℕ) - 1)) (zeroExtend x 0 j)

/-- On a compact continuous injective feature family, one genuine depth-two
shared-bias network has two ordinary affine readouts that exactly realize the
chosen adjacent minimum and maximum.  Its complete hidden representation is
still injective on the family. -/
theorem exists_protectedAdjacentLatticeReadouts_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (hrows : 0 < rows)
    (F : X → Image rows cols) (hF : ContinuousFeatureOn K F)
    (hFinjective : Set.InjOn F K)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    ∃ M : ℝ, 0 < M ∧
      ∃ net : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2),
        net.net.depth = 2 ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K ∧
        ∃ minWeight maxWeight : Image (rows + 2) (cols + 2),
          ∃ minConstant maxConstant : ℝ,
            (∀ x ∈ K,
              (∑ p, ∑ q, minWeight p q * net.eval (F x) p q) +
                  minConstant =
                min (zeroExtend (F x) 0 ((j : ℕ) - 1))
                  (zeroExtend (F x) 0 j)) ∧
            (∀ x ∈ K,
              (∑ p, ∑ q, maxWeight p q * net.eval (F x) p q) +
                  maxConstant =
                max (zeroExtend (F x) 0 ((j : ℕ) - 1))
                  (zeroExtend (F x) 0 j)) := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_feature_margin hK F hF 0
  let net : SharedBiasNetworkTo 2 2 rows cols (rows + 2) (cols + 2) :=
    protectedAdjacentRidgeNetwork 1 (-1) 0 M
  refine ⟨M, hM, net, protectedAdjacentRidgeNetwork_depth 1 (-1) 0 M,
    ?_, protectedAdjacentMinReadoutWeight hrows j hj,
    protectedAdjacentMaxReadoutWeight hrows j,
    protectedAdjacentMinReadoutConstant M hrows j hj,
    protectedAdjacentMaxReadoutConstant M hrows j, ?_, ?_⟩
  · exact protectedAdjacentRidgeNetwork_injectiveOn
      F 1 (-1) 0 M hM.le
      (fun x hx i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      hFinjective
  · intro x hx
    exact protectedAdjacentRidgeNetwork_realize_adjacent_min
      (F x) M hrows hM.le
      (fun i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      j hj
  · intro x hx
    exact protectedAdjacentRidgeNetwork_realize_adjacent_max
      (F x) M hrows hM.le
      (fun i j ↦ by
        have := hbound x hx i j
        simpa using this.le)
      j hj

end OneChannelCNNUniversality
