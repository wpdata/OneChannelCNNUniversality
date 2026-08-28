import OneChannelCNNUniversality.SharedBiasCausality
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear recovery after Pascal transport

The zero-bias Pascal stages do not merely preserve distinct inputs.  Their
complete output admits a linear left inverse, so features created before later
Pascal transports remain exactly recoverable by a linear operation.
-/

namespace OneChannelCNNUniversality

/-- Reassemble an image from a function on row-column pairs. -/
def unflattenImageLinearMap (rows cols : ℕ) :
    ((Fin rows × Fin cols) → ℝ) →ₗ[ℝ] Image rows cols where
  toFun z i j := z (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite weight image representing a linear functional on images. -/
noncomputable def linearReadoutWeights {rows cols : ℕ}
    (f : Image rows cols →ₗ[ℝ] ℝ) : Image rows cols :=
  fun i j ↦ (f.comp (unflattenImageLinearMap rows cols))
    (fun ij ↦ if (i, j) = ij then 1 else 0)

/-- Every linear functional on a finite image is exactly a weight-sum
readout. -/
theorem linearReadoutWeights_apply {rows cols : ℕ}
    (f : Image rows cols →ₗ[ℝ] ℝ) (x : Image rows cols) :
    (∑ i, ∑ j, linearReadoutWeights f i j * x i j) = f x := by
  let g := f.comp (unflattenImageLinearMap rows cols)
  have h := LinearMap.pi_apply_eq_sum_univ g
    (fun ij : Fin rows × Fin cols ↦ x ij.1 ij.2)
  change f x = _ at h
  rw [Fintype.sum_prod_type] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [linearReadoutWeights, g, smul_eq_mul]
  ring

/-- Zero extension commutes with scalar multiplication. -/
theorem zeroExtend_smul {rows cols : ℕ}
    (a : ℝ) (x : Image rows cols) (i j : ℕ) :
    zeroExtend (a • x) i j = a * zeroExtend x i j := by
  by_cases hi : i < rows
  · by_cases hj : j < cols <;> simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

/-- Full convolution commutes with scalar multiplication. -/
theorem fullConvImage_smul {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (a : ℝ) (x : Image rows cols) :
    fullConvImage w (a • x) = a • fullConvImage w x := by
  funext p q
  simp only [fullConvImage, fullConv, Pi.smul_apply, smul_eq_mul]
  simp only [zeroExtend_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  split_ifs
  · ring
  · ring

/-- Every finite full-convolution iteration commutes with scalar
multiplication. -/
theorem iterateFullConv_smul {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (steps : ℕ) (a : ℝ) (x : Image rows cols) :
    iterateFullConv w steps (a • x) = a • iterateFullConv w steps x := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      change iterateFullConv w steps (fullConvImage w (a • x)) =
        a • iterateFullConv w steps (fullConvImage w x)
      rw [fullConvImage_smul, ih]

/-- The horizontal-then-vertical Pascal transport as a linear map. -/
def pascalGridLinearMap {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    Image rows cols →ₗ[ℝ]
      Image
        (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
        (grownSize 2 (grownSize 2 cols colSteps) rowSteps) where
  toFun x :=
    iterateFullConv verticalAccumulationKernel rowSteps
      (iterateFullConv horizontalAccumulationKernel colSteps x)
  map_add' x y := by
    rw [iterateFullConv_add horizontalAccumulationKernel]
    rw [iterateFullConv_add verticalAccumulationKernel]
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [iterateFullConv_smul horizontalAccumulationKernel]
    rw [iterateFullConv_smul verticalAccumulationKernel]

/-- The Pascal transport linear map is injective. -/
theorem pascalGridLinearMap_injective {rows cols : ℕ}
    (rowSteps colSteps : ℕ) :
    Function.Injective
      (pascalGridLinearMap (rows := rows) (cols := cols) rowSteps colSteps) := by
  simpa [pascalGridLinearMap, horizontalPairKernel_two_eq_accumulation,
    verticalPairKernel_two_eq_accumulation] using
      (pascalGridTransform_injective (rows := rows) (cols := cols)
        rowSteps colSteps)

/-- A chosen linear left inverse of the Pascal grid transport. -/
noncomputable def pascalGridLeftInverse {rows cols : ℕ}
    (rowSteps colSteps : ℕ) :
    Image
        (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
        (grownSize 2 (grownSize 2 cols colSteps) rowSteps) →ₗ[ℝ]
      Image rows cols :=
  (pascalGridLinearMap (rows := rows) (cols := cols)
    rowSteps colSteps).leftInverse

/-- Applying the chosen recovery map after Pascal transport returns the
original feature image exactly. -/
theorem pascalGridLeftInverse_apply {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (x : Image rows cols) :
    pascalGridLeftInverse rowSteps colSteps
        (pascalGridLinearMap rowSteps colSteps x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr
    (pascalGridLinearMap_injective rowSteps colSteps)

/-- Coordinate-free existence form of exact linear recovery. -/
theorem exists_pascalGrid_linear_recovery {rows cols : ℕ}
    (rowSteps colSteps : ℕ) :
    ∃ recover :
        Image
            (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
            (grownSize 2 (grownSize 2 cols colSteps) rowSteps) →ₗ[ℝ]
          Image rows cols,
      ∀ x, recover (pascalGridLinearMap rowSteps colSteps x) = x := by
  exact ⟨pascalGridLeftInverse rowSteps colSteps,
    pascalGridLeftInverse_apply rowSteps colSteps⟩

/-- Every original coordinate can be recovered from the transported feature
image by an ordinary finite linear readout. -/
theorem exists_pascalGrid_coordinate_readout {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (i : Fin rows) (j : Fin cols) :
    ∃ weight :
        Image
          (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
          (grownSize 2 (grownSize 2 cols colSteps) rowSteps),
      ∀ x : Image rows cols,
        (∑ p, ∑ q,
          weight p q * pascalGridLinearMap rowSteps colSteps x p q) = x i j := by
  let coordinate : Image rows cols →ₗ[ℝ] ℝ :=
    LinearMap.proj j ∘ₗ LinearMap.proj i
  let recoverCoordinate := coordinate.comp
    (pascalGridLeftInverse rowSteps colSteps)
  refine ⟨linearReadoutWeights recoverCoordinate, ?_⟩
  intro x
  rw [linearReadoutWeights_apply]
  change coordinate
    (pascalGridLeftInverse rowSteps colSteps
      (pascalGridLinearMap rowSteps colSteps x)) = x i j
  rw [pascalGridLeftInverse_apply]
  rfl

/-- On nonnegative feature images, the concrete zero-bias shared-ReLU Pascal
network admits the same exact coordinate readout.  This is the network-level
form used after a ReLU-generated feature has been stored. -/
theorem exists_zeroBiasPascalGridNetwork_coordinate_readout
    {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (i : Fin rows) (j : Fin cols) :
    ∃ weight :
        Image
          (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
          (grownSize 2 (grownSize 2 cols colSteps) rowSteps),
      ∀ x : Image rows cols, ImageNonnegative x →
        (∑ p, ∑ q,
          weight p q *
            (zeroBiasPascalGridNetwork rowSteps colSteps).eval x p q) = x i j := by
  obtain ⟨weight, hweight⟩ :=
    exists_pascalGrid_coordinate_readout rowSteps colSteps i j
  refine ⟨weight, ?_⟩
  intro x hx
  rw [zeroBiasPascalGridNetwork_eval_of_nonnegative
    rowSteps colSteps x hx]
  simpa [pascalGridLinearMap] using hweight x

end OneChannelCNNUniversality
