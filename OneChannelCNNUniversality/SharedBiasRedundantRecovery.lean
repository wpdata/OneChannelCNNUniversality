import OneChannelCNNUniversality.SharedBiasProtectionObstruction
import OneChannelCNNUniversality.SharedBiasChainSelection

/-!
# Recovery from an adjacent redundant work register

The global root-protection invariant forces a selected register to be
constant.  This file replaces that invariant by one spatial redundancy
relation on a row chain: columns zero and one store the same mutable value.
The selected ReLU may alter the zero-th Pascal output, while the first
unmodified Pascal output still determines that value.  All remaining input
coordinates are then recovered by injectivity of the full protected Pascal
transport.
-/

namespace OneChannelCNNUniversality

/-- The mutable northwest work register is copied once into its eastern
neighbor.  Zero extension makes the definition total; the recovery theorem
assumes that the chain has at least two columns. -/
def EastRootDuplicate {n : ℕ} (x : Image 1 n) : Prop :=
  zeroExtend x 0 0 = zeroExtend x 0 1

private theorem zeroExtend_iterateHorizontal_zero
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols) (p : ℕ) :
    zeroExtend (iterateFullConv horizontalAccumulationKernel steps x) p 0 =
      zeroExtend x p 0 := by
  rw [← horizontalPairKernel_two_eq_accumulation]
  rw [zeroExtend_iterateFullConv_horizontal
    (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega)]
  rw [← congrFun (iteratePairKernel_eq_iterate steps
    (fun t ↦ zeroExtend x p t)) 0]
  simp [iteratePairKernel_eq_sum_choose]

private theorem zeroExtend_iterateHorizontal_one
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols) (p : ℕ) :
    zeroExtend (iterateFullConv horizontalAccumulationKernel steps x) p 1 =
      zeroExtend x p 1 + (steps : ℝ) * zeroExtend x p 0 := by
  rw [← horizontalPairKernel_two_eq_accumulation]
  rw [zeroExtend_iterateFullConv_horizontal
    (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega)]
  rw [← congrFun (iteratePairKernel_eq_iterate steps
    (fun t ↦ zeroExtend x p t)) 1]
  rw [iteratePairKernel_eq_sum_choose]
  norm_num [Finset.sum_range_succ]
  ring

private theorem zeroExtend_iterateVertical_zero
    {rows cols : ℕ} (steps : ℕ) (x : Image rows cols) (q : ℕ) :
    zeroExtend (iterateFullConv verticalAccumulationKernel steps x) 0 q =
      zeroExtend x 0 q := by
  rw [← verticalPairKernel_two_eq_accumulation]
  rw [zeroExtend_iterateFullConv_vertical
    (show 2 ≤ 2 by omega) (show 2 ≤ 2 by omega)]
  rw [← congrFun (iteratePairKernel_eq_iterate steps
    (fun t ↦ zeroExtend x t q)) 0]
  simp [iteratePairKernel_eq_sum_choose]

/-- The protected Pascal signal at the northwest root is the original work
register, independently of the number of horizontal and vertical steps. -/
theorem protectedLinearizedPascalSignal_rowZero_zero
    {n : ℕ} (hn : 0 < n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨0, hn⟩ : Fin n) =
      x rowZero ⟨0, hn⟩ := by
  unfold protectedLinearizedPascalSignal linearizedPascalSignal
  simp only [rowZero]
  rw [zeroExtend_iterateVertical_zero]
  rw [zeroExtend_iterateHorizontal_zero]
  rw [zeroExtend_fullConvImage,
    fullConv_horizontalAccumulationKernel_nat]
  simp [zeroExtend, hn]

/-- At the eastern backup coordinate, the first genuine horizontal layer and
the remaining `extraColSteps` layers expose the backup plus
`extraColSteps + 1` copies of the work register. -/
theorem protectedLinearizedPascalSignal_rowZero_one
    {n : ℕ} (hn : 2 ≤ n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨1, by omega⟩ : Fin n) =
      x rowZero ⟨1, by omega⟩ +
        (extraColSteps + 1 : ℕ) * x rowZero ⟨0, by omega⟩ := by
  unfold protectedLinearizedPascalSignal linearizedPascalSignal
  simp only [rowZero]
  rw [zeroExtend_iterateVertical_zero]
  rw [zeroExtend_iterateHorizontal_one]
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_horizontalAccumulationKernel_nat,
    fullConv_horizontalAccumulationKernel_nat]
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  simp [zeroExtend, hn0, hn1]
  ring

/-- A genuine protected Pascal selector at the northwest work register is
injective on row-chain features whose work value is copied into the adjacent
eastern register.  Unlike root-punctured recovery, the selected value may
vary arbitrarily across the compact family. -/
theorem BundledPascalGridSelectionSpec.injective_on_eastRootDuplicate
    {X : Type*} {K : Set X} {n : ℕ} (hn : 2 ≤ n)
    {V : X → Image 1 n} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 1 n
      (protectedSelectionSize 1 rowSteps extraColSteps)
      (protectedSelectionSize n rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      rowZero (⟨0, by omega⟩ : Fin n) c b net)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxdup : EastRootDuplicate (V x))
    (hydup : EastRootDuplicate (V y))
    (heval : net.eval (V x + constantImage 1 n c) =
      net.eval (V y + constantImage 1 n c)) :
    V x = V y := by
  apply protectedLinearizedPascalSignal_injective rowSteps extraColSteps
  funext i j
  let targetCol : Fin n := ⟨0, by omega⟩
  by_cases hroot : (i, j) = (rowZero, targetCol)
  · have hi : i = rowZero := congrArg Prod.fst hroot
    have hj : j = targetCol := congrArg Prod.snd hroot
    subst i
    subst j
    let backupCol : Fin n := ⟨1, by omega⟩
    have hprotected : southeastProtected rowZero targetCol rowZero backupCol := by
      simp [southeastProtected, rowZero, targetCol, backupCol]
    have hxspec := hspec.2 x hx rowZero backupCol hprotected
    have hyspec := hspec.2 y hy rowZero backupCol hprotected
    have hbackup_ne : (rowZero, backupCol) ≠ (rowZero, targetCol) := by
      simp [backupCol, targetCol]
    have hevalBackup := congrFun (congrFun heval
      (⟨rowZero, by
        have := original_lt_pascalStage 1 extraColSteps rowSteps rowZero
        simp only [protectedSelectionSize]
        omega⟩))
      (⟨backupCol, by
        have := original_lt_pascalStage n extraColSteps rowSteps backupCol
        simp only [protectedSelectionSize]
        omega⟩)
    rw [hxspec, hyspec, if_neg hbackup_ne, if_neg hbackup_ne]
      at hevalBackup
    have hsignalBackup :
        protectedLinearizedPascalSignal rowSteps extraColSteps (V x)
            rowZero backupCol =
          protectedLinearizedPascalSignal rowSteps extraColSteps (V y)
            rowZero backupCol := by
      linarith
    have hxdup' : V x rowZero targetCol = V x rowZero backupCol := by
      have hn0 : 0 < n := by omega
      have hn1 : 1 < n := by omega
      simpa [EastRootDuplicate, zeroExtend, hn0, hn1, rowZero,
        targetCol, backupCol] using hxdup
    have hydup' : V y rowZero targetCol = V y rowZero backupCol := by
      have hn0 : 0 < n := by omega
      have hn1 : 1 < n := by omega
      simpa [EastRootDuplicate, zeroExtend, hn0, hn1, rowZero,
        targetCol, backupCol] using hydup
    rw [protectedLinearizedPascalSignal_rowZero_one hn,
      protectedLinearizedPascalSignal_rowZero_one hn,
      ← hxdup', ← hydup'] at hsignalBackup
    rw [protectedLinearizedPascalSignal_rowZero_zero (by omega),
      protectedLinearizedPascalSignal_rowZero_zero (by omega)]
    have hpositive : (0 : ℝ) < extraColSteps + 2 := by positivity
    nlinarith
  · have hprotected : southeastProtected rowZero targetCol i j := by
      refine ⟨Fin.zero_le i, ?_⟩
      change (0 : ℕ) ≤ (j : ℕ)
      exact Nat.zero_le _
    have hxspec := hspec.2 x hx i j hprotected
    have hyspec := hspec.2 y hy i j hprotected
    have hevalij := congrFun (congrFun heval
      (⟨i, by
        have := original_lt_pascalStage 1 extraColSteps rowSteps i
        simp only [protectedSelectionSize]
        omega⟩))
      (⟨j, by
        have := original_lt_pascalStage n extraColSteps rowSteps j
        simp only [protectedSelectionSize]
        omega⟩)
    rw [hxspec, hyspec, if_neg hroot, if_neg hroot] at hevalij
    linarith

end OneChannelCNNUniversality
