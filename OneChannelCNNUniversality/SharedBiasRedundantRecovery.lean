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
def EastRootDuplicate {rows cols : ℕ} (x : Image rows cols) : Prop :=
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
register, independently of the rectangle size and the number of steps. -/
theorem protectedLinearizedPascalSignal_northwest_zero
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (rowSteps extraColSteps : ℕ) (x : Image rows cols) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x
        (⟨0, hrows⟩ : Fin rows) (⟨0, hcols⟩ : Fin cols) =
      x ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  unfold protectedLinearizedPascalSignal linearizedPascalSignal
  rw [zeroExtend_iterateVertical_zero]
  rw [zeroExtend_iterateHorizontal_zero]
  rw [zeroExtend_fullConvImage,
    fullConv_horizontalAccumulationKernel_nat]
  simp [zeroExtend, hrows, hcols]

/-- At the eastern backup coordinate, the first genuine horizontal layer and
the remaining `extraColSteps` layers expose the backup plus
`extraColSteps + 1` copies of the work register. -/
theorem protectedLinearizedPascalSignal_northwest_one
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 2 ≤ cols)
    (rowSteps extraColSteps : ℕ) (x : Image rows cols) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x
        (⟨0, hrows⟩ : Fin rows) (⟨1, by omega⟩ : Fin cols) =
      x ⟨0, hrows⟩ ⟨1, by omega⟩ +
        (extraColSteps + 1 : ℕ) * x ⟨0, hrows⟩ ⟨0, by omega⟩ := by
  unfold protectedLinearizedPascalSignal linearizedPascalSignal
  rw [zeroExtend_iterateVertical_zero]
  rw [zeroExtend_iterateHorizontal_one]
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_horizontalAccumulationKernel_nat,
    fullConv_horizontalAccumulationKernel_nat]
  have hn0 : 0 < cols := by omega
  have hn1 : 1 < cols := by omega
  simp [zeroExtend, hrows, hn0, hn1]
  ring

/-- One-row compatibility specialization of the northwest-root formula. -/
theorem protectedLinearizedPascalSignal_rowZero_zero
    {n : ℕ} (hn : 0 < n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨0, hn⟩ : Fin n) =
      x rowZero ⟨0, hn⟩ := by
  simpa [rowZero] using
    protectedLinearizedPascalSignal_northwest_zero
      (rows := 1) (cols := n) (by omega) hn rowSteps extraColSteps x

/-- One-row compatibility specialization of the eastern-backup formula. -/
theorem protectedLinearizedPascalSignal_rowZero_one
    {n : ℕ} (hn : 2 ≤ n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨1, by omega⟩ : Fin n) =
      x rowZero ⟨1, by omega⟩ +
        (extraColSteps + 1 : ℕ) * x rowZero ⟨0, by omega⟩ := by
  simpa [rowZero] using
    protectedLinearizedPascalSignal_northwest_one
      (rows := 1) (cols := n) (by omega) hn rowSteps extraColSteps x

/-- A genuine protected Pascal selector at the northwest work register is
injective on row-chain features whose work value is copied into the adjacent
eastern register.  Unlike root-punctured recovery, the selected value may
vary arbitrarily across the compact family. -/
theorem BundledPascalGridSelectionSpec.injective_on_eastRootDuplicate
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 2 ≤ cols)
    {V : X → Image rows cols} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin rows) (⟨0, by omega⟩ : Fin cols) c b net)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxdup : EastRootDuplicate (V x))
    (hydup : EastRootDuplicate (V y))
    (heval : net.eval (V x + constantImage rows cols c) =
      net.eval (V y + constantImage rows cols c)) :
    V x = V y := by
  apply protectedLinearizedPascalSignal_injective rowSteps extraColSteps
  funext i j
  let targetRow : Fin rows := ⟨0, hrows⟩
  let targetCol : Fin cols := ⟨0, by omega⟩
  by_cases hroot : (i, j) = (targetRow, targetCol)
  · have hi : i = targetRow := congrArg Prod.fst hroot
    have hj : j = targetCol := congrArg Prod.snd hroot
    subst i
    subst j
    let backupCol : Fin cols := ⟨1, by omega⟩
    have hprotected :
        southeastProtected targetRow targetCol targetRow backupCol := by
      simp [southeastProtected, targetRow, targetCol, backupCol]
    have hxspec := hspec.2 x hx targetRow backupCol hprotected
    have hyspec := hspec.2 y hy targetRow backupCol hprotected
    have hbackup_ne : (targetRow, backupCol) ≠ (targetRow, targetCol) := by
      simp [backupCol, targetCol]
    have hevalBackup := congrFun (congrFun heval
      (⟨targetRow, by
        have := original_lt_pascalStage rows extraColSteps rowSteps targetRow
        simp only [protectedSelectionSize]
        omega⟩))
      (⟨backupCol, by
        have := original_lt_pascalStage cols extraColSteps rowSteps backupCol
        simp only [protectedSelectionSize]
        omega⟩)
    rw [hxspec, hyspec, if_neg hbackup_ne, if_neg hbackup_ne]
      at hevalBackup
    have hsignalBackup :
        protectedLinearizedPascalSignal rowSteps extraColSteps (V x)
            targetRow backupCol =
          protectedLinearizedPascalSignal rowSteps extraColSteps (V y)
            targetRow backupCol := by
      linarith
    have hxdup' : V x targetRow targetCol = V x targetRow backupCol := by
      have hn0 : 0 < cols := by omega
      have hn1 : 1 < cols := by omega
      simpa [EastRootDuplicate, zeroExtend, hrows, hn0, hn1, targetRow,
        targetCol, backupCol] using hxdup
    have hydup' : V y targetRow targetCol = V y targetRow backupCol := by
      have hn0 : 0 < cols := by omega
      have hn1 : 1 < cols := by omega
      simpa [EastRootDuplicate, zeroExtend, hrows, hn0, hn1, targetRow,
        targetCol, backupCol] using hydup
    rw [protectedLinearizedPascalSignal_northwest_one hrows hcols,
      protectedLinearizedPascalSignal_northwest_one hrows hcols,
      ← hxdup', ← hydup'] at hsignalBackup
    rw [protectedLinearizedPascalSignal_northwest_zero hrows (by omega),
      protectedLinearizedPascalSignal_northwest_zero hrows (by omega)]
    have hpositive : (0 : ℝ) < extraColSteps + 2 := by positivity
    nlinarith
  · have hprotected : southeastProtected targetRow targetCol i j := by
      constructor
      · change (0 : ℕ) ≤ (i : ℕ)
        exact Nat.zero_le _
      · change (0 : ℕ) ≤ (j : ℕ)
        exact Nat.zero_le _
    have hxspec := hspec.2 x hx i j hprotected
    have hyspec := hspec.2 y hy i j hprotected
    have hevalij := congrFun (congrFun heval
      (⟨i, by
        have := original_lt_pascalStage rows extraColSteps rowSteps i
        simp only [protectedSelectionSize]
        omega⟩))
      (⟨j, by
        have := original_lt_pascalStage cols extraColSteps rowSteps j
        simp only [protectedSelectionSize]
        omega⟩)
    rw [hxspec, hyspec, if_neg hroot, if_neg hroot] at hevalij
    linarith

end OneChannelCNNUniversality
