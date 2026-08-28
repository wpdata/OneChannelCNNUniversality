import ICM2022NumCS97.LatticeCompiler

/-!
# Exact simulation of lattice expressions by the original CNN

This module joins the sparse encoder, grid-machine compiler, and affine
readout.  The exported theorem returns an actual finite-depth expansive
single-channel ReLU convolutional network, not merely an abstract register
program.
-/

namespace ICM2022NumCS97

noncomputable def encoderGridValue
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image d₁ d₂) (s : Site) : ℝ :=
  zeroExtend ((sparseEncoderProgram hkRows hkCols).eval x) s.1 s.2

theorem encoderGridValue_eq_zero_of_not_master
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image d₁ d₂) (s : Site) (hs : ¬ IsMasterSite d₁ d₂ s) :
    encoderGridValue hkRows hkCols x s = 0 := by
  rcases s with ⟨p, q⟩
  unfold encoderGridValue
  by_cases hp : p < encoderOutRows kRows d₁ d₂
  · by_cases hq : q < encoderOutCols kCols d₁ d₂
    · rw [zeroExtend_of_lt _ hp hq]
      apply sparseEncoderProgram_eval_off_master
      intro hmaster
      rcases hmaster with ⟨⟨i, hi⟩, j, hj⟩
      apply hs
      refine ⟨i, j, ?_⟩
      apply Prod.ext
      · exact hi
      · exact hj
    · exact zeroExtend_col_outside _ (Nat.le_of_not_gt hq)
  · exact zeroExtend_row_outside _ (Nat.le_of_not_gt hp)

theorem encoderGridValue_master
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (x : Image d₁ d₂) (i : Fin d₁) (j : Fin d₂) :
    encoderGridValue hkRows hkCols x (gridSite d₁ d₂ i j) =
      sparseEncodedValue x i j := by
  unfold encoderGridValue
  change zeroExtend ((sparseEncoderProgram hkRows hkCols).eval x)
      (encoderSite d₁ i) (encoderSite d₂ j) = _
  have hrow : encoderSite d₁ i < encoderOutRows kRows d₁ d₂ :=
    (encoderOutRowFin (d₂ := d₂) hkRows i).isLt
  have hcol : encoderSite d₂ j < encoderOutCols kCols d₁ d₂ :=
    (encoderOutColFin (d₁ := d₁) hkCols j).isLt
  simp only [zeroExtend, hrow, hcol, ↓reduceDIte]
  have hrowFin : (⟨encoderSite d₁ i, hrow⟩ :
      Fin (encoderOutRows kRows d₁ d₂)) =
      encoderOutRowFin (d₂ := d₂) hkRows i := Fin.ext rfl
  have hcolFin : (⟨encoderSite d₂ j, hcol⟩ :
      Fin (encoderOutCols kCols d₁ d₂)) =
      encoderOutColFin (d₁ := d₁) hkCols j := Fin.ext rfl
  rw [hrowFin, hcolFin]
  exact sparseEncoderProgram_eval_master hkRows hkCols hd₁ hd₂ x i j

theorem sparseEncoderProgram_represents_grid
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image d₁ d₂) :
    RepresentsInfinite ((sparseEncoderProgram hkRows hkCols).eval x)
      (staticState (gridSupport d₁ d₂)
        (encoderGridValue hkRows hkCols x)) := by
  intro p q
  by_cases hs : gridSupport d₁ d₂ (p, q) = true
  · simp [staticState, encoderGridValue, hs]
  · have hsfalse : gridSupport d₁ d₂ (p, q) = false :=
      Bool.eq_false_of_not_eq_true hs
    have hnotMaster : ¬ IsMasterSite d₁ d₂ (p, q) := by
      intro hmaster
      rcases hmaster with ⟨i, j, hij⟩
      apply hs
      rw [gridSupport_eq_true_iff]
      exact ⟨i, j, by simpa using hij⟩
    have hz := encoderGridValue_eq_zero_of_not_master
      hkRows hkCols x (p, q) hnotMaster
    change encoderGridValue hkRows hkCols x (p, q) = _
    simpa [staticState, hsfalse] using hz

theorem encoderGridValue_circuitNode_zero
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image d₁ d₂) (t : ℕ) :
    encoderGridValue hkRows hkCols x (circuitNodeSite d₁ d₂ t) = 0 := by
  apply encoderGridValue_eq_zero_of_not_master hkRows hkCols
  rintro ⟨i, j, h⟩
  have hrow := congrArg Prod.fst h
  unfold circuitNodeSite masterSite gridSite encoderSite at hrow
  have hi := i.isLt
  omega

namespace LatticeExpr

noncomputable def finalCommands {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂) :
    List (GridCommand d₁ d₂) :=
  e.compileCommands 0 ++
    [activateNodeCommand (e.outputIndex 0) (.translate 0)]

theorem execute_finalCommands_output {d₁ d₂ : ℕ}
    (e : LatticeExpr d₁ d₂) (x : Image d₁ d₂) (value : Site → ℝ)
    (hmaster : ∀ i : Fin d₁, ∀ j : Fin d₂,
      value (gridSite d₁ d₂ i j) = sparseEncodedValue x i j)
    (hfresh : ∀ t, value (circuitNodeSite d₁ d₂ t) = 0) :
    executeGridCommands e.finalCommands value
        (circuitNodeSite d₁ d₂ (e.outputIndex 0)) =
      e.evalEncoded x := by
  rw [finalCommands, executeGridCommands_append]
  simp only [executeGridCommands, activateNodeCommand_evalValue,
    ActivationMode.eval, add_zero, updateAt_same]
  exact e.compileCommands_output 0 x value hmaster
    (fun t _ ↦ hfresh t)

end LatticeExpr

noncomputable def latticeOutRows (kRows d₁ d₂ : ℕ)
    (e : LatticeExpr d₁ d₂) : ℕ :=
  gridCommandOutRows kRows (encoderOutRows kRows d₁ d₂) e.finalCommands

noncomputable def latticeOutCols (kCols d₁ d₂ : ℕ)
    (e : LatticeExpr d₁ d₂) : ℕ :=
  gridCommandOutCols kCols (encoderOutCols kCols d₁ d₂) e.finalCommands

theorem latticeOutputRow_lt {kRows d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (e : LatticeExpr d₁ d₂) :
    (circuitNodeSite d₁ d₂ (e.outputIndex 0)).1 <
      latticeOutRows kRows d₁ d₂ e := by
  unfold latticeOutRows LatticeExpr.finalCommands
  rw [gridCommandOutRows_append]
  simp only [gridCommandOutRows, GridCommand.outRows, activateNodeCommand]
  simpa [circuitNodeSite] using
    (gridPadded_targetRow_lt
      (rows := gridCommandOutRows kRows (encoderOutRows kRows d₁ d₂)
        (e.compileCommands 0))
      (d₁ := d₁) (d₂ := d₂)
      (r := d₁ + e.outputIndex 0) (c := d₂ + e.outputIndex 0) hkRows)

theorem latticeOutputCol_lt {kCols d₁ d₂ : ℕ}
    (hkCols : 2 ≤ kCols) (e : LatticeExpr d₁ d₂) :
    (circuitNodeSite d₁ d₂ (e.outputIndex 0)).2 <
      latticeOutCols kCols d₁ d₂ e := by
  unfold latticeOutCols LatticeExpr.finalCommands
  rw [gridCommandOutCols_append]
  simp only [gridCommandOutCols, GridCommand.outCols, activateNodeCommand]
  simpa [circuitNodeSite] using
    (gridPadded_targetCol_lt
      (cols := gridCommandOutCols kCols (encoderOutCols kCols d₁ d₂)
        (e.compileCommands 0))
      (d₁ := d₁) (d₂ := d₂)
      (r := d₁ + e.outputIndex 0) (c := d₂ + e.outputIndex 0) hkCols)

def latticeOutputRowFin {kRows d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (e : LatticeExpr d₁ d₂) :
    Fin (latticeOutRows kRows d₁ d₂ e) :=
  ⟨(circuitNodeSite d₁ d₂ (e.outputIndex 0)).1,
    latticeOutputRow_lt hkRows e⟩

def latticeOutputColFin {kCols d₁ d₂ : ℕ}
    (hkCols : 2 ≤ kCols) (e : LatticeExpr d₁ d₂) :
    Fin (latticeOutCols kCols d₁ d₂ e) :=
  ⟨(circuitNodeSite d₁ d₂ (e.outputIndex 0)).2,
    latticeOutputCol_lt hkCols e⟩

noncomputable def latticeSymbolicProgram
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (e : LatticeExpr d₁ d₂) :
    HybridProgramTo kRows kCols d₁ d₂
      (latticeOutRows kRows d₁ d₂ e)
      (latticeOutCols kCols d₁ d₂ e) :=
  (HybridProgramTo.ofMaskProgramTo
      (sparseEncoderProgram hkRows hkCols)).append
    (gridCommandProgram hkRows hkCols e.finalCommands)

theorem latticeSymbolicProgram_output
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (e : LatticeExpr d₁ d₂) (x : Image d₁ d₂) :
    (latticeSymbolicProgram hkRows hkCols e).eval x
        (latticeOutputRowFin hkRows e)
        (latticeOutputColFin hkCols e) = e.evalEncoded x := by
  let encoded := (sparseEncoderProgram hkRows hkCols).eval x
  let value := encoderGridValue hkRows hkCols x
  have hencoded : RepresentsInfinite encoded
      (staticState (gridSupport d₁ d₂) value) :=
    sparseEncoderProgram_represents_grid hkRows hkCols x
  have hcommands := gridCommandProgram_represents hkRows hkCols
    e.finalCommands encoded value hencoded
  have hpoint := hcommands
    (circuitNodeSite d₁ d₂ (e.outputIndex 0)).1
    (circuitNodeSite d₁ d₂ (e.outputIndex 0)).2
  have hrow := latticeOutputRow_lt hkRows e
  have hcol := latticeOutputCol_lt hkCols e
  unfold latticeOutRows at hrow
  unfold latticeOutCols at hcol
  simp only [zeroExtend, hrow, hcol, ↓reduceDIte] at hpoint
  have hsupport := gridSupport_circuitNode d₁ d₂ (e.outputIndex 0)
  have hideal := e.execute_finalCommands_output x value
    (fun i j ↦ encoderGridValue_master hkRows hkCols hd₁ hd₂ x i j)
    (fun t ↦ encoderGridValue_circuitNode_zero hkRows hkCols x t)
  change (gridCommandProgram hkRows hkCols e.finalCommands).eval encoded
      (latticeOutputRowFin hkRows e) (latticeOutputColFin hkCols e) = _ at hpoint
  rw [staticState, if_pos hsupport, hideal] at hpoint
  rw [latticeSymbolicProgram, HybridProgramTo.eval_append,
    HybridProgramTo.eval_ofMaskProgramTo]
  exact hpoint

def pointReadoutWeight {rows cols : ℕ} (row : Fin rows) (col : Fin cols) :
    Image rows cols :=
  fun i j ↦ if i = row then if j = col then 1 else 0 else 0

theorem pointReadoutWeight_sum {rows cols : ℕ}
    (row : Fin rows) (col : Fin cols) (y : Image rows cols) :
    (∑ i, ∑ j, pointReadoutWeight row col i j * y i j) = y row col := by
  classical
  simp [pointReadoutWeight]

/-- Every finite affine lattice expression is realized exactly on a compact
set by an actual expansive one-channel ReLU CNN with the prescribed fixed
kernel rectangle. -/
theorem exists_network_realizing_latticeExpr
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (e : LatticeExpr d₁ d₂) :
    ∃ (net : NetworkTo kRows kCols d₁ d₂
          (latticeOutRows kRows d₁ d₂ e)
          (latticeOutCols kCols d₁ d₂ e))
      (weight : Image (latticeOutRows kRows d₁ d₂ e)
        (latticeOutCols kCols d₁ d₂ e))
      (constant : ℝ),
      ∀ x ∈ K, net.realize weight constant x = e.evalEncoded x := by
  let program := latticeSymbolicProgram hkRows hkCols e
  obtain ⟨net, carrier, hnet⟩ := program.exists_network hK
    (fun x : Image d₁ d₂ ↦ x) (fun x ↦ x) 0
    (by intro x hx; simp) (continuousFeatureOn_identity K)
  let row := latticeOutputRowFin hkRows e
  let col := latticeOutputColFin hkCols e
  let weight := pointReadoutWeight row col
  let constant := -carrier row col
  refine ⟨net, weight, constant, ?_⟩
  intro x hx
  unfold NetworkTo.realize
  rw [hnet x hx]
  rw [pointReadoutWeight_sum]
  change program.eval x row col + carrier row col + constant = _
  rw [latticeSymbolicProgram_output hkRows hkCols hd₁ hd₂ e x]
  dsimp [constant]
  ring

end ICM2022NumCS97
