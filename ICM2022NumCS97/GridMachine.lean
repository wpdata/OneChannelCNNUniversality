import ICM2022NumCS97.GridRouting
import ICM2022NumCS97.HybridProgram

/-!
# A verified instruction language on the gap-three grid

The instruction language has exactly two operations:

* route and add a scaled earlier register into a later register;
* apply either a linear translation or a genuine shifted ReLU at one grid
  register.

Each instruction is compiled to the exact one-channel expansive CNN
semantics.  Activation instructions first add harmless identity-padding
layers; this makes their target coordinate available without carrying any
fragile dimension side condition through the circuit compiler.
-/

namespace ICM2022NumCS97

noncomputable def gridActivateKeep (d₁ d₂ : ℕ) {rows cols : ℕ}
    (p : Fin rows) (q : Fin cols) : Bool :=
  gridSupport d₁ d₂ (p, q)

noncomputable def gridActivateMode (d₁ d₂ r c : ℕ)
    (selected : ActivationMode) {rows cols : ℕ}
    (p : Fin rows) (q : Fin cols) : ActivationMode :=
  if ((p : ℕ), (q : ℕ)) = gridSite d₁ d₂ r c then selected else .linear

noncomputable def gridActivateProgram {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (d₁ d₂ r c : ℕ) (selected : ActivationMode) :
    HybridProgramTo kRows kCols rows cols
      (rows + kRows - 1) (cols + kCols - 1) :=
  HybridProgramTo.cons (identityKernel hkRows hkCols)
    (gridActivateKeep d₁ d₂)
    (gridActivateMode d₁ d₂ r c selected)
    (HybridProgramTo.nil (rows + kRows - 1) (cols + kCols - 1)
      kRows kCols)

noncomputable def gridActivateState (d₁ d₂ r c : ℕ)
    (selected : ActivationMode) (z : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun p q ↦ if gridSupport d₁ d₂ (p, q) then
    if (p, q) = gridSite d₁ d₂ r c then selected.eval (z p q) else z p q
  else 0

theorem gridActivateState_static (d₁ d₂ r c : ℕ)
    (selected : ActivationMode) (value : Site → ℝ) :
    gridActivateState d₁ d₂ r c selected
        (staticState (gridSupport d₁ d₂) value) =
      staticState (gridSupport d₁ d₂)
        (updateAt value (gridSite d₁ d₂ r c)
          (selected.eval (value (gridSite d₁ d₂ r c)))) := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : gridSupport d₁ d₂ s = true
  · by_cases ht : s = gridSite d₁ d₂ r c
    · simp [gridActivateState, staticState, updateAt, s, hs, ht]
    · simp [gridActivateState, staticState, updateAt, s, hs, ht]
  · have hsfalse : gridSupport d₁ d₂ s = false :=
      Bool.eq_false_of_not_eq_true hs
    simp [gridActivateState, staticState, s, hsfalse]

theorem gridActivateProgram_represents
    {kRows kCols rows cols d₁ d₂ r c : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (selected : ActivationMode) (x : Image rows cols)
    (z : ℕ → ℕ → ℝ) (hx : RepresentsInfinite x z)
    (htargetRow : (gridSite d₁ d₂ r c).1 < rows + kRows - 1)
    (htargetCol : (gridSite d₁ d₂ r c).2 < cols + kCols - 1) :
    RepresentsInfinite
      ((gridActivateProgram hkRows hkCols d₁ d₂ r c selected).eval x)
      (gridActivateState d₁ d₂ r c selected z) := by
  intro p q
  by_cases hp : p < rows + kRows - 1
  · by_cases hq : q < cols + kCols - 1
    · rw [zeroExtend_of_lt _ hp hq]
      rw [gridActivateProgram, HybridProgramTo.eval_cons,
        HybridProgramTo.eval_nil]
      simp only [gridActivateKeep, gridActivateMode]
      change (if gridSupport d₁ d₂ (p, q) = true then
          ActivationMode.eval
            (if (p, q) = gridSite d₁ d₂ r c then selected else .linear)
            (fullConv (identityKernel hkRows hkCols) x p q)
        else 0) = gridActivateState d₁ d₂ r c selected z p q
      rw [fullConv_identityKernel hkRows hkCols, hx p q]
      by_cases hs : gridSupport d₁ d₂ (p, q) = true
      · by_cases ht : (p, q) = gridSite d₁ d₂ r c
        · simp [gridActivateState, ActivationMode.eval, hs, ht]
        · simp [gridActivateState, ActivationMode.eval, hs, ht]
      · have hsfalse : gridSupport d₁ d₂ (p, q) = false :=
          Bool.eq_false_of_not_eq_true hs
        simp [gridActivateState, hsfalse]
    · rw [zeroExtend_col_outside (hj := Nat.le_of_not_gt hq)]
      have hinput : cols ≤ q := by omega
      have hz : z p q = 0 := by
        rw [← hx p q, zeroExtend_col_outside x hinput]
      have hnotTarget : (p, q) ≠ gridSite d₁ d₂ r c := by
        intro h
        have := congrArg Prod.snd h
        simp only at this
        omega
      simp [gridActivateState, hnotTarget, hz]
  · rw [zeroExtend_row_outside (hi := Nat.le_of_not_gt hp)]
    have hinput : rows ≤ p := by omega
    have hz : z p q = 0 := by
      rw [← hx p q, zeroExtend_row_outside x hinput]
    have hnotTarget : (p, q) ≠ gridSite d₁ d₂ r c := by
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
    simp [gridActivateState, hnotTarget, hz]

theorem gridActivateProgram_represents_static
    {kRows kCols rows cols d₁ d₂ r c : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (selected : ActivationMode) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (gridSupport d₁ d₂) value))
    (htargetRow : (gridSite d₁ d₂ r c).1 < rows + kRows - 1)
    (htargetCol : (gridSite d₁ d₂ r c).2 < cols + kCols - 1) :
    RepresentsInfinite
      ((gridActivateProgram hkRows hkCols d₁ d₂ r c selected).eval x)
      (staticState (gridSupport d₁ d₂)
        (updateAt value (gridSite d₁ d₂ r c)
          (selected.eval (value (gridSite d₁ d₂ r c))))) := by
  rw [← gridActivateState_static]
  exact gridActivateProgram_represents hkRows hkCols selected x _ hx
    htargetRow htargetCol

noncomputable def gridPaddingStep (d₁ d₂ : ℕ) : RouteStep :=
  { direction := .east
    coefficient := 0
    keep := fun p q ↦ gridSupport d₁ d₂ (p, q) }

noncomputable def gridPaddingSteps (d₁ d₂ steps : ℕ) : List RouteStep :=
  List.replicate steps (gridPaddingStep d₁ d₂)

theorem executeRoute_gridPaddingSteps (d₁ d₂ steps : ℕ)
    (value : Site → ℝ) :
    executeRoute (gridPaddingSteps d₁ d₂ steps)
        (staticState (gridSupport d₁ d₂) value) =
      staticState (gridSupport d₁ d₂) value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [gridPaddingSteps, List.replicate_succ, executeRoute]
      change executeRoute (List.replicate steps (gridPaddingStep d₁ d₂))
        (routeStep .east 0 (fun p q ↦ gridSupport d₁ d₂ (p, q))
          (staticState (gridSupport d₁ d₂) value)) = _
      rw [routeStep_restrict_static .east (gridSupport d₁ d₂)
        (gridSupport d₁ d₂) value (fun _ h ↦ h)]
      exact ih

noncomputable def gridLinearRouteProgram {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : List RouteStep) :
    HybridProgramTo kRows kCols rows cols
      (grownSize kRows rows steps.length)
      (grownSize kCols cols steps.length) :=
  HybridProgramTo.ofMaskProgramTo (routeProgram hkRows hkCols steps)

@[simp] theorem gridLinearRouteProgram_eval
    {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : List RouteStep) (x : Image rows cols) :
    (gridLinearRouteProgram hkRows hkCols steps).eval x =
      (routeProgram hkRows hkCols steps).eval x :=
  HybridProgramTo.eval_ofMaskProgramTo _ x

def gridActivationPadding (d₁ d₂ r c : ℕ) : ℕ :=
  max ((gridSite d₁ d₂ r c).1 + 1) ((gridSite d₁ d₂ r c).2 + 1)

noncomputable def gridPaddedRows (kRows rows d₁ d₂ r c : ℕ) : ℕ :=
  grownSize kRows rows
    (gridPaddingSteps d₁ d₂ (gridActivationPadding d₁ d₂ r c)).length

noncomputable def gridPaddedCols (kCols cols d₁ d₂ r c : ℕ) : ℕ :=
  grownSize kCols cols
    (gridPaddingSteps d₁ d₂ (gridActivationPadding d₁ d₂ r c)).length

theorem gridPadded_targetRow_lt {kRows rows d₁ d₂ r c : ℕ}
    (hkRows : 2 ≤ kRows) :
    (gridSite d₁ d₂ r c).1 <
      gridPaddedRows kRows rows d₁ d₂ r c + kRows - 1 := by
  have hmax : (gridSite d₁ d₂ r c).1 <
      gridActivationPadding d₁ d₂ r c := by
    unfold gridActivationPadding
    omega
  have hgrow := grownSize_ge_add_steps kRows rows
    (gridActivationPadding d₁ d₂ r c) hkRows
  simp only [gridPaddedRows, gridPaddingSteps, List.length_replicate]
  omega

theorem gridPadded_targetCol_lt {kCols cols d₁ d₂ r c : ℕ}
    (hkCols : 2 ≤ kCols) :
    (gridSite d₁ d₂ r c).2 <
      gridPaddedCols kCols cols d₁ d₂ r c + kCols - 1 := by
  have hmax : (gridSite d₁ d₂ r c).2 <
      gridActivationPadding d₁ d₂ r c := by
    unfold gridActivationPadding
    omega
  have hgrow := grownSize_ge_add_steps kCols cols
    (gridActivationPadding d₁ d₂ r c) hkCols
  simp only [gridPaddedCols, gridPaddingSteps, List.length_replicate]
  omega

noncomputable def gridPaddedActivateProgram
    {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (d₁ d₂ r c : ℕ) (selected : ActivationMode) :
    HybridProgramTo kRows kCols rows cols
      (gridPaddedRows kRows rows d₁ d₂ r c + kRows - 1)
      (gridPaddedCols kCols cols d₁ d₂ r c + kCols - 1) :=
  let padding := gridPaddingSteps d₁ d₂
    (gridActivationPadding d₁ d₂ r c)
  let first : HybridProgramTo kRows kCols rows cols
      (gridPaddedRows kRows rows d₁ d₂ r c)
      (gridPaddedCols kCols cols d₁ d₂ r c) :=
    gridLinearRouteProgram hkRows hkCols padding
  let second := gridActivateProgram
    (rows := gridPaddedRows kRows rows d₁ d₂ r c)
    (cols := gridPaddedCols kCols cols d₁ d₂ r c)
    hkRows hkCols d₁ d₂ r c selected
  first.append second

theorem gridPaddedActivateProgram_represents_static
    {kRows kCols rows cols d₁ d₂ r c : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (selected : ActivationMode) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (gridSupport d₁ d₂) value)) :
    RepresentsInfinite
      ((gridPaddedActivateProgram hkRows hkCols d₁ d₂ r c selected).eval x)
      (staticState (gridSupport d₁ d₂)
        (updateAt value (gridSite d₁ d₂ r c)
          (selected.eval (value (gridSite d₁ d₂ r c))))) := by
  let padding := gridPaddingSteps d₁ d₂
    (gridActivationPadding d₁ d₂ r c)
  have hfirst : RepresentsInfinite
      ((gridLinearRouteProgram hkRows hkCols padding).eval x)
      (staticState (gridSupport d₁ d₂) value) := by
    rw [gridLinearRouteProgram_eval]
    have h := routeProgram_represents hkRows hkCols padding x
      (staticState (gridSupport d₁ d₂) value) hx
    rw [executeRoute_gridPaddingSteps] at h
    exact h
  have hrowMax : (gridSite d₁ d₂ r c).1 <
      gridActivationPadding d₁ d₂ r c := by
    unfold gridActivationPadding
    omega
  have hcolMax : (gridSite d₁ d₂ r c).2 <
      gridActivationPadding d₁ d₂ r c := by
    unfold gridActivationPadding
    omega
  have hgrowRows := grownSize_ge_add_steps kRows rows
    (gridActivationPadding d₁ d₂ r c) hkRows
  have hgrowCols := grownSize_ge_add_steps kCols cols
    (gridActivationPadding d₁ d₂ r c) hkCols
  have htargetRow : (gridSite d₁ d₂ r c).1 <
      gridPaddedRows kRows rows d₁ d₂ r c + kRows - 1 := by
    simp only [gridPaddedRows, gridPaddingSteps, List.length_replicate]
    omega
  have htargetCol : (gridSite d₁ d₂ r c).2 <
      gridPaddedCols kCols cols d₁ d₂ r c + kCols - 1 := by
    simp only [gridPaddedCols, gridPaddingSteps, List.length_replicate]
    omega
  let second := gridActivateProgram
    (rows := gridPaddedRows kRows rows d₁ d₂ r c)
    (cols := gridPaddedCols kCols cols d₁ d₂ r c)
    hkRows hkCols d₁ d₂ r c selected
  rw [gridPaddedActivateProgram, HybridProgramTo.eval_append]
  exact gridActivateProgram_represents_static hkRows hkCols selected
    ((gridLinearRouteProgram hkRows hkCols padding).eval x) value hfirst
    htargetRow htargetCol

/-- High-level commands used by the finite ReLU-circuit compiler.  The
strict inequalities stored in a route command are precisely the geometric
condition needed by `executeRoute_routeGridToGrid`. -/
inductive GridCommand (d₁ d₂ : ℕ)
  | route (sourceRow sourceCol destinationRow destinationCol : ℕ)
      (row_lt : sourceRow < destinationRow)
      (col_lt : sourceCol < destinationCol)
      (coefficient : ℝ)
  | activate (row col : ℕ) (mode : ActivationMode)

namespace GridCommand

def evalValue {d₁ d₂ : ℕ} : GridCommand d₁ d₂ → (Site → ℝ) → Site → ℝ
  | .route r c R C _ _ coefficient, value =>
      updateAt value (gridSite d₁ d₂ R C)
        (value (gridSite d₁ d₂ R C) +
          coefficient * value (gridSite d₁ d₂ r c))
  | .activate r c mode, value =>
      updateAt value (gridSite d₁ d₂ r c)
        (mode.eval (value (gridSite d₁ d₂ r c)))

noncomputable def outRows {d₁ d₂ : ℕ} (kRows rows : ℕ) :
    GridCommand d₁ d₂ → ℕ
  | .route r c R C _ _ coefficient =>
      grownSize kRows rows
        (routeGridToGridSteps d₁ d₂ r c R C coefficient).length
  | .activate r c _ => gridPaddedRows kRows rows d₁ d₂ r c + kRows - 1

noncomputable def outCols {d₁ d₂ : ℕ} (kCols cols : ℕ) :
    GridCommand d₁ d₂ → ℕ
  | .route r c R C _ _ coefficient =>
      grownSize kCols cols
        (routeGridToGridSteps d₁ d₂ r c R C coefficient).length
  | .activate r c _ => gridPaddedCols kCols cols d₁ d₂ r c + kCols - 1

noncomputable def compile {d₁ d₂ kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (command : GridCommand d₁ d₂) :
    HybridProgramTo kRows kCols rows cols
      (command.outRows kRows rows) (command.outCols kCols cols) :=
  match command with
  | .route r c R C _ _ coefficient =>
      gridLinearRouteProgram hkRows hkCols
        (routeGridToGridSteps d₁ d₂ r c R C coefficient)
  | .activate r c mode =>
      gridPaddedActivateProgram hkRows hkCols d₁ d₂ r c mode

theorem compile_represents {d₁ d₂ kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (command : GridCommand d₁ d₂) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (gridSupport d₁ d₂) value)) :
    RepresentsInfinite ((command.compile hkRows hkCols).eval x)
      (staticState (gridSupport d₁ d₂) (command.evalValue value)) := by
  cases command with
  | route r c R C hr hc coefficient =>
      change RepresentsInfinite
        ((gridLinearRouteProgram hkRows hkCols
          (routeGridToGridSteps d₁ d₂ r c R C coefficient)).eval x)
        (staticState (gridSupport d₁ d₂)
          (updateAt value (gridSite d₁ d₂ R C)
            (value (gridSite d₁ d₂ R C) +
              coefficient * value (gridSite d₁ d₂ r c))))
      rw [gridLinearRouteProgram_eval]
      have h := routeProgram_represents hkRows hkCols
        (routeGridToGridSteps d₁ d₂ r c R C coefficient) x
        (staticState (gridSupport d₁ d₂) value) hx
      rw [executeRoute_routeGridToGrid hr hc] at h
      exact h
  | activate r c mode =>
      exact gridPaddedActivateProgram_represents_static
        hkRows hkCols mode x value hx

end GridCommand

def executeGridCommands {d₁ d₂ : ℕ} :
    List (GridCommand d₁ d₂) → (Site → ℝ) → Site → ℝ
  | [], value => value
  | command :: tail, value =>
      executeGridCommands tail (command.evalValue value)

noncomputable def gridCommandOutRows {d₁ d₂ : ℕ} (kRows rows : ℕ) :
    List (GridCommand d₁ d₂) → ℕ
  | [] => rows
  | command :: tail =>
      gridCommandOutRows kRows (command.outRows kRows rows) tail

noncomputable def gridCommandOutCols {d₁ d₂ : ℕ} (kCols cols : ℕ) :
    List (GridCommand d₁ d₂) → ℕ
  | [] => cols
  | command :: tail =>
      gridCommandOutCols kCols (command.outCols kCols cols) tail

theorem gridCommandOutRows_append {d₁ d₂ : ℕ} (kRows rows : ℕ)
    (first second : List (GridCommand d₁ d₂)) :
    gridCommandOutRows kRows rows (first ++ second) =
      gridCommandOutRows kRows
        (gridCommandOutRows kRows rows first) second := by
  induction first generalizing rows with
  | nil => rfl
  | cons command tail ih =>
      simp only [List.cons_append, gridCommandOutRows]
      exact ih (command.outRows kRows rows)

theorem gridCommandOutCols_append {d₁ d₂ : ℕ} (kCols cols : ℕ)
    (first second : List (GridCommand d₁ d₂)) :
    gridCommandOutCols kCols cols (first ++ second) =
      gridCommandOutCols kCols
        (gridCommandOutCols kCols cols first) second := by
  induction first generalizing cols with
  | nil => rfl
  | cons command tail ih =>
      simp only [List.cons_append, gridCommandOutCols]
      exact ih (command.outCols kCols cols)

noncomputable def gridCommandProgram
    {d₁ d₂ kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) :
    (commands : List (GridCommand d₁ d₂)) → {rows cols : ℕ} →
      HybridProgramTo kRows kCols rows cols
        (gridCommandOutRows kRows rows commands)
        (gridCommandOutCols kCols cols commands)
  | [], rows, cols => HybridProgramTo.nil rows cols kRows kCols
  | command :: tail, rows, cols =>
      (command.compile hkRows hkCols).append
        (gridCommandProgram hkRows hkCols tail)

theorem gridCommandProgram_represents
    {kRows kCols rows cols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (commands : List (GridCommand d₁ d₂)) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (gridSupport d₁ d₂) value)) :
    RepresentsInfinite
      ((gridCommandProgram hkRows hkCols commands).eval x)
      (staticState (gridSupport d₁ d₂)
        (executeGridCommands commands value)) := by
  induction commands generalizing rows cols x value with
  | nil => exact hx
  | cons command tail ih =>
      rw [gridCommandProgram, HybridProgramTo.eval_append]
      exact ih ((command.compile hkRows hkCols).eval x)
        (command.evalValue value)
        (command.compile_represents hkRows hkCols x value hx)

end ICM2022NumCS97
