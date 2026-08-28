import OneChannelCNNUniversality.HybridProgram

/-!
# A genuine ReLU at the work register

The routing phases are linearized by compact carriers.  This module supplies
the one symbolic instruction at which the work register is intentionally
allowed to cross zero.  All other static registers remain linear, and the
hybrid compiler later turns this symbolic instruction into an actual CNN
layer with the required spatial biases.
-/

namespace OneChannelCNNUniversality

noncomputable def activateWorkKeep (d₁ d₂ : ℕ) {rows cols : ℕ}
    (p : Fin rows) (q : Fin cols) : Bool :=
  registerSupport d₁ d₂ (p, q)

noncomputable def activateWorkMode (d₁ d₂ : ℕ) (offset : ℝ)
    {rows cols : ℕ} (p : Fin rows) (q : Fin cols) : ActivationMode :=
  if ((p : ℕ), (q : ℕ)) = workSite d₁ d₂ then .relu offset else .linear

noncomputable def activateWorkProgram {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (d₁ d₂ : ℕ) (offset : ℝ) :
    HybridProgramTo kRows kCols rows cols
      (rows + kRows - 1) (cols + kCols - 1) :=
  HybridProgramTo.cons (identityKernel hkRows hkCols)
    (activateWorkKeep d₁ d₂) (activateWorkMode d₁ d₂ offset)
    (HybridProgramTo.nil (rows + kRows - 1) (cols + kCols - 1)
      kRows kCols)

noncomputable def activateWorkState (d₁ d₂ : ℕ) (offset : ℝ)
    (z : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun p q ↦ if registerSupport d₁ d₂ (p, q) then
    if (p, q) = workSite d₁ d₂ then relu (z p q + offset) else z p q
  else 0

theorem activateWorkState_static (d₁ d₂ : ℕ) (offset : ℝ)
    (value : Site → ℝ) :
    activateWorkState d₁ d₂ offset
        (staticState (registerSupport d₁ d₂) value) =
      staticState (registerSupport d₁ d₂)
        (updateAt value (workSite d₁ d₂)
          (relu (value (workSite d₁ d₂) + offset))) := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : registerSupport d₁ d₂ s = true
  · by_cases hw : s = workSite d₁ d₂
    · simp [activateWorkState, staticState, updateAt, s, hs, hw]
    · simp [activateWorkState, staticState, updateAt, s, hs, hw]
  · have hsfalse : registerSupport d₁ d₂ s = false :=
      Bool.eq_false_of_not_eq_true hs
    simp [activateWorkState, staticState, s, hsfalse]

/-- Finite one-layer activation refines its infinite sparse-state semantics.
The two bounds merely state that the work site has already been reached by
the preceding routes. -/
theorem activateWorkProgram_represents
    {kRows kCols rows cols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (offset : ℝ) (x : Image rows cols) (z : ℕ → ℕ → ℝ)
    (hx : RepresentsInfinite x z)
    (hworkRow : (workSite d₁ d₂).1 < rows + kRows - 1)
    (hworkCol : (workSite d₁ d₂).2 < cols + kCols - 1) :
    RepresentsInfinite
      ((activateWorkProgram hkRows hkCols d₁ d₂ offset).eval x)
      (activateWorkState d₁ d₂ offset z) := by
  intro p q
  by_cases hp : p < rows + kRows - 1
  · by_cases hq : q < cols + kCols - 1
    · rw [zeroExtend_of_lt _ hp hq]
      rw [activateWorkProgram, HybridProgramTo.eval_cons,
        HybridProgramTo.eval_nil]
      simp only [activateWorkKeep, activateWorkMode]
      change (if registerSupport d₁ d₂ (p, q) = true then
          ActivationMode.eval
            (if (p, q) = workSite d₁ d₂ then .relu offset else .linear)
            (fullConv (identityKernel hkRows hkCols) x p q)
        else 0) = activateWorkState d₁ d₂ offset z p q
      rw [fullConv_identityKernel hkRows hkCols, hx p q]
      by_cases hs : registerSupport d₁ d₂ (p, q) = true
      · by_cases hw : (p, q) = workSite d₁ d₂
        · simp [activateWorkState, ActivationMode.eval, hs, hw]
        · simp [activateWorkState, ActivationMode.eval, hs, hw]
      · have hsfalse : registerSupport d₁ d₂ (p, q) = false :=
          Bool.eq_false_of_not_eq_true hs
        simp [activateWorkState, hsfalse]
    · rw [zeroExtend_col_outside (hj := Nat.le_of_not_gt hq)]
      have hinput : cols ≤ q := by omega
      have hz : z p q = 0 := by
        rw [← hx p q, zeroExtend_col_outside x hinput]
      have hnotWork : (p, q) ≠ workSite d₁ d₂ := by
        intro h
        have := congrArg Prod.snd h
        simp only at this
        omega
      simp [activateWorkState, hnotWork, hz]
  · rw [zeroExtend_row_outside (hi := Nat.le_of_not_gt hp)]
    have hinput : rows ≤ p := by omega
    have hz : z p q = 0 := by
      rw [← hx p q, zeroExtend_row_outside x hinput]
    have hnotWork : (p, q) ≠ workSite d₁ d₂ := by
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
    simp [activateWorkState, hnotWork, hz]

theorem activateWorkProgram_represents_static
    {kRows kCols rows cols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (offset : ℝ) (x : Image rows cols) (value : Site → ℝ)
    (hx : RepresentsInfinite x
      (staticState (registerSupport d₁ d₂) value))
    (hworkRow : (workSite d₁ d₂).1 < rows + kRows - 1)
    (hworkCol : (workSite d₁ d₂).2 < cols + kCols - 1) :
    RepresentsInfinite
      ((activateWorkProgram hkRows hkCols d₁ d₂ offset).eval x)
      (staticState (registerSupport d₁ d₂)
        (updateAt value (workSite d₁ d₂)
          (relu (value (workSite d₁ d₂) + offset)))) := by
  rw [← activateWorkState_static]
  exact activateWorkProgram_represents hkRows hkCols offset x _ hx
    hworkRow hworkCol

noncomputable def linearRouteProgram {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (steps : List RouteStep) :
    HybridProgramTo kRows kCols rows cols
      (grownSize kRows rows steps.length) (grownSize kCols cols steps.length) :=
  HybridProgramTo.ofMaskProgramTo (routeProgram hkRows hkCols steps)

@[simp] theorem linearRouteProgram_eval {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (steps : List RouteStep)
    (x : Image rows cols) :
    (linearRouteProgram hkRows hkCols steps).eval x =
      (routeProgram hkRows hkCols steps).eval x := by
  exact HybridProgramTo.eval_ofMaskProgramTo _ x

noncomputable def ridgeMidRows (kRows rows d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  grownSize kRows rows
    (routeMastersToWorkSteps d₁ d₂ coefficient entries).length

noncomputable def ridgeMidCols (kCols cols d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  grownSize kCols cols
    (routeMastersToWorkSteps d₁ d₂ coefficient entries).length

noncomputable def ridgeActivatedRows (kRows rows d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  ridgeMidRows kRows rows d₁ d₂ coefficient entries + kRows - 1

noncomputable def ridgeActivatedCols (kCols cols d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  ridgeMidCols kCols cols d₁ d₂ coefficient entries + kCols - 1

noncomputable def ridgeOutRows (kRows rows d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  grownSize kRows (ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
    (routeWorkToSumSteps d₁ d₂ 0).length

noncomputable def ridgeOutCols (kCols cols d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℕ :=
  grownSize kCols (ridgeActivatedCols kCols cols d₁ d₂ coefficient entries)
    (routeWorkToSumSteps d₁ d₂ 0).length

/-- One complete ridge block: form a linear functional at work, trigger one
actual ReLU, scale/merge into sum, and clear work. -/
noncomputable def ridgeBlock {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) (offset outputCoefficient : ℝ) :
    HybridProgramTo kRows kCols rows cols
      (ridgeOutRows kRows rows d₁ d₂ coefficient entries)
      (ridgeOutCols kCols cols d₁ d₂ coefficient entries) :=
  let masterSteps := routeMastersToWorkSteps d₁ d₂ coefficient entries
  let first : HybridProgramTo kRows kCols rows cols
      (ridgeMidRows kRows rows d₁ d₂ coefficient entries)
      (ridgeMidCols kCols cols d₁ d₂ coefficient entries) :=
    linearRouteProgram hkRows hkCols masterSteps
  let activate : HybridProgramTo kRows kCols
      (ridgeMidRows kRows rows d₁ d₂ coefficient entries)
      (ridgeMidCols kCols cols d₁ d₂ coefficient entries)
      (ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
      (ridgeActivatedCols kCols cols d₁ d₂ coefficient entries) :=
    activateWorkProgram hkRows hkCols d₁ d₂ offset
  let workSteps := routeWorkToSumSteps d₁ d₂ outputCoefficient
  let finish : HybridProgramTo kRows kCols
      (ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
      (ridgeActivatedCols kCols cols d₁ d₂ coefficient entries)
      (ridgeOutRows kRows rows d₁ d₂ coefficient entries)
      (ridgeOutCols kCols cols d₁ d₂ coefficient entries) :=
    linearRouteProgram hkRows hkCols workSteps
  (first.append activate).append finish

def clearWorkValue (d₁ d₂ : ℕ) (value : Site → ℝ) : Site → ℝ :=
  updateAt value (workSite d₁ d₂) 0

theorem static_ridgeSupport_eq_clearWork (d₁ d₂ : ℕ)
    (value : Site → ℝ) :
    staticState (ridgeSupport d₁ d₂) value =
      staticState (registerSupport d₁ d₂) (clearWorkValue d₁ d₂ value) := by
  funext p q
  let s : Site := (p, q)
  by_cases hw : s = workSite d₁ d₂
  · have hsmall : ridgeSupport d₁ d₂ s = false := by
      rw [hw]
      exact ridgeSupport_work d₁ d₂
    have hbig : registerSupport d₁ d₂ s = true := by
      rw [hw]
      exact registerSupport_work d₁ d₂
    simp [staticState, clearWorkValue, s, hsmall, hbig, hw]
  · by_cases hs : registerSupport d₁ d₂ s = true
    · have hsmall : ridgeSupport d₁ d₂ s = true :=
        (ridgeSupport_eq_true_iff d₁ d₂ s).mpr ⟨hs, hw⟩
      simp [staticState, clearWorkValue, s, hs, hsmall, hw]
    · have hsfalse : registerSupport d₁ d₂ s = false :=
        Bool.eq_false_of_not_eq_true hs
      have hsmall : ridgeSupport d₁ d₂ s = false := by
        apply Bool.eq_false_of_not_eq_true
        intro h
        exact hs (ridgeSupport_sub_register d₁ d₂ s h)
      simp [staticState, s, hsfalse, hsmall]

def ridgeTransform (d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂))
    (offset outputCoefficient : ℝ) (value : Site → ℝ) : Site → ℝ :=
  let linear := accumulateAt value (workSite d₁ d₂)
    (masterWeightedSum d₁ d₂ coefficient value entries)
  let activated := updateAt linear (workSite d₁ d₂)
    (relu (linear (workSite d₁ d₂) + offset))
  let merged := updateAt activated (sumSite d₁ d₂)
    (activated (sumSite d₁ d₂) +
      outputCoefficient * activated (workSite d₁ d₂))
  clearWorkValue d₁ d₂ merged

theorem ridgeBlock_represents
    {kRows kCols rows cols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (coefficient : Fin d₁ → Fin d₂ → ℝ)
    (entries : List (Fin d₁ × Fin d₂))
    (offset outputCoefficient : ℝ) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (registerSupport d₁ d₂) value))
    (hworkRow : (workSite d₁ d₂).1 <
      ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
    (hworkCol : (workSite d₁ d₂).2 <
      ridgeActivatedCols kCols cols d₁ d₂ coefficient entries) :
    RepresentsInfinite
      ((ridgeBlock hkRows hkCols d₁ d₂ coefficient entries offset
        outputCoefficient).eval x)
      (staticState (registerSupport d₁ d₂)
        (ridgeTransform d₁ d₂ coefficient entries offset outputCoefficient value)) := by
  let masterSteps := routeMastersToWorkSteps d₁ d₂ coefficient entries
  let first : HybridProgramTo kRows kCols rows cols
      (ridgeMidRows kRows rows d₁ d₂ coefficient entries)
      (ridgeMidCols kCols cols d₁ d₂ coefficient entries) :=
    linearRouteProgram hkRows hkCols masterSteps
  let linear := accumulateAt value (workSite d₁ d₂)
    (masterWeightedSum d₁ d₂ coefficient value entries)
  have hfirst : RepresentsInfinite (first.eval x)
      (staticState (registerSupport d₁ d₂) linear) := by
    change RepresentsInfinite
      ((linearRouteProgram hkRows hkCols masterSteps).eval x)
      (staticState (registerSupport d₁ d₂) linear)
    rw [linearRouteProgram_eval]
    have h := routeProgram_represents hkRows hkCols masterSteps x
      (staticState (registerSupport d₁ d₂) value) hx
    rw [executeRoute_routeMastersToWork hd₁ hd₂] at h
    exact h
  let activate : HybridProgramTo kRows kCols
      (ridgeMidRows kRows rows d₁ d₂ coefficient entries)
      (ridgeMidCols kCols cols d₁ d₂ coefficient entries)
      (ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
      (ridgeActivatedCols kCols cols d₁ d₂ coefficient entries) :=
    activateWorkProgram hkRows hkCols d₁ d₂ offset
  let activated := updateAt linear (workSite d₁ d₂)
    (relu (linear (workSite d₁ d₂) + offset))
  have hactivate : RepresentsInfinite (activate.eval (first.eval x))
      (staticState (registerSupport d₁ d₂) activated) := by
    exact activateWorkProgram_represents_static hkRows hkCols offset
      (first.eval x) linear hfirst hworkRow hworkCol
  let workSteps := routeWorkToSumSteps d₁ d₂ outputCoefficient
  let finish : HybridProgramTo kRows kCols
      (ridgeActivatedRows kRows rows d₁ d₂ coefficient entries)
      (ridgeActivatedCols kCols cols d₁ d₂ coefficient entries)
      (ridgeOutRows kRows rows d₁ d₂ coefficient entries)
      (ridgeOutCols kCols cols d₁ d₂ coefficient entries) :=
    linearRouteProgram hkRows hkCols workSteps
  let merged := updateAt activated (sumSite d₁ d₂)
    (activated (sumSite d₁ d₂) +
      outputCoefficient * activated (workSite d₁ d₂))
  have hfinish : RepresentsInfinite (finish.eval (activate.eval (first.eval x)))
      (staticState (registerSupport d₁ d₂) (clearWorkValue d₁ d₂ merged)) := by
    change RepresentsInfinite
      ((linearRouteProgram hkRows hkCols workSteps).eval
        (activate.eval (first.eval x)))
      (staticState (registerSupport d₁ d₂) (clearWorkValue d₁ d₂ merged))
    rw [linearRouteProgram_eval]
    have h := routeProgram_represents hkRows hkCols workSteps
      (activate.eval (first.eval x))
      (staticState (registerSupport d₁ d₂) activated) hactivate
    rw [executeRoute_routeWorkToSum] at h
    rw [static_ridgeSupport_eq_clearWork] at h
    exact h
  rw [ridgeBlock, HybridProgramTo.eval_append, HybridProgramTo.eval_append]
  exact hfinish

end OneChannelCNNUniversality
