import ICM2022NumCS97.RouteGeometry

/-!
# Routing on an unbounded gap-three register grid

The sparse encoder places its master values on one residue-three grid.  This
module extends that grid indefinitely to the southeast.  An unbounded support
is harmless: all but finitely many values are zero, while each finite program
only sees a finite rectangle.  The benefit is that every later ReLU-circuit
node can be assigned a fresh grid point and reached by the same verified
collision-free route.
-/

namespace ICM2022NumCS97

def gridSite (d₁ d₂ r c : ℕ) : Site :=
  (d₁ - 1 + 3 * r, d₂ - 1 + 3 * c)

def IsGridSite (d₁ d₂ : ℕ) (s : Site) : Prop :=
  ∃ r c : ℕ, s = gridSite d₁ d₂ r c

noncomputable def gridSupport (d₁ d₂ : ℕ) (s : Site) : Bool := by
  classical
  exact decide (IsGridSite d₁ d₂ s)

@[simp] theorem gridSupport_eq_true_iff (d₁ d₂ : ℕ) (s : Site) :
    gridSupport d₁ d₂ s = true ↔ IsGridSite d₁ d₂ s := by
  classical
  simp [gridSupport]

@[simp] theorem gridSupport_site (d₁ d₂ r c : ℕ) :
    gridSupport d₁ d₂ (gridSite d₁ d₂ r c) = true := by
  rw [gridSupport_eq_true_iff]
  exact ⟨r, c, rfl⟩

theorem gridSupport_coordinate_form (d₁ d₂ : ℕ) (s : Site)
    (hs : gridSupport d₁ d₂ s = true) :
    (∃ r, s.1 = d₁ - 1 + 3 * r) ∧
      ∃ c, s.2 = d₂ - 1 + 3 * c := by
  rw [gridSupport_eq_true_iff] at hs
  obtain ⟨r, c, rfl⟩ := hs
  exact ⟨⟨r, rfl⟩, c, rfl⟩

theorem gridSupport_advance_eq_false (d₁ d₂ : ℕ)
    (direction : RouteDirection) (s : Site)
    (hs : gridSupport d₁ d₂ s = true) :
    gridSupport d₁ d₂ (advanceSite direction s) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨⟨r, hr⟩, c, hc⟩ :=
    gridSupport_coordinate_form d₁ d₂ s hs
  obtain ⟨⟨r', hr'⟩, c', hc'⟩ :=
    gridSupport_coordinate_form d₁ d₂ (advanceSite direction s) ht
  cases direction <;> simp only [advanceSite] at hr' hc' <;> omega

theorem gridSupport_incomingClear (d₁ d₂ : ℕ)
    (direction : RouteDirection) :
    IncomingClear direction (gridSupport d₁ d₂) :=
  incomingClear_of_advance_eq_false direction (gridSupport d₁ d₂)
    (gridSupport_advance_eq_false d₁ d₂ direction)

@[simp] theorem gridSite_masterSite {d₁ d₂ : ℕ}
    (i : Fin d₁) (j : Fin d₂) :
    gridSite d₁ d₂ i j = masterSite d₁ d₂ i j := rfl

/-- Circuit node `t` is one grid step beyond the input rectangle for `t = 0`
and then advances diagonally by one full gap-three step per node. -/
def circuitNodeSite (d₁ d₂ t : ℕ) : Site :=
  gridSite d₁ d₂ (d₁ + t) (d₂ + t)

@[simp] theorem gridSupport_circuitNode (d₁ d₂ t : ℕ) :
    gridSupport d₁ d₂ (circuitNodeSite d₁ d₂ t) = true :=
  gridSupport_site d₁ d₂ (d₁ + t) (d₂ + t)

def gridExit (d₁ d₂ r c : ℕ) : Site :=
  advanceSite .southeast (gridSite d₁ d₂ r c)

def gridEastSteps (c C : ℕ) : ℕ := 3 * (C - c) - 2

def gridSouthSteps (r R : ℕ) : ℕ := 3 * (R - r) - 2

def gridCorner (d₁ d₂ r c R C : ℕ) : Site :=
  advanceN .east (gridExit d₁ d₂ r c) (gridEastSteps c C)

def gridPreDestination (d₁ d₂ r c R C : ℕ) : Site :=
  advanceN .south (gridCorner d₁ d₂ r c R C) (gridSouthSteps r R)

theorem gridExit_eq (d₁ d₂ r c : ℕ) :
    gridExit d₁ d₂ r c =
      ((gridSite d₁ d₂ r c).1 + 1,
        (gridSite d₁ d₂ r c).2 + 1) := rfl

theorem gridCorner_eq {d₁ d₂ r c R C : ℕ} (hc : c < C) :
    gridCorner d₁ d₂ r c R C =
      ((gridSite d₁ d₂ r c).1 + 1,
        (gridSite d₁ d₂ R C).2 - 1) := by
  rw [gridCorner, gridExit_eq, advanceN_east]
  apply Prod.ext
  · rfl
  · simp only
    unfold gridEastSteps gridSite
    omega

theorem gridPreDestination_eq {d₁ d₂ r c R C : ℕ}
    (hr : r < R) (hc : c < C) :
    gridPreDestination d₁ d₂ r c R C =
      ((gridSite d₁ d₂ R C).1 - 1,
        (gridSite d₁ d₂ R C).2 - 1) := by
  rw [gridPreDestination, gridCorner_eq hc, advanceN_south]
  apply Prod.ext
  · simp only
    unfold gridSouthSteps gridSite
    omega
  · rfl

theorem advance_gridPreDestination_eq {d₁ d₂ r c R C : ℕ}
    (hr : r < R) (hc : c < C) :
    advanceSite .southeast (gridPreDestination d₁ d₂ r c R C) =
      gridSite d₁ d₂ R C := by
  rw [gridPreDestination_eq hr hc]
  unfold advanceSite gridSite
  apply Prod.ext <;> simp only <;> omega

/-- The row one site southeast of a grid row is outside the static grid. -/
theorem gridOffsetRow_not_grid (d₁ d₂ r c q : ℕ) :
    gridSupport d₁ d₂ ((gridSite d₁ d₂ r c).1 + 1, q) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r', hr'⟩, c', hc'⟩ :=
    gridSupport_coordinate_form d₁ d₂
      ((gridSite d₁ d₂ r c).1 + 1, q) hs
  simp only at hr'
  unfold gridSite at hr'
  omega

/-- The column immediately west of a strictly later grid column is outside
the static grid. -/
theorem gridPreDestinationCol_not_grid {d₁ d₂ c C : ℕ} (hc : c < C)
    (R p : ℕ) :
    gridSupport d₁ d₂ (p, (gridSite d₁ d₂ R C).2 - 1) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r', hr'⟩, c', hc'⟩ :=
    gridSupport_coordinate_form d₁ d₂
      (p, (gridSite d₁ d₂ R C).2 - 1) hs
  simp only at hc'
  unfold gridSite at hc'
  omega

/-- Copy a value from grid coordinate `(r,c)`, move it through off-grid
corridors, and merge it into the strictly southeast grid coordinate `(R,C)`.
Every other grid register is preserved. -/
noncomputable def routeGridToGridSteps (d₁ d₂ r c R C : ℕ)
    (coefficient : ℝ) : List RouteStep :=
  let support := gridSupport d₁ d₂
  let exit := gridExit d₁ d₂ r c
  let corner := gridCorner d₁ d₂ r c R C
  { direction := .southeast
    coefficient := coefficient
    keep := keepStaticOr support exit } ::
    (moveSteps .east support exit (gridEastSteps c C) ++
      (moveSteps .south support corner (gridSouthSteps r R) ++
        [{ direction := .southeast
           coefficient := 1
           keep := fun p q ↦ support (p, q) }]))

/-- Exact no-crosstalk semantics of the generic grid route. -/
theorem executeRoute_routeGridToGrid {d₁ d₂ r c R C : ℕ}
    (hr : r < R) (hc : c < C)
    (coefficient : ℝ) (value : Site → ℝ) :
    executeRoute
        (routeGridToGridSteps d₁ d₂ r c R C coefficient)
        (staticState (gridSupport d₁ d₂) value) =
      staticState (gridSupport d₁ d₂)
        (updateAt value (gridSite d₁ d₂ R C)
          (value (gridSite d₁ d₂ R C) +
            coefficient * value (gridSite d₁ d₂ r c))) := by
  let support := gridSupport d₁ d₂
  let source := gridSite d₁ d₂ r c
  let destination := gridSite d₁ d₂ R C
  let exit := gridExit d₁ d₂ r c
  let corner := gridCorner d₁ d₂ r c R C
  let pre := gridPreDestination d₁ d₂ r c R C
  let token := coefficient * value source
  have hsource : support source = true := gridSupport_site d₁ d₂ r c
  have hexit : support exit = false := by
    dsimp only [support, exit]
    rw [gridExit_eq]
    exact gridOffsetRow_not_grid d₁ d₂ r c _
  have hcopyQuiet : ∀ s, support s = true →
      shiftedValue .southeast (staticState support value) s.1 s.2 = 0 := by
    intro s hs
    exact shiftedValue_staticState_eq_zero .southeast support
      (gridSupport_incomingClear d₁ d₂ .southeast) value s hs
  have hcopy :
      routeStep .southeast coefficient (keepStaticOr support exit)
          (staticState support value) =
        movingState support value exit token := by
    exact routeStep_copy_from_static .southeast coefficient support value source
      hsource hexit hcopyQuiet
  have heastFree : ∀ t ≤ gridEastSteps c C,
      support (advanceN .east exit t) = false := by
    intro t ht
    dsimp only [support, exit]
    rw [gridExit_eq, advanceN_east]
    exact gridOffsetRow_not_grid d₁ d₂ r c _
  have heast :
      executeRoute (moveSteps .east support exit (gridEastSteps c C))
          (movingState support value exit token) =
        movingState support value corner token := by
    have h := executeRoute_moveSteps .east support
      (gridSupport_incomingClear d₁ d₂ .east) value exit token
      (gridEastSteps c C) heastFree
    change executeRoute (moveSteps .east support exit (gridEastSteps c C))
        (movingState support value exit token) =
      movingState support value
        (advanceN .east exit (gridEastSteps c C)) token
    exact h
  have hsouthFree : ∀ t ≤ gridSouthSteps r R,
      support (advanceN .south corner t) = false := by
    intro t ht
    dsimp only [support, corner]
    rw [gridCorner_eq hc, advanceN_south]
    exact gridPreDestinationCol_not_grid hc R _
  have hsouth :
      executeRoute (moveSteps .south support corner (gridSouthSteps r R))
          (movingState support value corner token) =
        movingState support value pre token := by
    have h := executeRoute_moveSteps .south support
      (gridSupport_incomingClear d₁ d₂ .south) value corner token
      (gridSouthSteps r R) hsouthFree
    change executeRoute (moveSteps .south support corner (gridSouthSteps r R))
        (movingState support value corner token) =
      movingState support value
        (advanceN .south corner (gridSouthSteps r R)) token
    exact h
  have hdestination : support destination = true :=
    gridSupport_site d₁ d₂ R C
  have hpre : support pre = false := by
    dsimp only [support, pre]
    rw [gridPreDestination_eq hr hc]
    exact gridPreDestinationCol_not_grid hc R _
  have hadvance : advanceSite .southeast pre = destination := by
    exact advance_gridPreDestination_eq hr hc
  have hmergeQuiet : ∀ s, support s = true → s ≠ destination →
      shiftedValue .southeast (movingState support value pre token)
        s.1 s.2 = 0 := by
    intro s hs hne
    apply shiftedValue_movingState_eq_zero_of_advance_ne .southeast support
      (gridSupport_incomingClear d₁ d₂ .southeast)
      value pre token s hs
    rw [hadvance]
    exact hne.symm
  have hmerge :
      routeStep .southeast 1 (fun p q ↦ support (p, q))
          (movingState support value pre token) =
        staticState support
          (updateAt value destination (value destination + token)) := by
    exact routeStep_merge_token .southeast support value pre destination token
      hdestination hpre hadvance hmergeQuiet
  change executeRoute
      ({ direction := .southeast
         coefficient := coefficient
         keep := keepStaticOr support exit } ::
        (moveSteps .east support exit (gridEastSteps c C) ++
          (moveSteps .south support corner (gridSouthSteps r R) ++
            [{ direction := .southeast
               coefficient := 1
               keep := fun p q ↦ support (p, q) }])))
      (staticState support value) = _
  simp only [executeRoute]
  change executeRoute
      (moveSteps .east support exit (gridEastSteps c C) ++
        (moveSteps .south support corner (gridSouthSteps r R) ++
          [{ direction := .southeast
             coefficient := 1
             keep := fun p q ↦ support (p, q) }]))
      (routeStep .southeast coefficient (keepStaticOr support exit)
        (staticState support value)) = _
  rw [hcopy, executeRoute_append, heast, executeRoute_append, hsouth]
  simp only [executeRoute]
  change routeStep .southeast 1 (fun p q ↦ support (p, q))
      (movingState support value pre token) = _
  simpa [support, source, destination, token] using hmerge

end ICM2022NumCS97
