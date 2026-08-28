import ICM2022NumCS97.RegisterProgram

/-!
# Fixed gap-three register geometry

The encoder masters, the work register, and the sum register all lie on the
same residue-three grid in each coordinate.  Consequently none of the three
two-tap routing kernels can read one static register into another.  This file
turns that arithmetic fact into the `IncomingClear` invariant used by the
verified register instructions.
-/

namespace ICM2022NumCS97

def masterSite (d₁ d₂ : ℕ) (i : Fin d₁) (j : Fin d₂) : Site :=
  (encoderSite d₁ i, encoderSite d₂ j)

def IsMasterSite (d₁ d₂ : ℕ) (s : Site) : Prop :=
  ∃ i : Fin d₁, ∃ j : Fin d₂, s = masterSite d₁ d₂ i j

/-- The first grid point strictly beyond every master coordinate when the
corresponding input dimension is positive. -/
def workSite (d₁ d₂ : ℕ) : Site :=
  (d₁ - 1 + 3 * d₁, d₂ - 1 + 3 * d₂)

/-- A second reserved point, one full gap-three step southeast of `workSite`. -/
def sumSite (d₁ d₂ : ℕ) : Site :=
  (d₁ - 1 + 3 * (d₁ + 1), d₂ - 1 + 3 * (d₂ + 1))

def IsRegisterSite (d₁ d₂ : ℕ) (s : Site) : Prop :=
  IsMasterSite d₁ d₂ s ∨ s = workSite d₁ d₂ ∨ s = sumSite d₁ d₂

noncomputable def registerSupport (d₁ d₂ : ℕ) (s : Site) : Bool := by
  classical
  exact decide (IsRegisterSite d₁ d₂ s)

@[simp] theorem registerSupport_eq_true_iff (d₁ d₂ : ℕ) (s : Site) :
    registerSupport d₁ d₂ s = true ↔ IsRegisterSite d₁ d₂ s := by
  classical
  simp [registerSupport]

@[simp] theorem registerSupport_master {d₁ d₂ : ℕ}
    (i : Fin d₁) (j : Fin d₂) :
    registerSupport d₁ d₂ (masterSite d₁ d₂ i j) = true := by
  rw [registerSupport_eq_true_iff]
  exact Or.inl ⟨i, j, rfl⟩

@[simp] theorem registerSupport_work (d₁ d₂ : ℕ) :
    registerSupport d₁ d₂ (workSite d₁ d₂) = true := by
  rw [registerSupport_eq_true_iff]
  exact Or.inr (Or.inl rfl)

@[simp] theorem registerSupport_sum (d₁ d₂ : ℕ) :
    registerSupport d₁ d₂ (sumSite d₁ d₂) = true := by
  rw [registerSupport_eq_true_iff]
  exact Or.inr (Or.inr rfl)

theorem masterSite_ne_work {d₁ d₂ : ℕ} (i : Fin d₁) (j : Fin d₂) :
    masterSite d₁ d₂ i j ≠ workSite d₁ d₂ := by
  intro h
  have hrow := congrArg Prod.fst h
  have hi : (i : ℕ) < d₁ := i.isLt
  unfold masterSite encoderSite workSite at hrow
  omega

theorem sumSite_ne_work (d₁ d₂ : ℕ) :
    sumSite d₁ d₂ ≠ workSite d₁ d₂ := by
  intro h
  have hrow := congrArg Prod.fst h
  unfold sumSite workSite at hrow
  omega

/-- Static support after the work register has been consumed. -/
noncomputable def ridgeSupport (d₁ d₂ : ℕ) (s : Site) : Bool :=
  registerSupport d₁ d₂ s && decide (s ≠ workSite d₁ d₂)

@[simp] theorem ridgeSupport_eq_true_iff (d₁ d₂ : ℕ) (s : Site) :
    ridgeSupport d₁ d₂ s = true ↔
      registerSupport d₁ d₂ s = true ∧ s ≠ workSite d₁ d₂ := by
  classical
  simp [ridgeSupport]

@[simp] theorem ridgeSupport_master {d₁ d₂ : ℕ}
    (i : Fin d₁) (j : Fin d₂) :
    ridgeSupport d₁ d₂ (masterSite d₁ d₂ i j) = true := by
  rw [ridgeSupport_eq_true_iff]
  exact ⟨registerSupport_master i j, masterSite_ne_work i j⟩

@[simp] theorem ridgeSupport_sum (d₁ d₂ : ℕ) :
    ridgeSupport d₁ d₂ (sumSite d₁ d₂) = true := by
  rw [ridgeSupport_eq_true_iff]
  exact ⟨registerSupport_sum d₁ d₂, sumSite_ne_work d₁ d₂⟩

@[simp] theorem ridgeSupport_work (d₁ d₂ : ℕ) :
    ridgeSupport d₁ d₂ (workSite d₁ d₂) = false := by
  classical
  simp [ridgeSupport]

theorem ridgeSupport_sub_register (d₁ d₂ : ℕ) (s : Site)
    (hs : ridgeSupport d₁ d₂ s = true) :
    registerSupport d₁ d₂ s = true :=
  (ridgeSupport_eq_true_iff d₁ d₂ s).mp hs |>.1

/-- Every retained coordinate is on the same residue-three grid. -/
theorem registerSupport_coordinate_form (d₁ d₂ : ℕ) (s : Site)
    (hs : registerSupport d₁ d₂ s = true) :
    (∃ r, s.1 = d₁ - 1 + 3 * r) ∧
      ∃ c, s.2 = d₂ - 1 + 3 * c := by
  rw [registerSupport_eq_true_iff] at hs
  rcases hs with ⟨i, j, rfl⟩ | hwork | hsum
  · exact ⟨⟨i, rfl⟩, j, rfl⟩
  · subst s
    exact ⟨⟨d₁, rfl⟩, d₂, rfl⟩
  · subst s
    exact ⟨⟨d₁ + 1, rfl⟩, d₂ + 1, rfl⟩

/-- Advancing one east, south, or southeast step always leaves the static
gap-three grid. -/
theorem registerSupport_advance_eq_false (d₁ d₂ : ℕ)
    (direction : RouteDirection) (s : Site)
    (hs : registerSupport d₁ d₂ s = true) :
    registerSupport d₁ d₂ (advanceSite direction s) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨⟨r, hr⟩, c, hc⟩ := registerSupport_coordinate_form d₁ d₂ s hs
  obtain ⟨⟨r', hr'⟩, c', hc'⟩ :=
    registerSupport_coordinate_form d₁ d₂ (advanceSite direction s) ht
  cases direction <;> simp only [advanceSite] at hr' hc' <;> omega

/-- The fixed register support satisfies the global no-crosstalk invariant
for every routing direction. -/
theorem registerSupport_incomingClear (d₁ d₂ : ℕ)
    (direction : RouteDirection) :
    IncomingClear direction (registerSupport d₁ d₂) := by
  intro s hs
  rcases s with ⟨p, q⟩
  cases direction with
  | east =>
      by_cases hq : 1 ≤ q
      · have hpred := registerSupport_advance_eq_false d₁ d₂ .east
            (p, q - 1)
        by_cases hp : registerSupport d₁ d₂ (p, q - 1) = true
        · have hout := hpred hp
          have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hq
          simp [advanceSite, hqeq, hs] at hout
        · have hp' : registerSupport d₁ d₂ (p, q - 1) = false :=
            Bool.eq_false_of_not_eq_true hp
          simp [shiftedSupport, hq, hp']
      · simp [shiftedSupport, hq]
  | south =>
      by_cases hp : 1 ≤ p
      · have hpred := registerSupport_advance_eq_false d₁ d₂ .south
            (p - 1, q)
        by_cases hsource : registerSupport d₁ d₂ (p - 1, q) = true
        · have hout := hpred hsource
          have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hp
          simp [advanceSite, hpeq, hs] at hout
        · have hsource' : registerSupport d₁ d₂ (p - 1, q) = false :=
            Bool.eq_false_of_not_eq_true hsource
          simp [shiftedSupport, hp, hsource']
      · simp [shiftedSupport, hp]
  | southeast =>
      by_cases hpq : 1 ≤ p ∧ 1 ≤ q
      · have hpred := registerSupport_advance_eq_false d₁ d₂ .southeast
            (p - 1, q - 1)
        by_cases hsource : registerSupport d₁ d₂ (p - 1, q - 1) = true
        · have hout := hpred hsource
          have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hpq.1
          have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hpq.2
          simp [advanceSite, hpeq, hqeq, hs] at hout
        · have hsource' : registerSupport d₁ d₂ (p - 1, q - 1) = false :=
            Bool.eq_false_of_not_eq_true hsource
          simp [shiftedSupport, hpq, hsource']
      · simp [shiftedSupport, hpq]

theorem ridgeSupport_advance_eq_false (d₁ d₂ : ℕ)
    (direction : RouteDirection) (s : Site)
    (hs : ridgeSupport d₁ d₂ s = true) :
    ridgeSupport d₁ d₂ (advanceSite direction s) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  have hsBig := ridgeSupport_sub_register d₁ d₂ s hs
  have htBig := ridgeSupport_sub_register d₁ d₂ _ ht
  rw [registerSupport_advance_eq_false d₁ d₂ direction s hsBig] at htBig
  contradiction

theorem ridgeSupport_incomingClear (d₁ d₂ : ℕ)
    (direction : RouteDirection) :
    IncomingClear direction (ridgeSupport d₁ d₂) :=
  incomingClear_of_advance_eq_false direction (ridgeSupport d₁ d₂)
    (ridgeSupport_advance_eq_false d₁ d₂ direction)

/-- A whole row one site below a master row is outside the residue-three
register grid. -/
theorem masterOffsetRow_not_register {d₁ d₂ : ℕ} (i : Fin d₁) (q : ℕ) :
    registerSupport d₁ d₂ (encoderSite d₁ i + 1, q) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r, hr⟩, c, hc⟩ :=
    registerSupport_coordinate_form d₁ d₂
      (encoderSite d₁ i + 1, q) hs
  simp only at hr
  unfold encoderSite at hr
  omega

/-- The column immediately west of the work register is off the grid. -/
theorem preWorkCol_not_register {d₁ d₂ : ℕ} (hd₂ : 0 < d₂) (p : ℕ) :
    registerSupport d₁ d₂ (p, (workSite d₁ d₂).2 - 1) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r, hr⟩, c, hc⟩ :=
    registerSupport_coordinate_form d₁ d₂
      (p, (workSite d₁ d₂).2 - 1) hs
  simp only at hc
  unfold workSite at hc
  omega

def masterExit (d₁ d₂ : ℕ) (i : Fin d₁) (j : Fin d₂) : Site :=
  advanceSite .southeast (masterSite d₁ d₂ i j)

def masterEastSteps {d₂ : ℕ} (j : Fin d₂) : ℕ :=
  3 * (d₂ - (j : ℕ)) - 2

def masterSouthSteps {d₁ : ℕ} (i : Fin d₁) : ℕ :=
  3 * (d₁ - (i : ℕ)) - 2

def masterCorner (d₁ d₂ : ℕ) (i : Fin d₁) (j : Fin d₂) : Site :=
  advanceN .east (masterExit d₁ d₂ i j) (masterEastSteps j)

def masterPreWork (d₁ d₂ : ℕ) (i : Fin d₁) (j : Fin d₂) : Site :=
  advanceN .south (masterCorner d₁ d₂ i j) (masterSouthSteps i)

theorem masterExit_eq (d₁ d₂ : ℕ) (i : Fin d₁) (j : Fin d₂) :
    masterExit d₁ d₂ i j =
      (encoderSite d₁ i + 1, encoderSite d₂ j + 1) := by
  rfl

theorem masterCorner_eq {d₁ d₂ : ℕ} (hd₂ : 0 < d₂)
    (i : Fin d₁) (j : Fin d₂) :
    masterCorner d₁ d₂ i j =
      (encoderSite d₁ i + 1, (workSite d₁ d₂).2 - 1) := by
  rw [masterCorner, masterExit_eq, advanceN_east]
  apply Prod.ext
  · rfl
  · simp only
    have hj : (j : ℕ) < d₂ := j.isLt
    unfold masterEastSteps encoderSite workSite
    omega

theorem masterPreWork_eq {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (i : Fin d₁) (j : Fin d₂) :
    masterPreWork d₁ d₂ i j =
      ((workSite d₁ d₂).1 - 1, (workSite d₁ d₂).2 - 1) := by
  rw [masterPreWork, masterCorner_eq hd₂, advanceN_south]
  apply Prod.ext
  · simp only
    have hi : (i : ℕ) < d₁ := i.isLt
    unfold masterSouthSteps encoderSite workSite
    omega
  · rfl

theorem advance_masterPreWork_eq_work {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (i : Fin d₁) (j : Fin d₂) :
    advanceSite .southeast (masterPreWork d₁ d₂ i j) =
      workSite d₁ d₂ := by
  rw [masterPreWork_eq hd₁ hd₂]
  unfold advanceSite workSite
  apply Prod.ext <;> simp only <;> omega

/-- Concrete diagonal/east/south/diagonal route from one master to the work
register. -/
noncomputable def routeMasterToWorkSteps (d₁ d₂ : ℕ)
    (i : Fin d₁) (j : Fin d₂) (coefficient : ℝ) : List RouteStep :=
  let support := registerSupport d₁ d₂
  let exit := masterExit d₁ d₂ i j
  let corner := masterCorner d₁ d₂ i j
  let preWork := masterPreWork d₁ d₂ i j
  { direction := .southeast
    coefficient := coefficient
    keep := keepStaticOr support exit } ::
    (moveSteps .east support exit (masterEastSteps j) ++
      (moveSteps .south support corner (masterSouthSteps i) ++
        [{ direction := .southeast
           coefficient := 1
           keep := fun p q ↦ support (p, q) }]))

/-- Exact ideal semantics of the complete master-to-work route. -/
theorem executeRoute_routeMasterToWork {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (i : Fin d₁) (j : Fin d₂) (coefficient : ℝ) (value : Site → ℝ) :
    executeRoute (routeMasterToWorkSteps d₁ d₂ i j coefficient)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (registerSupport d₁ d₂)
        (updateAt value (workSite d₁ d₂)
          (value (workSite d₁ d₂) +
            coefficient * value (masterSite d₁ d₂ i j))) := by
  let support := registerSupport d₁ d₂
  let source := masterSite d₁ d₂ i j
  let exit := masterExit d₁ d₂ i j
  let corner := masterCorner d₁ d₂ i j
  let preWork := masterPreWork d₁ d₂ i j
  let token := coefficient * value source
  have hsource : support source = true := by
    exact registerSupport_master i j
  have hexit : support exit = false := by
    dsimp only [support, exit]
    rw [masterExit_eq]
    exact masterOffsetRow_not_register i _
  have hcopyQuiet : ∀ s, support s = true →
      shiftedValue .southeast (staticState support value) s.1 s.2 = 0 := by
    intro s hs
    exact shiftedValue_staticState_eq_zero .southeast support
      (registerSupport_incomingClear d₁ d₂ .southeast) value s hs
  have hcopy :
      routeStep .southeast coefficient (keepStaticOr support exit)
          (staticState support value) =
        movingState support value exit token := by
    exact routeStep_copy_from_static .southeast coefficient support value source
      hsource hexit hcopyQuiet
  have heastFree : ∀ t ≤ masterEastSteps j,
      support (advanceN .east exit t) = false := by
    intro t ht
    dsimp only [support, exit]
    rw [masterExit_eq, advanceN_east]
    exact masterOffsetRow_not_register i _
  have heast :
      executeRoute (moveSteps .east support exit (masterEastSteps j))
          (movingState support value exit token) =
        movingState support value corner token := by
    have h := executeRoute_moveSteps .east support
      (registerSupport_incomingClear d₁ d₂ .east) value exit token
      (masterEastSteps j) heastFree
    change executeRoute (moveSteps .east support exit (masterEastSteps j))
        (movingState support value exit token) =
      movingState support value
        (advanceN .east exit (masterEastSteps j)) token
    exact h
  have hsouthFree : ∀ t ≤ masterSouthSteps i,
      support (advanceN .south corner t) = false := by
    intro t ht
    dsimp only [support, corner]
    rw [masterCorner_eq hd₂, advanceN_south]
    exact preWorkCol_not_register hd₂ _
  have hsouth :
      executeRoute (moveSteps .south support corner (masterSouthSteps i))
          (movingState support value corner token) =
        movingState support value preWork token := by
    have h := executeRoute_moveSteps .south support
      (registerSupport_incomingClear d₁ d₂ .south) value corner token
      (masterSouthSteps i) hsouthFree
    change executeRoute (moveSteps .south support corner (masterSouthSteps i))
        (movingState support value corner token) =
      movingState support value
        (advanceN .south corner (masterSouthSteps i)) token
    exact h
  have hwork : support (workSite d₁ d₂) = true :=
    registerSupport_work d₁ d₂
  have hpreWork : support preWork = false := by
    dsimp only [support, preWork]
    rw [masterPreWork_eq hd₁ hd₂]
    exact preWorkCol_not_register hd₂ _
  have hadvance : advanceSite .southeast preWork = workSite d₁ d₂ := by
    exact advance_masterPreWork_eq_work hd₁ hd₂ i j
  have hmergeQuiet : ∀ s, support s = true → s ≠ workSite d₁ d₂ →
      shiftedValue .southeast (movingState support value preWork token)
        s.1 s.2 = 0 := by
    intro s hs hne
    apply shiftedValue_movingState_eq_zero_of_advance_ne .southeast support
      (registerSupport_incomingClear d₁ d₂ .southeast)
      value preWork token s hs
    rw [hadvance]
    exact hne.symm
  have hmerge :
      routeStep .southeast 1 (fun p q ↦ support (p, q))
          (movingState support value preWork token) =
        staticState support
          (updateAt value (workSite d₁ d₂)
            (value (workSite d₁ d₂) + token)) := by
    exact routeStep_merge_token .southeast support value preWork
      (workSite d₁ d₂) token hwork hpreWork hadvance hmergeQuiet
  change executeRoute
      ({ direction := .southeast
         coefficient := coefficient
         keep := keepStaticOr support exit } ::
        (moveSteps .east support exit (masterEastSteps j) ++
          (moveSteps .south support corner (masterSouthSteps i) ++
            [{ direction := .southeast
               coefficient := 1
               keep := fun p q ↦ support (p, q) }])))
      (staticState support value) = _
  simp only [executeRoute]
  change executeRoute
      (moveSteps .east support exit (masterEastSteps j) ++
        (moveSteps .south support corner (masterSouthSteps i) ++
          [{ direction := .southeast
             coefficient := 1
             keep := fun p q ↦ support (p, q) }]))
      (routeStep .southeast coefficient (keepStaticOr support exit)
        (staticState support value)) = _
  rw [hcopy, executeRoute_append, heast, executeRoute_append, hsouth]
  simp only [executeRoute]
  change routeStep .southeast 1 (fun p q ↦ support (p, q))
      (movingState support value preWork token) = _
  simpa [support, source, token] using hmerge

def accumulateAt (value : Site → ℝ) (destination : Site) (amount : ℝ) :
    Site → ℝ :=
  updateAt value destination (value destination + amount)

@[simp] theorem accumulateAt_zero (value : Site → ℝ) (destination : Site) :
    accumulateAt value destination 0 = value := by
  funext s
  by_cases h : s = destination
  · subst s
    simp [accumulateAt]
  · simp [accumulateAt, h]

theorem accumulateAt_accumulateAt (value : Site → ℝ) (destination : Site)
    (a b : ℝ) :
    accumulateAt (accumulateAt value destination a) destination b =
      accumulateAt value destination (a + b) := by
  funext s
  by_cases h : s = destination
  · subst s
    simp [accumulateAt]
    ring
  · simp [accumulateAt, h]

def masterWeightedSum (d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ) (value : Site → ℝ) :
    List (Fin d₁ × Fin d₂) → ℝ
  | [] => 0
  | entry :: tail =>
      coefficient entry.1 entry.2 *
          value (masterSite d₁ d₂ entry.1 entry.2) +
        masterWeightedSum d₁ d₂ coefficient value tail

theorem masterWeightedSum_accumulateAt_work {d₁ d₂ : ℕ}
    (coefficient : Fin d₁ → Fin d₂ → ℝ) (value : Site → ℝ)
    (amount : ℝ) (entries : List (Fin d₁ × Fin d₂)) :
    masterWeightedSum d₁ d₂ coefficient
        (accumulateAt value (workSite d₁ d₂) amount) entries =
      masterWeightedSum d₁ d₂ coefficient value entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      simp only [masterWeightedSum]
      rw [ih]
      congr 1
      simp [accumulateAt, masterSite_ne_work entry.1 entry.2]

noncomputable def routeMastersToWorkSteps (d₁ d₂ : ℕ)
    (coefficient : Fin d₁ → Fin d₂ → ℝ) :
    List (Fin d₁ × Fin d₂) → List RouteStep
  | [] => []
  | entry :: tail =>
      routeMasterToWorkSteps d₁ d₂ entry.1 entry.2
          (coefficient entry.1 entry.2) ++
        routeMastersToWorkSteps d₁ d₂ coefficient tail

theorem executeRoute_routeMastersToWork {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (coefficient : Fin d₁ → Fin d₂ → ℝ) (value : Site → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) :
    executeRoute (routeMastersToWorkSteps d₁ d₂ coefficient entries)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (registerSupport d₁ d₂)
        (accumulateAt value (workSite d₁ d₂)
          (masterWeightedSum d₁ d₂ coefficient value entries)) := by
  induction entries generalizing value with
  | nil =>
      change staticState (registerSupport d₁ d₂) value =
        staticState (registerSupport d₁ d₂)
          (accumulateAt value (workSite d₁ d₂) 0)
      rw [accumulateAt_zero]
  | cons entry tail ih =>
      rw [routeMastersToWorkSteps, executeRoute_append,
        executeRoute_routeMasterToWork hd₁ hd₂]
      let term := coefficient entry.1 entry.2 *
        value (masterSite d₁ d₂ entry.1 entry.2)
      change executeRoute (routeMastersToWorkSteps d₁ d₂ coefficient tail)
          (staticState (registerSupport d₁ d₂)
            (accumulateAt value (workSite d₁ d₂) term)) = _
      rw [ih]
      rw [masterWeightedSum_accumulateAt_work]
      rw [accumulateAt_accumulateAt]
      rfl

def workExit (d₁ d₂ : ℕ) : Site :=
  advanceSite .southeast (workSite d₁ d₂)

def workCorner (d₁ d₂ : ℕ) : Site :=
  advanceN .east (workExit d₁ d₂) 1

def preSum (d₁ d₂ : ℕ) : Site :=
  advanceN .south (workCorner d₁ d₂) 1

theorem workExit_eq (d₁ d₂ : ℕ) :
    workExit d₁ d₂ =
      ((workSite d₁ d₂).1 + 1, (workSite d₁ d₂).2 + 1) := rfl

theorem workCorner_eq (d₁ d₂ : ℕ) :
    workCorner d₁ d₂ =
      ((workSite d₁ d₂).1 + 1, (workSite d₁ d₂).2 + 2) := by
  rw [workCorner, workExit_eq, advanceN_east]

theorem preSum_eq (d₁ d₂ : ℕ) :
    preSum d₁ d₂ =
      ((workSite d₁ d₂).1 + 2, (workSite d₁ d₂).2 + 2) := by
  rw [preSum, workCorner_eq, advanceN_south]

theorem advance_preSum_eq_sum (d₁ d₂ : ℕ) :
    advanceSite .southeast (preSum d₁ d₂) = sumSite d₁ d₂ := by
  rw [preSum_eq]
  unfold advanceSite workSite sumSite
  apply Prod.ext <;> simp only <;> omega

theorem workOffsetRow_not_register (d₁ d₂ q : ℕ) :
    registerSupport d₁ d₂ ((workSite d₁ d₂).1 + 1, q) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r, hr⟩, c, hc⟩ :=
    registerSupport_coordinate_form d₁ d₂
      ((workSite d₁ d₂).1 + 1, q) hs
  simp only at hr
  unfold workSite at hr
  omega

theorem preSumCol_not_register (d₁ d₂ p : ℕ) :
    registerSupport d₁ d₂ (p, (workSite d₁ d₂).2 + 2) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hs
  obtain ⟨⟨r, hr⟩, c, hc⟩ :=
    registerSupport_coordinate_form d₁ d₂
      (p, (workSite d₁ d₂).2 + 2) hs
  simp only at hc
  unfold workSite at hc
  omega

/-- Copy the activated work value, scale it, merge it into the sum register,
and erase work. -/
noncomputable def routeWorkToSumSteps (d₁ d₂ : ℕ)
    (coefficient : ℝ) : List RouteStep :=
  let support := registerSupport d₁ d₂
  let exit := workExit d₁ d₂
  let corner := workCorner d₁ d₂
  { direction := .southeast
    coefficient := coefficient
    keep := keepStaticOr support exit } ::
    (moveSteps .east support exit 1 ++
      (moveSteps .south support corner 1 ++
        [{ direction := .southeast
           coefficient := 1
           keep := fun p q ↦ support (p, q) },
         { direction := .east
           coefficient := 0
           keep := fun p q ↦ ridgeSupport d₁ d₂ (p, q) }]))

theorem executeRoute_routeWorkToSum (d₁ d₂ : ℕ)
    (coefficient : ℝ) (value : Site → ℝ) :
    executeRoute (routeWorkToSumSteps d₁ d₂ coefficient)
        (staticState (registerSupport d₁ d₂) value) =
      staticState (ridgeSupport d₁ d₂)
        (updateAt value (sumSite d₁ d₂)
          (value (sumSite d₁ d₂) +
            coefficient * value (workSite d₁ d₂))) := by
  let support := registerSupport d₁ d₂
  let small := ridgeSupport d₁ d₂
  let source := workSite d₁ d₂
  let exit := workExit d₁ d₂
  let corner := workCorner d₁ d₂
  let pre := preSum d₁ d₂
  let token := coefficient * value source
  have hsource : support source = true := registerSupport_work d₁ d₂
  have hexit : support exit = false := by
    dsimp only [support, exit]
    rw [workExit_eq]
    exact workOffsetRow_not_register d₁ d₂ _
  have hcopyQuiet : ∀ s, support s = true →
      shiftedValue .southeast (staticState support value) s.1 s.2 = 0 := by
    intro s hs
    exact shiftedValue_staticState_eq_zero .southeast support
      (registerSupport_incomingClear d₁ d₂ .southeast) value s hs
  have hcopy :
      routeStep .southeast coefficient (keepStaticOr support exit)
          (staticState support value) =
        movingState support value exit token := by
    exact routeStep_copy_from_static .southeast coefficient support value source
      hsource hexit hcopyQuiet
  have heastFree : ∀ t ≤ 1, support (advanceN .east exit t) = false := by
    intro t ht
    dsimp only [support, exit]
    rw [workExit_eq, advanceN_east]
    exact workOffsetRow_not_register d₁ d₂ _
  have heast :
      executeRoute (moveSteps .east support exit 1)
          (movingState support value exit token) =
        movingState support value corner token := by
    have h := executeRoute_moveSteps .east support
      (registerSupport_incomingClear d₁ d₂ .east) value exit token 1 heastFree
    change executeRoute (moveSteps .east support exit 1)
        (movingState support value exit token) =
      movingState support value (advanceN .east exit 1) token
    exact h
  have hsouthFree : ∀ t ≤ 1,
      support (advanceN .south corner t) = false := by
    intro t ht
    dsimp only [support, corner]
    rw [workCorner_eq, advanceN_south]
    exact preSumCol_not_register d₁ d₂ _
  have hsouth :
      executeRoute (moveSteps .south support corner 1)
          (movingState support value corner token) =
        movingState support value pre token := by
    have h := executeRoute_moveSteps .south support
      (registerSupport_incomingClear d₁ d₂ .south) value corner token 1 hsouthFree
    change executeRoute (moveSteps .south support corner 1)
        (movingState support value corner token) =
      movingState support value (advanceN .south corner 1) token
    exact h
  have hsum : support (sumSite d₁ d₂) = true := registerSupport_sum d₁ d₂
  have hpre : support pre = false := by
    dsimp only [support, pre]
    rw [preSum_eq]
    exact preSumCol_not_register d₁ d₂ _
  have hadvance : advanceSite .southeast pre = sumSite d₁ d₂ :=
    advance_preSum_eq_sum d₁ d₂
  have hmergeQuiet : ∀ s, support s = true → s ≠ sumSite d₁ d₂ →
      shiftedValue .southeast (movingState support value pre token)
        s.1 s.2 = 0 := by
    intro s hs hne
    apply shiftedValue_movingState_eq_zero_of_advance_ne .southeast support
      (registerSupport_incomingClear d₁ d₂ .southeast)
      value pre token s hs
    rw [hadvance]
    exact hne.symm
  let updated := updateAt value (sumSite d₁ d₂)
    (value (sumSite d₁ d₂) + token)
  have hmerge :
      routeStep .southeast 1 (fun p q ↦ support (p, q))
          (movingState support value pre token) =
        staticState support updated := by
    exact routeStep_merge_token .southeast support value pre
      (sumSite d₁ d₂) token hsum hpre hadvance hmergeQuiet
  have herase :
      routeStep .east 0 (fun p q ↦ small (p, q))
          (staticState support updated) = staticState small updated := by
    apply routeStep_restrict_static .east support small updated
    intro s hs
    exact ridgeSupport_sub_register d₁ d₂ s hs
  change executeRoute
      ({ direction := .southeast
         coefficient := coefficient
         keep := keepStaticOr support exit } ::
        (moveSteps .east support exit 1 ++
          (moveSteps .south support corner 1 ++
            [{ direction := .southeast
               coefficient := 1
               keep := fun p q ↦ support (p, q) },
             { direction := .east
               coefficient := 0
               keep := fun p q ↦ small (p, q) }])))
      (staticState support value) = _
  simp only [executeRoute]
  change executeRoute
      (moveSteps .east support exit 1 ++
        (moveSteps .south support corner 1 ++
          [{ direction := .southeast
             coefficient := 1
             keep := fun p q ↦ support (p, q) },
           { direction := .east
             coefficient := 0
             keep := fun p q ↦ small (p, q) }]))
      (routeStep .southeast coefficient (keepStaticOr support exit)
        (staticState support value)) = _
  rw [hcopy, executeRoute_append, heast, executeRoute_append, hsouth]
  simp only [executeRoute]
  change routeStep .east 0 (fun p q ↦ small (p, q))
      (routeStep .southeast 1 (fun p q ↦ support (p, q))
        (movingState support value pre token)) = _
  rw [hmerge, herase]

end ICM2022NumCS97
