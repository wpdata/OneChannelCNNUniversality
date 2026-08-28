import ICM2022NumCS97.SparseEncoder
import ICM2022NumCS97.Routing

/-!
# Infinite sparse-state semantics for finite register programs

The finite image dimensions grow at every expansive layer, whereas register
locations are most naturally described by ordinary natural coordinates.
`RepresentsInfinite` bridges the two descriptions using zero extension.
The main theorem proves that every list of east, south, or southeast
two-tap instructions has exactly the advertised infinite sparse semantics.
-/

namespace ICM2022NumCS97

inductive RouteDirection
  | east
  | south
  | southeast
  deriving DecidableEq, Repr

/-- Value one east/south/southeast predecessor behind `(p,q)`. -/
def shiftedValue (direction : RouteDirection) (z : ℕ → ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  match direction with
  | .east => if 1 ≤ q then z p (q - 1) else 0
  | .south => if 1 ≤ p then z (p - 1) q else 0
  | .southeast => if 1 ≤ p ∧ 1 ≤ q then z (p - 1) (q - 1) else 0

/-- One ideal linear register instruction. -/
def routeStep (direction : RouteDirection) (coefficient : ℝ)
    (keep : ℕ → ℕ → Bool) (z : ℕ → ℕ → ℝ) :
    ℕ → ℕ → ℝ :=
  fun p q ↦ if keep p q then
    z p q + coefficient * shiftedValue direction z p q else 0

structure RouteStep where
  direction : RouteDirection
  coefficient : ℝ
  keep : ℕ → ℕ → Bool

def RouteStep.eval (step : RouteStep) (z : ℕ → ℕ → ℝ) :
    ℕ → ℕ → ℝ :=
  routeStep step.direction step.coefficient step.keep z

def executeRoute : List RouteStep → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | [], z => z
  | step :: tail, z => executeRoute tail (step.eval z)

/-- A finite image represents an infinite zero-extended register state. -/
def RepresentsInfinite {rows cols : ℕ} (x : Image rows cols)
    (z : ℕ → ℕ → ℝ) : Prop :=
  ∀ p q, zeroExtend x p q = z p q

def routeKernel {kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (direction : RouteDirection) (coefficient : ℝ) : Kernel kRows kCols :=
  match direction with
  | .east =>
      twoTapKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols)
        (finZeroOfTwo hkRows) (finOneOfTwo hkCols) coefficient
  | .south =>
      twoTapKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols)
        (finOneOfTwo hkRows) (finZeroOfTwo hkCols) coefficient
  | .southeast =>
      twoTapKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols)
        (finOneOfTwo hkRows) (finOneOfTwo hkCols) coefficient

theorem fullConv_routeKernel {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (direction : RouteDirection) (coefficient : ℝ)
    (x : Image rows cols) (p q : ℕ) :
    fullConv (routeKernel hkRows hkCols direction coefficient) x p q =
      zeroExtend x p q + coefficient *
        shiftedValue direction (fun r c ↦ zeroExtend x r c) p q := by
  cases direction with
  | east =>
      rw [routeKernel, fullConv_twoTapKernel]
      simp [finZeroOfTwo, finOneOfTwo, shiftedValue]
  | south =>
      rw [routeKernel, fullConv_twoTapKernel]
      simp [finZeroOfTwo, finOneOfTwo, shiftedValue]
  | southeast =>
      rw [routeKernel, fullConv_twoTapKernel]
      simp [finZeroOfTwo, finOneOfTwo, shiftedValue]

def finiteRouteStep {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (step : RouteStep)
    (x : Image rows cols) : Image (rows + kRows - 1) (cols + kCols - 1) :=
  fun p q ↦ if step.keep p q then
    fullConv (routeKernel hkRows hkCols step.direction step.coefficient) x p q else 0

theorem zeroExtend_finiteRouteStep {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (step : RouteStep)
    (x : Image rows cols) (p q : ℕ) :
    zeroExtend (finiteRouteStep hkRows hkCols step x) p q =
      if step.keep p q then
        fullConv (routeKernel hkRows hkCols step.direction step.coefficient) x p q else 0 := by
  by_cases hp : p < rows + kRows - 1
  · by_cases hq : q < cols + kCols - 1
    · simp [zeroExtend, finiteRouteStep, hp, hq]
    · rw [zeroExtend_col_outside (hj := Nat.le_of_not_gt hq)]
      rw [fullConv_eq_zero_of_col_ge _ _ _ _ (Nat.le_of_not_gt hq)]
      simp
  · rw [zeroExtend_row_outside (hi := Nat.le_of_not_gt hp)]
    rw [fullConv_eq_zero_of_row_ge _ _ _ _ (Nat.le_of_not_gt hp)]
    simp

theorem finiteRouteStep_represents {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (step : RouteStep)
    (x : Image rows cols) (z : ℕ → ℕ → ℝ)
    (hx : RepresentsInfinite x z) :
    RepresentsInfinite (finiteRouteStep hkRows hkCols step x) (step.eval z) := by
  intro p q
  rw [zeroExtend_finiteRouteStep, fullConv_routeKernel]
  have hshift : shiftedValue step.direction
      (fun r c ↦ zeroExtend x r c) p q = shiftedValue step.direction z p q := by
    cases step.direction with
    | east =>
        by_cases hq : 1 ≤ q
        · simp [shiftedValue, hq, hx p (q - 1)]
        · simp [shiftedValue, hq]
    | south =>
        by_cases hp : 1 ≤ p
        · simp [shiftedValue, hp, hx (p - 1) q]
        · simp [shiftedValue, hp]
    | southeast =>
        by_cases hpq : 1 ≤ p ∧ 1 ≤ q
        · simp [shiftedValue, hpq, hx (p - 1) (q - 1)]
        · simp [shiftedValue, hpq]
  rw [hx p q, hshift]
  rfl

/-- Compile a finite ideal route to typed masked convolutions. -/
def routeProgram {kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) :
    (steps : List RouteStep) → {rows cols : ℕ} →
      MaskProgramTo kRows kCols rows cols
        (grownSize kRows rows steps.length) (grownSize kCols cols steps.length)
  | [], rows, cols => MaskProgramTo.nil rows cols kRows kCols
  | step :: tail, rows, cols =>
      MaskProgramTo.cons
        (routeKernel hkRows hkCols step.direction step.coefficient)
        (fun p q ↦ step.keep p q)
        (routeProgram hkRows hkCols tail)

/-- Kernel-checked refinement of the whole ideal route semantics. -/
theorem routeProgram_represents {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : List RouteStep) (x : Image rows cols) (z : ℕ → ℕ → ℝ)
    (hx : RepresentsInfinite x z) :
    RepresentsInfinite ((routeProgram hkRows hkCols steps).eval x)
      (executeRoute steps z) := by
  induction steps generalizing rows cols x z with
  | nil =>
      simp only [routeProgram, executeRoute]
      intro p q
      change zeroExtend x p q = z p q
      exact hx p q
  | cons step tail ih =>
      rw [routeProgram, MaskProgramTo.eval_cons]
      exact ih (finiteRouteStep hkRows hkCols step x) (step.eval z)
        (finiteRouteStep_represents hkRows hkCols step x z hx)

def advanceSite : RouteDirection → Site → Site
  | .east, s => (s.1, s.2 + 1)
  | .south, s => (s.1 + 1, s.2)
  | .southeast, s => (s.1 + 1, s.2 + 1)

/-- Repeated movement in one routing direction.  Recursing from the current
site matches the order in which `executeRoute` consumes instructions. -/
def advanceN (direction : RouteDirection) : Site → ℕ → Site
  | s, 0 => s
  | s, steps + 1 => advanceN direction (advanceSite direction s) steps

@[simp] theorem advanceN_zero (direction : RouteDirection) (s : Site) :
    advanceN direction s 0 = s := rfl

theorem advanceN_shift (direction : RouteDirection) (s : Site) (steps : ℕ) :
    advanceN direction (advanceSite direction s) steps =
      advanceN direction s (steps + 1) := rfl

theorem advanceN_east (r c steps : ℕ) :
    advanceN .east (r, c) steps = (r, c + steps) := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      rw [← advanceN_shift, advanceSite, ih]
      congr 1 <;> omega

theorem advanceN_south (r c steps : ℕ) :
    advanceN .south (r, c) steps = (r + steps, c) := by
  induction steps generalizing r with
  | zero => rfl
  | succ steps ih =>
      rw [← advanceN_shift, advanceSite, ih]
      congr 1 <;> omega

theorem advanceN_southeast (r c steps : ℕ) :
    advanceN .southeast (r, c) steps = (r + steps, c + steps) := by
  induction steps generalizing r c with
  | zero => rfl
  | succ steps ih =>
      rw [← advanceN_shift, advanceSite, ih]
      congr 1 <;> omega

theorem advanceSite_ne (direction : RouteDirection) (s : Site) :
    advanceSite direction s ≠ s := by
  rcases s with ⟨r, c⟩
  cases direction <;> simp [advanceSite]

@[simp] theorem shiftedValue_advanceSite (direction : RouteDirection)
    (z : ℕ → ℕ → ℝ) (s : Site) :
    shiftedValue direction z (advanceSite direction s).1
      (advanceSite direction s).2 = z s.1 s.2 := by
  cases direction <;> simp [shiftedValue, advanceSite]

def staticState (support : Site → Bool) (value : Site → ℝ) :
    ℕ → ℕ → ℝ :=
  fun p q ↦ if support (p, q) then value (p, q) else 0

def movingState (support : Site → Bool) (value : Site → ℝ)
    (position : Site) (token : ℝ) : ℕ → ℕ → ℝ :=
  fun p q ↦ if (p, q) = position then token
    else if support (p, q) then value (p, q) else 0

def keepStaticOr (support : Site → Bool) (destination : Site) :
    ℕ → ℕ → Bool :=
  fun p q ↦ support (p, q) || decide ((p, q) = destination)

def updateAt (value : Site → ℝ) (destination : Site) (newValue : ℝ) :
    Site → ℝ :=
  fun s ↦ if s = destination then newValue else value s

@[simp] theorem updateAt_same (value : Site → ℝ) (destination : Site)
    (newValue : ℝ) :
    updateAt value destination newValue destination = newValue := by
  simp [updateAt]

@[simp] theorem updateAt_of_ne (value : Site → ℝ) (destination s : Site)
    (newValue : ℝ) (h : s ≠ destination) :
    updateAt value destination newValue s = value s := by
  simp [updateAt, h]

/-- Whether the one-step predecessor read by a routing kernel belongs to a
static support.  Boundary sites have no predecessor. -/
def shiftedSupport (direction : RouteDirection) (support : Site → Bool)
    (p q : ℕ) : Bool :=
  match direction with
  | .east => if 1 ≤ q then support (p, q - 1) else false
  | .south => if 1 ≤ p then support (p - 1, q) else false
  | .southeast =>
      if 1 ≤ p ∧ 1 ≤ q then support (p - 1, q - 1) else false

/-- No retained static register has another retained register at the
predecessor read by the indicated two-tap kernel. -/
def IncomingClear (direction : RouteDirection) (support : Site → Bool) : Prop :=
  ∀ s, support s = true → shiftedSupport direction support s.1 s.2 = false

/-- It suffices to check that every outgoing one-step neighbor of a retained
site is nonretained. -/
theorem incomingClear_of_advance_eq_false
    (direction : RouteDirection) (support : Site → Bool)
    (hadvance : ∀ s, support s = true →
      support (advanceSite direction s) = false) :
    IncomingClear direction support := by
  intro s hs
  rcases s with ⟨p, q⟩
  cases direction with
  | east =>
      by_cases hq : 1 ≤ q
      · by_cases hsource : support (p, q - 1) = true
        · have hout := hadvance (p, q - 1) hsource
          have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hq
          simp [advanceSite, hqeq, hs] at hout
        · have hsource' : support (p, q - 1) = false :=
            Bool.eq_false_of_not_eq_true hsource
          simp [shiftedSupport, hq, hsource']
      · simp [shiftedSupport, hq]
  | south =>
      by_cases hp : 1 ≤ p
      · by_cases hsource : support (p - 1, q) = true
        · have hout := hadvance (p - 1, q) hsource
          have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hp
          simp [advanceSite, hpeq, hs] at hout
        · have hsource' : support (p - 1, q) = false :=
            Bool.eq_false_of_not_eq_true hsource
          simp [shiftedSupport, hp, hsource']
      · simp [shiftedSupport, hp]
  | southeast =>
      by_cases hpq : 1 ≤ p ∧ 1 ≤ q
      · by_cases hsource : support (p - 1, q - 1) = true
        · have hout := hadvance (p - 1, q - 1) hsource
          have hpeq : p - 1 + 1 = p := Nat.sub_add_cancel hpq.1
          have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hpq.2
          simp [advanceSite, hpeq, hqeq, hs] at hout
        · have hsource' : support (p - 1, q - 1) = false :=
            Bool.eq_false_of_not_eq_true hsource
          simp [shiftedSupport, hpq, hsource']
      · simp [shiftedSupport, hpq]

theorem shiftedValue_staticState_eq_zero
    (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support) (value : Site → ℝ)
    (s : Site) (hs : support s = true) :
    shiftedValue direction (staticState support value) s.1 s.2 = 0 := by
  have hc := hclear s hs
  rcases s with ⟨p, q⟩
  cases direction with
  | east =>
      by_cases hq : 1 ≤ q
      · have hc' : support (p, q - 1) = false := by
          simpa [shiftedSupport, hq] using hc
        simp [shiftedValue, hq, staticState, hc']
      · simp [shiftedValue, hq]
  | south =>
      by_cases hp : 1 ≤ p
      · have hc' : support (p - 1, q) = false := by
          simpa [shiftedSupport, hp] using hc
        simp [shiftedValue, hp, staticState, hc']
      · simp [shiftedValue, hp]
  | southeast =>
      by_cases hpq : 1 ≤ p ∧ 1 ≤ q
      · have hc' : support (p - 1, q - 1) = false := by
          simpa [shiftedSupport, hpq] using hc
        simp [shiftedValue, hpq, staticState, hc']
      · simp [shiftedValue, hpq]

/-- Core no-crosstalk lemma for a moving token: at a static site, the shifted
read is zero unless that site is exactly the token's next destination. -/
theorem shiftedValue_movingState_eq_zero_of_advance_ne
    (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support) (value : Site → ℝ)
    (position : Site) (token : ℝ) (s : Site) (hs : support s = true)
    (hne : advanceSite direction position ≠ s) :
    shiftedValue direction (movingState support value position token)
      s.1 s.2 = 0 := by
  have hc := hclear s hs
  rcases s with ⟨p, q⟩
  rcases position with ⟨r, c⟩
  cases direction with
  | east =>
      by_cases hq : 1 ≤ q
      · have hc' : support (p, q - 1) = false := by
          simpa [shiftedSupport, hq] using hc
        by_cases heq : (p, q - 1) = (r, c)
        · have hpr : p = r := congrArg Prod.fst heq
          have hqc : q - 1 = c := congrArg Prod.snd heq
          have hadv : advanceSite .east (r, c) = (p, q) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only
            · exact hpr.symm
            · omega
          exact (hne hadv).elim
        · simp [shiftedValue, hq, movingState, heq, hc']
      · simp [shiftedValue, hq]
  | south =>
      by_cases hp : 1 ≤ p
      · have hc' : support (p - 1, q) = false := by
          simpa [shiftedSupport, hp] using hc
        by_cases heq : (p - 1, q) = (r, c)
        · have hpr : p - 1 = r := congrArg Prod.fst heq
          have hqc : q = c := congrArg Prod.snd heq
          have hadv : advanceSite .south (r, c) = (p, q) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only
            · omega
            · exact hqc.symm
          exact (hne hadv).elim
        · simp [shiftedValue, hp, movingState, heq, hc']
      · simp [shiftedValue, hp]
  | southeast =>
      by_cases hpq : 1 ≤ p ∧ 1 ≤ q
      · have hc' : support (p - 1, q - 1) = false := by
          simpa [shiftedSupport, hpq] using hc
        by_cases heq : (p - 1, q - 1) = (r, c)
        · have hpr : p - 1 = r := congrArg Prod.fst heq
          have hqc : q - 1 = c := congrArg Prod.snd heq
          have hadv : advanceSite .southeast (r, c) = (p, q) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only <;> omega
          exact (hne hadv).elim
        · simp [shiftedValue, hpq, movingState, heq, hc']
      · simp [shiftedValue, hpq]

/-- A moving token cannot disturb any static register when the static
support is incoming-clear and the token's next site is nonstatic. -/
theorem shiftedValue_movingState_eq_zero
    (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support) (value : Site → ℝ)
    (position : Site) (token : ℝ) (s : Site) (hs : support s = true)
    (hdest : support (advanceSite direction position) = false) :
    shiftedValue direction (movingState support value position token)
      s.1 s.2 = 0 := by
  have hc := hclear s hs
  rcases s with ⟨p, q⟩
  rcases position with ⟨r, c⟩
  cases direction with
  | east =>
      by_cases hq : 1 ≤ q
      · have hc' : support (p, q - 1) = false := by
          simpa [shiftedSupport, hq] using hc
        by_cases heq : (p, q - 1) = (r, c)
        · have hpr : p = r := congrArg Prod.fst heq
          have hqc : q - 1 = c := congrArg Prod.snd heq
          have hadv : (p, q) = advanceSite .east (r, c) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only
            · exact hpr
            · omega
          have : support (p, q) = false := by simpa [hadv] using hdest
          simp [this] at hs
        · simp [shiftedValue, hq, movingState, heq, hc']
      · simp [shiftedValue, hq]
  | south =>
      by_cases hp : 1 ≤ p
      · have hc' : support (p - 1, q) = false := by
          simpa [shiftedSupport, hp] using hc
        by_cases heq : (p - 1, q) = (r, c)
        · have hpr : p - 1 = r := congrArg Prod.fst heq
          have hqc : q = c := congrArg Prod.snd heq
          have hadv : (p, q) = advanceSite .south (r, c) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only
            · omega
            · exact hqc
          have : support (p, q) = false := by simpa [hadv] using hdest
          simp [this] at hs
        · simp [shiftedValue, hp, movingState, heq, hc']
      · simp [shiftedValue, hp]
  | southeast =>
      by_cases hpq : 1 ≤ p ∧ 1 ≤ q
      · have hc' : support (p - 1, q - 1) = false := by
          simpa [shiftedSupport, hpq] using hc
        by_cases heq : (p - 1, q - 1) = (r, c)
        · have hpr : p - 1 = r := congrArg Prod.fst heq
          have hqc : q - 1 = c := congrArg Prod.snd heq
          have hadv : (p, q) = advanceSite .southeast (r, c) := by
            simp only [advanceSite]
            apply Prod.ext <;> simp only <;> omega
          have : support (p, q) = false := by simpa [hadv] using hdest
          simp [this] at hs
        · simp [shiftedValue, hpq, movingState, heq, hc']
      · simp [shiftedValue, hpq]

/-- Copy a coefficient-scaled static register into one fresh adjacent
moving register while preserving the whole static state. -/
theorem routeStep_copy_from_static
    (direction : RouteDirection) (coefficient : ℝ)
    (support : Site → Bool) (value : Site → ℝ) (source : Site)
    (hsource : support source = true)
    (hdest : support (advanceSite direction source) = false)
    (hquiet : ∀ s, support s = true →
      shiftedValue direction (staticState support value) s.1 s.2 = 0) :
    routeStep direction coefficient
        (keepStaticOr support (advanceSite direction source))
        (staticState support value) =
      movingState support value (advanceSite direction source)
        (coefficient * value source) := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : support s = true
  · have hne : s ≠ advanceSite direction source := by
      intro h
      rw [h] at hs
      simp [hdest] at hs
    simp [routeStep, keepStaticOr, movingState, staticState, s, hs, hne,
      hquiet s hs]
  · have hsfalse : support s = false := Bool.eq_false_of_not_eq_true hs
    by_cases hdestEq : s = advanceSite direction source
    · have hpEq : p = (advanceSite direction source).1 :=
        congrArg Prod.fst hdestEq
      have hqEq : q = (advanceSite direction source).2 :=
        congrArg Prod.snd hdestEq
      rw [hpEq, hqEq]
      simp [routeStep, keepStaticOr, movingState, staticState, hdest,
        hsource, shiftedValue_advanceSite]
    · simp [routeStep, keepStaticOr, movingState, staticState, s, hsfalse,
        hdestEq]

/-- Move a temporary register one step, preserving a static support. -/
theorem routeStep_move_token
    (direction : RouteDirection) (support : Site → Bool) (value : Site → ℝ)
    (position : Site) (token : ℝ)
    (hposition : support position = false)
    (hdest : support (advanceSite direction position) = false)
    (hneq : advanceSite direction position ≠ position)
    (hquiet : ∀ s, support s = true →
      shiftedValue direction (movingState support value position token) s.1 s.2 = 0) :
    routeStep direction 1
        (keepStaticOr support (advanceSite direction position))
        (movingState support value position token) =
      movingState support value (advanceSite direction position) token := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : support s = true
  · have hspos : s ≠ position := by
      intro h
      rw [h, hposition] at hs
      contradiction
    have hsdest : s ≠ advanceSite direction position := by
      intro h
      rw [h, hdest] at hs
      contradiction
    simp [routeStep, keepStaticOr, movingState, s, hs, hspos, hsdest,
      hquiet s hs]
  · have hsfalse : support s = false := Bool.eq_false_of_not_eq_true hs
    by_cases hdestEq : s = advanceSite direction position
    · have hpEq : p = (advanceSite direction position).1 :=
        congrArg Prod.fst hdestEq
      have hqEq : q = (advanceSite direction position).2 :=
        congrArg Prod.snd hdestEq
      rw [hpEq, hqEq]
      simp [routeStep, keepStaticOr, movingState, hdest, hposition, hneq,
        shiftedValue_advanceSite]
    · simp [routeStep, keepStaticOr, movingState, s, hsfalse, hdestEq]

/-- Merge a temporary register into an adjacent static destination and
delete the temporary register. -/
theorem routeStep_merge_token
    (direction : RouteDirection) (support : Site → Bool) (value : Site → ℝ)
    (position destination : Site) (token : ℝ)
    (hdestination : support destination = true)
    (hposition : support position = false)
    (hadvance : advanceSite direction position = destination)
    (hquiet : ∀ s, support s = true → s ≠ destination →
      shiftedValue direction (movingState support value position token) s.1 s.2 = 0) :
    routeStep direction 1 (fun p q ↦ support (p, q))
        (movingState support value position token) =
      staticState support (updateAt value destination (value destination + token)) := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : support s = true
  · have hspos : s ≠ position := by
      intro h
      rw [h, hposition] at hs
      contradiction
    by_cases hsdest : s = destination
    · have hpEq : p = destination.1 := congrArg Prod.fst hsdest
      have hqEq : q = destination.2 := congrArg Prod.snd hsdest
      have hdestpos : destination ≠ position := by
        intro h
        rw [h, hposition] at hdestination
        contradiction
      have hshift : shiftedValue direction
          (movingState support value position token) destination.1 destination.2 = token := by
        rw [← hadvance, shiftedValue_advanceSite]
        simp [movingState]
      rw [hpEq, hqEq]
      simp [routeStep, movingState, staticState, updateAt, hdestination,
        hposition, hdestpos, hshift]
    · simp [routeStep, movingState, staticState, updateAt, s, hs, hspos,
        hsdest, hquiet s hs hsdest]
  · have hsfalse : support s = false := Bool.eq_false_of_not_eq_true hs
    simp [routeStep, staticState, s, hsfalse]

/-- With shifted coefficient zero, a routing instruction is an exact support
restriction of a static state. -/
theorem routeStep_restrict_static
    (direction : RouteDirection) (large small : Site → Bool)
    (value : Site → ℝ)
    (hsub : ∀ s, small s = true → large s = true) :
    routeStep direction 0 (fun p q ↦ small (p, q))
        (staticState large value) = staticState small value := by
  funext p q
  let s : Site := (p, q)
  by_cases hs : small s = true
  · have hl := hsub s hs
    simp [routeStep, staticState, s, hs, hl]
  · have hsfalse : small s = false := Bool.eq_false_of_not_eq_true hs
    simp [routeStep, staticState, s, hsfalse]

/-- A list of unit-coefficient moves, retaining the static support and the
new token destination at every step. -/
def moveSteps (direction : RouteDirection) (support : Site → Bool) :
    Site → ℕ → List RouteStep
  | _, 0 => []
  | position, steps + 1 =>
      { direction := direction
        coefficient := 1
        keep := keepStaticOr support (advanceSite direction position) } ::
      moveSteps direction support (advanceSite direction position) steps

/-- The verified semantics of an arbitrary collision-free straight path. -/
theorem executeRoute_moveSteps
    (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support) (value : Site → ℝ)
    (position : Site) (token : ℝ) (steps : ℕ)
    (hfree : ∀ t ≤ steps,
      support (advanceN direction position t) = false) :
    executeRoute (moveSteps direction support position steps)
        (movingState support value position token) =
      movingState support value (advanceN direction position steps) token := by
  induction steps generalizing position with
  | zero => rfl
  | succ steps ih =>
      have hposition : support position = false := by
        simpa using hfree 0 (by omega)
      have hdest : support (advanceSite direction position) = false := by
        simpa [← advanceN_shift] using hfree 1 (by omega)
      have hquiet : ∀ s, support s = true →
          shiftedValue direction
            (movingState support value position token) s.1 s.2 = 0 := by
        intro s hs
        exact shiftedValue_movingState_eq_zero direction support hclear
          value position token s hs hdest
      have hfirst := routeStep_move_token direction support value position token
        hposition hdest (advanceSite_ne direction position) hquiet
      simp only [moveSteps, executeRoute]
      change executeRoute (moveSteps direction support
          (advanceSite direction position) steps)
          (routeStep direction 1
            (keepStaticOr support (advanceSite direction position))
            (movingState support value position token)) = _
      rw [hfirst]
      apply ih (advanceSite direction position)
      intro t ht
      rw [advanceN_shift]
      exact hfree (t + 1) (by omega)

theorem executeRoute_append (first second : List RouteStep)
    (z : ℕ → ℕ → ℝ) :
    executeRoute (first ++ second) z =
      executeRoute second (executeRoute first z) := by
  induction first generalizing z with
  | nil => rfl
  | cons step tail ih =>
      simp only [List.cons_append, executeRoute]
      exact ih (step.eval z)

end ICM2022NumCS97
