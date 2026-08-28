import ICM2022NumCS97.RegisterProgram

open ICM2022NumCS97

example (z : ℕ → ℕ → ℝ) (a : ℝ) (p q : ℕ) :
    routeStep .east a (fun _ _ ↦ true) z p q =
      z p q + a * predecessor (fun t ↦ z p t) q := by
  rcases q with _ | q <;> simp [routeStep, shiftedValue, predecessor]

example {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : List RouteStep) (x : Image rows cols) (z : ℕ → ℕ → ℝ)
    (hx : RepresentsInfinite x z) (p q : ℕ) :
    zeroExtend (routeProgram hkRows hkCols steps |>.eval x) p q =
      executeRoute steps z p q := by
  exact routeProgram_represents hkRows hkCols steps x z hx p q

example (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support)
    (value : Site → ℝ) (s : Site) (hs : support s = true) :
    shiftedValue direction (staticState support value) s.1 s.2 = 0 := by
  exact shiftedValue_staticState_eq_zero direction support hclear value s hs

example (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support)
    (value : Site → ℝ) (position s : Site) (token : ℝ)
    (hs : support s = true)
    (hdest : support (advanceSite direction position) = false) :
    shiftedValue direction (movingState support value position token)
      s.1 s.2 = 0 := by
  exact shiftedValue_movingState_eq_zero direction support hclear value position token s hs hdest

example (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support)
    (value : Site → ℝ) (position s : Site) (token : ℝ)
    (hs : support s = true) (hne : advanceSite direction position ≠ s) :
    shiftedValue direction (movingState support value position token)
      s.1 s.2 = 0 := by
  exact shiftedValue_movingState_eq_zero_of_advance_ne direction support
    hclear value position token s hs hne

example (r c n : ℕ) : advanceN .east (r, c) n = (r, c + n) := by
  exact advanceN_east r c n

example (direction : RouteDirection) (support : Site → Bool)
    (hclear : IncomingClear direction support) (value : Site → ℝ)
    (position : Site) (token : ℝ) (steps : ℕ)
    (hfree : ∀ t ≤ steps, support (advanceN direction position t) = false) :
    executeRoute (moveSteps direction support position steps)
        (movingState support value position token) =
      movingState support value (advanceN direction position steps) token := by
  exact executeRoute_moveSteps direction support hclear value position token steps hfree

example (direction : RouteDirection) (support : Site → Bool)
    (hadvance : ∀ s, support s = true →
      support (advanceSite direction s) = false) :
    IncomingClear direction support := by
  exact incomingClear_of_advance_eq_false direction support hadvance

example (direction : RouteDirection) (large small : Site → Bool)
    (value : Site → ℝ)
    (hsub : ∀ s, small s = true → large s = true) :
    routeStep direction 0 (fun p q ↦ small (p, q))
        (staticState large value) = staticState small value := by
  exact routeStep_restrict_static direction large small value hsub
