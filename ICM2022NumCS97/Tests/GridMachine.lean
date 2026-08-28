import ICM2022NumCS97.GridMachine

open ICM2022NumCS97

example {kRows kCols rows cols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (commands : List (GridCommand d₁ d₂)) (x : Image rows cols)
    (value : Site → ℝ)
    (hx : RepresentsInfinite x (staticState (gridSupport d₁ d₂) value)) :
    RepresentsInfinite
      ((gridCommandProgram hkRows hkCols commands).eval x)
      (staticState (gridSupport d₁ d₂)
        (executeGridCommands commands value)) := by
  exact gridCommandProgram_represents hkRows hkCols commands x value hx
