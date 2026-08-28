import ICM2022NumCS97.Ridge

open ICM2022NumCS97

example {kRows kCols rows cols d₁ d₂ : ℕ}
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
  exact activateWorkProgram_represents_static (d₁ := d₁) (d₂ := d₂)
    hkRows hkCols offset x value hx hworkRow hworkCol

example {kRows kCols rows cols d₁ d₂ : ℕ}
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
  exact ridgeBlock_represents hkRows hkCols hd₁ hd₂ coefficient entries
    offset outputCoefficient x value hx hworkRow hworkCol
