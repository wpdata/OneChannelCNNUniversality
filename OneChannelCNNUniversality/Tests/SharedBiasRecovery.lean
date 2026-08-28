import OneChannelCNNUniversality.SharedBiasRecovery

open OneChannelCNNUniversality

example {rows cols : ℕ} (f : Image rows cols →ₗ[ℝ] ℝ)
    (x : Image rows cols) :
    (∑ i, ∑ j, linearReadoutWeights f i j * x i j) = f x := by
  exact linearReadoutWeights_apply f x

example {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (x : Image rows cols) :
    pascalGridLeftInverse rowSteps colSteps
        (pascalGridLinearMap rowSteps colSteps x) = x := by
  exact pascalGridLeftInverse_apply rowSteps colSteps x

example {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    ∃ recover :
        Image
            (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
            (grownSize 2 (grownSize 2 cols colSteps) rowSteps) →ₗ[ℝ]
          Image rows cols,
      ∀ x, recover (pascalGridLinearMap rowSteps colSteps x) = x := by
  exact exists_pascalGrid_linear_recovery rowSteps colSteps

example {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (i : Fin rows) (j : Fin cols) :
    ∃ weight :
        Image
          (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
          (grownSize 2 (grownSize 2 cols colSteps) rowSteps),
      ∀ x : Image rows cols,
        (∑ p, ∑ q,
          weight p q * pascalGridLinearMap rowSteps colSteps x p q) = x i j := by
  exact exists_pascalGrid_coordinate_readout rowSteps colSteps i j

example {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (i : Fin rows) (j : Fin cols) :
    ∃ weight :
        Image
          (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
          (grownSize 2 (grownSize 2 cols colSteps) rowSteps),
      ∀ x : Image rows cols, ImageNonnegative x →
        (∑ p, ∑ q,
          weight p q *
            (zeroBiasPascalGridNetwork rowSteps colSteps).eval x p q) = x i j := by
  exact exists_zeroBiasPascalGridNetwork_coordinate_readout
    rowSteps colSteps i j
