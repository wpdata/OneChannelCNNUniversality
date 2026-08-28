import OneChannelCNNUniversality.Encoder

open Matrix
open OneChannelCNNUniversality

example (u : ℕ → ℝ) (steps q : ℕ) :
    iteratePairKernel (steps + 1) u q =
      iteratePairKernel steps u q + predecessor (iteratePairKernel steps u) q :=
  iteratePairKernel_succ steps u q

example : gapMatrix 2 = !![(1 : ℝ), 4; 4, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gapMatrix, encoderDepth]

example : Matrix.det (gapMatrix 2) = (-15 : ℝ) := by
  norm_num [Matrix.det_fin_two, gapMatrix, encoderDepth]

example (n : ℕ) (hn : 0 < n) : Matrix.det (gapMatrix n) ≠ 0 :=
  gapMatrix_det_ne_zero n hn

example (n : ℕ) (hn : 0 < n) : IsUnit (Matrix.det (gapMatrix n)) :=
  gapMatrix_det_isUnit n hn
