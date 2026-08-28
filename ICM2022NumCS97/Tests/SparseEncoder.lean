import ICM2022NumCS97.SparseEncoder

open ICM2022NumCS97

example {kRows kCols rows cols : ℕ} (hkRows : 2 ≤ kRows)
    (hkCols : 2 ≤ kCols) (x : Image rows cols) (p q : ℕ) :
    fullConv (horizontalPairKernel hkRows hkCols) x p q =
      zeroExtend x p q + predecessor (fun t ↦ zeroExtend x p t) q := by
  exact fullConv_horizontalPairKernel hkRows hkCols x p q

example (steps q : ℕ) (u : ℕ → ℝ) :
    iteratePairKernel steps u q =
      ∑ j ∈ Finset.range (q + 1),
        (Nat.choose steps (q - j) : ℝ) * u j := by
  exact iteratePairKernel_eq_sum_choose steps u q

example {kRows kCols rows n : ℕ} (hkRows : 2 ≤ kRows)
    (hkCols : 2 ≤ kCols) (hn : 0 < n)
    (x : Image rows n) (p : ℕ) (i : Fin n) :
    zeroExtend
        (iterateFullConv (horizontalPairKernel hkRows hkCols)
          (encoderDepth n) x)
        p (encoderSite n i) =
      ∑ j : Fin n, gapMatrix n i j * zeroExtend x p (Fin.rev j) := by
  exact horizontal_encoder_sample hkRows hkCols hn x p i

example {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (x : Image d₁ d₂) (i : Fin d₁) (j : Fin d₂) :
    (sparseEncoderProgram hkRows hkCols).eval x
        (encoderOutRowFin (d₂ := d₂) hkRows i)
        (encoderOutColFin (d₁ := d₁) hkCols j) =
      sparseEncodedValue x i j := by
  exact sparseEncoderProgram_eval_master hkRows hkCols hd₁ hd₂ x i j
