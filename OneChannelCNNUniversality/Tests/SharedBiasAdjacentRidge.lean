import OneChannelCNNUniversality.SharedBiasAdjacentRidge

/-!
# Regression tests for the protected adjacent-ridge primitive
-/

namespace OneChannelCNNUniversality

#check protectedAdjacentRidgeKernel
#check protectedAdjacentRidgeCarrier
#check adjacentRidgeBackupCode
#check protectedAdjacentRidgeNetwork
#check protectedAdjacentRidgeNetwork_depth
#check protectedAdjacentRidgeNetwork_gate
#check protectedAdjacentRidgeNetwork_east_fringe
#check protectedAdjacentRidgeNetwork_backup
#check adjacentRidgeBackupCode_injective
#check protectedAdjacentRidgeNetwork_injectiveOn
#check exists_protectedAdjacentRidgeNetwork_on_compact

example {rows cols : ℕ} (alpha beta gamma M : ℝ) :
    (protectedAdjacentRidgeNetwork (rows := rows) (cols := cols)
      alpha beta gamma M).net.depth = 2 := by
  exact protectedAdjacentRidgeNetwork_depth alpha beta gamma M

example {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (j : Fin cols) (hj : 1 ≤ (j : ℕ)) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) 0 j =
      relu (alpha * zeroExtend x 0 ((j : ℕ) - 1) +
        beta * zeroExtend x 0 j + gamma) := by
  exact protectedAdjacentRidgeNetwork_gate
    x alpha beta gamma M hM hbound j hj

example {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hcols : 0 < cols) (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x) 0 cols =
      relu (alpha * zeroExtend x 0 (cols - 1) + gamma) := by
  exact protectedAdjacentRidgeNetwork_east_fringe
    x alpha beta gamma M hcols hM hbound

example {rows cols : ℕ} (x : Image rows cols) (alpha beta gamma M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (i : Fin rows) (j : Fin cols) :
    zeroExtend
        ((protectedAdjacentRidgeNetwork alpha beta gamma M).eval x)
          (i + 1) (j + 1) =
      adjacentRidgeBackupCode alpha beta
        (protectedAdjacentRidgeCarrier alpha beta gamma M + gamma) x i j := by
  exact protectedAdjacentRidgeNetwork_backup
    x alpha beta gamma M hM hbound i j

example {rows cols : ℕ} (alpha beta C : ℝ) :
    Function.Injective
      (adjacentRidgeBackupCode (rows := rows) (cols := cols) alpha beta C) := by
  exact adjacentRidgeBackupCode_injective alpha beta C

end OneChannelCNNUniversality
