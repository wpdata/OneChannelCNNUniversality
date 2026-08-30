import OneChannelCNNUniversality.SharedBiasGridGate

open OneChannelCNNUniversality

#check protectedGridGateCarrier
#check southTriangularCode
#check southTriangularCode_recover
#check southTriangularCode_injective
#check protectedGridGateNetwork
#check protectedGridGateNetwork_depth
#check protectedGridGateNetwork_gate
#check protectedGridGateNetwork_backup
#check protectedGridGateNetwork_injectiveOn
#check exists_protectedGridGateNetwork_on_compact

example {rows cols : ℕ} (x : Image rows cols) (a c M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M) (j : Fin cols) :
    zeroExtend ((protectedGridGateNetwork (rows := rows) (cols := cols)
      a c M).eval x) 0 j = relu (a * zeroExtend x 0 j + c) := by
  exact protectedGridGateNetwork_gate x a c M hM hbound j

example {rows cols : ℕ} (x : Image rows cols) (a c M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ i j, |x i j| ≤ M)
    (i : Fin rows) (j : Fin cols) :
    zeroExtend ((protectedGridGateNetwork (rows := rows) (cols := cols)
      a c M).eval x) (i + 1) j =
        southTriangularCode a (protectedGridGateCarrier a c M + c) x i j := by
  exact protectedGridGateNetwork_backup x a c M hM hbound i j

example {rows cols : ℕ} (x : Image rows cols) (a C : ℝ)
    (i : Fin rows) (j : Fin cols) :
    southTriangularCode a C x i j - C -
        a * zeroExtend x (i + 1) j = x i j := by
  exact southTriangularCode_recover x a C i j
