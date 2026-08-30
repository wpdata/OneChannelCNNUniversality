import OneChannelCNNUniversality.SharedBiasRowGate

open OneChannelCNNUniversality

#check protectedRowGateKernel
#check protectedRowGateNetwork
#check protectedRowGateNetwork_depth
#check protectedRowGateNetwork_gate
#check protectedRowGateNetwork_recover
#check protectedRowGateNetwork_injectiveOn
#check exists_protectedRowGateNetwork_on_compact

example {cols : ℕ} (x : Image 1 cols) (a c M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ j, |x 0 j| ≤ M) (j : Fin cols) :
    zeroExtend ((protectedRowGateNetwork (cols := cols) a c M).eval x)
        0 j = relu (a * x 0 j + c) := by
  exact protectedRowGateNetwork_gate x a c M hM hbound j

example {cols : ℕ} (x : Image 1 cols) (a c M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ j, |x 0 j| ≤ M) (j : Fin cols) :
    zeroExtend ((protectedRowGateNetwork (cols := cols) a c M).eval x)
        1 j - (M + |c| + c) = x 0 j := by
  exact protectedRowGateNetwork_recover x a c M hM hbound j
