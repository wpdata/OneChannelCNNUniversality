import OneChannelCNNUniversality.SharedBiasSignedGate

open OneChannelCNNUniversality

#check signedPairKernel
#check protectedAffineGateKernel
#check protectedSignedGateNetwork
#check protectedSignedGateNetwork_depth
#check protectedSignedGateNetwork_gate
#check protectedSignedGateNetwork_code_left
#check protectedSignedGateNetwork_code_right
#check protectedSignedGateNetwork_recover
#check protectedSignedGateNetwork_injectiveOn
#check exists_protectedSignedGateNetwork_on_compact

example (x a c M : ℝ) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    zeroExtend
        ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 0 1 =
      relu (a * x + c) := by
  exact protectedSignedGateNetwork_gate a c M hM x hx

example (x a c M : ℝ) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    (zeroExtend
          ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 0 -
        zeroExtend
          ((protectedSignedGateNetwork a c M).eval (scalarImage x)) 2 1) /
        2 = x := by
  exact protectedSignedGateNetwork_recover a c M hM x hx
