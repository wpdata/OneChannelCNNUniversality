import OneChannelCNNUniversality.SharedBiasAffineMixGate

open OneChannelCNNUniversality

#check horizontalWeightedKernel
#check fullConv_horizontalWeightedKernel_nat
#check fullConvImage_horizontalWeightedKernel_injective
#check weightedMixLayer
#check weightedMixGateNetwork
#check weightedMixGateNetwork_depth
#check weightedMixGateNetwork_gate
#check weightedMixLayer_injectiveOn
#check weightedMixGateNetwork_injectiveOn
#check exists_weightedMixGateNetwork_on_compact

example {rows cols : ℕ} (x : Image rows cols) (weight b a c M : ℝ)
    (hcols : 0 < cols)
    (hlinear : ∀ p q,
      (weightedMixLayer weight b).eval x p q =
        fullConv (horizontalWeightedKernel weight) x p q + b)
    (hM : 0 ≤ M)
    (hbound : ∀ i j, |(weightedMixLayer weight b).eval x i j| ≤ M) :
    zeroExtend ((weightedMixGateNetwork weight b a c M).eval x) 0 1 =
      relu (a * (zeroExtend x 0 1 + weight * zeroExtend x 0 0) + c) := by
  exact weightedMixGateNetwork_gate
    x weight b a c M hcols hlinear hM hbound

example {rows cols : ℕ} (weight : ℝ) :
    Function.Injective
      (fun x : Image rows cols ↦
        fullConvImage (horizontalWeightedKernel weight) x) := by
  exact fullConvImage_horizontalWeightedKernel_injective weight
