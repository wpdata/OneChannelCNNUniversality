import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeRealization

/-!
# Regression tests for signed-stripe realization bridges
-/

namespace OneChannelCNNUniversality

#check generalRidgeStripeTwistedFactors_eq_proper_append_last
#check generalRidgeStripeSeedAddressImage_eq_fullConvChain_north
#check generalRidgeStripeFinalLocalAddressImage_eq_fullConv_north
#check generalRidgeStripeVariableSignal
#check continuousFeatureOn_generalRidgeStripeVariableSignal
#check generalRidgeStripeVariableSignal_target

#print axioms generalRidgeStripeTwistedFactors_eq_proper_append_last
#print axioms generalRidgeStripeSeedAddressImage_eq_fullConvChain_north
#print axioms generalRidgeStripeFinalLocalAddressImage_eq_fullConv_north
#print axioms continuousFeatureOn_generalRidgeStripeVariableSignal
#print axioms generalRidgeStripeVariableSignal_target

/-- At the smallest admitted width, the full twisted list is the unique
proper factor followed by the final factor. -/
example (w : Fin 2 → ℝ) (T : ℝ) :
    generalRidgeStripeTwistedFactors (n := 0) w T =
      generalRidgeStripeTwistedProperFactors w T ++
        [generalRidgeStripeTwistedLastFactor w T] := by
  exact generalRidgeStripeTwistedFactors_eq_proper_append_last w T

/-- The algebraic full-chain seed address is the northern-two-row response
of the actual formal convolution chain, including the `n = 0` boundary. -/
example (w : Fin 2 → ℝ) (T : ℝ) (p q : ℕ) (hp : p ≤ 1) :
    zeroExtend
        (fullConvChain (generalRidgeStripeTwistedFactors (n := 0) w T)
          (constantImage 2 3 1)) p q =
      zeroExtend (generalRidgeStripeSeedAddressImage w T) p q := by
  exact generalRidgeStripeSeedAddressImage_eq_fullConvChain_north
    w T p hp q

/-- The local address image is exactly the last factor's response on every
protected northern coordinate. -/
example (w : Fin 2 → ℝ) (T : ℝ)
    (p : Fin 4) (hp : (p : ℕ) ≤ 1) (q : Fin 5) :
    fullConv (generalRidgeStripeTwistedLastFactor w T).kernel
        (constantImage 3 4 1) p q =
      generalRidgeStripeFinalLocalAddressImage w T p q := by
  exact generalRidgeStripeFinalLocalAddressImage_eq_fullConv_north
    w T p hp q

/-- The variable signal carries the requested two-coordinate dot product at
the protected target for the smallest stripe. -/
example (w : Fin 2 → ℝ) (T : ℝ) (hT : T ≠ 0)
    (x : Image 1 2) :
    generalRidgeStripeVariableSignal w T x
        (generalRidgeStripeTarget 0).1
        (generalRidgeStripeTarget 0).2 =
      ∑ j, w j * x 0 j := by
  exact generalRidgeStripeVariableSignal_target w T hT x

end OneChannelCNNUniversality
