import OneChannelCNNUniversality.SharedBiasGeneralRidgeRecovery

/-!
# Regression tests for arbitrary-width northern-row recovery
-/

namespace OneChannelCNNUniversality

#check rowPolynomial_zero_injective
#check generalRidgeFullConvNorthRow
#check generalRidgeFullConvNorthRow_apply
#check generalRidgeFullConvNorthRow_eq_output_apply
#check generalRidgeFullConv_north_eq_imp_eq
#check generalRidgeFullConv_north_injective
#check generalRidgeFullConv_north_add_injective

example {d : ℕ} (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Function.Injective
      (fun x : Image 1 (d + 1) ↦
        generalRidgeFullConvNorthRow w η x) :=
  generalRidgeFullConv_north_injective w η

example {d : ℕ} (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (offset : Fin (grownSize 2 (d + 1) d) → ℝ) :
    Function.Injective
      (fun x : Image 1 (d + 1) ↦
        fun q : Fin (grownSize 2 (d + 1) d) ↦
          generalRidgeFullConvNorthRow w η x q + offset q) :=
  generalRidgeFullConv_north_add_injective w η offset

/-- The empty factor chain retains its single northern input coordinate. -/
example (w : Fin 1 → ℝ) (η : Fin 0 → ℝ) :
    Function.Injective
      (fun x : Image 1 1 ↦ generalRidgeFullConvNorthRow w η x) :=
  generalRidgeFullConv_north_injective w η

#print axioms rowPolynomial_zero_injective
#print axioms generalRidgeFullConv_north_eq_imp_eq
#print axioms generalRidgeFullConv_north_injective
#print axioms generalRidgeFullConv_north_add_injective

end OneChannelCNNUniversality
