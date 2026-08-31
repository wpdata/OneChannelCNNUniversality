import Mathlib

/-!
# Arbitrary-width ridge polynomial factorization

This file isolates the algebraic factorization behind a one-row, one-channel
shared-bias ridge construction.  For depth `d`, the horizontal factors are the
monic polynomials

\[
  A_i(X)=X+(i+1), \qquad 0\leq i<d.
\]

These are deliberately *not* identified with the differently normalized
factors used in the explicit four-point construction.  Natural-order ridge
weights are stored in reversed polynomial-coefficient order, matching the
reversal in a valid convolution at output column `d`.

The results here are purely algebraic.  They do not yet construct or linearize
an arbitrary-depth ReLU CNN.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- The distinct negative interpolation nodes `-(i+1)`. -/
noncomputable def generalRidgeNode {d : ℕ} (i : Fin d) : ℝ :=
  -((i : ℕ) + 1 : ℝ)

theorem generalRidgeNode_injective {d : ℕ} :
    Function.Injective (generalRidgeNode (d := d)) := by
  intro i j hij
  apply Fin.ext
  dsimp [generalRidgeNode] at hij
  have hnat : (i : ℕ) + 1 = (j : ℕ) + 1 := by
    exact_mod_cast
      (neg_inj.mp hij : ((i : ℕ) + 1 : ℝ) = ((j : ℕ) + 1 : ℝ))
  omega

/-- The monic horizontal factor `X + (i+1)`. -/
noncomputable def generalRidgeNodalFactor {d : ℕ} (i : Fin d) : ℝ[X] :=
  X + C (((i : ℕ) + 1 : ℕ) : ℝ)

/-- Product of all monic horizontal factors. -/
noncomputable def generalRidgeNodalProduct (d : ℕ) : ℝ[X] :=
  ∏ i : Fin d, generalRidgeNodalFactor i

/-- Product of all horizontal factors except the factor indexed by `i`. -/
noncomputable def generalRidgeNodalComplement {d : ℕ} (i : Fin d) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase i, generalRidgeNodalFactor j

private theorem generalRidgeNodalFactor_eq_X_sub_C {d : ℕ} (i : Fin d) :
    generalRidgeNodalFactor i = X - C (generalRidgeNode i) := by
  simp [generalRidgeNodalFactor, generalRidgeNode]
  ring

private theorem generalRidgeNodalFactor_eval_node {d : ℕ} (i : Fin d) :
    (generalRidgeNodalFactor i).eval (generalRidgeNode i) = 0 := by
  rw [generalRidgeNodalFactor_eq_X_sub_C]
  simp

theorem generalRidgeNodalProduct_monic (d : ℕ) :
    (generalRidgeNodalProduct d).Monic := by
  classical
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_add_C _

theorem generalRidgeNodalProduct_natDegree (d : ℕ) :
    (generalRidgeNodalProduct d).natDegree = d := by
  classical
  rw [generalRidgeNodalProduct, Polynomial.natDegree_prod_of_monic]
  · simp only [generalRidgeNodalFactor, Polynomial.natDegree_X_add_C]
    simp
  · intro i hi
    exact Polynomial.monic_X_add_C _

/--
The target polynomial for natural-order weights.  Coefficient `j` is the
weight at the reversed index, because valid convolution at the final output
column pairs coefficient `j` with input column `d-j`.
-/
noncomputable def generalRidgeTargetPolynomial {d : ℕ}
    (w : Fin (d + 1) → ℝ) : ℝ[X] :=
  Polynomial.ofFn (d + 1) (fun j ↦ w (Fin.rev j))

theorem generalRidgeTargetPolynomial_coeff {d : ℕ}
    (w : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    (generalRidgeTargetPolynomial w).coeff j = w (Fin.rev j) := by
  rw [generalRidgeTargetPolynomial,
    Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt]

/-- Reversal in the polynomial coefficients exactly cancels convolution reversal. -/
theorem generalRidgeTargetPolynomial_reversed_dot {d : ℕ}
    (w x : Fin (d + 1) → ℝ) :
    ∑ j : Fin (d + 1),
        (generalRidgeTargetPolynomial w).coeff j * x (Fin.rev j) =
      ∑ j : Fin (d + 1), w j * x j := by
  simp_rw [generalRidgeTargetPolynomial_coeff]
  exact Equiv.sum_comp Fin.revPerm (fun j : Fin (d + 1) ↦ w j * x j)

/-- Remove the leading multiple of the monic nodal product. -/
noncomputable def generalRidgeResidualPolynomial {d : ℕ}
    (w : Fin (d + 1) → ℝ) : ℝ[X] :=
  generalRidgeTargetPolynomial w - C (w 0) * generalRidgeNodalProduct d

theorem generalRidgeResidualPolynomial_degree_lt {d : ℕ}
    (w : Fin (d + 1) → ℝ) :
    (generalRidgeResidualPolynomial w).degree < d := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [generalRidgeResidualPolynomial, coeff_sub, coeff_C_mul]
  rcases eq_or_lt_of_le hm with rfl | hdm
  · have hq : (generalRidgeNodalProduct d).coeff d = 1 := by
      simpa only [generalRidgeNodalProduct_natDegree] using
        (generalRidgeNodalProduct_monic d).coeff_natDegree
    rw [generalRidgeTargetPolynomial,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega), hq]
    simp only [mul_one]
    change w (Fin.rev (Fin.last d)) - w 0 = 0
    simp
  · rw [generalRidgeTargetPolynomial,
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
    have hq : (generalRidgeNodalProduct d).coeff m = 0 :=
      coeff_eq_zero_of_natDegree_lt
        (by simpa [generalRidgeNodalProduct_natDegree] using hdm)
    rw [hq]
    ring

/-- Normalization of the Lagrange basis at a negative integer node. -/
noncomputable def generalRidgeNormalization {d : ℕ} (i : Fin d) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (generalRidgeNode i - generalRidgeNode j)⁻¹

private theorem generalRidgeBasis_eq_normalization_mul_complement
    {d : ℕ} (i : Fin d) :
    Lagrange.basis Finset.univ generalRidgeNode i =
      C (generalRidgeNormalization i) * generalRidgeNodalComplement i := by
  classical
  simp only [Lagrange.basis, Lagrange.basisDivisor,
    generalRidgeNormalization, generalRidgeNodalComplement,
    generalRidgeNodalFactor_eq_X_sub_C, Finset.prod_mul_distrib,
    map_prod]

private theorem generalRidgeSum_basis_complements_eq_interpolate
    {d : ℕ} (r : Fin d → ℝ) :
    ∑ i : Fin d,
        C (r i * generalRidgeNormalization i) *
          generalRidgeNodalComplement i =
      Lagrange.interpolate Finset.univ generalRidgeNode r := by
  classical
  rw [Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [generalRidgeBasis_eq_normalization_mul_complement]
  simp only [map_mul]
  ring

/-- Lagrange coefficient of the degree-`< d` residual. -/
noncomputable def generalRidgeBeta {d : ℕ}
    (w : Fin (d + 1) → ℝ) (i : Fin d) : ℝ :=
  (generalRidgeResidualPolynomial w).eval (generalRidgeNode i) *
    generalRidgeNormalization i

/-- Lagrange decomposition, including the algebraic boundary case `d = 0`. -/
theorem generalRidgeTargetPolynomial_decomposition {d : ℕ}
    (w : Fin (d + 1) → ℝ) :
    generalRidgeTargetPolynomial w =
      C (w 0) * generalRidgeNodalProduct d +
        ∑ i : Fin d,
          C (generalRidgeBeta w i) * generalRidgeNodalComplement i := by
  have hdeg :
      (generalRidgeResidualPolynomial w).degree <
        ((Finset.univ : Finset (Fin d)).card : WithBot ℕ) := by
    simpa using generalRidgeResidualPolynomial_degree_lt w
  have hinterp :
      generalRidgeResidualPolynomial w =
        Lagrange.interpolate Finset.univ generalRidgeNode
          (fun i ↦ (generalRidgeResidualPolynomial w).eval
            (generalRidgeNode i)) :=
    Lagrange.eq_interpolate generalRidgeNode_injective.injOn hdeg
  have hsum :=
    generalRidgeSum_basis_complements_eq_interpolate (d := d)
      (fun i : Fin d ↦
        (generalRidgeResidualPolynomial w).eval (generalRidgeNode i))
  rw [← hsum] at hinterp
  simp only [generalRidgeBeta]
  rw [← hinterp]
  rw [generalRidgeResidualPolynomial]
  ring

/-- At depth zero, the decomposition reduces to the constant target exactly. -/
theorem generalRidgeTargetPolynomial_zero (w : Fin 1 → ℝ) :
    generalRidgeTargetPolynomial w = C (w 0) := by
  simpa [generalRidgeNodalProduct] using
    (generalRidgeTargetPolynomial_decomposition (d := 0) w)

/-- The lower (vertical-linear) polynomial allocated to factor `i`. -/
noncomputable def generalRidgeLowerFactor {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) (i : Fin d) : ℝ[X] :=
  C (generalRidgeBeta w i) +
    C (η i) * generalRidgeNodalFactor i

theorem generalRidgeLowerFactor_decomposition {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hη : ∑ i, η i = w 0) :
    ∑ i : Fin d,
        generalRidgeLowerFactor w η i * generalRidgeNodalComplement i =
      generalRidgeTargetPolynomial w := by
  classical
  rw [generalRidgeTargetPolynomial_decomposition]
  simp only [generalRidgeLowerFactor, add_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  calc
    ∑ i : Fin d,
          C (η i) * generalRidgeNodalFactor i *
            generalRidgeNodalComplement i =
        ∑ i : Fin d, C (η i) * generalRidgeNodalProduct d := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [generalRidgeNodalComplement, generalRidgeNodalProduct,
            mul_assoc,
            Finset.mul_prod_erase Finset.univ generalRidgeNodalFactor
              (Finset.mem_univ i)]
    _ = C (∑ i : Fin d, η i) * generalRidgeNodalProduct d := by
          rw [map_sum, Finset.sum_mul]
    _ = C (w 0) * generalRidgeNodalProduct d := by rw [hη]

/-- Coefficient of degree one in a finite product of linear polynomials. -/
theorem generalRidgeCoeffOne_product
    {R : Type*} [CommRing R] {I : Type*} [DecidableEq I]
    (s : Finset I) (A B : I → R) :
    (coeff (∏ i ∈ s, (C (A i) + C (B i) * X : R[X])) 1) =
      ∑ i ∈ s, B i * ∏ j ∈ s.erase i, A j := by
  have hcoeff (p : R[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]
    symm
    simpa using coeff_derivative p 0
  rw [hcoeff, derivative_prod_finset]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eval_mul, eval_prod, derivative_add, derivative_C,
    zero_add, derivative_mul, derivative_X, mul_one, zero_mul,
    eval_C, eval_add, eval_X]
  simp only [mul_zero, add_zero]
  exact mul_comm _ _

/-- A polynomial in the vertical variable whose coefficients are horizontal polynomials. -/
abbrev GeneralRidgeBiPolynomial := Polynomial (ℝ[X])

/-- The bivariate factor `A(X) + Y B(X)`, represented as a polynomial in `Y`. -/
noncomputable def generalRidgeBiFactor (A B : ℝ[X]) :
    GeneralRidgeBiPolynomial :=
  C A + C B * X

/-- The coefficient of `Y` in the factor product is the target horizontal polynomial. -/
theorem generalRidgeBiProduct_vertical_one {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hη : ∑ i, η i = w 0) :
    (coeff
      (∏ i : Fin d,
        generalRidgeBiFactor (generalRidgeNodalFactor i)
          (generalRidgeLowerFactor w η i)) 1) =
      generalRidgeTargetPolynomial w := by
  rw [show
      coeff
          (∏ i : Fin d,
            generalRidgeBiFactor (generalRidgeNodalFactor i)
              (generalRidgeLowerFactor w η i)) 1 =
        ∑ i : Fin d,
          generalRidgeLowerFactor w η i *
            generalRidgeNodalComplement i by
      simpa [generalRidgeBiFactor, generalRidgeNodalComplement] using
        generalRidgeCoeffOne_product Finset.univ
          generalRidgeNodalFactor (generalRidgeLowerFactor w η)]
  exact generalRidgeLowerFactor_decomposition w η hη

/-- For positive depth, place the full leading coefficient at the first factor. -/
theorem exists_generalRidgeLeadingAllocation {d : ℕ} (hd : 0 < d)
    (w : Fin (d + 1) → ℝ) :
    ∃ η : Fin d → ℝ, ∑ i, η i = w 0 := by
  let i₀ : Fin d := ⟨0, hd⟩
  refine ⟨fun i ↦ if i = i₀ then w 0 else 0, ?_⟩
  simp [i₀]

/-- Positive depth admits an explicit factor product with the desired `Y` coefficient. -/
theorem exists_generalRidgeBiProduct_vertical_one {d : ℕ} (hd : 0 < d)
    (w : Fin (d + 1) → ℝ) :
    ∃ η : Fin d → ℝ,
      (∑ i, η i = w 0) ∧
        (coeff
          (∏ i : Fin d,
            generalRidgeBiFactor (generalRidgeNodalFactor i)
              (generalRidgeLowerFactor w η i)) 1) =
          generalRidgeTargetPolynomial w := by
  obtain ⟨η, hη⟩ := exists_generalRidgeLeadingAllocation hd w
  exact ⟨η, hη, generalRidgeBiProduct_vertical_one w η hη⟩

end OneChannelCNNUniversality
