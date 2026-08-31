import OneChannelCNNUniversality.SharedBiasGeneralRidgePolynomial
import OneChannelCNNUniversality.SharedBias
import OneChannelCNNUniversality.SparseEncoder

/-!
# From arbitrary-width ridge polynomials to expansive convolution

This file identifies a bilinear polynomial

\[
  K(X,Y)=(a_0+a_1X)+Y(b_0+b_1X)
\]

with the expansive `2 × 2` kernel whose rows are `(a₀,a₁)` and
`(b₀,b₁)`.  For a heterogeneous list of such kernels, the northern and
first southern row-generating polynomials obey the same recursion as the
coefficients of `Y⁰` and `Y¹` in the product of the bilinear factors.  This
gives an exact convolutional realization of the arbitrary-width algebraic
ridge factorization.

The zero-bias network result below is conditional: every preactivation along
the specified input must already lie in ReLU's linear branch.  This module
does not yet choose the shared carriers needed to establish that condition
uniformly on a compact input family.  The algebra includes `d = 0`; the
southern coordinate `(1,0)` is then outside the depth-zero output, so the
nontrivial network target starts at positive depth.
-/

namespace OneChannelCNNUniversality

open scoped BigOperators Polynomial
open Polynomial

/-- The `2 × 2` kernel represented by
`(a₀ + a₁ X) + Y (b₀ + b₁ X)`. -/
def bilinearKernel (a0 a1 b0 b1 : ℝ) : Kernel 2 2 :=
  fun i j ↦
    deltaKernel (0 : Fin 2) (0 : Fin 2) a0 i j +
      (deltaKernel (0 : Fin 2) (1 : Fin 2) a1 i j +
        (deltaKernel (1 : Fin 2) (0 : Fin 2) b0 i j +
          deltaKernel (1 : Fin 2) (1 : Fin 2) b1 i j))

/-- Direct zero-extended convolution formula for a bilinear kernel. -/
theorem fullConv_bilinearKernel_nat
    {rows cols : ℕ} (x : Image rows cols)
    (a0 a1 b0 b1 : ℝ) (p q : ℕ) :
    fullConv (bilinearKernel a0 a1 b0 b1) x p q =
      a0 * zeroExtend x p q +
        (if 1 ≤ q then a1 * zeroExtend x p (q - 1) else 0) +
        (if 1 ≤ p then b0 * zeroExtend x (p - 1) q else 0) +
        (if 1 ≤ p ∧ 1 ≤ q then
          b1 * zeroExtend x (p - 1) (q - 1) else 0) := by
  unfold bilinearKernel
  rw [fullConv_kernel_add, fullConv_deltaKernel, fullConv_kernel_add,
    fullConv_deltaKernel, fullConv_kernel_add, fullConv_deltaKernel,
    fullConv_deltaKernel]
  simp
  ring_nf

/-- A horizontal polynomial of degree at most one. -/
noncomputable def linearPolynomial (c0 c1 : ℝ) : ℝ[X] :=
  C c0 + C c1 * X

/-- The polynomial in `Y`, with coefficients in `ℝ[X]`, corresponding to
one bilinear kernel. -/
noncomputable def bilinearKernelPolynomial
    (a0 a1 b0 b1 : ℝ) : GeneralRidgeBiPolynomial :=
  C (linearPolynomial a0 a1) + C (linearPolynomial b0 b1) * X

@[simp] theorem bilinearKernelPolynomial_coeff_zero
    (a0 a1 b0 b1 : ℝ) :
    (bilinearKernelPolynomial a0 a1 b0 b1).coeff 0 =
      linearPolynomial a0 a1 := by
  simp [bilinearKernelPolynomial]

@[simp] theorem bilinearKernelPolynomial_coeff_one
    (a0 a1 b0 b1 : ℝ) :
    (bilinearKernelPolynomial a0 a1 b0 b1).coeff 1 =
      linearPolynomial b0 b1 := by
  simp [bilinearKernelPolynomial]

@[simp] theorem bilinearKernelPolynomial_coeff_of_two_le
    (a0 a1 b0 b1 : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (bilinearKernelPolynomial a0 a1 b0 b1).coeff n = 0 := by
  have hn0 : n ≠ 0 := by omega
  have h1n : 1 ≠ n := by omega
  rw [bilinearKernelPolynomial, coeff_add, coeff_C_mul, coeff_C, coeff_X]
  simp [hn0, h1n]

/-- Finite generating polynomial of row `p`, with the image zero-extended
vertically. -/
noncomputable def rowPolynomial {rows cols : ℕ}
    (x : Image rows cols) (p : ℕ) : ℝ[X] :=
  ∑ j : Fin cols, monomial (j : ℕ) (zeroExtend x p j)

@[simp] theorem rowPolynomial_coeff {rows cols : ℕ}
    (x : Image rows cols) (p q : ℕ) :
    (rowPolynomial x p).coeff q = zeroExtend x p q := by
  classical
  by_cases hq : q < cols
  · rw [rowPolynomial]
    change (Polynomial.lcoeff ℝ q)
        (∑ j : Fin cols, monomial (j : ℕ) (zeroExtend x p j)) = _
    rw [map_sum]
    change (∑ j : Fin cols,
        (monomial (j : ℕ) (zeroExtend x p j)).coeff q) = _
    rw [Fintype.sum_eq_single ⟨q, hq⟩]
    · simp
    · intro j hj
      simp only [coeff_monomial]
      split_ifs with h
      · exfalso
        apply hj
        apply Fin.ext
        exact h
      · rfl
  · have hzero : zeroExtend x p q = 0 :=
      zeroExtend_col_outside x (Nat.le_of_not_gt hq)
    rw [hzero, rowPolynomial]
    change (Polynomial.lcoeff ℝ q)
        (∑ j : Fin cols, monomial (j : ℕ) (zeroExtend x p j)) = _
    rw [map_sum]
    change (∑ j : Fin cols,
        (monomial (j : ℕ) (zeroExtend x p j)).coeff q) = _
    apply Finset.sum_eq_zero
    intro j hj
    simp only [coeff_monomial]
    split_ifs with h
    · have : q < cols := by simpa [h] using j.isLt
      exact (hq this).elim
    · rfl

private theorem linearPolynomial_mul_coeff
    (c0 c1 : ℝ) (P : ℝ[X]) (q : ℕ) :
    (linearPolynomial c0 c1 * P).coeff q =
      c0 * P.coeff q +
        if 1 ≤ q then c1 * P.coeff (q - 1) else 0 := by
  rcases q with _ | q
  · simp [linearPolynomial, add_mul, mul_assoc]
  · rw [linearPolynomial, add_mul, coeff_add, coeff_C_mul, mul_assoc,
      coeff_C_mul]
    simp only [coeff_X_mul]
    simp

/-- At the northern boundary, a bilinear convolution multiplies the row
polynomial by its horizontal factor `A`. -/
theorem rowPolynomial_fullConv_zero
    {rows cols : ℕ} (x : Image rows cols)
    (a0 a1 b0 b1 : ℝ) :
    rowPolynomial (fullConvImage (bilinearKernel a0 a1 b0 b1) x) 0 =
      linearPolynomial a0 a1 * rowPolynomial x 0 := by
  ext q
  rw [rowPolynomial_coeff, zeroExtend_fullConvImage,
    fullConv_bilinearKernel_nat, linearPolynomial_mul_coeff,
    rowPolynomial_coeff, rowPolynomial_coeff]
  simp

/-- At row one, a bilinear convolution implements
`S' = A S + B N`. -/
theorem rowPolynomial_fullConv_one
    {rows cols : ℕ} (x : Image rows cols)
    (a0 a1 b0 b1 : ℝ) :
    rowPolynomial (fullConvImage (bilinearKernel a0 a1 b0 b1) x) 1 =
      linearPolynomial a0 a1 * rowPolynomial x 1 +
        linearPolynomial b0 b1 * rowPolynomial x 0 := by
  ext q
  rw [rowPolynomial_coeff, zeroExtend_fullConvImage,
    fullConv_bilinearKernel_nat, coeff_add,
    linearPolynomial_mul_coeff, linearPolynomial_mul_coeff,
    rowPolynomial_coeff, rowPolynomial_coeff,
    rowPolynomial_coeff, rowPolynomial_coeff]
  simp
  ring

/-- Four coefficients specifying one factor `A(X) + Y B(X)`. -/
structure BilinearKernelFactor where
  a0 : ℝ
  a1 : ℝ
  b0 : ℝ
  b1 : ℝ

namespace BilinearKernelFactor

/-- Horizontal factor `A`. -/
noncomputable def A (f : BilinearKernelFactor) : ℝ[X] :=
  linearPolynomial f.a0 f.a1

/-- Lower factor `B`. -/
noncomputable def B (f : BilinearKernelFactor) : ℝ[X] :=
  linearPolynomial f.b0 f.b1

/-- The corresponding expansive `2 × 2` kernel. -/
def kernel (f : BilinearKernelFactor) : Kernel 2 2 :=
  bilinearKernel f.a0 f.a1 f.b0 f.b1

/-- The corresponding element of `ℝ[X][Y]`. -/
noncomputable def polynomial
    (f : BilinearKernelFactor) : GeneralRidgeBiPolynomial :=
  bilinearKernelPolynomial f.a0 f.a1 f.b0 f.b1

@[simp] theorem polynomial_coeff_zero (f : BilinearKernelFactor) :
    f.polynomial.coeff 0 = f.A := by
  simp [polynomial, A]

@[simp] theorem polynomial_coeff_one (f : BilinearKernelFactor) :
    f.polynomial.coeff 1 = f.B := by
  simp [polynomial, B]

@[simp] theorem polynomial_coeff_of_two_le (f : BilinearKernelFactor)
    {n : ℕ} (hn : 2 ≤ n) : f.polynomial.coeff n = 0 := by
  exact bilinearKernelPolynomial_coeff_of_two_le _ _ _ _ hn

end BilinearKernelFactor

/-- Product of all horizontal factors. -/
noncomputable def horizontalProduct (fs : List BilinearKernelFactor) : ℝ[X] :=
  (fs.map BilinearKernelFactor.A).prod

/-- Recursive expression for the coefficient of `Y` in the factor product. -/
noncomputable def verticalOne : List BilinearKernelFactor → ℝ[X]
  | [] => 0
  | f :: fs =>
      f.A * verticalOne fs + f.B * horizontalProduct fs

/-- Literal product of the factors in `ℝ[X][Y]`. -/
noncomputable def bivariateProduct
    (fs : List BilinearKernelFactor) : GeneralRidgeBiPolynomial :=
  (fs.map BilinearKernelFactor.polynomial).prod

private theorem bilinearKernelPolynomial_mul_coeff_one
    (f : BilinearKernelFactor) (P : GeneralRidgeBiPolynomial) :
    (f.polynomial * P).coeff 1 =
      f.A * P.coeff 1 + f.B * P.coeff 0 := by
  rw [Polynomial.mul_coeff_one]
  simp [BilinearKernelFactor.polynomial, bilinearKernelPolynomial,
    BilinearKernelFactor.A, BilinearKernelFactor.B]

theorem bivariateProduct_coeff_zero (fs : List BilinearKernelFactor) :
    (bivariateProduct fs).coeff 0 = horizontalProduct fs := by
  induction fs with
  | nil => simp [bivariateProduct, horizontalProduct, Polynomial.coeff_one]
  | cons f fs ih =>
      change (f.polynomial * bivariateProduct fs).coeff 0 =
        f.A * horizontalProduct fs
      rw [Polynomial.mul_coeff_zero,
        BilinearKernelFactor.polynomial_coeff_zero, ih]

/-- The recursive lower-row expression is exactly the coefficient of `Y` in
the literal product. -/
theorem bivariateProduct_coeff_one (fs : List BilinearKernelFactor) :
    (bivariateProduct fs).coeff 1 = verticalOne fs := by
  induction fs with
  | nil => simp [bivariateProduct, verticalOne, Polynomial.coeff_one]
  | cons f fs ih =>
      change (f.polynomial * bivariateProduct fs).coeff 1 =
        f.A * verticalOne fs + f.B * horizontalProduct fs
      rw [bilinearKernelPolynomial_mul_coeff_one, ih,
        bivariateProduct_coeff_zero]

/-- Apply a heterogeneous finite sequence of expansive `2 × 2`
convolutions, without biases or ReLU. -/
def fullConvChain : (fs : List BilinearKernelFactor) →
    {rows cols : ℕ} → Image rows cols →
      Image (grownSize 2 rows fs.length) (grownSize 2 cols fs.length)
  | [], _, _, x => x
  | f :: fs, _, _, x => fullConvChain fs (fullConvImage f.kernel x)

theorem rowPolynomial_fullConvChain_zero
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols) :
    rowPolynomial (fullConvChain fs x) 0 =
      horizontalProduct fs * rowPolynomial x 0 := by
  induction fs generalizing rows cols with
  | nil =>
      simp only [fullConvChain, horizontalProduct, List.map_nil,
        List.prod_nil, one_mul]
      rfl
  | cons f fs ih =>
      change rowPolynomial
          (fullConvChain fs (fullConvImage f.kernel x)) 0 =
        (f.A * horizontalProduct fs) * rowPolynomial x 0
      calc
        _ = horizontalProduct fs *
              rowPolynomial (fullConvImage f.kernel x) 0 :=
          ih (fullConvImage f.kernel x)
        _ = horizontalProduct fs * (f.A * rowPolynomial x 0) := by
          rw [BilinearKernelFactor.kernel, rowPolynomial_fullConv_zero]
          rfl
        _ = (f.A * horizontalProduct fs) * rowPolynomial x 0 := by ring

theorem rowPolynomial_fullConvChain_one
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols) :
    rowPolynomial (fullConvChain fs x) 1 =
      horizontalProduct fs * rowPolynomial x 1 +
        verticalOne fs * rowPolynomial x 0 := by
  induction fs generalizing rows cols with
  | nil =>
      simp only [fullConvChain, horizontalProduct, verticalOne,
        List.map_nil, List.prod_nil, one_mul, zero_mul, add_zero]
      rfl
  | cons f fs ih =>
      change rowPolynomial
          (fullConvChain fs (fullConvImage f.kernel x)) 1 =
        (f.A * horizontalProduct fs) * rowPolynomial x 1 +
          (f.A * verticalOne fs + f.B * horizontalProduct fs) *
            rowPolynomial x 0
      calc
        _ = horizontalProduct fs *
              rowPolynomial (fullConvImage f.kernel x) 1 +
            verticalOne fs *
              rowPolynomial (fullConvImage f.kernel x) 0 :=
          ih (fullConvImage f.kernel x)
        _ = horizontalProduct fs *
              (f.A * rowPolynomial x 1 + f.B * rowPolynomial x 0) +
            verticalOne fs * (f.A * rowPolynomial x 0) := by
          rw [BilinearKernelFactor.kernel, rowPolynomial_fullConv_one,
            rowPolynomial_fullConv_zero]
          rfl
        _ = (f.A * horizontalProduct fs) * rowPolynomial x 1 +
            (f.A * verticalOne fs + f.B * horizontalProduct fs) *
              rowPolynomial x 0 := by ring

private theorem coeff_mul_monomial_any
    (P : ℝ[X]) (n d : ℕ) (r : ℝ) :
    (P * monomial n r).coeff d =
      if n ≤ d then P.coeff (d - n) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow',
    coeff_mul_C]

private theorem coeff_mul_rowPolynomial
    {rows cols : ℕ} (P : ℝ[X]) (x : Image rows cols) (p d : ℕ) :
    (P * rowPolynomial x p).coeff d =
      ∑ j : Fin cols,
        if (j : ℕ) ≤ d then P.coeff (d - (j : ℕ)) * zeroExtend x p j
        else 0 := by
  rw [rowPolynomial, Finset.mul_sum]
  change (Polynomial.lcoeff ℝ d)
      (∑ j : Fin cols, P * monomial (j : ℕ) (zeroExtend x p j)) = _
  rw [map_sum]
  change (∑ j : Fin cols,
      (P * monomial (j : ℕ) (zeroExtend x p j)).coeff d) = _
  apply Finset.sum_congr rfl
  intro j hj
  exact coeff_mul_monomial_any P j d (zeroExtend x p j)

/-- End-to-end convolution bridge at row one. -/
theorem fullConvChain_row_one_reversed_dot
    (fs : List BilinearKernelFactor) {cols : ℕ} (x : Image 1 cols) (d : ℕ) :
    zeroExtend (fullConvChain fs x) 1 d =
      ∑ j : Fin cols,
        if (j : ℕ) ≤ d then
          ((bivariateProduct fs).coeff 1).coeff (d - (j : ℕ)) * x 0 j
        else 0 := by
  rw [← rowPolynomial_coeff]
  rw [rowPolynomial_fullConvChain_one]
  have hsouth : rowPolynomial x 1 = 0 := by
    ext q
    simp
  rw [hsouth, mul_zero, zero_add, ← bivariateProduct_coeff_one,
    coeff_mul_rowPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  simp

/-- The heterogeneous kernel list as a genuine shared-bias network with all
scalar biases equal to zero. -/
def zeroBiasBilinearNetwork : (fs : List BilinearKernelFactor) →
    {rows cols : ℕ} →
      SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 rows fs.length) (grownSize 2 cols fs.length)
  | [], rows, cols => SharedBiasNetworkTo.nil rows cols 2 2
  | f :: fs, _, _ =>
      SharedBiasNetworkTo.cons f.kernel 0 (zeroBiasBilinearNetwork fs)

/-- Conditional hypothesis saying that every preactivation encountered by
the zero-bias network lies in ReLU's linear branch. -/
def LinearBranchAlong : (fs : List BilinearKernelFactor) →
    {rows cols : ℕ} → Image rows cols → Prop
  | [], _, _, _ => True
  | f :: fs, rows, cols, x =>
      (∀ p : Fin (rows + 2 - 1), ∀ q : Fin (cols + 2 - 1),
          0 ≤ fullConv f.kernel x p q) ∧
        LinearBranchAlong fs (fullConvImage f.kernel x)

private theorem sharedLayerEval_zero_eq_fullConvImage_of_nonnegative
    {rows cols : ℕ} (w : Kernel 2 2) (x : Image rows cols)
    (h : ∀ p : Fin (rows + 2 - 1), ∀ q : Fin (cols + 2 - 1),
      0 ≤ fullConv w x p q) :
    sharedLayerEval w 0 x = fullConvImage w x := by
  funext p q
  change relu (fullConv w x p q + 0) = fullConv w x p q
  rw [add_zero, relu_of_nonneg (h p q)]

/-- Under `LinearBranchAlong`, the actual zero-bias ReLU network is exactly
the formal convolution chain. -/
theorem zeroBiasBilinearNetwork_eval_eq_fullConvChain
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols)
    (hlinear : LinearBranchAlong fs x) :
    (zeroBiasBilinearNetwork fs).eval x = fullConvChain fs x := by
  induction fs generalizing rows cols with
  | nil =>
      funext p q
      rfl
  | cons f fs ih =>
      rcases hlinear with ⟨hfirst, htail⟩
      change (zeroBiasBilinearNetwork fs).eval
          (sharedLayerEval f.kernel 0 x) =
        fullConvChain fs (fullConvImage f.kernel x)
      rw [sharedLayerEval_zero_eq_fullConvImage_of_nonnegative
        f.kernel x hfirst]
      exact ih (fullConvImage f.kernel x) htail

/-- At input width `depth + 1`, the natural output `(1,depth)` is the full
reversed coefficient dot product, for the genuine zero-bias network under
the linear-branch hypothesis. -/
theorem zeroBiasBilinearNetwork_natural_target_reversed_dot
    (fs : List BilinearKernelFactor) (x : Image 1 (fs.length + 1))
    (hlinear : LinearBranchAlong fs x) :
    zeroExtend ((zeroBiasBilinearNetwork fs).eval x) 1 fs.length =
      ∑ j : Fin (fs.length + 1),
        ((bivariateProduct fs).coeff 1).coeff
            (fs.length - (j : ℕ)) * x 0 j := by
  rw [zeroBiasBilinearNetwork_eval_eq_fullConvChain fs x hlinear,
    fullConvChain_row_one_reversed_dot]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_pos]
  omega

/-! ## Specialization to the arbitrary-width ridge factorization -/

/-- The kernel factor attached to interpolation node `i`.  Its four entries
are `[[i+1, 1], [βᵢ + ηᵢ(i+1), ηᵢ]]`. -/
noncomputable def generalRidgeKernelFactor {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) (i : Fin d) :
    BilinearKernelFactor where
  a0 := (((i : ℕ) + 1 : ℕ) : ℝ)
  a1 := 1
  b0 := generalRidgeBeta w i +
    η i * (((i : ℕ) + 1 : ℕ) : ℝ)
  b1 := η i

private theorem generalRidgeKernelFactor_A {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) (i : Fin d) :
    (generalRidgeKernelFactor w η i).A = generalRidgeNodalFactor i := by
  simp [generalRidgeKernelFactor, BilinearKernelFactor.A,
    linearPolynomial, generalRidgeNodalFactor]
  ring

private theorem generalRidgeKernelFactor_B {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) (i : Fin d) :
    (generalRidgeKernelFactor w η i).B =
      generalRidgeLowerFactor w η i := by
  simp [generalRidgeKernelFactor, BilinearKernelFactor.B,
    linearPolynomial, generalRidgeLowerFactor, generalRidgeNodalFactor]
  ring

private theorem generalRidgeKernelFactor_polynomial {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) (i : Fin d) :
    (generalRidgeKernelFactor w η i).polynomial =
      generalRidgeBiFactor (generalRidgeNodalFactor i)
        (generalRidgeLowerFactor w η i) := by
  change C ((generalRidgeKernelFactor w η i).A) +
      C ((generalRidgeKernelFactor w η i).B) * X =
    C (generalRidgeNodalFactor i) +
      C (generalRidgeLowerFactor w η i) * X
  rw [generalRidgeKernelFactor_A, generalRidgeKernelFactor_B]

/-- Natural-order list of all depth-`d` ridge factors. -/
noncomputable def generalRidgeFactorList {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    List BilinearKernelFactor :=
  List.ofFn (generalRidgeKernelFactor w η)

@[simp] theorem generalRidgeFactorList_length {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    (generalRidgeFactorList w η).length = d := by
  simp [generalRidgeFactorList]

/-- The list product is exactly the finite product used by the algebraic
factorization module. -/
theorem generalRidgeFactorList_bivariateProduct {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    bivariateProduct (generalRidgeFactorList w η) =
      ∏ i : Fin d,
        generalRidgeBiFactor (generalRidgeNodalFactor i)
          (generalRidgeLowerFactor w η i) := by
  rw [bivariateProduct, generalRidgeFactorList, List.map_ofFn,
    List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Function.comp_apply]
  exact generalRidgeKernelFactor_polynomial w η i

/-- The horizontal product of the general-ridge factor list is the fixed
monic nodal polynomial, independently of the lower-factor allocation. -/
theorem generalRidgeFactorList_horizontalProduct {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    horizontalProduct (generalRidgeFactorList w η) =
      generalRidgeNodalProduct d := by
  rw [horizontalProduct, generalRidgeFactorList, List.map_ofFn,
    List.prod_ofFn, generalRidgeNodalProduct]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Function.comp_apply]
  exact generalRidgeKernelFactor_A w η i

/-- Pure heterogeneous full convolution implementing the general ridge
factor list. -/
noncomputable def generalRidgeFullConv {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) :=
  fullConvChain (generalRidgeFactorList w η) x

/-- Under the sole algebraic allocation condition, the natural southern
target is the requested affine linear form without its scalar offset.  At
`d = 0`, that condition forces `w 0 = 0` and both sides are zero. -/
theorem generalRidgeFullConv_target {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (hη : ∑ i, η i = w 0) (x : Image 1 (d + 1)) :
    zeroExtend (generalRidgeFullConv w η x) 1 d =
      ∑ j : Fin (d + 1), w j * x 0 j := by
  rw [generalRidgeFullConv, fullConvChain_row_one_reversed_dot]
  have hproduct :
      (bivariateProduct (generalRidgeFactorList w η)).coeff 1 =
        generalRidgeTargetPolynomial w := by
    rw [generalRidgeFactorList_bivariateProduct]
    exact generalRidgeBiProduct_vertical_one w η hη
  rw [hproduct]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_pos]
  · have hrev : d - (j : ℕ) = (Fin.rev j : ℕ) := by
      simp only [Fin.val_rev]
      omega
    rw [hrev, generalRidgeTargetPolynomial_coeff]
    simp
  · omega

/-- The northern row is the nodal-product triangular transform of the input
row, independently of the lower-factor allocation. -/
theorem generalRidgeFullConv_north {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) :
    rowPolynomial (generalRidgeFullConv w η x) 0 =
      generalRidgeNodalProduct d * rowPolynomial x 0 := by
  rw [generalRidgeFullConv, rowPolynomial_fullConvChain_zero,
    generalRidgeFactorList_horizontalProduct]

end OneChannelCNNUniversality
