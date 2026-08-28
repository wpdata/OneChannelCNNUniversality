import OneChannelCNNUniversality.Carrier
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A certified gap-three encoder

Repeated use of the one-dimensional two-tap kernel `(1,1)` gives binomial
coefficients.  We deliberately take four times as many steps as the minimal
paper construction.  Sampling at `n - 1 + 3 i` then gives the matrix

`gapMatrix n i j = choose (4 (n-1)) (3 i + j)`

on the reversed input vector.  The extra padding exposes this matrix as a
row-scaled evaluation matrix of a polynomial basis.  Its determinant is
nonzero by a Vandermonde argument.  This avoids importing an unformalized LGV
lemma while preserving gap three, which is the separation needed by routing.
-/

namespace OneChannelCNNUniversality

open scoped BigOperators Polynomial

/-- The zero-extended value immediately to the west of `q`. -/
def predecessor (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | q + 1 => u q

/-- Iteration of the one-dimensional kernel `delta_0 + delta_1`. -/
def iteratePairKernel : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, u => u
  | steps + 1, u => fun q ↦
      iteratePairKernel steps u q + predecessor (iteratePairKernel steps u) q

@[simp] theorem iteratePairKernel_zero (u : ℕ → ℝ) :
    iteratePairKernel 0 u = u := rfl

theorem iteratePairKernel_succ (steps : ℕ) (u : ℕ → ℝ) (q : ℕ) :
    iteratePairKernel (steps + 1) u q =
      iteratePairKernel steps u q + predecessor (iteratePairKernel steps u) q := rfl

/-- Rectangle size after `steps` expansive layers, defined in the same
front-to-back recursion used by `Network.cons`. -/
def grownSize (kernelSize start : ℕ) : ℕ → ℕ
  | 0 => start
  | steps + 1 => grownSize kernelSize (start + kernelSize - 1) steps

/-- Formal linear iteration of one convolution kernel, with ReLU and carriers
temporarily omitted. -/
def iterateFullConv {kRows kCols : ℕ} (w : Kernel kRows kCols) :
    (steps : ℕ) → {rows cols : ℕ} → Image rows cols →
      Image (grownSize kRows rows steps) (grownSize kCols cols steps)
  | 0, _, _, x => x
  | steps + 1, _, _, x => iterateFullConv w steps (fullConvImage w x)

/-- `steps` iterations of `w`, followed by one final convolution with
`finalKernel`. -/
def iterateThenConv {kRows kCols : ℕ}
    (w finalKernel : Kernel kRows kCols) :
    (steps : ℕ) → {rows cols : ℕ} → Image rows cols →
      Image (grownSize kRows rows (steps + 1)) (grownSize kCols cols (steps + 1))
  | 0, _, _, x => fullConvImage finalKernel x
  | steps + 1, _, _, x => iterateThenConv w finalKernel steps (fullConvImage w x)

def maskedImage {rows cols : ℕ}
    (keep : Fin rows → Fin cols → Prop) [DecidableRel keep]
    (x : Image rows cols) : Image rows cols :=
  fun i j ↦ if keep i j then x i j else 0

/-- Number of binomial-convolution steps used by the gap-three encoder. -/
def encoderDepth (n : ℕ) : ℕ := 4 * (n - 1)

/-- Output location of the `i`-th separated register. -/
def encoderSite (n : ℕ) (i : Fin n) : ℕ := n - 1 + 3 * (i : ℕ)

/-- Binomial sampling matrix acting on the reversed input coordinates. -/
def gapMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (Nat.choose (encoderDepth n) (3 * (i : ℕ) + (j : ℕ)) : ℝ)

namespace EncoderPolynomial

open Polynomial

/-- The common denominator-clearing polynomial basis used in the
Vandermonde proof. -/
noncomputable def basisPolynomial (n : ℕ) (j : Fin n) : ℝ[X] :=
  (∏ t ∈ Finset.range (j : ℕ),
      (X - Polynomial.C (((encoderDepth n : ℕ) : ℝ) - (t : ℝ)))) *
    (∏ t ∈ Finset.Ico ((j : ℕ) + 1) n,
      (X + Polynomial.C (t : ℝ)))

/-- Evaluation matrix of the denominator-cleared basis. -/
noncomputable def evalMatrix (n : ℕ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (basisPolynomial n j).eval (v i)

/-- Coefficient matrix of the denominator-cleared basis. -/
noncomputable def coeffMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (basisPolynomial n j).coeff (i : ℕ)

theorem basisPolynomial_monic (n : ℕ) (j : Fin n) :
    (basisPolynomial n j).Monic := by
  apply Polynomial.Monic.mul
  · exact Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _
  · exact Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_add_C _

theorem basisPolynomial_natDegree (n : ℕ) (j : Fin n) (hn : 0 < n) :
    (basisPolynomial n j).natDegree = n - 1 := by
  rw [basisPolynomial, Polynomial.natDegree_mul
    ((Polynomial.monic_prod_of_monic _ _
      fun _ _ ↦ Polynomial.monic_X_sub_C _).ne_zero)
    ((Polynomial.monic_prod_of_monic _ _
      fun _ _ ↦ Polynomial.monic_X_add_C _).ne_zero),
    Polynomial.natDegree_prod_of_monic,
    Polynomial.natDegree_prod_of_monic]
  · have hsub : ∀ t : ℕ,
        (X - Polynomial.C (((encoderDepth n : ℕ) : ℝ) - (t : ℝ))).natDegree = 1 :=
      fun t ↦ Polynomial.natDegree_X_sub_C _
    have hadd : ∀ t : ℕ,
        (X + Polynomial.C (t : ℝ)).natDegree = 1 :=
      fun t ↦ Polynomial.natDegree_X_add_C _
    simp_rw [hsub, hadd]
    simp
    omega
  · intro i hi
    exact Polynomial.monic_X_add_C _
  · intro i hi
    exact Polynomial.monic_X_sub_C _

/-- Evaluation is Vandermonde multiplication by the coefficient matrix. -/
theorem evalMatrix_eq_vandermonde_mul_coeffMatrix (n : ℕ) (hn : 0 < n)
    (v : Fin n → ℝ) :
    evalMatrix n v = Matrix.vandermonde v * coeffMatrix n := by
  ext i j
  simp only [evalMatrix, coeffMatrix, Matrix.mul_apply, Matrix.vandermonde_apply]
  have hdeg : (basisPolynomial n j).natDegree < n := by
    rw [basisPolynomial_natDegree n j hn]
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [mul_comm]

theorem basisPolynomial_eval (n : ℕ) (j : Fin n) (x : ℝ) :
    (basisPolynomial n j).eval x =
      (∏ t ∈ Finset.range (j : ℕ),
        (x - (((encoderDepth n : ℕ) : ℝ) - (t : ℝ)))) *
      (∏ t ∈ Finset.Ico ((j : ℕ) + 1) n, (x + (t : ℝ))) := by
  simp [basisPolynomial, Polynomial.eval_mul, Polynomial.eval_prod]

/-- Test points at which the basis-evaluation matrix is triangular. -/
def specialPoint (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.cases ((encoderDepth (m + 1) : ℕ) : ℝ)
    (fun i ↦ -(((i : ℕ) + 1 : ℕ) : ℝ))

theorem specialPoint_injective (m : ℕ) : Function.Injective (specialPoint m) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
          simp only [specialPoint, Fin.cases_zero, Fin.cases_succ] at hij
          have hj : (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
          have hd : (0 : ℝ) ≤ ((encoderDepth (m + 1) : ℕ) : ℝ) := by positivity
          exfalso
          linarith
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          simp only [specialPoint, Fin.cases_zero, Fin.cases_succ] at hij
          have hi : (0 : ℝ) < (((i : ℕ) + 1 : ℕ) : ℝ) := by positivity
          have hd : (0 : ℝ) ≤ ((encoderDepth (m + 1) : ℕ) : ℝ) := by positivity
          exfalso
          linarith
      | succ j =>
          simp only [specialPoint, Fin.cases_succ] at hij
          apply Fin.succ_inj.mpr
          apply Fin.ext
          have hv : (i : ℕ) + 1 = (j : ℕ) + 1 := by
            exact_mod_cast (neg_inj.mp hij)
          omega

theorem evalMatrix_special_upperTriangular (m : ℕ) :
    (evalMatrix (m + 1) (specialPoint m)).BlockTriangular id := by
  intro i j hji
  change (basisPolynomial (m + 1) j).eval (specialPoint m i) = 0
  induction i using Fin.cases with
  | zero =>
      have : j < (0 : Fin (m + 1)) := by simpa using hji
      exact (Fin.not_lt_zero j this).elim
  | succ i =>
      rw [basisPolynomial_eval]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero
      · apply Finset.mem_Ico.mpr
        constructor
        · have : j < i.succ := by simpa using hji
          exact this
        · omega
      · simp [specialPoint]

theorem specialPoint_first_factor_ne_zero (m : ℕ) (i : Fin (m + 1))
    (t : ℕ) (ht : t < (i : ℕ)) :
    specialPoint m i - (((encoderDepth (m + 1) : ℕ) : ℝ) - (t : ℝ)) ≠ 0 := by
  induction i using Fin.cases with
  | zero => simp at ht
  | succ i =>
      simp only [specialPoint, Fin.cases_succ]
      have hi : (i : ℕ) < m := i.isLt
      have ht' : t ≤ m := by omega
      have hcast : (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast ht'
      have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
      simp [encoderDepth]
      nlinarith

theorem specialPoint_second_factor_ne_zero (m : ℕ) (i : Fin (m + 1))
    (t : ℕ) (ht : (i : ℕ) + 1 ≤ t) :
    specialPoint m i + (t : ℝ) ≠ 0 := by
  induction i using Fin.cases with
  | zero =>
      simp only [specialPoint, Fin.cases_zero]
      have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have hd : (0 : ℝ) ≤ ((encoderDepth (m + 1) : ℕ) : ℝ) := by positivity
      linarith
  | succ i =>
      simp only [specialPoint, Fin.cases_succ]
      have ht' : (((i : ℕ) + 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      norm_num at ht' ⊢
      linarith

theorem evalMatrix_special_diagonal_ne_zero (m : ℕ) (i : Fin (m + 1)) :
    evalMatrix (m + 1) (specialPoint m) i i ≠ 0 := by
  change (basisPolynomial (m + 1) i).eval (specialPoint m i) ≠ 0
  rw [basisPolynomial_eval]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact specialPoint_first_factor_ne_zero m i t (Finset.mem_range.mp ht)
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact specialPoint_second_factor_ne_zero m i t (Finset.mem_Ico.mp ht).1

theorem evalMatrix_special_det_ne_zero (m : ℕ) :
    Matrix.det (evalMatrix (m + 1) (specialPoint m)) ≠ 0 := by
  rw [Matrix.det_of_upperTriangular (evalMatrix_special_upperTriangular m)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ evalMatrix_special_diagonal_ne_zero m i

theorem coeffMatrix_det_ne_zero (m : ℕ) :
    Matrix.det (coeffMatrix (m + 1)) ≠ 0 := by
  have heval := evalMatrix_special_det_ne_zero m
  rw [evalMatrix_eq_vandermonde_mul_coeffMatrix (m + 1) (by omega),
    Matrix.det_mul] at heval
  exact right_ne_zero_of_mul heval

theorem evalMatrix_det_ne_zero_of_injective (n : ℕ) (hn : 0 < n)
    (v : Fin n → ℝ) (hv : Function.Injective v) :
    Matrix.det (evalMatrix n v) ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [evalMatrix_eq_vandermonde_mul_coeffMatrix (m + 1) (by omega), Matrix.det_mul]
  exact mul_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
    (coeffMatrix_det_ne_zero m)

theorem choose_mul_ascFactorial (L x j : ℕ) :
    L.choose (x + j) * (x + 1).ascFactorial j =
      L.choose x * (L - x).descFactorial j := by
  rw [Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hchoose := Nat.choose_mul (n := L) (k := x + j) (s := x) (by omega)
  rw [Nat.add_sub_cancel_left] at hchoose
  rw [Nat.choose_symm_add] at hchoose
  calc
    L.choose (x + j) * (j.factorial * (x + j).choose j) =
        j.factorial * (L.choose (x + j) * (x + j).choose j) := by ac_rfl
    _ = j.factorial * (L.choose x * (L - x).choose j) := by rw [hchoose]
    _ = L.choose x * (j.factorial * (L - x).choose j) := by ac_rfl

theorem basisPolynomial_eval_nat (n : ℕ) (j : Fin n) (x : ℕ)
    (hxl : x + (j : ℕ) ≤ encoderDepth n) :
    (basisPolynomial n j).eval (x : ℝ) =
      (-1 : ℝ) ^ (j : ℕ) * ((encoderDepth n - x).descFactorial (j : ℕ) : ℕ) *
        (((x + (j : ℕ) + 1).ascFactorial (n - ((j : ℕ) + 1)) : ℕ) : ℝ) := by
  rw [basisPolynomial_eval]
  congr 1
  · have hfactor : ∀ t ∈ Finset.range (j : ℕ),
        (x : ℝ) - (((encoderDepth n : ℕ) : ℝ) - (t : ℝ)) =
          -(((encoderDepth n - x - t : ℕ) : ℝ)) := by
      intro t ht
      have hx : x ≤ encoderDepth n := by omega
      have ht' : t ≤ encoderDepth n - x := by
        simp only [Finset.mem_range] at ht
        omega
      rw [Nat.cast_sub ht', Nat.cast_sub hx]
      push_cast
      ring
    rw [Finset.prod_congr rfl hfactor]
    rw [Finset.prod_neg]
    simp [Nat.descFactorial_eq_prod_range]
  · rw [Finset.prod_Ico_eq_prod_range]
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro t ht
    push_cast
    ring

end EncoderPolynomial

/-- Distinct nonnegative evaluation nodes used by the binomial sampler. -/
def encoderNode (n : ℕ) (i : Fin n) : ℝ := (3 * (i : ℕ) : ℕ)

theorem encoderNode_injective (n : ℕ) : Function.Injective (encoderNode n) := by
  intro i j hij
  apply Fin.ext
  norm_num [encoderNode] at hij
  exact_mod_cast hij

def denominatorFactor (n : ℕ) (i : Fin n) : ℝ :=
  (((3 * (i : ℕ) + 1).ascFactorial (n - 1) : ℕ) : ℝ)

def chooseFactor (n : ℕ) (i : Fin n) : ℝ :=
  (Nat.choose (encoderDepth n) (3 * (i : ℕ)) : ℝ)

def signFactor (n : ℕ) (j : Fin n) : ℝ := (-1 : ℝ) ^ (j : ℕ)

theorem gapMatrix_scaled_entry (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    denominatorFactor n i * gapMatrix n i j =
      chooseFactor n i *
        (EncoderPolynomial.evalMatrix n (encoderNode n) i j * signFactor n j) := by
  let x : ℕ := 3 * (i : ℕ)
  let k : ℕ := j
  let L : ℕ := encoderDepth n
  have hi : (i : ℕ) ≤ n - 1 := by omega
  have hj : k ≤ n - 1 := by dsimp [k]; omega
  have hxk : x + k ≤ L := by
    dsimp [x, k, L, encoderDepth]
    omega
  have hsplit :
      (x + 1).ascFactorial k * (x + k + 1).ascFactorial (n - (k + 1)) =
        (x + 1).ascFactorial (n - 1) := by
    have h := Nat.ascFactorial_mul_ascFactorial (x + 1) k (n - (k + 1))
    rw [show x + 1 + k = x + k + 1 by omega,
      show k + (n - (k + 1)) = n - 1 by omega] at h
    exact h
  have hchoose := EncoderPolynomial.choose_mul_ascFactorial L x k
  have hpoly := EncoderPolynomial.basisPolynomial_eval_nat n j x hxk
  have hsign : signFactor n j * signFactor n j = 1 := by
    change (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1
    rw [← pow_add, show k + k = 2 * k by omega, pow_mul]
    norm_num
  simp only [denominatorFactor, gapMatrix, chooseFactor,
    EncoderPolynomial.evalMatrix, encoderNode]
  change (((x + 1).ascFactorial (n - 1) : ℕ) : ℝ) *
      ((L.choose (x + k) : ℕ) : ℝ) =
    ((L.choose x : ℕ) : ℝ) *
      ((EncoderPolynomial.basisPolynomial n j).eval (x : ℝ) * signFactor n j)
  rw [mul_comm (((x + 1).ascFactorial (n - 1) : ℕ) : ℝ)]
  have hsplitR : (((x + 1).ascFactorial (n - 1) : ℕ) : ℝ) =
      (((x + 1).ascFactorial k : ℕ) : ℝ) *
        (((x + k + 1).ascFactorial (n - (k + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hsplit.symm
  have hchooseR : ((L.choose (x + k) : ℕ) : ℝ) *
      (((x + 1).ascFactorial k : ℕ) : ℝ) =
        ((L.choose x : ℕ) : ℝ) *
          (((L - x).descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  rw [hsplitR, ← mul_assoc, hchooseR]
  rw [hpoly]
  simp only [signFactor] at hsign ⊢
  ring_nf at hsign ⊢
  rw [hsign]
  simp [L, k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

noncomputable def denominatorDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (denominatorFactor n)

noncomputable def chooseDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (chooseFactor n)

noncomputable def signDiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (signFactor n)

theorem scaled_gapMatrix_eq (n : ℕ) (hn : 0 < n) :
    denominatorDiagonal n * gapMatrix n =
      chooseDiagonal n * EncoderPolynomial.evalMatrix n (encoderNode n) * signDiagonal n := by
  ext i j
  simp [denominatorDiagonal, chooseDiagonal, signDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, gapMatrix_scaled_entry n hn, mul_assoc]

theorem denominatorFactor_ne_zero (n : ℕ) (i : Fin n) :
    denominatorFactor n i ≠ 0 := by
  unfold denominatorFactor
  exact_mod_cast (Nat.ne_of_gt (Nat.ascFactorial_pos (3 * (i : ℕ)) (n - 1)))

theorem chooseFactor_ne_zero (n : ℕ) (hn : 0 < n) (i : Fin n) :
    chooseFactor n i ≠ 0 := by
  unfold chooseFactor encoderDepth
  have hi : (i : ℕ) ≤ n - 1 := by omega
  have hle : 3 * (i : ℕ) ≤ 4 * (n - 1) := by omega
  exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hle))

theorem signFactor_ne_zero (n : ℕ) (j : Fin n) : signFactor n j ≠ 0 := by
  exact pow_ne_zero _ (by norm_num [signFactor])

theorem denominatorDiagonal_det_ne_zero (n : ℕ) :
    Matrix.det (denominatorDiagonal n) ≠ 0 := by
  rw [denominatorDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ denominatorFactor_ne_zero n i

theorem chooseDiagonal_det_ne_zero (n : ℕ) (hn : 0 < n) :
    Matrix.det (chooseDiagonal n) ≠ 0 := by
  rw [chooseDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ chooseFactor_ne_zero n hn i

theorem signDiagonal_det_ne_zero (n : ℕ) :
    Matrix.det (signDiagonal n) ≠ 0 := by
  rw [signDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ signFactor_ne_zero n j

/-- The gap-three binomial sampler is nonsingular in every positive
dimension.  The proof is entirely internal: diagonal scaling, a polynomial
coefficient basis certified at triangular test points, and Mathlib's
Vandermonde determinant theorem. -/
theorem gapMatrix_det_ne_zero (n : ℕ) (hn : 0 < n) :
    Matrix.det (gapMatrix n) ≠ 0 := by
  have hmatrix := congrArg Matrix.det (scaled_gapMatrix_eq n hn)
  simp only [Matrix.det_mul] at hmatrix
  have hright : Matrix.det (chooseDiagonal n) *
      Matrix.det (EncoderPolynomial.evalMatrix n (encoderNode n)) *
        Matrix.det (signDiagonal n) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (chooseDiagonal_det_ne_zero n hn)
        (EncoderPolynomial.evalMatrix_det_ne_zero_of_injective n hn
          (encoderNode n) (encoderNode_injective n)))
      (signDiagonal_det_ne_zero n)
  intro hgap
  apply hright
  rw [← hmatrix, hgap, mul_zero]

theorem gapMatrix_det_isUnit (n : ℕ) (hn : 0 < n) :
    IsUnit (Matrix.det (gapMatrix n)) :=
  isUnit_iff_ne_zero.mpr (gapMatrix_det_ne_zero n hn)

end OneChannelCNNUniversality
