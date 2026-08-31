import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution

/-!
# Collision-free algebra for parallel affine ridges

Let the input width be `m` and let `r` independent weight vectors be given.
The coefficient blocks

\[
  sm+1,\ldots,(s+1)m,\qquad 0\le s<r,
\]

are pairwise disjoint.  Store the reversed coefficients of weight vector
`s` in block `s`.  Convolution at output column

\[
  q_s=(s+1)m
\]

then reads exactly that weight vector and no other block.  The general ridge
factorization realizes the whole packed polynomial in one depth-`rm`
bilinear chain.  This module proves that algebraic parallelization theorem;
compact shared-bias carrier and simultaneous ReLU selection are separate
network-level obligations.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- Coefficient zero is reserved.  The remaining `r*m` coefficients are
identified with `r` disjoint blocks of length `m`; the within-block index is
reversed to match convolution. -/
def parallelRidgePackedCoefficient {r m : ℕ}
    (weights : Fin r → Fin m → ℝ) : Fin (r * m + 1) → ℝ :=
  Fin.cases 0 (fun k ↦
    let sj := (finProdFinEquiv (m := r) (n := m)).symm k
    weights sj.1 (Fin.rev sj.2))

@[simp] theorem parallelRidgePackedCoefficient_zero {r m : ℕ}
    (weights : Fin r → Fin m → ℝ) :
    parallelRidgePackedCoefficient weights 0 = 0 := rfl

/-- The coefficient at the position read by input coordinate `j` at target
`s` is exactly the requested weight. -/
theorem parallelRidgePackedCoefficient_window {r m : ℕ}
    (weights : Fin r → Fin m → ℝ) (s : Fin r) (j : Fin m) :
    parallelRidgePackedCoefficient weights
        ⟨((s : ℕ) + 1) * m - (j : ℕ), by
          have hs : (s : ℕ) + 1 ≤ r := Nat.succ_le_iff.mpr s.isLt
          have htarget : ((s : ℕ) + 1) * m ≤ r * m :=
            Nat.mul_le_mul_right m hs
          exact lt_of_le_of_lt
            ((Nat.sub_le _ _).trans htarget) (Nat.lt_succ_self _)⟩ =
      weights s j := by
  let e := finProdFinEquiv (m := r) (n := m)
  let k : Fin (r * m) := e (s, Fin.rev j)
  have hindex :
      (⟨((s : ℕ) + 1) * m - (j : ℕ), by
          have hs : (s : ℕ) + 1 ≤ r := Nat.succ_le_iff.mpr s.isLt
          have htarget : ((s : ℕ) + 1) * m ≤ r * m :=
            Nat.mul_le_mul_right m hs
          exact lt_of_le_of_lt
            ((Nat.sub_le _ _).trans htarget) (Nat.lt_succ_self _)⟩ :
        Fin (r * m + 1)) = k.succ := by
    apply Fin.ext
    simp [k, e, finProdFinEquiv, Nat.mul_comm, Nat.mul_succ]
    omega
  rw [hindex]
  change weights (e.symm k).1 (Fin.rev (e.symm k).2) = weights s j
  have hk : e.symm k = (s, Fin.rev j) := by
    simp [k]
  rw [hk]
  simp

/-- Natural-order general-ridge weights obtained by reversing the packed
polynomial coefficients. -/
def parallelRidgePackedWeights {r m : ℕ}
    (weights : Fin r → Fin m → ℝ) : Fin (r * m + 1) → ℝ :=
  fun i ↦ parallelRidgePackedCoefficient weights (Fin.rev i)

/-- The general-ridge target polynomial is exactly the packed coefficient
array. -/
theorem parallelRidgePackedTargetPolynomial_coeff {r m : ℕ}
    (weights : Fin r → Fin m → ℝ) (k : Fin (r * m + 1)) :
    (generalRidgeTargetPolynomial
      (parallelRidgePackedWeights weights)).coeff k =
        parallelRidgePackedCoefficient weights k := by
  rw [generalRidgeTargetPolynomial_coeff]
  simp [parallelRidgePackedWeights]

/-- Put the leading target weight in the first allocation slot and zero in
all other slots. -/
def parallelRidgeAllocation {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (weights : Fin r → Fin m → ℝ) : Fin (r * m) → ℝ :=
  fun i ↦ if i = (⟨0, Nat.mul_pos hr hm⟩ : Fin (r * m)) then
    parallelRidgePackedWeights weights 0 else 0

/-- The packed allocation has the leading total required by the general
ridge factorization. -/
theorem parallelRidgeAllocation_sum {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (weights : Fin r → Fin m → ℝ) :
    ∑ i : Fin (r * m), parallelRidgeAllocation hr hm weights i =
      parallelRidgePackedWeights weights 0 := by
  classical
  simp [parallelRidgeAllocation]

/-- The one-chain factor list realizing all packed ridge linear forms. -/
noncomputable def parallelRidgeFactorList {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (weights : Fin r → Fin m → ℝ) :
    List BilinearKernelFactor :=
  generalRidgeFactorList (parallelRidgePackedWeights weights)
    (parallelRidgeAllocation hr hm weights)

@[simp] theorem parallelRidgeFactorList_length {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (weights : Fin r → Fin m → ℝ) :
    (parallelRidgeFactorList hr hm weights).length = r * m := by
  simp [parallelRidgeFactorList]

/-- The vertical-degree-one polynomial of the packed factor list is exactly
the collision-free packed target polynomial. -/
theorem parallelRidgeFactorList_verticalOne {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (weights : Fin r → Fin m → ℝ) :
    verticalOne (parallelRidgeFactorList hr hm weights) =
      generalRidgeTargetPolynomial (parallelRidgePackedWeights weights) := by
  rw [parallelRidgeFactorList, ← bivariateProduct_coeff_one,
    generalRidgeFactorList_bivariateProduct]
  exact generalRidgeBiProduct_vertical_one
    (parallelRidgePackedWeights weights)
    (parallelRidgeAllocation hr hm weights)
    (parallelRidgeAllocation_sum hr hm weights)

/-- One pure depth-`r*m` bilinear convolution chain computes all `r`
independent linear forms at the separated row-one targets `(1,(s+1)*m)`.
No padding hypothesis is needed: unused packed coefficients simply do not
meet the width-`m` input window. -/
theorem parallelRidgeFullConv_target {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (weights : Fin r → Fin m → ℝ)
    (x : Image 1 m) (s : Fin r) :
    zeroExtend (fullConvChain (parallelRidgeFactorList hr hm weights) x)
        1 (((s : ℕ) + 1) * m) =
      ∑ j : Fin m, weights s j * x 0 j := by
  rw [fullConvChain_row_one_reversed_dot]
  rw [bivariateProduct_coeff_one,
    parallelRidgeFactorList_verticalOne hr hm weights]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [if_pos]
  · have hk : ((s : ℕ) + 1) * m - (j : ℕ) < r * m + 1 := by
      have hs : (s : ℕ) + 1 ≤ r := Nat.succ_le_iff.mpr s.isLt
      have htarget : ((s : ℕ) + 1) * m ≤ r * m :=
        Nat.mul_le_mul_right m hs
      exact lt_of_le_of_lt
        ((Nat.sub_le _ _).trans htarget) (Nat.lt_succ_self _)
    let k : Fin (r * m + 1) :=
      ⟨((s : ℕ) + 1) * m - (j : ℕ), hk⟩
    have hpacked := parallelRidgePackedTargetPolynomial_coeff weights k
    have hwindow := parallelRidgePackedCoefficient_window weights s j
    change
      (generalRidgeTargetPolynomial
        (parallelRidgePackedWeights weights)).coeff k * x 0 j = _
    rw [hpacked, hwindow]
  · have hj := j.isLt
    have hone : 1 ≤ (s : ℕ) + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hbase : m ≤ ((s : ℕ) + 1) * m := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hone
    exact (Nat.le_of_lt hj).trans hbase

end OneChannelCNNUniversality
