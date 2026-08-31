import OneChannelCNNUniversality.SharedBiasCausality
import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution

/-!
# Linearization restricted to the northern two rows

A `2 × 2` full convolution at output row zero or one reads only input rows
zero and one.  Consequently, if the preactivation is nonnegative on just
those two rows at every stage, the genuine zero-bias ReLU network agrees with
the formal convolution chain there.  ReLU may take either branch farther
south without feeding any discrepancy back toward the northern boundary.

This is weaker than `LinearBranchAlong`, which requires every output site at
every stage to remain linear, and is tailored to the two-row carrier used by
the strengthened arbitrary-width ridge block.
-/

namespace OneChannelCNNUniversality

/-- Two images agree at every natural coordinate in rows zero and one.  Zero
extension makes this definition uniform for empty and one-row images. -/
def NorthTwoAgree {rows cols : ℕ} (x y : Image rows cols) : Prop :=
  ∀ p, p ≤ 1 → ∀ q, zeroExtend x p q = zeroExtend y p q

namespace NorthTwoAgree

theorem refl {rows cols : ℕ} (x : Image rows cols) :
    NorthTwoAgree x x := by
  intro p hp q
  rfl

theorem symm {rows cols : ℕ} {x y : Image rows cols}
    (hxy : NorthTwoAgree x y) : NorthTwoAgree y x := by
  intro p hp q
  exact (hxy p hp q).symm

theorem trans {rows cols : ℕ} {x y z : Image rows cols}
    (hxy : NorthTwoAgree x y) (hyz : NorthTwoAgree y z) :
    NorthTwoAgree x z := by
  intro p hp q
  exact (hxy p hp q).trans (hyz p hp q)

end NorthTwoAgree

/-- Every genuine shared-bias layer preserves agreement of the northern two
rows, regardless of what happens farther south. -/
theorem northTwoAgree_sharedLayerEval
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (b : ℝ)
    {x y : Image rows cols} (hxy : NorthTwoAgree x y) :
    NorthTwoAgree (sharedLayerEval w b x) (sharedLayerEval w b y) := by
  intro p hp q
  have hnorthwest : NorthwestAgree x y p q := by
    intro i hi j hj
    exact hxy i (hi.trans hp) j
  exact northwestAgree_sharedLayerEval w b hnorthwest p le_rfl q le_rfl

/-- Every finite explicitly typed shared-bias network preserves northern-two
agreement. -/
theorem northTwoAgree_sharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} (hxy : NorthTwoAgree x y) :
    NorthTwoAgree (net.eval x) (net.eval y) := by
  intro p hp q
  have hnorthwest : NorthwestAgree x y p q := by
    intro i hi j hj
    exact hxy i (hi.trans hp) j
  exact northwestAgree_sharedBiasNetworkTo_eval net hnorthwest p le_rfl q le_rfl

/-- Stagewise nonnegativity hypothesis only on output rows zero and one. -/
def NorthTwoLinearAlong : (fs : List BilinearKernelFactor) →
    {rows cols : ℕ} → Image rows cols → Prop
  | [], _, _, _ => True
  | f :: fs, rows, cols, x =>
      (∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
        ∀ q : Fin (cols + 2 - 1), 0 ≤ fullConv f.kernel x p q) ∧
      NorthTwoLinearAlong fs (fullConvImage f.kernel x)

/-- Full-image linearity implies northern-two-row linearity. -/
theorem linearBranchAlong_imp_northTwoLinearAlong
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols)
    (hlinear : LinearBranchAlong fs x) : NorthTwoLinearAlong fs x := by
  induction fs generalizing rows cols with
  | nil => trivial
  | cons f fs ih =>
      rcases hlinear with ⟨hfirst, htail⟩
      refine ⟨?_, ih (fullConvImage f.kernel x) htail⟩
      intro p hp q
      exact hfirst p q

private theorem northTwoAgree_sharedLayerEval_zero_fullConvImage
    {rows cols : ℕ} (f : BilinearKernelFactor) (x : Image rows cols)
    (hnonneg : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1), 0 ≤ fullConv f.kernel x p q) :
    NorthTwoAgree (sharedLayerEval f.kernel 0 x)
      (fullConvImage f.kernel x) := by
  intro p hp q
  by_cases hprow : p < rows + 2 - 1
  · by_cases hqcol : q < cols + 2 - 1
    · let p' : Fin (rows + 2 - 1) := ⟨p, hprow⟩
      let q' : Fin (cols + 2 - 1) := ⟨q, hqcol⟩
      rw [zeroExtend_of_lt _ hprow hqcol,
        zeroExtend_of_lt _ hprow hqcol]
      change relu (fullConv f.kernel x p' q' + 0) =
        fullConv f.kernel x p' q'
      rw [add_zero, relu_of_nonneg (hnonneg p' hp q')]
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol),
        zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol)]
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hprow),
      zeroExtend_row_outside _ (Nat.le_of_not_gt hprow)]

/-- Under the northern-two-row hypothesis, the genuine zero-bias network and
the formal heterogeneous convolution chain agree throughout those rows. -/
theorem zeroBiasBilinearNetwork_northTwoAgree_fullConvChain
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols)
    (hlinear : NorthTwoLinearAlong fs x) :
    NorthTwoAgree ((zeroBiasBilinearNetwork fs).eval x)
      (fullConvChain fs x) := by
  induction fs generalizing rows cols with
  | nil => exact NorthTwoAgree.refl x
  | cons f fs ih =>
      rcases hlinear with ⟨hfirst, htail⟩
      let actualFirst := sharedLayerEval f.kernel 0 x
      let formalFirst := fullConvImage f.kernel x
      have hfirstAgree : NorthTwoAgree actualFirst formalFirst := by
        exact northTwoAgree_sharedLayerEval_zero_fullConvImage f x hfirst
      have htransport : NorthTwoAgree
          ((zeroBiasBilinearNetwork fs).eval actualFirst)
          ((zeroBiasBilinearNetwork fs).eval formalFirst) :=
        northTwoAgree_sharedBiasNetworkTo_eval
          (zeroBiasBilinearNetwork fs) hfirstAgree
      have hformal : NorthTwoAgree
          ((zeroBiasBilinearNetwork fs).eval formalFirst)
          (fullConvChain fs formalFirst) :=
        ih formalFirst htail
      exact htransport.trans hformal

/-- Finite-index evaluation form of northern-two-row agreement. -/
theorem zeroBiasBilinearNetwork_northTwo_eval_eq_fullConvChain
    (fs : List BilinearKernelFactor) {rows cols : ℕ} (x : Image rows cols)
    (hlinear : NorthTwoLinearAlong fs x)
    (p : Fin (grownSize 2 rows fs.length))
    (q : Fin (grownSize 2 cols fs.length)) (hp : (p : ℕ) ≤ 1) :
    (zeroBiasBilinearNetwork fs).eval x p q = fullConvChain fs x p q := by
  have hagree :=
    zeroBiasBilinearNetwork_northTwoAgree_fullConvChain fs x hlinear
      (p : ℕ) hp (q : ℕ)
  simpa only [zeroExtend_of_lt _ p.isLt q.isLt] using hagree

end OneChannelCNNUniversality
