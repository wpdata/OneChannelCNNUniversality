import OneChannelCNNUniversality.SharedBiasNorthTwoLinearization

/-!
# A heterogeneous chain biased only at its last layer

For a nonempty list of bilinear factors, this module realizes the same
heterogeneous expansive convolutional chain as `zeroBiasBilinearNetwork`,
except that a prescribed shared scalar bias is applied at the last layer
only.  If the corresponding formal chain is nonnegative on its northern two
rows and the last bias is nonnegative, the genuine ReLU network agrees there
with the formal convolution plus that constant.
-/

namespace OneChannelCNNUniversality

/-- Internal cons-form construction.  All layers preceding the last have
zero bias, while the last layer has bias `t`. -/
private def biasedLastBilinearNetworkCons (t : ℝ) :
    (f : BilinearKernelFactor) → (fs : List BilinearKernelFactor) →
      (rows cols : ℕ) →
      SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 rows (f :: fs).length)
        (grownSize 2 cols (f :: fs).length)
  | f, [], _, _ => SharedBiasNetworkTo.single f.kernel t
  | f, g :: fs, rows, cols =>
      SharedBiasNetworkTo.cons f.kernel 0
        (biasedLastBilinearNetworkCons t g fs
          (rows + 2 - 1) (cols + 2 - 1))

/-- The genuine shared-bias network associated with a nonempty factor list,
with bias zero at every layer except the last, where the bias is `t`. -/
def biasedLastBilinearNetwork
    (fs : List BilinearKernelFactor) (hne : fs ≠ []) (t : ℝ)
    (rows cols : ℕ) :
    SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 rows fs.length) (grownSize 2 cols fs.length) :=
  match fs with
  | [] => False.elim (hne rfl)
  | f :: rest => biasedLastBilinearNetworkCons t f rest rows cols

private theorem biasedLastBilinearNetworkCons_depth
    (t : ℝ) (f : BilinearKernelFactor) (fs : List BilinearKernelFactor)
    (rows cols : ℕ) :
    (biasedLastBilinearNetworkCons t f fs rows cols).net.depth =
      (f :: fs).length := by
  induction fs generalizing f rows cols with
  | nil => rfl
  | cons g fs ih =>
      change
        (biasedLastBilinearNetworkCons t g fs
          (rows + 2 - 1) (cols + 2 - 1)).net.depth + 1 =
          (f :: g :: fs).length
      rw [ih]
      simp

/-- The last-biased network has exactly one layer per factor. -/
theorem biasedLastBilinearNetwork_depth
    (fs : List BilinearKernelFactor) (hne : fs ≠ []) (t : ℝ)
    (rows cols : ℕ) :
    (biasedLastBilinearNetwork fs hne t rows cols).net.depth = fs.length := by
  cases fs with
  | nil => exact False.elim (hne rfl)
  | cons f rest =>
      exact biasedLastBilinearNetworkCons_depth t f rest rows cols

private theorem northTwoAgree_lastBiasedLayer_add_constant
    {rows cols : ℕ} (f : BilinearKernelFactor) (x : Image rows cols)
    (t : ℝ)
    (hnonneg : ∀ p : Fin (rows + 2 - 1), (p : ℕ) ≤ 1 →
      ∀ q : Fin (cols + 2 - 1), 0 ≤ fullConv f.kernel x p q)
    (ht : 0 ≤ t) :
    NorthTwoAgree (sharedLayerEval f.kernel t x)
      (fullConvImage f.kernel x +
        constantImage (rows + 2 - 1) (cols + 2 - 1) t) := by
  intro p hp q
  by_cases hprow : p < rows + 2 - 1
  · by_cases hqcol : q < cols + 2 - 1
    · let p' : Fin (rows + 2 - 1) := ⟨p, hprow⟩
      let q' : Fin (cols + 2 - 1) := ⟨q, hqcol⟩
      rw [zeroExtend_of_lt _ hprow hqcol,
        zeroExtend_of_lt _ hprow hqcol]
      change relu (fullConv f.kernel x p' q' + t) =
        fullConv f.kernel x p' q' + t
      exact relu_of_nonneg (add_nonneg (hnonneg p' hp q') ht)
    · rw [zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol),
        zeroExtend_col_outside _ (Nat.le_of_not_gt hqcol)]
  · rw [zeroExtend_row_outside _ (Nat.le_of_not_gt hprow),
      zeroExtend_row_outside _ (Nat.le_of_not_gt hprow)]

private theorem biasedLastBilinearNetworkCons_northTwoAgree
    (t : ℝ) (ht : 0 ≤ t)
    (f : BilinearKernelFactor) (fs : List BilinearKernelFactor)
    {rows cols : ℕ} (x : Image rows cols)
    (hlinear : NorthTwoLinearAlong (f :: fs) x) :
    NorthTwoAgree
      ((biasedLastBilinearNetworkCons t f fs rows cols).eval x)
      (fullConvChain (f :: fs) x +
        constantImage (grownSize 2 rows (f :: fs).length)
          (grownSize 2 cols (f :: fs).length) t) := by
  induction fs generalizing f rows cols x with
  | nil =>
      rcases hlinear with ⟨hfirst, -⟩
      exact northTwoAgree_lastBiasedLayer_add_constant f x t hfirst ht
  | cons g fs ih =>
      rcases hlinear with ⟨hfirst, htail⟩
      let actualFirst := sharedLayerEval f.kernel 0 x
      let formalFirst := fullConvImage f.kernel x
      have hfirstAgree : NorthTwoAgree actualFirst formalFirst := by
        have hz := northTwoAgree_lastBiasedLayer_add_constant
          f x 0 hfirst (by norm_num)
        have himage :
            fullConvImage f.kernel x +
                constantImage (rows + 2 - 1) (cols + 2 - 1) 0 =
              fullConvImage f.kernel x := by
          funext p q
          change fullConv f.kernel x p q + 0 = fullConv f.kernel x p q
          ring
        rw [himage] at hz
        exact hz
      have htransport : NorthTwoAgree
          ((biasedLastBilinearNetworkCons t g fs
            (rows + 2 - 1) (cols + 2 - 1)).eval actualFirst)
          ((biasedLastBilinearNetworkCons t g fs
            (rows + 2 - 1) (cols + 2 - 1)).eval formalFirst) :=
        northTwoAgree_sharedBiasNetworkTo_eval
          (biasedLastBilinearNetworkCons t g fs
            (rows + 2 - 1) (cols + 2 - 1)) hfirstAgree
      have hformal := ih g formalFirst htail
      exact htransport.trans hformal

/-- On the northern two rows, the genuine network biased only at its last
layer agrees with the formal convolution chain plus the shared last bias. -/
theorem biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
    (fs : List BilinearKernelFactor) (hne : fs ≠ []) (t : ℝ)
    {rows cols : ℕ} (x : Image rows cols)
    (hlinear : NorthTwoLinearAlong fs x) (ht : 0 ≤ t) :
    NorthTwoAgree ((biasedLastBilinearNetwork fs hne t rows cols).eval x)
      (fullConvChain fs x +
        constantImage (grownSize 2 rows fs.length)
          (grownSize 2 cols fs.length) t) := by
  cases fs with
  | nil => exact False.elim (hne rfl)
  | cons f rest =>
      exact biasedLastBilinearNetworkCons_northTwoAgree
        t ht f rest x hlinear

/-- Finite-coordinate form of the northern-two-row agreement for the
last-biased network. -/
theorem biasedLastBilinearNetwork_northTwo_eval_eq_fullConvChain_add_constant
    (fs : List BilinearKernelFactor) (hne : fs ≠ []) (t : ℝ)
    {rows cols : ℕ} (x : Image rows cols)
    (hlinear : NorthTwoLinearAlong fs x) (ht : 0 ≤ t)
    (p : Fin (grownSize 2 rows fs.length))
    (q : Fin (grownSize 2 cols fs.length)) (hp : (p : ℕ) ≤ 1) :
    (biasedLastBilinearNetwork fs hne t rows cols).eval x p q =
      fullConvChain fs x p q + t := by
  have hagree :=
    biasedLastBilinearNetwork_northTwoAgree_fullConvChain_add_constant
      fs hne t x hlinear ht (p : ℕ) hp (q : ℕ)
  simpa only [zeroExtend_of_lt _ p.isLt q.isLt, Pi.add_apply,
    constantImage] using hagree

end OneChannelCNNUniversality
