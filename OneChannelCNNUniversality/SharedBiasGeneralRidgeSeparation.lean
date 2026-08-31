import OneChannelCNNUniversality.SharedBiasGeneralRidgeCarrier
import OneChannelCNNUniversality.SharedBiasGeneralRidgeConvolution

/-!
# Final-factor separation for arbitrary-width ridge carriers

For depth `d ≥ 2`, apply the last separated ridge factor to a rectangular
constant carrier of size `d × (2d)`.  At the southern target `(1,d)`, all
four entries of the `2 × 2` kernel contribute and the response is at most
`-1`.  Along the entire northern row, only the positive horizontal entries
`d` and `1` contribute, so every response is at least `1`.  The resulting
north-to-target gap is therefore at least `2`.

These are pre-ReLU convolution statements.  They isolate the sign separation
needed when the final shared bias is chosen in the later carrier construction.
-/

namespace OneChannelCNNUniversality

/-- The last factor selected by the separated allocation. -/
noncomputable def generalRidgeSeparatedLastFactor {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) : BilinearKernelFactor :=
  generalRidgeKernelFactor w (generalRidgeSeparatedAllocation hd w)
    (generalRidgeLastIndex hd)

@[simp] theorem generalRidgeSeparatedLastFactor_eq {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    generalRidgeSeparatedLastFactor hd w =
      generalRidgeKernelFactor w (generalRidgeSeparatedAllocation hd w)
        (generalRidgeLastIndex hd) := rfl

/-- The expansive `2 × 2` kernel of the last separated factor. -/
noncomputable def generalRidgeSeparatedLastKernel {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) : Kernel 2 2 :=
  (generalRidgeSeparatedLastFactor hd w).kernel

@[simp] theorem generalRidgeSeparatedLastKernel_eq {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    generalRidgeSeparatedLastKernel hd w =
      (generalRidgeKernelFactor w (generalRidgeSeparatedAllocation hd w)
        (generalRidgeLastIndex hd)).kernel := rfl

/-- The factor slot immediately before the last one. -/
def generalRidgePenultimateIndex {d : ℕ} (hd : 2 ≤ d) : Fin d :=
  ⟨d - 2, by omega⟩

/-- The natural-order prefix before the final two ridge factors. -/
noncomputable def generalRidgeFactorPrefix {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    List BilinearKernelFactor :=
  List.ofFn fun i : Fin (d - 2) ↦
    generalRidgeKernelFactor w η ⟨i, by omega⟩

@[simp] theorem generalRidgeFactorPrefix_length {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    (generalRidgeFactorPrefix hd w η).length = d - 2 := by
  simp [generalRidgeFactorPrefix]

private theorem listOfFn_split_last_two {n : ℕ} {A : Type*}
    (f : Fin (n + 2) → A) :
    List.ofFn f =
      List.ofFn (fun i : Fin n ↦ f ⟨i, by omega⟩) ++
        [f ⟨n, by omega⟩, f ⟨n + 1, by omega⟩] := by
  rw [List.ofFn_succ']
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, List.append_assoc]
  congr 1

/-- A natural-order factor list consists of its prefix, penultimate factor,
and last factor.  The parameterization `n + 2` makes the two terminal slots
definitionally visible. -/
theorem generalRidgeFactorList_split_last_two {n : ℕ}
    (w : Fin (n + 3) → ℝ) (η : Fin (n + 2) → ℝ) :
    generalRidgeFactorList w η =
      generalRidgeFactorPrefix (d := n + 2) (by omega) w η ++
        [generalRidgeKernelFactor w η
            (generalRidgePenultimateIndex (d := n + 2) (by omega)),
          generalRidgeKernelFactor w η
            (generalRidgeLastIndex (d := n + 2) (by omega))] := by
  rw [generalRidgeFactorList]
  rw [listOfFn_split_last_two]
  simp [generalRidgeFactorPrefix, generalRidgePenultimateIndex,
    generalRidgeLastIndex]

/-- Exact last-kernel response at the southern target of the constant
carrier. -/
theorem fullConv_generalRidgeSeparatedLastKernel_target_eq
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ) :
    fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 d =
      generalRidgeBeta w (generalRidgeLastIndex hd) -
        |generalRidgeBeta w (generalRidgeLastIndex hd)| - 1 := by
  have hdpos : 0 < d := by omega
  have hone_lt : 1 < d := by omega
  have hone_le : 1 ≤ d := by omega
  have hd_lt : d < 2 * d := by omega
  have hpred_lt : d - 1 < 2 * d := by omega
  rw [generalRidgeSeparatedLastKernel_eq,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp [generalRidgeKernelFactor, zeroExtend, constantImage,
    hdpos, hone_lt, hone_le, hd_lt, hpred_lt,
    generalRidgeSeparatedAllocation_last]
  have hscale := generalRidgeCarrierScale_mul_succ hd w
  nlinarith

/-- The separated last factor sends the constant carrier target to a value
at most `-1`. -/
theorem fullConv_generalRidgeSeparatedLastKernel_target_le
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ) :
    fullConv (generalRidgeSeparatedLastKernel hd w)
        (constantImage d (2 * d) 1) 1 d ≤ -1 := by
  rw [fullConv_generalRidgeSeparatedLastKernel_target_eq hd w]
  have hβ := le_abs_self (generalRidgeBeta w (generalRidgeLastIndex hd))
  linarith

/-- Every output position on the northern row of the last-kernel carrier
response is at least one. -/
theorem fullConv_generalRidgeSeparatedLastKernel_north_ge_one
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ)
    (q : Fin (2 * d + 1)) :
    1 ≤ fullConv (generalRidgeSeparatedLastKernel hd w)
      (constantImage d (2 * d) 1) 0 q := by
  have hdpos : 0 < d := by omega
  have hqle : (q : ℕ) ≤ 2 * d := by omega
  rw [generalRidgeSeparatedLastKernel_eq,
    BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat]
  simp only [generalRidgeKernelFactor, zeroExtend, constantImage,
    generalRidgeLastIndex_val]
  by_cases hq0 : (q : ℕ) = 0
  · simp [hq0, hdpos]
    omega
  · by_cases hqend : (q : ℕ) = 2 * d
    · have htwo : 1 ≤ 2 * d := by omega
      simp [hqend, hdpos, htwo]
    · have hqpos : 1 ≤ (q : ℕ) := by omega
      have hqlt : (q : ℕ) < 2 * d := by omega
      have hpred_lt : (q : ℕ) - 1 < 2 * d := by omega
      simp [hdpos, hqpos, hqlt, hpred_lt]

/-- The northern carrier response exceeds the southern target response by at
least two. -/
theorem generalRidgeSeparatedLastKernel_gap
    {d : ℕ} (hd : 2 ≤ d) (w : Fin (d + 1) → ℝ)
    (q : Fin (2 * d + 1)) :
    2 ≤
      fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 0 q -
        fullConv (generalRidgeSeparatedLastKernel hd w)
          (constantImage d (2 * d) 1) 1 d := by
  have hnorth :=
    fullConv_generalRidgeSeparatedLastKernel_north_ge_one hd w q
  have htarget := fullConv_generalRidgeSeparatedLastKernel_target_le hd w
  linarith

end OneChannelCNNUniversality
