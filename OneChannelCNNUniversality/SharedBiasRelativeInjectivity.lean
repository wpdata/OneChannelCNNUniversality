import OneChannelCNNUniversality.SharedBiasSupport

/-!
# Protected Pascal injectivity

The expanded fringe is not needed to recover the input of a causal Pascal
transport.  Agreement on any northwest rectangle of the output can be
inverted back through horizontal and vertical accumulation on that same
rectangle.  In particular, restriction to the original input rectangle is
already injective.
-/

namespace OneChannelCNNUniversality

theorem fullConv_horizontalAccumulationKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (p q : ℕ) :
    fullConv horizontalAccumulationKernel x p q =
      zeroExtend x p q +
        if 1 ≤ q then zeroExtend x p (q - 1) else 0 := by
  unfold horizontalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp

theorem fullConv_verticalAccumulationKernel_nat
    {rows cols : ℕ} (x : Image rows cols) (p q : ℕ) :
    fullConv verticalAccumulationKernel x p q =
      zeroExtend x p q +
        if 1 ≤ p then zeroExtend x (p - 1) q else 0 := by
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp

/-- Horizontal accumulation can be inverted on any fixed northwest
rectangle, without observing the expansion fringe outside that rectangle. -/
theorem northwestAgree_of_horizontalAccumulation
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (fullConvImage horizontalAccumulationKernel x)
      (fullConvImage horizontalAccumulationKernel y) r s) :
    NorthwestAgree x y r s := by
  intro i hi j hj
  induction j with
  | zero =>
      have hentry := hout i hi 0 (Nat.zero_le s)
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        fullConv_horizontalAccumulationKernel_nat,
        fullConv_horizontalAccumulationKernel_nat] at hentry
      simpa using hentry
  | succ j ih =>
      have hjprev : j ≤ s := le_trans (Nat.le_succ j) hj
      have hentry := hout i hi (j + 1) hj
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        fullConv_horizontalAccumulationKernel_nat,
        fullConv_horizontalAccumulationKernel_nat] at hentry
      have hjpos : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      simp only [if_pos hjpos, Nat.add_sub_cancel] at hentry
      linarith [ih hjprev]

/-- Vertical accumulation has the analogous northwest-rectangle inverse. -/
theorem northwestAgree_of_verticalAccumulation
    {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (fullConvImage verticalAccumulationKernel x)
      (fullConvImage verticalAccumulationKernel y) r s) :
    NorthwestAgree x y r s := by
  intro i hi j hj
  induction i with
  | zero =>
      have hentry := hout 0 (Nat.zero_le r) j hj
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        fullConv_verticalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat] at hentry
      simpa using hentry
  | succ i ih =>
      have hiprev : i ≤ r := le_trans (Nat.le_succ i) hi
      have hentry := hout (i + 1) hi j hj
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        fullConv_verticalAccumulationKernel_nat,
        fullConv_verticalAccumulationKernel_nat] at hentry
      have hipos : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
      simp only [if_pos hipos, Nat.add_sub_cancel] at hentry
      linarith [ih hiprev]

/-- Any number of horizontal Pascal layers can be inverted on the observed
northwest rectangle. -/
theorem northwestAgree_of_horizontalAccumulationIterations
    {rows cols : ℕ} (steps : ℕ) {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (iterateFullConv horizontalAccumulationKernel steps x)
      (iterateFullConv horizontalAccumulationKernel steps y) r s) :
    NorthwestAgree x y r s := by
  induction steps generalizing rows cols with
  | zero => exact hout
  | succ steps ih =>
      exact northwestAgree_of_horizontalAccumulation (ih hout)

/-- Any number of vertical Pascal layers can be inverted on the observed
northwest rectangle. -/
theorem northwestAgree_of_verticalAccumulationIterations
    {rows cols : ℕ} (steps : ℕ) {x y : Image rows cols} {r s : ℕ}
    (hout : NorthwestAgree
      (iterateFullConv verticalAccumulationKernel steps x)
      (iterateFullConv verticalAccumulationKernel steps y) r s) :
    NorthwestAgree x y r s := by
  induction steps generalizing rows cols with
  | zero => exact hout
  | succ steps ih =>
      exact northwestAgree_of_verticalAccumulation (ih hout)

/-- The protected original-rectangle restriction of the linearized Pascal
signal is injective; no expansion-fringe coordinate is required. -/
theorem protectedLinearizedPascalSignal_injective {rows cols : ℕ}
    (rowSteps extraColSteps : ℕ) :
    Function.Injective
      (protectedLinearizedPascalSignal
        (rows := rows) (cols := cols) rowSteps extraColSteps) := by
  intro x y hxy
  funext i j
  have hout : NorthwestAgree
      (linearizedPascalSignal rowSteps extraColSteps x)
      (linearizedPascalSignal rowSteps extraColSteps y) i j := by
    intro p hp q hq
    have hpr : p < rows := lt_of_le_of_lt hp i.isLt
    have hqc : q < cols := lt_of_le_of_lt hq j.isLt
    have hentry := congrFun (congrFun hxy ⟨p, hpr⟩) ⟨q, hqc⟩
    simpa [protectedLinearizedPascalSignal, zeroExtend, hpr, hqc]
      using hentry
  have hvertical := northwestAgree_of_verticalAccumulationIterations
    rowSteps hout
  have hhorizontal := northwestAgree_of_horizontalAccumulationIterations
    extraColSteps hvertical
  have hfirst := northwestAgree_of_horizontalAccumulation hhorizontal
  simpa using hfirst i le_rfl j le_rfl

/-- Repeated full convolution cannot move a southeast-supported difference
outside its original southeast quadrant. -/
theorem agreeOutsideSoutheast_iterateFullConv
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps : ℕ) {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (iterateFullConv w steps x)
      (iterateFullConv w steps y) r s := by
  induction steps generalizing rows cols with
  | zero => exact hxy
  | succ steps ih =>
      exact ih (agreeOutsideSoutheast_fullConvImage w hxy)

/-- The complete linearized Pascal transport preserves the southeast support
of every input difference. -/
theorem agreeOutsideSoutheast_linearizedPascalSignal
    {rows cols : ℕ} (rowSteps extraColSteps : ℕ)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast
      (linearizedPascalSignal rowSteps extraColSteps x)
      (linearizedPascalSignal rowSteps extraColSteps y) r s := by
  apply agreeOutsideSoutheast_iterateFullConv verticalAccumulationKernel
  apply agreeOutsideSoutheast_iterateFullConv horizontalAccumulationKernel
  exact agreeOutsideSoutheast_fullConvImage
    horizontalAccumulationKernel hxy

/-- A bundled protected-selection block is injective relative to variations
supported in the target's southeast quadrant with the root removed.  Thus
the final ReLU selection does not destroy any information carried by such a
variation. -/
theorem BundledPascalGridSelectionSpec.injective_on_rootPuncturedSoutheast
    {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {θ : ℝ} {rowSteps extraColSteps : ℕ}
    {targetRow : Fin rows} {targetCol : Fin cols} {c b : ℝ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 (grownSize 2 (rows + 2 - 1) extraColSteps) rowSteps + 2 - 1)
      (grownSize 2 (grownSize 2 (cols + 2 - 1) extraColSteps) rowSteps + 2 - 1)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      targetRow targetCol c b net) {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hvar : AgreeOutsideStrictSoutheast
      (V x) (V y) targetRow targetCol)
    (heval : net.eval (V x + constantImage rows cols c) =
      net.eval (V y + constantImage rows cols c)) :
    V x = V y := by
  apply protectedLinearizedPascalSignal_injective rowSteps extraColSteps
  funext i j
  by_cases hp : southeastProtected targetRow targetCol i j
  · by_cases hroot : (i, j) = (targetRow, targetCol)
    · have hi : i = targetRow := congrArg Prod.fst hroot
      have hj : j = targetCol := congrArg Prod.snd hroot
      subst i
      subst j
      exact protectedLinearizedPascalSignal_eq_of_northwestAgree
        rowSteps extraColSteps targetRow targetCol hvar.northwestAgree
    · have hxspec := hspec.2 x hx i j hp
      have hyspec := hspec.2 y hy i j hp
      have hevalij := congrFun (congrFun heval
        (⟨i, by
          have := original_lt_pascalStage rows extraColSteps rowSteps i
          omega⟩))
        (⟨j, by
          have := original_lt_pascalStage cols extraColSteps rowSteps j
          omega⟩)
      rw [hxspec, hyspec, if_neg hroot, if_neg hroot] at hevalij
      linarith
  · have hnot : ¬ ((targetRow : ℕ) ≤ (i : ℕ) ∧
        (targetCol : ℕ) ≤ (j : ℕ)) := by
      intro hse
      apply hp
      exact ⟨by exact_mod_cast hse.1, by exact_mod_cast hse.2⟩
    exact agreeOutsideSoutheast_linearizedPascalSignal
      rowSteps extraColSteps hvar.1 i j hnot

end OneChannelCNNUniversality
