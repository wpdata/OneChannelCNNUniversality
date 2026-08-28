import OneChannelCNNUniversality.SharedBiasGridScan

/-!
# Genuine shared-bias layers for Pascal-grid selection

The Pascal carrier theorem is first exposed through an actual expansive
`2 × 2` convolution/ReLU layer.  The kernel has its only nonzero tap at the
northwest corner, so it acts pointwise on the protected original rectangle
while retaining the fixed expansive kernel shape.
-/

namespace OneChannelCNNUniversality

/-- Any finite sequence of formal convolutions can be realized exactly on a
compact signal family by a genuine network whose every layer uses one scalar
bias.  The biases keep all sites in ReLU's linear branch, while a fixed
carrier records their accumulated contribution. -/
theorem exists_shared_bias_full_iterations
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps : ℕ) (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : SharedBiasNetworkTo kRows kCols rows cols
        (grownSize kRows rows steps) (grownSize kCols cols steps))
      (carrier : Image (grownSize kRows rows steps)
        (grownSize kCols cols steps)),
      ∀ x ∈ K,
        net.eval (F x) = iterateFullConv w steps (V x) + carrier := by
  induction steps generalizing rows cols F V known with
  | zero =>
      exact ⟨SharedBiasNetworkTo.nil rows cols kRows kCols, known, hdecomp⟩
  | succ steps ih =>
      obtain ⟨b, nextCarrier, _hb, hfirst⟩ :=
        exists_shared_bias_carrier_layer hK F V known hdecomp hV w
      let nextF : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ sharedLayerEval w b (F x)
      let nextV : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ fullConvImage w (V x)
      have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + nextCarrier := by
        intro x hx
        simpa [nextF, nextV] using hfirst x hx
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV w p q
      obtain ⟨tail, finalCarrier, htail⟩ :=
        ih nextF nextV nextCarrier hnextDecomp hnextV
      refine ⟨SharedBiasNetworkTo.cons w b tail, finalCarrier, ?_⟩
      intro x hx
      rw [SharedBiasNetworkTo.eval_cons]
      exact htail x hx

/-- Horizontal Pascal accumulation followed by vertical Pascal accumulation
is realized by one fixed-`2 × 2`-shape shared-bias network.  Its variable part
is exactly the formal two-dimensional Pascal transform; all scalar-bias and
known-input contributions are collected in one fixed carrier. -/
theorem exists_shared_bias_pascal_grid_layers
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (rowSteps colSteps : ℕ)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
        (grownSize 2 (grownSize 2 cols colSteps) rowSteps))
      (carrier : Image
        (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
        (grownSize 2 (grownSize 2 cols colSteps) rowSteps)),
      ∀ x ∈ K,
        net.eval (F x) =
          iterateFullConv verticalAccumulationKernel rowSteps
              (iterateFullConv horizontalAccumulationKernel colSteps (V x)) +
            carrier := by
  induction colSteps generalizing rows cols F V known with
  | zero =>
      change ∃ (net : SharedBiasNetworkTo 2 2 rows cols
          (grownSize 2 rows rowSteps) (grownSize 2 cols rowSteps))
        (carrier : Image (grownSize 2 rows rowSteps)
          (grownSize 2 cols rowSteps)),
        ∀ x ∈ K,
          net.eval (F x) =
            iterateFullConv verticalAccumulationKernel rowSteps (V x) + carrier
      exact exists_shared_bias_full_iterations hK verticalAccumulationKernel
        rowSteps F V known hdecomp hV
  | succ colSteps ih =>
      obtain ⟨b, nextCarrier, _hb, hfirst⟩ :=
        exists_shared_bias_carrier_layer hK F V known hdecomp hV
          horizontalAccumulationKernel
      let nextF : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ sharedLayerEval horizontalAccumulationKernel b (F x)
      let nextV : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ fullConvImage horizontalAccumulationKernel (V x)
      have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + nextCarrier := by
        intro x hx
        simpa [nextF, nextV] using hfirst x hx
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        exact continuousFeatureOn_fullConv hV horizontalAccumulationKernel p q
      obtain ⟨tail, finalCarrier, htail⟩ :=
        ih nextF nextV nextCarrier hnextDecomp hnextV
      refine ⟨SharedBiasNetworkTo.cons horizontalAccumulationKernel b tail,
        finalCarrier, ?_⟩
      intro x hx
      rw [SharedBiasNetworkTo.eval_cons]
      exact htail x hx

/-- Pointwise nonnegativity of every kernel coefficient. -/
def KernelNonnegative {kRows kCols : ℕ} (w : Kernel kRows kCols) : Prop :=
  ∀ i j, 0 ≤ w i j

/-- Pointwise nonnegativity of an image. -/
def ImageNonnegative {rows cols : ℕ} (x : Image rows cols) : Prop :=
  ∀ i j, 0 ≤ x i j

theorem zeroExtend_nonnegative {rows cols : ℕ} {x : Image rows cols}
    (hx : ImageNonnegative x) (i j : ℕ) : 0 ≤ zeroExtend x i j := by
  by_cases hi : i < rows
  · by_cases hj : j < cols
    · simpa [zeroExtend, hi, hj] using hx ⟨i, hi⟩ ⟨j, hj⟩
    · simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

theorem fullConv_nonnegative {kRows kCols rows cols : ℕ}
    {w : Kernel kRows kCols} {x : Image rows cols}
    (hw : KernelNonnegative w) (hx : ImageNonnegative x) (p q : ℕ) :
    0 ≤ fullConv w x p q := by
  unfold fullConv
  apply Finset.sum_nonneg
  intro a _ha
  apply Finset.sum_nonneg
  intro b _hb
  split_ifs
  · exact mul_nonneg (hw a b) (zeroExtend_nonnegative hx _ _)
  · norm_num

theorem fullConvImage_nonnegative {kRows kCols rows cols : ℕ}
    {w : Kernel kRows kCols} {x : Image rows cols}
    (hw : KernelNonnegative w) (hx : ImageNonnegative x) :
    ImageNonnegative (fullConvImage w x) := by
  intro p q
  exact fullConv_nonnegative hw hx p q

theorem horizontalAccumulationKernel_nonnegative :
    KernelNonnegative horizontalAccumulationKernel := by
  intro i j
  unfold horizontalAccumulationKernel twoTapKernel deltaKernel
  split_ifs <;> norm_num

theorem verticalAccumulationKernel_nonnegative :
    KernelNonnegative verticalAccumulationKernel := by
  intro i j
  unfold verticalAccumulationKernel twoTapKernel deltaKernel
  split_ifs <;> norm_num

/-- On a nonnegative input, a nonnegative kernel with zero shared bias is
exactly linear; ReLU changes no coordinate. -/
theorem sharedLayerEval_zero_of_nonnegative
    {kRows kCols rows cols : ℕ} {w : Kernel kRows kCols}
    {x : Image rows cols} (hw : KernelNonnegative w)
    (hx : ImageNonnegative x) :
    sharedLayerEval w 0 x = fullConvImage w x := by
  funext p q
  change relu (fullConv w x p q + 0) = fullConv w x p q
  rw [add_zero, relu_of_nonneg (fullConv_nonnegative hw hx p q)]

/-- A concrete fixed-kernel network of `steps` zero-bias layers. -/
def zeroBiasIterations {kRows kCols : ℕ} (w : Kernel kRows kCols) :
    (steps : ℕ) → {rows cols : ℕ} →
      SharedBiasNetworkTo kRows kCols rows cols
        (grownSize kRows rows steps) (grownSize kCols cols steps)
  | 0, _, _ => SharedBiasNetworkTo.nil _ _ kRows kCols
  | steps + 1, _, _ =>
      SharedBiasNetworkTo.cons w 0 (zeroBiasIterations w steps)

theorem zeroBiasIterations_depth
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (steps : ℕ) :
    (zeroBiasIterations (rows := rows) (cols := cols) w steps).net.depth =
      steps := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      change
        (zeroBiasIterations
          (rows := rows + kRows - 1) (cols := cols + kCols - 1)
          w steps).net.depth + 1 = steps + 1
      rw [ih]

theorem zeroBiasIterations_eval_of_nonnegative
    {kRows kCols rows cols : ℕ} {w : Kernel kRows kCols}
    (hw : KernelNonnegative w) (steps : ℕ) (x : Image rows cols)
    (hx : ImageNonnegative x) :
    (zeroBiasIterations w steps).eval x = iterateFullConv w steps x := by
  induction steps generalizing rows cols with
  | zero =>
      change (SharedBiasNetworkTo.nil rows cols kRows kCols).eval x = x
      exact SharedBiasNetworkTo.eval_nil x
  | succ steps ih =>
      rw [zeroBiasIterations, SharedBiasNetworkTo.eval_cons, iterateFullConv]
      rw [sharedLayerEval_zero_of_nonnegative hw hx]
      exact ih (fullConvImage w x) (fullConvImage_nonnegative hw hx)

/-- A concrete `2 × 2` network: horizontal zero-bias Pascal layers followed
by vertical zero-bias Pascal layers. -/
def zeroBiasPascalGridNetwork (rowSteps : ℕ) :
    (colSteps : ℕ) → {rows cols : ℕ} →
      SharedBiasNetworkTo 2 2 rows cols
        (grownSize 2 (grownSize 2 rows colSteps) rowSteps)
        (grownSize 2 (grownSize 2 cols colSteps) rowSteps)
  | 0, _, _ => zeroBiasIterations verticalAccumulationKernel rowSteps
  | colSteps + 1, _, _ =>
      SharedBiasNetworkTo.cons horizontalAccumulationKernel 0
        (zeroBiasPascalGridNetwork rowSteps colSteps)

theorem zeroBiasPascalGridNetwork_depth
    {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    (zeroBiasPascalGridNetwork (rows := rows) (cols := cols)
      rowSteps colSteps).net.depth = rowSteps + colSteps := by
  induction colSteps generalizing rows cols with
  | zero =>
      exact zeroBiasIterations_depth verticalAccumulationKernel rowSteps
  | succ colSteps ih =>
      change
        (zeroBiasPascalGridNetwork
          (rows := rows + 2 - 1) (cols := cols + 2 - 1)
          rowSteps colSteps).net.depth + 1 = rowSteps + (colSteps + 1)
      rw [ih]
      omega

theorem zeroBiasPascalGridNetwork_eval_of_nonnegative
    {rows cols : ℕ} (rowSteps colSteps : ℕ) (x : Image rows cols)
    (hx : ImageNonnegative x) :
    (zeroBiasPascalGridNetwork rowSteps colSteps).eval x =
      iterateFullConv verticalAccumulationKernel rowSteps
        (iterateFullConv horizontalAccumulationKernel colSteps x) := by
  induction colSteps generalizing rows cols with
  | zero =>
      change (zeroBiasIterations verticalAccumulationKernel rowSteps).eval x =
        iterateFullConv verticalAccumulationKernel rowSteps x
      exact zeroBiasIterations_eval_of_nonnegative
        verticalAccumulationKernel_nonnegative rowSteps x hx
  | succ colSteps ih =>
      rw [zeroBiasPascalGridNetwork, SharedBiasNetworkTo.eval_cons,
        iterateFullConv]
      rw [sharedLayerEval_zero_of_nonnegative
        horizontalAccumulationKernel_nonnegative hx]
      exact ih (fullConvImage horizontalAccumulationKernel x)
        (fullConvImage_nonnegative horizontalAccumulationKernel_nonnegative hx)

/-- A `2 × 2` delta kernel that is the identity on every pre-existing
coordinate and creates only expansion fringe outside it. -/
def expansiveIdentityKernel : Kernel 2 2 :=
  deltaKernel (0 : Fin 2) (0 : Fin 2) 1

theorem fullConv_expansiveIdentityKernel_original {rows cols : ℕ}
    (x : Image rows cols) (i : Fin rows) (j : Fin cols) :
    fullConv expansiveIdentityKernel x i j = x i j := by
  unfold expansiveIdentityKernel
  rw [fullConv_deltaKernel]
  simp [zeroExtend, i.isLt, j.isLt]

/-- Genuine final-layer form of southeast Pascal selection.  The same
broadcast scalar bias is used at every site of an expansive `2 × 2` layer;
the theorem states its exact behavior on the protected original rectangle. -/
theorem exists_sharedLayer_southeast_pascal_selection
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (rowSteps colSteps : ℕ) (targetRow : Fin rows) (targetCol : Fin cols)
    (θ : ℝ) (hrowSteps : rows - 1 ≤ rowSteps)
    (hcolSteps : cols - 1 ≤ colSteps) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i j,
      southeastProtected targetRow targetCol i j →
      sharedLayerEval expansiveIdentityKernel
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol)
          (signal x +
            protectedPascalGridAddress rowSteps colSteps rows cols c)
          (⟨i, by omega⟩ : Fin (rows + 2 - 1))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1)) =
        if (i, j) = (targetRow, targetCol) then relu (signal x i j + θ)
        else signal x i j +
          protectedPascalGridAddress rowSteps colSteps rows cols c i j +
          (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
            targetRow targetCol) := by
  obtain ⟨c, hc, hselected⟩ :=
    exists_southeast_selected_relu hK signal hSignal rowSteps colSteps
      targetRow targetCol θ hrowSteps hcolSteps
  refine ⟨c, hc, ?_⟩
  intro x hx i j hp
  change relu
    (fullConv expansiveIdentityKernel
        (signal x +
          protectedPascalGridAddress rowSteps colSteps rows cols c) i j +
      (θ - protectedPascalGridAddress rowSteps colSteps rows cols c
        targetRow targetCol)) = _
  rw [fullConv_expansiveIdentityKernel_original]
  exact hselected x hx i j hp

end OneChannelCNNUniversality
