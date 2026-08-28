import OneChannelCNNUniversality.SharedBiasGridNetwork

open OneChannelCNNUniversality

/-! Regression interface for a genuine expansive shared-bias final gate. -/

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps : ℕ) (x y : Image rows cols) :
    iterateFullConv w steps (x + y) =
      iterateFullConv w steps x + iterateFullConv w steps y := by
  exact iterateFullConv_add w steps x y

example {rows cols : ℕ} (rowSteps extraColSteps : ℕ) (c b : ℝ)
    (i : Fin rows) (j : Fin cols) :
    protectedLinearizedPascalCarrier rowSteps extraColSteps rows cols c b i j =
      c * pascalPrefix rowSteps i * pascalPrefix (extraColSteps + 1) j +
        b * pascalPrefix rowSteps i * pascalPrefix extraColSteps j := by
  exact protectedLinearizedPascalCarrier_eq
    rowSteps extraColSteps c b i j

/-- Asymmetric concrete regression: the seed has two horizontal Pascal
steps, while the first shared bias has one. -/
example : protectedLinearizedPascalCarrier 2 1 2 3 2 3
    (⟨1, by omega⟩ : Fin 2) (⟨2, by omega⟩ : Fin 3) = 42 := by
  rw [protectedLinearizedPascalCarrier_eq]
  norm_num [pascalPrefix, Finset.sum_range_succ, Nat.choose]

example {rows cols : ℕ} (rowSteps extraColSteps : ℕ) (c b : ℝ)
    (targetRow : Fin rows) (targetCol : Fin cols)
    (hrowSteps : rows - 1 ≤ rowSteps)
    (hcolSteps : cols - 1 ≤ extraColSteps + 1)
    (hc : 0 ≤ c) (hb : 0 ≤ b) :
    ∀ i j, southeastProtected targetRow targetCol i j →
      (i, j) ≠ (targetRow, targetCol) →
      c ≤ protectedLinearizedPascalCarrier
          rowSteps extraColSteps rows cols c b i j -
        protectedLinearizedPascalCarrier
          rowSteps extraColSteps rows cols c b targetRow targetCol := by
  exact protectedLinearizedPascalCarrier_gap_on rowSteps extraColSteps c b
    targetRow targetCol hrowSteps hcolSteps hc hb

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (b : ℝ)
    (x : Image rows cols) :
    (SharedBiasNetworkTo.single w b).eval x = sharedLayerEval w b x := by
  exact SharedBiasNetworkTo.eval_single w b x

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (steps : ℕ)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : SharedBiasNetworkTo kRows kCols rows cols
        (grownSize kRows rows steps) (grownSize kCols cols steps))
      (carrier : Image (grownSize kRows rows steps)
        (grownSize kCols cols steps)),
      ∀ x ∈ K,
        net.eval (F x) = iterateFullConv w steps (V x) + carrier := by
  exact exists_shared_bias_full_iterations hK w steps F V known hdecomp hV

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (rowSteps colSteps : ℕ) (F V : X → Image rows cols)
    (known : Image rows cols) (hdecomp : ∀ x ∈ K, F x = V x + known)
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
  exact exists_shared_bias_pascal_grid_layers hK rowSteps colSteps
    F V known hdecomp hV

example {rows cols : ℕ} (rowSteps colSteps : ℕ) (x : Image rows cols)
    (hx : ∀ i j, 0 ≤ x i j) :
    (zeroBiasPascalGridNetwork rowSteps colSteps).eval x =
      iterateFullConv verticalAccumulationKernel rowSteps
        (iterateFullConv horizontalAccumulationKernel colSteps x) := by
  exact zeroBiasPascalGridNetwork_eval_of_nonnegative
    rowSteps colSteps x hx

example {rows cols : ℕ} (rowSteps colSteps : ℕ) :
    (zeroBiasPascalGridNetwork (rows := rows) (cols := cols)
      rowSteps colSteps).net.depth = rowSteps + colSteps := by
  exact zeroBiasPascalGridNetwork_depth rowSteps colSteps

/-- Zero steps reduce definitionally to the identity network. -/
example {rows cols : ℕ} (x : Image rows cols) :
    (zeroBiasPascalGridNetwork 0 0).eval x = x := by
  exact SharedBiasNetworkTo.eval_nil x

/-- The exact evaluation theorem also covers an empty row dimension. -/
example (x : Image 0 3) :
    (zeroBiasPascalGridNetwork 2 4).eval x =
      iterateFullConv verticalAccumulationKernel 2
        (iterateFullConv horizontalAccumulationKernel 4 x) := by
  exact zeroBiasPascalGridNetwork_eval_of_nonnegative 2 4 x
    (fun i _j ↦ Fin.elim0 i)

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (signal : X → Image rows cols) (hSignal : ContinuousFeatureOn K signal)
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
  exact exists_sharedLayer_southeast_pascal_selection hK signal hSignal
    rowSteps colSteps targetRow targetCol θ hrowSteps hcolSteps

example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {rows cols : ℕ}
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V)
    (rowSteps extraColSteps : ℕ)
    (targetRow : Fin rows) (targetCol : Fin cols) (θ : ℝ)
    (hrowSteps : rows - 1 ≤ rowSteps)
    (hcolSteps : cols - 1 ≤ extraColSteps + 1) :
    ∃ c b : ℝ, 0 < c ∧ 0 < b ∧
      PascalGridProtectedSelectionSpec K V θ rowSteps extraColSteps
        targetRow targetCol c b := by
  exact exists_pascal_grid_protected_selection_layers hK V hV
    rowSteps extraColSteps targetRow targetCol θ hrowSteps hcolSteps
