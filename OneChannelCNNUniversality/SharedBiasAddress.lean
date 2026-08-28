import OneChannelCNNUniversality.SharedBiasSelection

/-!
# A non-destructive northwest address from shared-bias layers

Two positive two-tap convolutions turn a positive constant summand into a
spatial address.  On the rectangle occupied by the original image, the
northwest register is the unique minimum.  Both layers use only one shared
scalar bias; no coordinate-dependent bias is assumed.
-/

namespace OneChannelCNNUniversality

/-- Horizontal causal accumulation with taps `1, 1`. -/
def horizontalAccumulationKernel : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) 1

/-- Vertical causal accumulation with taps `1, 1`. -/
def verticalAccumulationKernel : Kernel 2 2 :=
  twoTapKernel (0 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) 1

/-- A `1 × 1` identity kernel, used for the final shared-bias ReLU gate. -/
def pointwiseIdentityKernel : Kernel 1 1 :=
  deltaKernel (0 : Fin 1) (0 : Fin 1) 1

theorem fullConv_pointwiseIdentityKernel {rows cols : ℕ}
    (x : Image rows cols) (p : Fin rows) (q : Fin cols) :
    fullConv pointwiseIdentityKernel x p q = x p q := by
  unfold pointwiseIdentityKernel
  rw [fullConv_deltaKernel]
  simp [zeroExtend, p.isLt, q.isLt]

/-- The input-dependent part after the two address-generation convolutions. -/
def twoLayerAccumulationSignal {rows cols : ℕ} (x : Image rows cols) :
    Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
  fullConvImage verticalAccumulationKernel
    (fullConvImage horizontalAccumulationKernel x)

/-- Fixed carrier after the horizontal accumulation layer. -/
def horizontalAccumulationCarrier (rows cols : ℕ) (c b₁ : ℝ) :
    Image (rows + 2 - 1) (cols + 2 - 1) :=
  fun p q ↦
    fullConv horizontalAccumulationKernel (constantImage rows cols c) p q + b₁

/-- Fixed carrier after horizontal and then vertical accumulation. -/
def northwestAddressCarrier (rows cols : ℕ) (c b₁ b₂ : ℝ) :
    Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
  fun p q ↦
    fullConv verticalAccumulationKernel
      (horizontalAccumulationCarrier rows cols c b₁) p q + b₂

/-- Restriction of the actual expanded carrier to the protected register
rectangle occupied by the original image. -/
def protectedNorthwestAddress (rows cols : ℕ) (c b₁ b₂ : ℝ) :
    Image rows cols :=
  fun i j ↦
    northwestAddressCarrier rows cols c b₁ b₂
      (⟨i, by omega⟩ : Fin ((rows + 2 - 1) + 2 - 1))
      (⟨j, by omega⟩ : Fin ((cols + 2 - 1) + 2 - 1))

/-- The coordinates in the twice-expanded output that correspond to the
original input rectangle.  Expansion-fringe coordinates are deliberately
left unprotected. -/
def originalRectangleProtected (rows cols : ℕ) :
    Fin ((rows + 2 - 1) + 2 - 1) →
      Fin ((cols + 2 - 1) + 2 - 1) → Prop :=
  fun p q ↦ (p : ℕ) < rows ∧ (q : ℕ) < cols

/-- The northwest coordinate in the actual twice-expanded output. -/
def northwestOutputTarget (rows cols : ℕ)
    (_hrows : 0 < rows) (_hcols : 0 < cols) :
    Fin ((rows + 2 - 1) + 2 - 1) ×
      Fin ((cols + 2 - 1) + 2 - 1) :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

theorem horizontalAccumulationCarrier_left {rows cols : ℕ} (c b₁ : ℝ)
    (i : Fin rows) (hcols : 0 < cols) :
    horizontalAccumulationCarrier rows cols c b₁
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨0, by omega⟩ : Fin (cols + 2 - 1)) = c + b₁ := by
  unfold horizontalAccumulationCarrier horizontalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend, constantImage, i.isLt, hcols]

theorem horizontalAccumulationCarrier_interior {rows cols : ℕ} (c b₁ : ℝ)
    (i : Fin rows) (j : Fin cols) (hj : 0 < (j : ℕ)) :
    horizontalAccumulationCarrier rows cols c b₁
        (⟨i, by omega⟩ : Fin (rows + 2 - 1))
        (⟨j, by omega⟩ : Fin (cols + 2 - 1)) = 2 * c + b₁ := by
  unfold horizontalAccumulationCarrier horizontalAccumulationKernel
  rw [fullConv_twoTapKernel]
  have hjpred : (j : ℕ) - 1 < cols := by omega
  have hjone : 1 ≤ (j : ℕ) := by omega
  simp [zeroExtend, constantImage, i.isLt, j.isLt, hjone, hjpred]
  ring

theorem protectedNorthwestAddress_northwest {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols) :
    protectedNorthwestAddress rows cols c b₁ b₂
        ⟨0, hrows⟩ ⟨0, hcols⟩ = c + b₁ + b₂ := by
  unfold protectedNorthwestAddress northwestAddressCarrier
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend]
  simpa using
    horizontalAccumulationCarrier_left c b₁ (⟨0, hrows⟩ : Fin rows) hcols

theorem protectedNorthwestAddress_top {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (j : Fin cols) (hj : 0 < (j : ℕ)) :
    protectedNorthwestAddress rows cols c b₁ b₂
        ⟨0, hrows⟩ j = 2 * c + b₁ + b₂ := by
  unfold protectedNorthwestAddress northwestAddressCarrier
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend]
  simpa using horizontalAccumulationCarrier_interior c b₁
    (⟨0, hrows⟩ : Fin rows) j hj

theorem protectedNorthwestAddress_left {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (i : Fin rows) (hi : 0 < (i : ℕ)) (hcols : 0 < cols) :
    protectedNorthwestAddress rows cols c b₁ b₂
        i ⟨0, hcols⟩ = 2 * c + 2 * b₁ + b₂ := by
  unfold protectedNorthwestAddress northwestAddressCarrier
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  have hipred : (i : ℕ) - 1 < rows := by omega
  have hione : 1 ≤ (i : ℕ) := by omega
  have hibound : (i : ℕ) ≤ rows + 1 := by omega
  simp [horizontalAccumulationCarrier, horizontalAccumulationKernel,
    fullConv_twoTapKernel, zeroExtend, constantImage, hione, hipred,
    i.isLt, hcols]
  rw [if_pos hibound]
  ring

theorem protectedNorthwestAddress_interior {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (i : Fin rows) (j : Fin cols)
    (hi : 0 < (i : ℕ)) (hj : 0 < (j : ℕ)) :
    protectedNorthwestAddress rows cols c b₁ b₂ i j =
      4 * c + 2 * b₁ + b₂ := by
  unfold protectedNorthwestAddress northwestAddressCarrier
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  have hipred : (i : ℕ) - 1 < rows := by omega
  have hione : 1 ≤ (i : ℕ) := by omega
  have hjpred : (j : ℕ) - 1 < cols := by omega
  have hjone : 1 ≤ (j : ℕ) := by omega
  have hibound : (i : ℕ) ≤ rows + 1 := by omega
  simp [horizontalAccumulationCarrier, horizontalAccumulationKernel,
    fullConv_twoTapKernel, zeroExtend, constantImage, hione, hipred,
    hjone, hjpred, i.isLt, j.isLt]
  rw [if_pos hibound]
  ring

/-- Quantitative address gap with the seed amplitude itself as margin. -/
theorem protectedNorthwestAddress_gap {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 0 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ i j, (i, j) ≠ (⟨0, hrows⟩, ⟨0, hcols⟩) →
      c ≤ protectedNorthwestAddress rows cols c b₁ b₂ i j -
        protectedNorthwestAddress rows cols c b₁ b₂
          ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  intro i j hne
  rw [protectedNorthwestAddress_northwest c b₁ b₂ hrows hcols]
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, hrows⟩ := Fin.ext hi
    subst i
    have hj : 0 < (j : ℕ) := by
      by_contra hnot
      have hjzero : j = ⟨0, hcols⟩ := Fin.ext (by omega)
      exact hne (by simp [hjzero])
    rw [protectedNorthwestAddress_top c b₁ b₂ hrows j hj]
    linarith
  · have hiPos : 0 < (i : ℕ) := by omega
    by_cases hj : (j : ℕ) = 0
    · have hj' : j = ⟨0, hcols⟩ := Fin.ext hj
      subst j
      rw [protectedNorthwestAddress_left c b₁ b₂ i hiPos hcols]
      linarith
    · have hjPos : 0 < (j : ℕ) := by omega
      rw [protectedNorthwestAddress_interior c b₁ b₂ i j hiPos hjPos]
      linarith

/-- The same gap theorem expressed directly on the actual expanded output,
rather than on the proof-level restriction. -/
theorem northwestAddressCarrier_gap_on {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 0 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ p q, originalRectangleProtected rows cols p q →
      (p, q) ≠ northwestOutputTarget rows cols hrows hcols →
      c ≤ northwestAddressCarrier rows cols c b₁ b₂ p q -
        northwestAddressCarrier rows cols c b₁ b₂
          (northwestOutputTarget rows cols hrows hcols).1
          (northwestOutputTarget rows cols hrows hcols).2 := by
  intro p q hpq hne
  let i : Fin rows := ⟨p, hpq.1⟩
  let j : Fin cols := ⟨q, hpq.2⟩
  have hne' : (i, j) ≠ (⟨0, hrows⟩, ⟨0, hcols⟩) := by
    intro heq
    apply hne
    apply Prod.ext
    · apply Fin.ext
      change (p : ℕ) = 0
      have hi0 := congrArg (fun z : Fin rows × Fin cols ↦ (z.1 : ℕ)) heq
      simpa [i] using hi0
    · apply Fin.ext
      change (q : ℕ) = 0
      have hj0 := congrArg (fun z : Fin rows × Fin cols ↦ (z.2 : ℕ)) heq
      simpa [j] using hj0
  have hgap :=
    protectedNorthwestAddress_gap c b₁ b₂ hrows hcols hc hb₁ i j hne'
  simpa [protectedNorthwestAddress, northwestOutputTarget, i, j] using hgap

/-- If the constant seed is at least one and the first linearizing bias is
nonnegative, the northwest protected register is the unique minimum with a
unit quantitative gap.  The second shared bias cancels from every difference. -/
theorem protectedNorthwestAddress_unit_gap {rows cols : ℕ} (c b₁ b₂ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols)
    (hc : 1 ≤ c) (hb₁ : 0 ≤ b₁) :
    ∀ i j, (i, j) ≠ (⟨0, hrows⟩, ⟨0, hcols⟩) →
      1 ≤ protectedNorthwestAddress rows cols c b₁ b₂ i j -
        protectedNorthwestAddress rows cols c b₁ b₂
          ⟨0, hrows⟩ ⟨0, hcols⟩ := by
  intro i j hne
  have hc0 : 0 ≤ c := by linarith
  have hgap :=
    protectedNorthwestAddress_gap c b₁ b₂ hrows hcols hc0 hb₁ i j hne
  exact hc.trans hgap

private theorem horizontalAccumulationTransform_zero
    {rows n : ℕ} (x : Image rows (n + 1)) (i : Fin rows) :
    fullConv horizontalAccumulationKernel x i 0 = x i 0 := by
  unfold horizontalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend, i.isLt]

private theorem horizontalAccumulationTransform_succ
    {rows n : ℕ} (x : Image rows (n + 1)) (i : Fin rows) (j : Fin n) :
    fullConv horizontalAccumulationKernel x i ((j : ℕ) + 1) =
      x i j.succ + x i j.castSucc := by
  unfold horizontalAccumulationKernel
  rw [fullConv_twoTapKernel]
  have hsucc : (j : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (j : ℕ) + 1 := by omega
  simp [zeroExtend, i.isLt, hsucc, hone]
  congr 1

/-- Horizontal positive accumulation is injective: the first column is
unchanged and every later input is recovered from one output and its already
recovered predecessor. -/
theorem horizontalAccumulationTransform_injective {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage horizontalAccumulationKernel x) := by
  intro x y hxy
  by_cases hcols : cols = 0
  · subst cols
    funext i j
    exact Fin.elim0 j
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcols
    funext i j
    induction j using Fin.induction with
    | zero =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv horizontalAccumulationKernel x i 0 =
          fullConv horizontalAccumulationKernel y i 0 at hentry
        simpa only [horizontalAccumulationTransform_zero] using hentry
    | succ j ih =>
        have hentry := congrFun (congrFun hxy
          (⟨i, by omega⟩ : Fin (rows + 2 - 1)))
          (⟨(j : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1))
        change fullConv horizontalAccumulationKernel x i ((j : ℕ) + 1) =
          fullConv horizontalAccumulationKernel y i ((j : ℕ) + 1) at hentry
        rw [horizontalAccumulationTransform_succ,
          horizontalAccumulationTransform_succ] at hentry
        linarith

private theorem verticalAccumulationTransform_zero
    {n cols : ℕ} (x : Image (n + 1) cols) (j : Fin cols) :
    fullConv verticalAccumulationKernel x 0 j = x 0 j := by
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  simp [zeroExtend, j.isLt]

private theorem verticalAccumulationTransform_succ
    {n cols : ℕ} (x : Image (n + 1) cols) (i : Fin n) (j : Fin cols) :
    fullConv verticalAccumulationKernel x ((i : ℕ) + 1) j =
      x i.succ j + x i.castSucc j := by
  unfold verticalAccumulationKernel
  rw [fullConv_twoTapKernel]
  have hsucc : (i : ℕ) + 1 < n + 1 := by omega
  have hone : 1 ≤ (i : ℕ) + 1 := by omega
  simp [zeroExtend, j.isLt, hsucc, hone]
  congr 1

/-- Vertical positive accumulation is injective by the analogous row-wise
reconstruction. -/
theorem verticalAccumulationTransform_injective {rows cols : ℕ} :
    Function.Injective
      (fun x : Image rows cols ↦ fullConvImage verticalAccumulationKernel x) := by
  intro x y hxy
  by_cases hrows : rows = 0
  · subst rows
    funext i j
    exact Fin.elim0 i
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrows
    funext i j
    induction i using Fin.induction with
    | zero =>
        have hentry := congrFun (congrFun hxy
          (⟨0, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv verticalAccumulationKernel x 0 j =
          fullConv verticalAccumulationKernel y 0 j at hentry
        simpa only [verticalAccumulationTransform_zero] using hentry
    | succ i ih =>
        have hentry := congrFun (congrFun hxy
          (⟨(i : ℕ) + 1, by omega⟩ : Fin ((n + 1) + 2 - 1)))
          (⟨j, by omega⟩ : Fin (cols + 2 - 1))
        change fullConv verticalAccumulationKernel x ((i : ℕ) + 1) j =
          fullConv verticalAccumulationKernel y ((i : ℕ) + 1) j at hentry
        rw [verticalAccumulationTransform_succ,
          verticalAccumulationTransform_succ] at hentry
        linarith

/-- The two-layer variable transform is injective, so the address-generation
stage retains all information in the incoming feature image. -/
theorem twoLayerAccumulationTransform_injective {rows cols : ℕ} :
    Function.Injective (fun x : Image rows cols ↦
      fullConvImage verticalAccumulationKernel
        (fullConvImage horizontalAccumulationKernel x)) := by
  intro x y hxy
  apply horizontalAccumulationTransform_injective
  exact verticalAccumulationTransform_injective hxy

/-- On any compact input family, two genuine one-channel ReLU layers with
shared scalar biases simultaneously preserve an injective transform of the
variable signal and generate the explicit northwest address carrier. -/
theorem exists_northwest_address_layers
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (V : X → Image rows cols)
    (hV : ContinuousFeatureOn K V) (c : ℝ) :
    ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ ∀ x ∈ K,
      sharedLayerEval verticalAccumulationKernel b₂
          (sharedLayerEval horizontalAccumulationKernel b₁
            (V x + constantImage rows cols c)) =
        fullConvImage verticalAccumulationKernel
            (fullConvImage horizontalAccumulationKernel (V x)) +
          northwestAddressCarrier rows cols c b₁ b₂ := by
  let input : X → Image rows cols :=
    fun x ↦ V x + constantImage rows cols c
  have hinput : ContinuousFeatureOn K input := by
    intro i j
    exact (hV i j).add continuousOn_const
  obtain ⟨b₁, hb₁, hfirst⟩ :=
    exists_shared_bias_linearization hK input hinput horizontalAccumulationKernel
  let first : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
    fun x ↦ sharedLayerEval horizontalAccumulationKernel b₁ (input x)
  have hfirstContinuous : ContinuousFeatureOn K first := by
    simpa [first, sharedLayerEval] using continuousFeatureOn_layerEval hinput
      horizontalAccumulationKernel
      (constantImage (rows + 2 - 1) (cols + 2 - 1) b₁)
  obtain ⟨b₂, hb₂, hsecond⟩ :=
    exists_shared_bias_linearization hK first hfirstContinuous
      verticalAccumulationKernel
  refine ⟨b₁, b₂, hb₁, hb₂, ?_⟩
  intro x hx
  funext p q
  rw [hsecond x hx p q]
  change fullConv verticalAccumulationKernel
      (sharedLayerEval horizontalAccumulationKernel b₁
        (V x + constantImage rows cols c)) p q + b₂ = _
  have hfirstImage :
      sharedLayerEval horizontalAccumulationKernel b₁
          (V x + constantImage rows cols c) =
        fullConvImage horizontalAccumulationKernel (V x) +
          horizontalAccumulationCarrier rows cols c b₁ := by
    funext r s
    have hlinear := hfirst x hx r s
    change sharedLayerEval horizontalAccumulationKernel b₁ (input x) r s = _
    rw [hlinear]
    change fullConv horizontalAccumulationKernel
        (V x + constantImage rows cols c) r s + b₁ = _
    rw [fullConv_add]
    simp only [fullConvImage, horizontalAccumulationCarrier, Pi.add_apply]
    ring
  rw [hfirstImage, fullConv_add]
  simp only [fullConvImage, northwestAddressCarrier, Pi.add_apply]
  ring

/-- End-to-end specification for two address-generation layers followed by
a pointwise shared-bias selection layer.  It records both the exact
signal-plus-carrier decomposition and the selected ReLU behavior on the
protected original rectangle. -/
def NorthwestProtectedSelectionSpec {X : Type*} {rows cols : ℕ}
    (K : Set X) (V : X → Image rows cols) (θ : ℝ)
    (hrows : 0 < rows) (hcols : 0 < cols) (c b₁ b₂ : ℝ) : Prop :=
  ∀ x ∈ K,
    let signal := twoLayerAccumulationSignal (V x)
    let carrier := northwestAddressCarrier rows cols c b₁ b₂
    let target := northwestOutputTarget rows cols hrows hcols
    let stageTwo := sharedLayerEval verticalAccumulationKernel b₂
      (sharedLayerEval horizontalAccumulationKernel b₁
        (V x + constantImage rows cols c))
    stageTwo = signal + carrier ∧
      ∀ p q, originalRectangleProtected rows cols p q →
        sharedLayerEval pointwiseIdentityKernel
            (θ - carrier target.1 target.2) stageTwo p q =
          if (p, q) = target then relu (signal p q + θ)
          else signal p q + carrier p q +
            (θ - carrier target.1 target.2)

/-- Compactness chooses a seed amplitude larger than every transformed signal
value needed by the final gate.  Hence three genuine shared-bias,
one-channel ReLU layers realize a northwest-register update on the protected
rectangle, while the first two layers retain the input injectively. -/
theorem exists_northwest_protected_selection_layers
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (hrows : 0 < rows) (hcols : 0 < cols)
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) (θ : ℝ) :
    ∃ c b₁ b₂ : ℝ, 0 < c ∧ 0 < b₁ ∧ 0 < b₂ ∧
      NorthwestProtectedSelectionSpec K V θ hrows hcols c b₁ b₂ := by
  let signal : X →
      Image ((rows + 2 - 1) + 2 - 1) ((cols + 2 - 1) + 2 - 1) :=
    fun x ↦ twoLayerAccumulationSignal (V x)
  have hhorizontal : ContinuousFeatureOn K
      (fun x ↦ fullConvImage horizontalAccumulationKernel (V x)) := by
    intro p q
    change ContinuousOn
      (fun x ↦ fullConv horizontalAccumulationKernel (V x) p q) K
    exact continuousFeatureOn_fullConv hV horizontalAccumulationKernel p q
  have hsignal : ContinuousFeatureOn K signal := by
    intro p q
    change ContinuousOn (fun x ↦ fullConv verticalAccumulationKernel
      (fullConvImage horizontalAccumulationKernel (V x)) p q) K
    exact continuousFeatureOn_fullConv hhorizontal verticalAccumulationKernel p q
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_feature_margin hK signal hsignal θ
  obtain ⟨b₁, b₂, hb₁, hb₂, hlayers⟩ :=
    exists_northwest_address_layers hK V hV c
  refine ⟨c, b₁, b₂, hc, hb₁, hb₂, ?_⟩
  intro x hx
  dsimp only
  constructor
  · simpa [twoLayerAccumulationSignal] using hlayers x hx
  · intro p q hpq
    let carrier := northwestAddressCarrier rows cols c b₁ b₂
    let target := northwestOutputTarget rows cols hrows hcols
    have hgap : ∀ p q, originalRectangleProtected rows cols p q →
        (p, q) ≠ target →
        c ≤ carrier p q - carrier target.1 target.2 := by
      simpa [carrier, target] using
        northwestAddressCarrier_gap_on c b₁ b₂ hrows hcols hc.le hb₁.le
    have hselected := sharedBiasSelectiveActivation_on
      (twoLayerAccumulationSignal (V x)) carrier
      (originalRectangleProtected rows cols) target θ c hgap
      (fun p q _hpq ↦ hbound x hx p q)
    change relu
      (fullConv pointwiseIdentityKernel
          (sharedLayerEval verticalAccumulationKernel b₂
            (sharedLayerEval horizontalAccumulationKernel b₁
              (V x + constantImage rows cols c))) p q +
        (θ - carrier target.1 target.2)) = _
    rw [fullConv_pointwiseIdentityKernel]
    rw [hlayers x hx]
    exact hselected p q hpq

end OneChannelCNNUniversality
