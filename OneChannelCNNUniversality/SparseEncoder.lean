import OneChannelCNNUniversality.Program

/-!
# From binomial convolution to separated two-dimensional registers

This file connects the certified nonsingular matrix in `Encoder` to the
exact two-dimensional convolution semantics.  Only the four kernel sites
`(0,0)`, `(0,1)`, `(1,0)`, and `(1,1)` are ever needed, so the construction
embeds in every prescribed kernel rectangle whose two sides are at least two.
-/

namespace OneChannelCNNUniversality

def finZeroOfTwo {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def finOneOfTwo {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

/-- The horizontal Pascal kernel `δ_(0,0) + δ_(0,1)`, embedded in an
arbitrary fixed kernel rectangle. -/
def horizontalPairKernel {kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) : Kernel kRows kCols :=
  twoTapKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols)
    (finZeroOfTwo hkRows) (finOneOfTwo hkCols) 1

/-- The vertical Pascal kernel `δ_(0,0) + δ_(1,0)`. -/
def verticalPairKernel {kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) : Kernel kRows kCols :=
  twoTapKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols)
    (finOneOfTwo hkRows) (finZeroOfTwo hkCols) 1

/-- The identity delta kernel `δ_(0,0)`. -/
def identityKernel {kRows kCols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) : Kernel kRows kCols :=
  deltaKernel (finZeroOfTwo hkRows) (finZeroOfTwo hkCols) 1

theorem fullConv_horizontalPairKernel {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image rows cols) (p q : ℕ) :
    fullConv (horizontalPairKernel hkRows hkCols) x p q =
      zeroExtend x p q + predecessor (fun t ↦ zeroExtend x p t) q := by
  rw [horizontalPairKernel, fullConv_twoTapKernel]
  rcases q with _ | q
  · simp [finZeroOfTwo, finOneOfTwo, predecessor]
  · simp [finZeroOfTwo, finOneOfTwo, predecessor]

theorem fullConv_verticalPairKernel {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image rows cols) (p q : ℕ) :
    fullConv (verticalPairKernel hkRows hkCols) x p q =
      zeroExtend x p q + predecessor (fun t ↦ zeroExtend x t q) p := by
  rw [verticalPairKernel, fullConv_twoTapKernel]
  rcases p with _ | p
  · simp [finZeroOfTwo, finOneOfTwo, predecessor]
  · simp [finZeroOfTwo, finOneOfTwo, predecessor]

theorem fullConv_identityKernel {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image rows cols) (p q : ℕ) :
    fullConv (identityKernel hkRows hkCols) x p q = zeroExtend x p q := by
  rw [identityKernel, fullConv_deltaKernel]
  simp [finZeroOfTwo]

theorem fullConv_eq_zero_of_row_ge {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols) (p q : ℕ)
    (hp : rows + kRows - 1 ≤ p) : fullConv w x p q = 0 := by
  classical
  unfold fullConv
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  split_ifs with hab
  · rw [zeroExtend_row_outside]
    · simp
    · have haLt : (a : ℕ) < kRows := a.isLt
      omega
  · rfl

theorem fullConv_eq_zero_of_col_ge {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols) (p q : ℕ)
    (hq : cols + kCols - 1 ≤ q) : fullConv w x p q = 0 := by
  classical
  unfold fullConv
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  split_ifs with hab
  · rw [zeroExtend_col_outside]
    · simp
    · have hbLt : (b : ℕ) < kCols := b.isLt
      omega
  · rfl

/-- Zero-extending the declared full-convolution output changes no value:
the analytic convolution already vanishes outside its exact support box. -/
theorem zeroExtend_fullConvImage {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols) (p q : ℕ) :
    zeroExtend (fullConvImage w x) p q = fullConv w x p q := by
  by_cases hp : p < rows + kRows - 1
  · by_cases hq : q < cols + kCols - 1
    · simp [zeroExtend, fullConvImage, hp, hq]
    · rw [zeroExtend_col_outside (hj := Nat.le_of_not_gt hq),
        fullConv_eq_zero_of_col_ge w x p q (Nat.le_of_not_gt hq)]
  · rw [zeroExtend_row_outside (hi := Nat.le_of_not_gt hp),
      fullConv_eq_zero_of_row_ge w x p q (Nat.le_of_not_gt hp)]

/-- The linear operator represented by the one-dimensional pair kernel. -/
def pairOperator (u : ℕ → ℝ) : ℕ → ℝ :=
  fun q ↦ u q + predecessor u q

theorem iteratePairKernel_eq_iterate (steps : ℕ) (u : ℕ → ℝ) :
    iteratePairKernel steps u = (pairOperator^[steps]) u := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      funext q
      change iteratePairKernel steps u q +
          predecessor (iteratePairKernel steps u) q = _
      rw [ih]
      rfl

/-- Horizontal full-convolution iteration is exactly the one-dimensional
Pascal iteration on every zero-extended row. -/
theorem zeroExtend_iterateFullConv_horizontal
    {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : ℕ) (x : Image rows cols) (p q : ℕ) :
    zeroExtend (iterateFullConv (horizontalPairKernel hkRows hkCols) steps x) p q =
      ((pairOperator^[steps]) (fun t ↦ zeroExtend x p t)) q := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      change zeroExtend
          (iterateFullConv (horizontalPairKernel hkRows hkCols) steps
            (fullConvImage (horizontalPairKernel hkRows hkCols) x)) p q = _
      rw [ih]
      have hslice :
          (fun t ↦ zeroExtend
            (fullConvImage (horizontalPairKernel hkRows hkCols) x) p t) =
            pairOperator (fun t ↦ zeroExtend x p t) := by
        funext t
        rw [zeroExtend_fullConvImage,
          fullConv_horizontalPairKernel hkRows hkCols]
        rfl
      rw [hslice, ← Function.iterate_succ_apply]

/-- Vertical analogue of `zeroExtend_iterateFullConv_horizontal`. -/
theorem zeroExtend_iterateFullConv_vertical
    {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (steps : ℕ) (x : Image rows cols) (p q : ℕ) :
    zeroExtend (iterateFullConv (verticalPairKernel hkRows hkCols) steps x) p q =
      ((pairOperator^[steps]) (fun t ↦ zeroExtend x t q)) p := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      change zeroExtend
          (iterateFullConv (verticalPairKernel hkRows hkCols) steps
            (fullConvImage (verticalPairKernel hkRows hkCols) x)) p q = _
      rw [ih]
      have hslice :
          (fun t ↦ zeroExtend
            (fullConvImage (verticalPairKernel hkRows hkCols) x) t q) =
            pairOperator (fun t ↦ zeroExtend x t q) := by
        funext t
        rw [zeroExtend_fullConvImage,
          fullConv_verticalPairKernel hkRows hkCols]
        rfl
      rw [hslice, ← Function.iterate_succ_apply]

/-- Closed binomial formula for the one-dimensional Pascal recurrence. -/
theorem iteratePairKernel_eq_sum_choose (steps : ℕ) (u : ℕ → ℝ) (q : ℕ) :
    iteratePairKernel steps u q =
      ∑ j ∈ Finset.range (q + 1),
        (Nat.choose steps (q - j) : ℝ) * u j := by
  induction steps generalizing q with
  | zero =>
      rw [iteratePairKernel_zero]
      symm
      rw [Finset.sum_eq_single q]
      · simp
      · intro j hj hjq
        have hjrange : j < q + 1 := Finset.mem_range.mp hj
        have hjle : j ≤ q := by omega
        have hjlt : j < q := lt_of_le_of_ne hjle hjq
        have hpos : 0 < q - j := Nat.sub_pos_of_lt hjlt
        simp [Nat.choose_eq_zero_of_lt hpos]
      · simp
  | succ steps ih =>
      rw [iteratePairKernel_succ, ih]
      rcases q with _ | q
      · simp [predecessor]
      · simp only [predecessor]
        rw [ih]
        have hpascal : ∀ j ∈ Finset.range (q + 1),
            (Nat.choose (steps + 1) (q + 1 - j) : ℝ) * u j =
              (Nat.choose steps (q + 1 - j) : ℝ) * u j +
                (Nat.choose steps (q - j) : ℝ) * u j := by
          intro j hj
          have hjrange : j < q + 1 := Finset.mem_range.mp hj
          have hjle : j ≤ q := by omega
          have hsub : q + 1 - j = (q - j) + 1 := by omega
          rw [hsub, Nat.choose_succ_succ]
          push_cast
          ring
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one,
          one_mul]
        conv_rhs => rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one,
          one_mul]
        rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
        ring

theorem sum_choose_truncate_to_fin (steps n q : ℕ) (u : ℕ → ℝ)
    (hnq : n ≤ q + 1) (hu : ∀ j, n ≤ j → u j = 0) :
    (∑ j ∈ Finset.range (q + 1),
        (Nat.choose steps (q - j) : ℝ) * u j) =
      ∑ j : Fin n, (Nat.choose steps (q - (j : ℕ)) : ℝ) * u j := by
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (Nat.choose steps (q - j) : ℝ) * u j) n
  rw [hfin]
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hjLarge hjSmall
    have hjge : n ≤ j := by
      simpa only [Finset.mem_range, not_lt] using hjSmall
    rw [hu j hjge]
    ring

/-- A horizontal encoder sample is a row of `gapMatrix` acting on the
reversed finite input row. -/
theorem horizontal_encoder_sample
    {kRows kCols rows n : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (hn : 0 < n)
    (x : Image rows n) (p : ℕ) (i : Fin n) :
    zeroExtend
        (iterateFullConv (horizontalPairKernel hkRows hkCols)
          (encoderDepth n) x)
        p (encoderSite n i) =
      ∑ j : Fin n, gapMatrix n i j * zeroExtend x p (Fin.rev j) := by
  rw [zeroExtend_iterateFullConv_horizontal]
  rw [← congrFun (iteratePairKernel_eq_iterate (encoderDepth n)
    (fun t ↦ zeroExtend x p t)) (encoderSite n i)]
  rw [iteratePairKernel_eq_sum_choose]
  rw [sum_choose_truncate_to_fin (encoderDepth n) n (encoderSite n i)
    (fun t ↦ zeroExtend x p t)]
  · rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
    apply Finset.univ.sum_congr rfl
    intro j hj
    simp only [Fin.revPerm_apply, gapMatrix, encoderSite]
    have hjlt : (j : ℕ) < n := j.isLt
    have hiLt : (i : ℕ) < n := i.isLt
    have hindex : n - 1 + 3 * (i : ℕ) - (Fin.rev j : ℕ) =
        3 * (i : ℕ) + (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    rw [hindex]
  · unfold encoderSite
    omega
  · intro j hj
    exact zeroExtend_col_outside x hj

/-- A vertical encoder sample is the analogous action on a reversed input
column. -/
theorem vertical_encoder_sample
    {kRows kCols n cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (hn : 0 < n)
    (x : Image n cols) (q : ℕ) (i : Fin n) :
    zeroExtend
        (iterateFullConv (verticalPairKernel hkRows hkCols)
          (encoderDepth n) x)
        (encoderSite n i) q =
      ∑ j : Fin n, gapMatrix n i j * zeroExtend x (Fin.rev j) q := by
  rw [zeroExtend_iterateFullConv_vertical]
  rw [← congrFun (iteratePairKernel_eq_iterate (encoderDepth n)
    (fun t ↦ zeroExtend x t q)) (encoderSite n i)]
  rw [iteratePairKernel_eq_sum_choose]
  rw [sum_choose_truncate_to_fin (encoderDepth n) n (encoderSite n i)
    (fun t ↦ zeroExtend x t q)]
  · rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
    apply Finset.univ.sum_congr rfl
    intro j hj
    simp only [Fin.revPerm_apply, gapMatrix, encoderSite]
    have hjlt : (j : ℕ) < n := j.isLt
    have hiLt : (i : ℕ) < n := i.isLt
    have hindex : n - 1 + 3 * (i : ℕ) - (Fin.rev j : ℕ) =
        3 * (i : ℕ) + (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    rw [hindex]
  · unfold encoderSite
    omega
  · intro j hj
    exact zeroExtend_row_outside x hj

theorem vertical_encoder_sample_of_support
    {kRows kCols rows cols n : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (hn : 0 < n)
    (x : Image rows cols) (q : ℕ) (i : Fin n)
    (hsupport : ∀ p, n ≤ p → zeroExtend x p q = 0) :
    zeroExtend
        (iterateFullConv (verticalPairKernel hkRows hkCols)
          (encoderDepth n) x)
        (encoderSite n i) q =
      ∑ j : Fin n, gapMatrix n i j * zeroExtend x (Fin.rev j) q := by
  rw [zeroExtend_iterateFullConv_vertical]
  rw [← congrFun (iteratePairKernel_eq_iterate (encoderDepth n)
    (fun t ↦ zeroExtend x t q)) (encoderSite n i)]
  rw [iteratePairKernel_eq_sum_choose]
  rw [sum_choose_truncate_to_fin (encoderDepth n) n (encoderSite n i)
    (fun t ↦ zeroExtend x t q)]
  · rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))]
    apply Finset.univ.sum_congr rfl
    intro j hj
    simp only [Fin.revPerm_apply, gapMatrix, encoderSite]
    have hjlt : (j : ℕ) < n := j.isLt
    have hiLt : (i : ℕ) < n := i.isLt
    have hindex : n - 1 + 3 * (i : ℕ) - (Fin.rev j : ℕ) =
        3 * (i : ℕ) + (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    rw [hindex]
  · unfold encoderSite
    omega
  · exact hsupport

theorem iterateThenConv_apply_eq_finalConv
    {kRows kCols rows cols : ℕ} (w finalKernel : Kernel kRows kCols)
    (steps : ℕ) (x : Image rows cols)
    (p : Fin (grownSize kRows rows (steps + 1)))
    (q : Fin (grownSize kCols cols (steps + 1))) :
    iterateThenConv w finalKernel steps x p q =
      fullConv finalKernel (iterateFullConv w steps x) p q := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      exact ih (fullConvImage w x) p q

theorem iterateThenConv_identity_apply
    {kRows kCols rows cols : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (w : Kernel kRows kCols) (steps : ℕ) (x : Image rows cols)
    (p : Fin (grownSize kRows rows (steps + 1)))
    (q : Fin (grownSize kCols cols (steps + 1))) :
    iterateThenConv w (identityKernel hkRows hkCols) steps x p q =
      zeroExtend (iterateFullConv w steps x) p q := by
  rw [iterateThenConv_apply_eq_finalConv,
    fullConv_identityKernel hkRows hkCols]

theorem grownSize_ge_add_steps (kernelSize start steps : ℕ)
    (hk : 2 ≤ kernelSize) : start + steps ≤ grownSize kernelSize start steps := by
  induction steps generalizing start with
  | zero => simp [grownSize]
  | succ steps ih =>
      rw [grownSize]
      have h := ih (start + kernelSize - 1)
      omega

def encoderMidRows (kRows d₁ d₂ : ℕ) : ℕ :=
  grownSize kRows d₁ (encoderDepth d₂ + 1)

def encoderMidCols (kCols d₁ d₂ : ℕ) : ℕ :=
  grownSize kCols d₂ (encoderDepth d₂ + 1)

def encoderOutRows (kRows d₁ d₂ : ℕ) : ℕ :=
  grownSize kRows (encoderMidRows kRows d₁ d₂) (encoderDepth d₁ + 1)

def encoderOutCols (kCols d₁ d₂ : ℕ) : ℕ :=
  grownSize kCols (encoderMidCols kCols d₁ d₂) (encoderDepth d₁ + 1)

def horizontalEncoderKeep (d₁ d₂ : ℕ) {rows cols : ℕ}
    (p : Fin rows) (q : Fin cols) : Bool :=
  decide ((p : ℕ) < d₁ ∧ ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j)

def sparseEncoderKeep (d₁ d₂ : ℕ) {rows cols : ℕ}
    (p : Fin rows) (q : Fin cols) : Bool :=
  decide ((∃ i : Fin d₁, (p : ℕ) = encoderSite d₁ i) ∧
    ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j)

@[simp] theorem horizontalEncoderKeep_eq_true_iff (d₁ d₂ : ℕ)
    {rows cols : ℕ} (p : Fin rows) (q : Fin cols) :
    horizontalEncoderKeep d₁ d₂ p q = true ↔
      (p : ℕ) < d₁ ∧ ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j := by
  simp [horizontalEncoderKeep]

@[simp] theorem sparseEncoderKeep_eq_true_iff (d₁ d₂ : ℕ)
    {rows cols : ℕ} (p : Fin rows) (q : Fin cols) :
    sparseEncoderKeep d₁ d₂ p q = true ↔
      ((∃ i : Fin d₁, (p : ℕ) = encoderSite d₁ i) ∧
        ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j) := by
  simp [sparseEncoderKeep]

/-- The complete horizontal-then-vertical gap-three encoder program. -/
def sparseEncoderProgram {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) :
    MaskProgramTo kRows kCols d₁ d₂
      (encoderOutRows kRows d₁ d₂) (encoderOutCols kCols d₁ d₂) :=
  MaskProgramTo.iterationsThenMask
    (horizontalPairKernel hkRows hkCols) (identityKernel hkRows hkCols)
    (encoderDepth d₂) (horizontalEncoderKeep d₁ d₂)
    (MaskProgramTo.iterationsThenMask
      (verticalPairKernel hkRows hkCols) (identityKernel hkRows hkCols)
      (encoderDepth d₁) (sparseEncoderKeep d₁ d₂)
      (MaskProgramTo.nil
        (encoderOutRows kRows d₁ d₂) (encoderOutCols kCols d₁ d₂)
        kRows kCols))

def sparseEncodedValue {d₁ d₂ : ℕ} (x : Image d₁ d₂)
    (i : Fin d₁) (j : Fin d₂) : ℝ :=
  ∑ r : Fin d₁, ∑ c : Fin d₂,
    gapMatrix d₁ i r * gapMatrix d₂ j c * x (Fin.rev r) (Fin.rev c)

theorem encoderSite_le_encoderDepth {n : ℕ} (i : Fin n) :
    encoderSite n i ≤ encoderDepth n := by
  have hi : (i : ℕ) < n := i.isLt
  unfold encoderSite encoderDepth
  omega

def encoderMidRowFin {kRows d₁ d₂ : ℕ} (hkRows : 2 ≤ kRows)
    (i : Fin d₁) : Fin (encoderMidRows kRows d₁ d₂) :=
  ⟨i, by
    have h := grownSize_ge_add_steps kRows d₁ (encoderDepth d₂ + 1) hkRows
    unfold encoderMidRows
    omega⟩

def encoderMidColFin {kCols d₁ d₂ : ℕ} (hkCols : 2 ≤ kCols)
    (j : Fin d₂) : Fin (encoderMidCols kCols d₁ d₂) :=
  ⟨encoderSite d₂ j, by
    have h := grownSize_ge_add_steps kCols d₂ (encoderDepth d₂ + 1) hkCols
    have hsite := encoderSite_le_encoderDepth j
    unfold encoderMidCols
    omega⟩

def encoderOutRowFin {kRows d₁ d₂ : ℕ} (hkRows : 2 ≤ kRows)
    (i : Fin d₁) : Fin (encoderOutRows kRows d₁ d₂) :=
  ⟨encoderSite d₁ i, by
    have h := grownSize_ge_add_steps kRows (encoderMidRows kRows d₁ d₂)
      (encoderDepth d₁ + 1) hkRows
    have hsite := encoderSite_le_encoderDepth i
    unfold encoderOutRows
    omega⟩

def encoderOutColFin {kCols d₁ d₂ : ℕ} (hkCols : 2 ≤ kCols)
    (j : Fin d₂) : Fin (encoderOutCols kCols d₁ d₂) :=
  ⟨encoderSite d₂ j, by
    have hmid := grownSize_ge_add_steps kCols d₂ (encoderDepth d₂ + 1) hkCols
    have hout := grownSize_ge_add_steps kCols
      (grownSize kCols d₂ (encoderDepth d₂ + 1))
      (encoderDepth d₁ + 1) hkCols
    have hsite := encoderSite_le_encoderDepth j
    unfold encoderOutCols encoderMidCols
    omega⟩

def horizontalEncoderVariable {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (x : Image d₁ d₂) :
    Image (encoderMidRows kRows d₁ d₂) (encoderMidCols kCols d₁ d₂) :=
  fun p q ↦ if horizontalEncoderKeep d₁ d₂ p q then
    iterateThenConv (horizontalPairKernel hkRows hkCols)
      (identityKernel hkRows hkCols) (encoderDepth d₂) x p q else 0

theorem horizontalEncoderVariable_zeroExtend_row_ge
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (x : Image d₁ d₂)
    (p q : ℕ) (hp : d₁ ≤ p) :
    zeroExtend (horizontalEncoderVariable hkRows hkCols x) p q = 0 := by
  by_cases hpr : p < encoderMidRows kRows d₁ d₂
  · by_cases hqc : q < encoderMidCols kCols d₁ d₂
    · simp [zeroExtend, horizontalEncoderVariable, horizontalEncoderKeep,
        hpr, hqc, hp]
    · exact zeroExtend_col_outside _ (Nat.le_of_not_gt hqc)
  · exact zeroExtend_row_outside _ (Nat.le_of_not_gt hpr)

theorem horizontalEncoderVariable_sample
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (hd₂ : 0 < d₂)
    (x : Image d₁ d₂) (r : Fin d₁) (j : Fin d₂) :
    horizontalEncoderVariable hkRows hkCols x
        (encoderMidRowFin (d₂ := d₂) hkRows r)
        (encoderMidColFin (d₁ := d₁) hkCols j) =
      ∑ c : Fin d₂, gapMatrix d₂ j c * x r (Fin.rev c) := by
  have hsample := horizontal_encoder_sample hkRows hkCols hd₂ x (r : ℕ) j
  rw [horizontalEncoderVariable]
  have hkeep : horizontalEncoderKeep d₁ d₂
      (encoderMidRowFin (d₂ := d₂) hkRows r)
      (encoderMidColFin (d₁ := d₁) hkCols j) = true := by
    rw [horizontalEncoderKeep_eq_true_iff]
    exact ⟨r.isLt, j, rfl⟩
  rw [if_pos hkeep]
  rw [iterateThenConv_identity_apply]
  change zeroExtend
      (iterateFullConv (horizontalPairKernel hkRows hkCols) (encoderDepth d₂) x)
      (r : ℕ) (encoderSite d₂ j) = _
  rw [hsample]
  apply Finset.univ.sum_congr rfl
  intro c hc
  rw [zeroExtend_inside x r (Fin.rev c)]

theorem horizontalEncoderVariable_zeroExtend_sample
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols) (hd₂ : 0 < d₂)
    (x : Image d₁ d₂) (r : Fin d₁) (j : Fin d₂) :
    zeroExtend (horizontalEncoderVariable hkRows hkCols x)
        (r : ℕ) (encoderSite d₂ j) =
      ∑ c : Fin d₂, gapMatrix d₂ j c * x r (Fin.rev c) := by
  have hr := (encoderMidRowFin (d₂ := d₂) hkRows r).isLt
  have hc := (encoderMidColFin (d₁ := d₁) hkCols j).isLt
  have hr' : (r : ℕ) < encoderMidRows kRows d₁ d₂ := by
    exact hr
  have hc' : encoderSite d₂ j < encoderMidCols kCols d₁ d₂ := by
    exact hc
  rw [zeroExtend_of_lt _ hr' hc']
  exact horizontalEncoderVariable_sample hkRows hkCols hd₂ x r j

/-- The symbolic two-dimensional encoder has the certified Kronecker
sampling value at every separated master register. -/
theorem sparseEncoderProgram_eval_master
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (x : Image d₁ d₂) (i : Fin d₁) (j : Fin d₂) :
    (sparseEncoderProgram hkRows hkCols).eval x
        (encoderOutRowFin (d₂ := d₂) hkRows i)
        (encoderOutColFin (d₁ := d₁) hkCols j) =
      sparseEncodedValue x i j := by
  rw [sparseEncoderProgram, MaskProgramTo.eval_iterationsThenMask,
    MaskProgramTo.eval_iterationsThenMask]
  change (if sparseEncoderKeep d₁ d₂
      (encoderOutRowFin (d₂ := d₂) hkRows i)
      (encoderOutColFin (d₁ := d₁) hkCols j) then
        iterateThenConv (verticalPairKernel hkRows hkCols)
          (identityKernel hkRows hkCols) (encoderDepth d₁)
          (horizontalEncoderVariable hkRows hkCols x)
          (encoderOutRowFin (d₂ := d₂) hkRows i)
          (encoderOutColFin (d₁ := d₁) hkCols j)
      else 0) = _
  have hkeep : sparseEncoderKeep d₁ d₂
      (encoderOutRowFin (d₂ := d₂) hkRows i)
      (encoderOutColFin (d₁ := d₁) hkCols j) = true := by
    rw [sparseEncoderKeep_eq_true_iff]
    exact ⟨⟨i, rfl⟩, j, rfl⟩
  rw [if_pos hkeep, iterateThenConv_identity_apply]
  change zeroExtend
      (iterateFullConv (verticalPairKernel hkRows hkCols) (encoderDepth d₁)
        (horizontalEncoderVariable hkRows hkCols x))
      (encoderSite d₁ i) (encoderSite d₂ j) = _
  rw [vertical_encoder_sample_of_support hkRows hkCols hd₁
    (horizontalEncoderVariable hkRows hkCols x) (encoderSite d₂ j) i
    (fun p hp ↦ horizontalEncoderVariable_zeroExtend_row_ge
      hkRows hkCols x p (encoderSite d₂ j) hp)]
  unfold sparseEncodedValue
  apply Finset.univ.sum_congr rfl
  intro r hr
  rw [horizontalEncoderVariable_zeroExtend_sample hkRows hkCols hd₂ x (Fin.rev r) j,
    Finset.mul_sum]
  apply Finset.univ.sum_congr rfl
  intro c hc
  ring

theorem sparseEncoderProgram_eval_off_master
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (x : Image d₁ d₂)
    (p : Fin (encoderOutRows kRows d₁ d₂))
    (q : Fin (encoderOutCols kCols d₁ d₂))
    (hoff : ¬ ((∃ i : Fin d₁, (p : ℕ) = encoderSite d₁ i) ∧
      ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j)) :
    (sparseEncoderProgram hkRows hkCols).eval x p q = 0 := by
  rw [sparseEncoderProgram, MaskProgramTo.eval_iterationsThenMask,
    MaskProgramTo.eval_iterationsThenMask]
  change (if sparseEncoderKeep d₁ d₂ p q then
      iterateThenConv (verticalPairKernel hkRows hkCols)
        (identityKernel hkRows hkCols) (encoderDepth d₁)
        (horizontalEncoderVariable hkRows hkCols x) p q else 0) = 0
  have hkeep : sparseEncoderKeep d₁ d₂ p q = false := by
    apply Bool.eq_false_of_not_eq_true
    simpa using hoff
  simp [hkeep]

/-- The symbolic encoder compiled into the original expansive ReLU network.
At every master site its variable part is the certified nonsingular
Kronecker transform, and away from all masters the variable part is zero. -/
theorem exists_sparseEncoder_network
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K) :
    ∃ (net : NetworkTo kRows kCols d₁ d₂
        (encoderOutRows kRows d₁ d₂) (encoderOutCols kCols d₁ d₂))
      (carrier : Image (encoderOutRows kRows d₁ d₂)
        (encoderOutCols kCols d₁ d₂)),
      (∀ x ∈ K, ∀ i : Fin d₁, ∀ j : Fin d₂,
        net.eval x (encoderOutRowFin (d₂ := d₂) hkRows i)
            (encoderOutColFin (d₁ := d₁) hkCols j) =
          sparseEncodedValue x i j +
            carrier (encoderOutRowFin (d₂ := d₂) hkRows i)
              (encoderOutColFin (d₁ := d₁) hkCols j)) ∧
      (∀ x ∈ K,
        ∀ (p : Fin (encoderOutRows kRows d₁ d₂))
          (q : Fin (encoderOutCols kCols d₁ d₂)),
        ¬ ((∃ i : Fin d₁, (p : ℕ) = encoderSite d₁ i) ∧
          ∃ j : Fin d₂, (q : ℕ) = encoderSite d₂ j) →
        net.eval x p q = carrier p q) := by
  obtain ⟨net, carrier, hnet⟩ :=
    (sparseEncoderProgram hkRows hkCols).exists_network hK
      (fun x : Image d₁ d₂ ↦ x) (fun x ↦ x) 0
      (by intro x hx; simp) (continuousFeatureOn_identity K)
  refine ⟨net, carrier, ?_, ?_⟩
  · intro x hx i j
    have h := congrFun (congrFun (hnet x hx)
      (encoderOutRowFin (d₂ := d₂) hkRows i))
      (encoderOutColFin (d₁ := d₁) hkCols j)
    change net.eval x (encoderOutRowFin (d₂ := d₂) hkRows i)
        (encoderOutColFin (d₁ := d₁) hkCols j) =
      (sparseEncoderProgram hkRows hkCols).eval x
          (encoderOutRowFin (d₂ := d₂) hkRows i)
          (encoderOutColFin (d₁ := d₁) hkCols j) +
        carrier (encoderOutRowFin (d₂ := d₂) hkRows i)
          (encoderOutColFin (d₁ := d₁) hkCols j) at h
    rw [sparseEncoderProgram_eval_master hkRows hkCols hd₁ hd₂] at h
    exact h
  · intro x hx p q hoff
    have h := congrFun (congrFun (hnet x hx) p) q
    change net.eval x p q =
      (sparseEncoderProgram hkRows hkCols).eval x p q + carrier p q at h
    rw [sparseEncoderProgram_eval_off_master hkRows hkCols x p q hoff] at h
    simpa using h

/-- Reverse both finite input axes. -/
def reverseImageMatrix {d₁ d₂ : ℕ} (x : Image d₁ d₂) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  fun r c ↦ x (Fin.rev r) (Fin.rev c)

def sparseEncodedMatrix {d₁ d₂ : ℕ} (x : Image d₁ d₂) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  fun i j ↦ sparseEncodedValue x i j

theorem sparseEncodedMatrix_eq {d₁ d₂ : ℕ} (x : Image d₁ d₂) :
    sparseEncodedMatrix x =
      gapMatrix d₁ * reverseImageMatrix x * Matrix.transpose (gapMatrix d₂) := by
  ext i j
  simp only [sparseEncodedMatrix, sparseEncodedValue, Matrix.mul_apply,
    Matrix.transpose_apply, reverseImageMatrix]
  rw [Finset.sum_comm]
  apply Finset.univ.sum_congr rfl
  intro r hr
  rw [Finset.sum_mul]
  apply Finset.univ.sum_congr rfl
  intro c hc
  ring

theorem recover_reverseImageMatrix {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (x : Image d₁ d₂) :
    (gapMatrix d₁)⁻¹ * sparseEncodedMatrix x *
        Matrix.transpose ((gapMatrix d₂)⁻¹) =
      reverseImageMatrix x := by
  rw [sparseEncodedMatrix_eq]
  calc
    (gapMatrix d₁)⁻¹ *
          (gapMatrix d₁ * reverseImageMatrix x * Matrix.transpose (gapMatrix d₂)) *
          Matrix.transpose ((gapMatrix d₂)⁻¹) =
        (((gapMatrix d₁)⁻¹ * gapMatrix d₁) * reverseImageMatrix x *
          Matrix.transpose (gapMatrix d₂)) *
          Matrix.transpose ((gapMatrix d₂)⁻¹) := by
            simp only [Matrix.mul_assoc]
    _ = (reverseImageMatrix x * Matrix.transpose (gapMatrix d₂)) *
          Matrix.transpose ((gapMatrix d₂)⁻¹) := by
            rw [Matrix.nonsing_inv_mul (gapMatrix d₁)
              (gapMatrix_det_isUnit d₁ hd₁), Matrix.one_mul]
    _ = reverseImageMatrix x *
          (Matrix.transpose (gapMatrix d₂) *
            Matrix.transpose ((gapMatrix d₂)⁻¹)) := by
            rw [Matrix.mul_assoc]
    _ = reverseImageMatrix x *
          Matrix.transpose ((gapMatrix d₂)⁻¹ * gapMatrix d₂) := by
            rw [Matrix.transpose_mul]
    _ = reverseImageMatrix x := by
            rw [Matrix.nonsing_inv_mul (gapMatrix d₂)
              (gapMatrix_det_isUnit d₂ hd₂), Matrix.transpose_one,
              Matrix.mul_one]

/-- No input degree of freedom is lost by the separated two-dimensional
encoder. -/
theorem sparseEncodedMatrix_injective {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    Function.Injective (@sparseEncodedMatrix d₁ d₂) := by
  intro x y hxy
  have hrev : reverseImageMatrix x = reverseImageMatrix y := by
    rw [← recover_reverseImageMatrix hd₁ hd₂ x,
      ← recover_reverseImageMatrix hd₁ hd₂ y, hxy]
  funext i j
  have h := congrFun (congrFun hrev (Fin.rev i)) (Fin.rev j)
  simpa [reverseImageMatrix] using h

end OneChannelCNNUniversality
