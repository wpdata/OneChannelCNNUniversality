import ICM2022NumCS97.RouteGeometry

/-!
# Mixed linear/ReLU symbolic programs

`MaskProgram` deliberately keeps every retained coordinate in ReLU's linear
region.  Universal approximation also needs selected coordinates to cross an
actual ReLU threshold.  `HybridProgram` records, coordinate by coordinate,
whether the next retained preactivation is linearized with a compact carrier
or is passed through a genuine shifted ReLU.  Its compiler returns an actual
one-channel expansive CNN in the original semantics.
-/

namespace ICM2022NumCS97

inductive ActivationMode
  | linear
  | translate (offset : ℝ)
  | relu (offset : ℝ)

def ActivationMode.eval : ActivationMode → ℝ → ℝ
  | .linear, z => z
  | .translate offset, z => z + offset
  | .relu offset, z => ICM2022NumCS97.relu (z + offset)

inductive HybridProgram (kRows kCols : ℕ) : ℕ → ℕ → Type
  | nil (rows cols : ℕ) : HybridProgram kRows kCols rows cols
  | cons {rows cols : ℕ}
      (kernel : Kernel kRows kCols)
      (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
      (mode : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → ActivationMode)
      (tail : HybridProgram kRows kCols
        (rows + kRows - 1) (cols + kCols - 1)) :
      HybridProgram kRows kCols rows cols

namespace HybridProgram

def outRows {kRows kCols rows cols : ℕ} :
    HybridProgram kRows kCols rows cols → ℕ
  | .nil rows _ => rows
  | .cons _ _ _ tail => tail.outRows

def outCols {kRows kCols rows cols : ℕ} :
    HybridProgram kRows kCols rows cols → ℕ
  | .nil _ cols => cols
  | .cons _ _ _ tail => tail.outCols

def eval {kRows kCols rows cols : ℕ} :
    (program : HybridProgram kRows kCols rows cols) →
      Image rows cols → Image program.outRows program.outCols
  | .nil _ _, x => x
  | .cons kernel keep mode tail, x =>
      tail.eval (fun p q ↦ if keep p q then
        (mode p q).eval (fullConv kernel x p q) else 0)

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ} (x : Image rows cols) :
    (nil (kRows := kRows) (kCols := kCols) rows cols).eval x = x := rfl

@[simp] theorem eval_cons {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (mode : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → ActivationMode)
    (tail : HybridProgram kRows kCols
      (rows + kRows - 1) (cols + kCols - 1))
    (x : Image rows cols) :
    (cons kernel keep mode tail).eval x =
      tail.eval (fun p q ↦ if keep p q then
        (mode p q).eval (fullConv kernel x p q) else 0) := rfl

/-- Regard a fully linear masked program as a hybrid program. -/
def ofMaskProgram {kRows kCols rows cols : ℕ} :
    MaskProgram kRows kCols rows cols → HybridProgram kRows kCols rows cols
  | .nil rows cols => .nil rows cols
  | .cons kernel keep tail =>
      .cons kernel keep (fun _ _ ↦ .linear) (ofMaskProgram tail)

@[simp] theorem outRows_ofMaskProgram {kRows kCols rows cols : ℕ}
    (program : MaskProgram kRows kCols rows cols) :
    (ofMaskProgram program).outRows = program.outRows := by
  induction program with
  | nil => rfl
  | cons kernel keep tail ih => exact ih

@[simp] theorem outCols_ofMaskProgram {kRows kCols rows cols : ℕ}
    (program : MaskProgram kRows kCols rows cols) :
    (ofMaskProgram program).outCols = program.outCols := by
  induction program with
  | nil => rfl
  | cons kernel keep tail ih => exact ih

theorem eval_ofMaskProgram_heq {kRows kCols rows cols : ℕ}
    (program : MaskProgram kRows kCols rows cols) (x : Image rows cols) :
    HEq ((ofMaskProgram program).eval x) (program.eval x) := by
  induction program with
  | nil => rfl
  | cons kernel keep tail ih =>
      exact ih (fun p q ↦ if keep p q then fullConv kernel x p q else 0)

/-- Sequential composition of mixed programs. -/
def append {kRows kCols rows cols : ℕ} :
    (first : HybridProgram kRows kCols rows cols) →
      HybridProgram kRows kCols first.outRows first.outCols →
        HybridProgram kRows kCols rows cols
  | .nil _ _, second => second
  | .cons kernel keep mode tail, second =>
      .cons kernel keep mode (append tail second)

@[simp] theorem outRows_append {kRows kCols rows cols : ℕ}
    (first : HybridProgram kRows kCols rows cols)
    (second : HybridProgram kRows kCols first.outRows first.outCols) :
    (first.append second).outRows = second.outRows := by
  induction first with
  | nil => rfl
  | cons kernel keep mode tail ih => exact ih second

@[simp] theorem outCols_append {kRows kCols rows cols : ℕ}
    (first : HybridProgram kRows kCols rows cols)
    (second : HybridProgram kRows kCols first.outRows first.outCols) :
    (first.append second).outCols = second.outCols := by
  induction first with
  | nil => rfl
  | cons kernel keep mode tail ih => exact ih second

theorem eval_append_heq {kRows kCols rows cols : ℕ}
    (first : HybridProgram kRows kCols rows cols)
    (second : HybridProgram kRows kCols first.outRows first.outCols)
    (x : Image rows cols) :
    HEq ((first.append second).eval x) (second.eval (first.eval x)) := by
  induction first with
  | nil => rfl
  | cons kernel keep mode tail ih =>
      exact ih second (fun p q ↦ if keep p q then
        (mode p q).eval (fullConv kernel x p q) else 0)

/-- One mixed symbolic instruction is implemented by one actual ReLU layer,
with a positive carrier only at linearized coordinates. -/
theorem exists_mixed_layer {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ}
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (mode : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → ActivationMode) :
    ∃ (bias carrier : Image (rows + kRows - 1) (cols + kCols - 1)),
      (∀ x ∈ K, layerEval kernel bias (F x) =
        (fun p q ↦ if keep p q then
          (mode p q).eval (fullConv kernel (V x) p q) else 0) + carrier) ∧
      ContinuousFeatureOn K (fun x p q ↦ if keep p q then
        (mode p q).eval (fullConv kernel (V x) p q) else 0) := by
  have hb : ∀ p : Fin (rows + kRows - 1),
      ∀ q : Fin (cols + kCols - 1),
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, |fullConv kernel (V x) p q| < C := by
    intro p q
    exact exists_uniform_abs_bound hK _
      (continuousFeatureOn_fullConv hV kernel p q)
  choose C hCpos hCbound using hb
  let carrier : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ if keep p q then
      match mode p q with
      | .linear => C p q
      | .translate offset => C p q + |offset|
      | .relu _ => 0
    else 0
  let bias : Image (rows + kRows - 1) (cols + kCols - 1) :=
    fun p q ↦ if keep p q then
      match mode p q with
      | .linear => C p q - fullConv kernel known p q
      | .translate offset =>
          offset + (C p q + |offset|) - fullConv kernel known p q
      | .relu offset => offset - fullConv kernel known p q
    else -C p q - fullConv kernel known p q
  refine ⟨bias, carrier, ?_, ?_⟩
  · intro x hx
    funext p q
    have hconv : fullConv kernel (F x) p q =
        fullConv kernel (V x) p q + fullConv kernel known p q := by
      rw [hdecomp x hx, fullConv_add]
    change relu (fullConv kernel (F x) p q + bias p q) =
      (if keep p q = true then
        (mode p q).eval (fullConv kernel (V x) p q) else 0) + carrier p q
    by_cases hkeep : keep p q = true
    · rw [if_pos hkeep]
      cases hmode : mode p q with
      | linear =>
          change relu (fullConv kernel (F x) p q + bias p q) =
            fullConv kernel (V x) p q + carrier p q
          simp only [bias, carrier, hkeep, hmode, ↓reduceIte]
          rw [hconv]
          have hzle : -|fullConv kernel (V x) p q| ≤
              fullConv kernel (V x) p q := neg_abs_le _
          have hpos : 0 < fullConv kernel (V x) p q + C p q := by
            linarith [hCbound p q x hx]
          convert relu_of_nonneg hpos.le using 1 <;> ring
      | translate offset =>
          change relu (fullConv kernel (F x) p q + bias p q) =
            (fullConv kernel (V x) p q + offset) + carrier p q
          simp only [bias, carrier, hkeep, hmode, ↓reduceIte]
          rw [hconv]
          have hzle : -|fullConv kernel (V x) p q| ≤
              fullConv kernel (V x) p q := neg_abs_le _
          have hoffset : 0 ≤ offset + |offset| := by
            linarith [neg_abs_le offset]
          have hpos : 0 < fullConv kernel (V x) p q + offset +
              (C p q + |offset|) := by
            linarith [hCbound p q x hx]
          convert relu_of_nonneg hpos.le using 1 <;> ring
      | relu offset =>
          change relu (fullConv kernel (F x) p q + bias p q) =
            relu (fullConv kernel (V x) p q + offset) + carrier p q
          simp only [bias, carrier, hkeep, hmode, ↓reduceIte]
          rw [hconv]
          congr 1
          ring
    · have hkeepFalse : keep p q = false := Bool.eq_false_of_not_eq_true hkeep
      rw [if_neg hkeep]
      rw [hconv]
      simp only [bias, carrier, hkeepFalse, Bool.false_eq_true, if_false,
        add_zero]
      apply relu_of_nonpos
      have hzle : fullConv kernel (V x) p q ≤
          |fullConv kernel (V x) p q| := le_abs_self _
      linarith [hCbound p q x hx]
  · intro p q
    change ContinuousOn (fun x ↦ if keep p q = true then
      (mode p q).eval (fullConv kernel (V x) p q) else 0) K
    by_cases hkeep : keep p q = true
    · cases hmode : mode p q with
      | linear =>
          simpa [hkeep, hmode, ActivationMode.eval] using
            continuousFeatureOn_fullConv hV kernel p q
      | translate offset =>
          simp only [hkeep, ↓reduceIte, hmode, ActivationMode.eval]
          change ContinuousOn
            ((fun x ↦ fullConv kernel (V x) p q) +
              (fun _ : X ↦ offset)) K
          exact (continuousFeatureOn_fullConv hV kernel p q).add
            (continuousOn_const :
              ContinuousOn (fun _ : X ↦ offset) K)
      | relu offset =>
          have hpre : ContinuousOn
              (fun x ↦ fullConv kernel (V x) p q + offset) K :=
            (continuousFeatureOn_fullConv hV kernel p q).add continuousOn_const
          simp only [hkeep, ↓reduceIte, hmode, ActivationMode.eval]
          intro x hx
          change ContinuousWithinAt
            (fun y ↦ max (fullConv kernel (V y) p q + offset) 0) K x
          exact (hpre x hx).max (continuousWithinAt_const :
            ContinuousWithinAt (fun _ : X ↦ (0 : ℝ)) K x)
    · have hkeepFalse : keep p q = false := Bool.eq_false_of_not_eq_true hkeep
      simpa [hkeepFalse] using
        (continuousOn_const : ContinuousOn (fun _ : X ↦ (0 : ℝ)) K)

/-- Every finite mixed program compiles to the exact expansive one-channel
CNN semantics on a prescribed compact set. -/
theorem exists_network {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ}
    (program : HybridProgram kRows kCols rows cols)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols program.outRows program.outCols)
      (carrier : Image program.outRows program.outCols),
      ∀ x ∈ K, net.eval (F x) = program.eval (V x) + carrier := by
  induction program with
  | nil rows cols =>
      exact ⟨NetworkTo.nil rows cols kRows kCols, known, hdecomp⟩
  | @cons rows cols kernel keep mode tail ih =>
      obtain ⟨bias, nextCarrier, hfirst, hnextV⟩ :=
        exists_mixed_layer hK F V known hdecomp hV kernel keep mode
      let nextF : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ layerEval kernel bias (F x)
      let nextV : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x p q ↦ if keep p q then
          (mode p q).eval (fullConv kernel (V x) p q) else 0
      obtain ⟨tailNet, finalCarrier, htail⟩ :=
        ih nextF nextV nextCarrier (fun x hx ↦ hfirst x hx) hnextV
      refine ⟨NetworkTo.cons kernel bias tailNet, finalCarrier, ?_⟩
      intro x hx
      rw [NetworkTo.eval_cons]
      exact htail x hx

end HybridProgram

/-- A mixed program with explicit final dimensions. -/
structure HybridProgramTo (kRows kCols inRows inCols outRows outCols : ℕ) where
  program : HybridProgram kRows kCols inRows inCols
  rows_eq : program.outRows = outRows
  cols_eq : program.outCols = outCols

namespace HybridProgramTo

def eval {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : HybridProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) : Image outRows outCols :=
  fun i j ↦ program.program.eval x
    ⟨i, by simpa [program.rows_eq] using i.isLt⟩
    ⟨j, by simpa [program.cols_eq] using j.isLt⟩

theorem eval_heq_program {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : HybridProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) :
    HEq (program.eval x) (program.program.eval x) := by
  rcases program with ⟨program, rfl, rfl⟩
  rfl

theorem maskEval_heq_program {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) :
    HEq (program.eval x) (program.program.eval x) := by
  rcases program with ⟨program, rfl, rfl⟩
  rfl

def nil (rows cols kRows kCols : ℕ) :
    HybridProgramTo kRows kCols rows cols rows cols :=
  ⟨HybridProgram.nil rows cols, rfl, rfl⟩

def cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (mode : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → ActivationMode)
    (tail : HybridProgramTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols) :
    HybridProgramTo kRows kCols rows cols outRows outCols :=
  ⟨HybridProgram.cons kernel keep mode tail.program, tail.rows_eq, tail.cols_eq⟩

def ofMaskProgramTo {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols inRows inCols outRows outCols) :
    HybridProgramTo kRows kCols inRows inCols outRows outCols :=
  ⟨HybridProgram.ofMaskProgram program.program,
    (HybridProgram.outRows_ofMaskProgram program.program).trans program.rows_eq,
    (HybridProgram.outCols_ofMaskProgram program.program).trans program.cols_eq⟩

def append {kRows kCols inRows inCols midRows midCols outRows outCols : ℕ}
    (first : HybridProgramTo kRows kCols inRows inCols midRows midCols)
    (second : HybridProgramTo kRows kCols midRows midCols outRows outCols) :
    HybridProgramTo kRows kCols inRows inCols outRows outCols := by
  rcases first with ⟨first, rfl, rfl⟩
  exact ⟨first.append second.program,
    (HybridProgram.outRows_append first second.program).trans second.rows_eq,
    (HybridProgram.outCols_append first second.program).trans second.cols_eq⟩

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ} (x : Image rows cols) :
    (nil rows cols kRows kCols).eval x = x := by
  funext i j
  rfl

@[simp] theorem eval_cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (mode : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → ActivationMode)
    (tail : HybridProgramTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols)
    (x : Image rows cols) :
    (cons kernel keep mode tail).eval x =
      tail.eval (fun p q ↦ if keep p q then
        (mode p q).eval (fullConv kernel x p q) else 0) := by
  funext i j
  rfl

theorem eval_ofMaskProgramTo_heq {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) :
    HEq ((ofMaskProgramTo program).eval x) (program.eval x) := by
  exact (eval_heq_program (ofMaskProgramTo program) x).trans
    ((HybridProgram.eval_ofMaskProgram_heq program.program x).trans
      (maskEval_heq_program program x).symm)

theorem eval_ofMaskProgramTo {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) :
    (ofMaskProgramTo program).eval x = program.eval x :=
  eq_of_heq (eval_ofMaskProgramTo_heq program x)

theorem append_program_eval_heq
    {kRows kCols inRows inCols midRows midCols outRows outCols : ℕ}
    (first : HybridProgramTo kRows kCols inRows inCols midRows midCols)
    (second : HybridProgramTo kRows kCols midRows midCols outRows outCols)
    (x : Image inRows inCols) :
    HEq ((first.append second).program.eval x)
      (second.program.eval (first.eval x)) := by
  rcases first with ⟨first, rfl, rfl⟩
  rcases second with ⟨second, rfl, rfl⟩
  exact HybridProgram.eval_append_heq first second x

theorem eval_append_heq {kRows kCols inRows inCols midRows midCols outRows outCols : ℕ}
    (first : HybridProgramTo kRows kCols inRows inCols midRows midCols)
    (second : HybridProgramTo kRows kCols midRows midCols outRows outCols)
    (x : Image inRows inCols) :
    HEq ((first.append second).eval x) (second.eval (first.eval x)) := by
  exact (eval_heq_program (first.append second) x).trans
    ((append_program_eval_heq first second x).trans
      (eval_heq_program second (first.eval x)).symm)

theorem eval_append {kRows kCols inRows inCols midRows midCols outRows outCols : ℕ}
    (first : HybridProgramTo kRows kCols inRows inCols midRows midCols)
    (second : HybridProgramTo kRows kCols midRows midCols outRows outCols)
    (x : Image inRows inCols) :
    (first.append second).eval x = second.eval (first.eval x) :=
  eq_of_heq (eval_append_heq first second x)

theorem exists_network {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols outRows outCols : ℕ}
    (program : HybridProgramTo kRows kCols rows cols outRows outCols)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols outRows outCols)
      (carrier : Image outRows outCols),
      ∀ x ∈ K, net.eval (F x) = program.eval (V x) + carrier := by
  rcases program with ⟨program, rfl, rfl⟩
  exact program.exists_network hK F V known hdecomp hV

end HybridProgramTo

end ICM2022NumCS97
