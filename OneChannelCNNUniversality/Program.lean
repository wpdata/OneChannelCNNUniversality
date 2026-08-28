import OneChannelCNNUniversality.Register

/-!
# Masked-convolution programs and their exact CNN refinement

`MaskProgram` is a finite symbolic program.  Every instruction chooses one
shared convolution kernel and an arbitrary spatial Boolean mask.  Its
semantics keeps the selected complete preactivations and sets all other
coordinates to zero.  The refinement theorem below compiles every such
program into the original one-channel expansive convolution/ReLU semantics
on a prescribed compact input set.  Compact carriers make all retained
coordinates positive; spatial biases cancel the old carrier exactly.
-/

namespace OneChannelCNNUniversality

/-- A finite sequence of linear convolutions followed by spatial masks. -/
inductive MaskProgram (kRows kCols : ℕ) : ℕ → ℕ → Type
  | nil (rows cols : ℕ) : MaskProgram kRows kCols rows cols
  | cons {rows cols : ℕ}
      (kernel : Kernel kRows kCols)
      (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
      (tail : MaskProgram kRows kCols
        (rows + kRows - 1) (cols + kCols - 1)) :
      MaskProgram kRows kCols rows cols

namespace MaskProgram

def outRows {kRows kCols rows cols : ℕ} :
    MaskProgram kRows kCols rows cols → ℕ
  | .nil rows _ => rows
  | .cons _ _ tail => tail.outRows

def outCols {kRows kCols rows cols : ℕ} :
    MaskProgram kRows kCols rows cols → ℕ
  | .nil _ cols => cols
  | .cons _ _ tail => tail.outCols

/-- Linear masked semantics, before compact carrier constants are added. -/
def eval {kRows kCols rows cols : ℕ} :
    (program : MaskProgram kRows kCols rows cols) →
      Image rows cols → Image program.outRows program.outCols
  | .nil _ _, x => x
  | .cons kernel keep tail, x =>
      tail.eval (fun p q ↦ if keep p q then fullConv kernel x p q else 0)

/-- Prepend `steps` copies of `kernel`, then one copy of `finalKernel`
carrying the only nontrivial mask, before continuing with `tail`. -/
def iterationsThenMask {kRows kCols : ℕ}
    (kernel finalKernel : Kernel kRows kCols) :
    (steps : ℕ) → {rows cols : ℕ} →
      (keep : Fin (grownSize kRows rows (steps + 1)) →
        Fin (grownSize kCols cols (steps + 1)) → Bool) →
      MaskProgram kRows kCols
        (grownSize kRows rows (steps + 1))
        (grownSize kCols cols (steps + 1)) →
      MaskProgram kRows kCols rows cols
  | 0, _, _, keep, tail => .cons finalKernel keep tail
  | steps + 1, _, _, keep, tail =>
      .cons kernel (fun _ _ ↦ true)
        (iterationsThenMask kernel finalKernel steps keep tail)

theorem eval_iterationsThenMask_heq {kRows kCols rows cols : ℕ}
    (kernel finalKernel : Kernel kRows kCols) (steps : ℕ)
    (keep : Fin (grownSize kRows rows (steps + 1)) →
      Fin (grownSize kCols cols (steps + 1)) → Bool)
    (tail : MaskProgram kRows kCols
      (grownSize kRows rows (steps + 1))
      (grownSize kCols cols (steps + 1)))
    (x : Image rows cols) :
    HEq ((iterationsThenMask kernel finalKernel steps keep tail).eval x)
      (tail.eval (fun p q ↦
        if keep p q then iterateThenConv kernel finalKernel steps x p q else 0)) := by
  induction steps generalizing rows cols with
  | zero => exact HEq.rfl
  | succ steps ih =>
      change HEq
        ((iterationsThenMask kernel finalKernel steps keep tail).eval
          (fullConvImage kernel x))
        (tail.eval (fun p q ↦ if keep p q then
          iterateThenConv kernel finalKernel steps
            (fullConvImage kernel x) p q else 0))
      exact ih keep tail (fullConvImage kernel x)

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ} (x : Image rows cols) :
    (nil (kRows := kRows) (kCols := kCols) rows cols).eval x = x := rfl

@[simp] theorem eval_cons {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (tail : MaskProgram kRows kCols
      (rows + kRows - 1) (cols + kCols - 1))
    (x : Image rows cols) :
    (cons kernel keep tail).eval x =
      tail.eval (fun p q ↦ if keep p q then fullConv kernel x p q else 0) := rfl

/-- Every symbolic masked-convolution program is implemented exactly by an
actual one-channel expansive ReLU CNN on the chosen compact set. -/
theorem exists_network {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ}
    (program : MaskProgram kRows kCols rows cols)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols program.outRows program.outCols)
      (carrier : Image program.outRows program.outCols),
      ∀ x ∈ K, net.eval (F x) = program.eval (V x) + carrier := by
  induction program with
  | nil rows cols =>
      exact ⟨NetworkTo.nil rows cols kRows kCols, known, hdecomp⟩
  | @cons rows cols kernel keep tail ih =>
      let keepProp : Fin (rows + kRows - 1) →
          Fin (cols + kCols - 1) → Prop :=
        fun p q ↦ keep p q = true
      obtain ⟨bias, nextCarrier, hpositive, hfirst⟩ :=
        exists_positive_linearized_masking_layer
          hK F V known hdecomp hV kernel keepProp
      let nextF : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x ↦ layerEval kernel bias (F x)
      let nextV : X → Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun x p q ↦ if keep p q then fullConv kernel (V x) p q else 0
      let nextKnown : Image (rows + kRows - 1) (cols + kCols - 1) :=
        fun p q ↦ if keep p q then nextCarrier p q else 0
      have hnextDecomp : ∀ x ∈ K, nextF x = nextV x + nextKnown := by
        intro x hx
        funext p q
        change layerEval kernel bias (F x) p q =
          (if keep p q then fullConv kernel (V x) p q else 0) +
            (if keep p q then nextCarrier p q else 0)
        rw [hfirst x hx p q]
        by_cases hpq : keep p q = true
        · simp [keepProp, hpq]
        · have hfalse : keep p q = false := Bool.eq_false_of_not_eq_true hpq
          simp [keepProp, hfalse]
      have hnextV : ContinuousFeatureOn K nextV := by
        intro p q
        by_cases hpq : keep p q = true
        · simpa [nextV, hpq] using continuousFeatureOn_fullConv hV kernel p q
        · have hfalse : keep p q = false := Bool.eq_false_of_not_eq_true hpq
          simpa [nextV, hfalse] using
            (continuousOn_const : ContinuousOn (fun _ : X ↦ (0 : ℝ)) K)
      obtain ⟨tailNet, finalCarrier, htail⟩ :=
        ih nextF nextV nextKnown hnextDecomp hnextV
      refine ⟨NetworkTo.cons kernel bias tailNet, finalCarrier, ?_⟩
      intro x hx
      rw [NetworkTo.eval_cons]
      exact htail x hx

end MaskProgram

/-- A masked-convolution program with explicit final dimensions. -/
structure MaskProgramTo (kRows kCols inRows inCols outRows outCols : ℕ) where
  program : MaskProgram kRows kCols inRows inCols
  rows_eq : program.outRows = outRows
  cols_eq : program.outCols = outCols

namespace MaskProgramTo

def eval {kRows kCols inRows inCols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) : Image outRows outCols :=
  fun i j ↦ program.program.eval x
    ⟨i, by simpa [program.rows_eq] using i.isLt⟩
    ⟨j, by simpa [program.cols_eq] using j.isLt⟩

def nil (rows cols kRows kCols : ℕ) :
    MaskProgramTo kRows kCols rows cols rows cols :=
  ⟨MaskProgram.nil rows cols, rfl, rfl⟩

def cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (tail : MaskProgramTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols) :
    MaskProgramTo kRows kCols rows cols outRows outCols :=
  ⟨MaskProgram.cons kernel keep tail.program, tail.rows_eq, tail.cols_eq⟩

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ} (x : Image rows cols) :
    (nil rows cols kRows kCols).eval x = x := by
  funext i j
  rfl

@[simp] theorem eval_cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (keep : Fin (rows + kRows - 1) → Fin (cols + kCols - 1) → Bool)
    (tail : MaskProgramTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols)
    (x : Image rows cols) :
    (cons kernel keep tail).eval x =
      tail.eval (fun p q ↦ if keep p q then fullConv kernel x p q else 0) := by
  funext i j
  rfl

/-- Typed version of `MaskProgram.iterationsThenMask`. -/
def iterationsThenMask {kRows kCols outRows outCols : ℕ}
    (kernel finalKernel : Kernel kRows kCols) :
    (steps : ℕ) → {rows cols : ℕ} →
      (keep : Fin (grownSize kRows rows (steps + 1)) →
        Fin (grownSize kCols cols (steps + 1)) → Bool) →
      MaskProgramTo kRows kCols
        (grownSize kRows rows (steps + 1))
        (grownSize kCols cols (steps + 1)) outRows outCols →
      MaskProgramTo kRows kCols rows cols outRows outCols
  | 0, _, _, keep, tail => cons finalKernel keep tail
  | steps + 1, _, _, keep, tail =>
      cons kernel (fun _ _ ↦ true)
        (iterationsThenMask kernel finalKernel steps keep tail)

theorem eval_iterationsThenMask {kRows kCols rows cols outRows outCols : ℕ}
    (kernel finalKernel : Kernel kRows kCols) (steps : ℕ)
    (keep : Fin (grownSize kRows rows (steps + 1)) →
      Fin (grownSize kCols cols (steps + 1)) → Bool)
    (tail : MaskProgramTo kRows kCols
      (grownSize kRows rows (steps + 1))
      (grownSize kCols cols (steps + 1)) outRows outCols)
    (x : Image rows cols) :
    (iterationsThenMask kernel finalKernel steps keep tail).eval x =
      tail.eval (fun p q ↦
        if keep p q then iterateThenConv kernel finalKernel steps x p q else 0) := by
  induction steps generalizing rows cols with
  | zero => rfl
  | succ steps ih =>
      change (iterationsThenMask kernel finalKernel steps keep tail).eval
          (fullConvImage kernel x) = _
      exact ih keep tail (fullConvImage kernel x)

/-- Typed programs compile to typed actual CNNs with the same explicit final
rectangle. -/
theorem exists_network {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols outRows outCols : ℕ}
    (program : MaskProgramTo kRows kCols rows cols outRows outCols)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols outRows outCols)
      (carrier : Image outRows outCols),
      ∀ x ∈ K, net.eval (F x) = program.eval (V x) + carrier := by
  rcases program with ⟨program, rowsEq, colsEq⟩
  subst outRows
  subst outCols
  obtain ⟨net, carrier, hnet⟩ :=
    program.exists_network hK F V known hdecomp hV
  refine ⟨net, carrier, ?_⟩
  intro x hx
  rw [hnet x hx]
  congr 1

end MaskProgramTo

end OneChannelCNNUniversality
