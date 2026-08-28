import Mathlib

/-!
# Exact semantics for expansive one-channel convolutional networks

This file fixes the indexing convention used throughout the formalization.
Arrays are finite rectangular functions.  `fullConv` is discrete convolution
after zero extension: the output coordinate `(p,q)` reads the input coordinate
`(p-a,q-b)` from kernel coordinate `(a,b)`, and a term is zero if subtraction
would leave `ℕ` or if the resulting input coordinate is outside its rectangle.
-/

namespace ICM2022NumCS97

/-- A finite real rectangular array. -/
abbrev Image (rows cols : ℕ) := Fin rows → Fin cols → ℝ

/-- A convolution kernel; kept as a distinct name to document its role. -/
abbrev Kernel (rows cols : ℕ) := Fin rows → Fin cols → ℝ

/-- Entrywise ReLU on the real numbers. -/
def relu (x : ℝ) : ℝ := max x 0

@[simp] theorem relu_eq_max (x : ℝ) : relu x = max x 0 := rfl

@[simp] theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := by
  simp [relu, hx]

@[simp] theorem relu_of_nonpos {x : ℝ} (hx : x ≤ 0) : relu x = 0 := by
  simp [relu, hx]

/-- Zero extension of a finite image to natural coordinates. -/
def zeroExtend {rows cols : ℕ} (x : Image rows cols) (i j : ℕ) : ℝ :=
  if hi : i < rows then
    if hj : j < cols then x ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

@[simp] theorem zeroExtend_inside {rows cols : ℕ} (x : Image rows cols)
    (i : Fin rows) (j : Fin cols) : zeroExtend x i j = x i j := by
  simp [zeroExtend, i.isLt, j.isLt]

@[simp] theorem zeroExtend_of_lt {rows cols : ℕ} (x : Image rows cols)
    {i j : ℕ} (hi : i < rows) (hj : j < cols) :
    zeroExtend x i j = x ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [zeroExtend, hi, hj]

@[simp] theorem zeroExtend_row_outside {rows cols : ℕ} (x : Image rows cols)
    {i j : ℕ} (hi : rows ≤ i) : zeroExtend x i j = 0 := by
  simp [zeroExtend, Nat.not_lt.mpr hi]

@[simp] theorem zeroExtend_col_outside {rows cols : ℕ} (x : Image rows cols)
    {i j : ℕ} (hj : cols ≤ j) : zeroExtend x i j = 0 := by
  by_cases hi : i < rows
  · simp [zeroExtend, hi, Nat.not_lt.mpr hj]
  · simp [zeroExtend, hi]

@[simp] theorem zeroExtend_add {rows cols : ℕ} (x y : Image rows cols) (i j : ℕ) :
    zeroExtend (x + y) i j = zeroExtend x i j + zeroExtend y i j := by
  by_cases hi : i < rows
  · by_cases hj : j < cols <;> simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

@[simp] theorem zeroExtend_zero {rows cols : ℕ} (i j : ℕ) :
    zeroExtend (0 : Image rows cols) i j = 0 := by
  by_cases hi : i < rows
  · by_cases hj : j < cols <;> simp [zeroExtend, hi, hj]
  · simp [zeroExtend, hi]

/-- Full zero-extended two-dimensional discrete convolution at a natural site. -/
def fullConv {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols) (p q : ℕ) : ℝ :=
  ∑ a : Fin kRows, ∑ b : Fin kCols,
    if (a : ℕ) ≤ p ∧ (b : ℕ) ≤ q then
      w a b * zeroExtend x (p - a) (q - b)
    else 0

/-- The rectangular image produced by full convolution. -/
def fullConvImage {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x : Image rows cols) :
    Image (rows + kRows - 1) (cols + kCols - 1) :=
  fun p q ↦ fullConv w x p q

theorem fullConv_add {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (x y : Image rows cols) (p q : ℕ) :
    fullConv w (x + y) p q = fullConv w x p q + fullConv w y p q := by
  classical
  simp only [fullConv, zeroExtend_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

@[simp] theorem fullConv_zero {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (p q : ℕ) :
    fullConv w (0 : Image rows cols) p q = 0 := by
  simp [fullConv]

/-- One exact expansive convolution/ReLU layer with an arbitrary spatial bias. -/
def layerEval {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    (x : Image rows cols) :
    Image (rows + kRows - 1) (cols + kCols - 1) :=
  fun p q ↦ relu (fullConv w x p q + bias p q)

/-- A finite sequence of fixed-kernel-size, one-channel expansive layers. -/
inductive Network (kRows kCols : ℕ) : ℕ → ℕ → Type
  | nil (rows cols : ℕ) : Network kRows kCols rows cols
  | cons {rows cols : ℕ}
      (kernel : Kernel kRows kCols)
      (bias : Image (rows + kRows - 1) (cols + kCols - 1))
      (tail : Network kRows kCols (rows + kRows - 1) (cols + kCols - 1)) :
      Network kRows kCols rows cols

namespace Network

/-- Number of layers. -/
def depth {kRows kCols rows cols : ℕ} : Network kRows kCols rows cols → ℕ
  | .nil _ _ => 0
  | .cons _ _ tail => tail.depth + 1

/-- Row count of the final feature image. -/
def outRows {kRows kCols rows cols : ℕ} : Network kRows kCols rows cols → ℕ
  | .nil r _ => r
  | .cons _ _ tail => tail.outRows

/-- Column count of the final feature image. -/
def outCols {kRows kCols rows cols : ℕ} : Network kRows kCols rows cols → ℕ
  | .nil _ c => c
  | .cons _ _ tail => tail.outCols

/-- Exact evaluation of all hidden layers. -/
def eval {kRows kCols rows cols : ℕ} :
    (net : Network kRows kCols rows cols) →
      Image rows cols → Image net.outRows net.outCols
  | .nil _ _, x => x
  | .cons kernel bias tail, x => tail.eval (layerEval kernel bias x)

/-- Arbitrary affine readout of the last single-channel feature image. -/
def realize {kRows kCols rows cols : ℕ}
    (net : Network kRows kCols rows cols)
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (x : Image rows cols) : ℝ :=
  (∑ i, ∑ j, weight i j * net.eval x i j) + constant

/-- Sequential composition of two exact networks. -/
noncomputable def append {kRows kCols rows cols : ℕ} :
    (first : Network kRows kCols rows cols) →
      Network kRows kCols first.outRows first.outCols →
        Network kRows kCols rows cols
  | .nil _ _, second => second
  | .cons kernel bias tail, second => .cons kernel bias (append tail second)

@[simp] theorem outRows_append {kRows kCols rows cols : ℕ}
    (first : Network kRows kCols rows cols)
    (second : Network kRows kCols first.outRows first.outCols) :
    (first.append second).outRows = second.outRows := by
  induction first with
  | nil => rfl
  | cons kernel bias tail ih => exact ih second

@[simp] theorem outCols_append {kRows kCols rows cols : ℕ}
    (first : Network kRows kCols rows cols)
    (second : Network kRows kCols first.outRows first.outCols) :
    (first.append second).outCols = second.outCols := by
  induction first with
  | nil => rfl
  | cons kernel bias tail ih => exact ih second

theorem eval_append_heq {kRows kCols rows cols : ℕ}
    (first : Network kRows kCols rows cols)
    (second : Network kRows kCols first.outRows first.outCols)
    (x : Image rows cols) :
    HEq ((first.append second).eval x) (second.eval (first.eval x)) := by
  induction first with
  | nil => rfl
  | cons kernel bias tail ih => exact ih second (layerEval kernel bias x)

/-- A network consisting of exactly one expansive convolution/ReLU layer. -/
def single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1)) :
    Network kRows kCols rows cols :=
  .cons kernel bias (.nil _ _)

@[simp] theorem eval_single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    (x : Image rows cols) :
    (single kernel bias).eval x = layerEval kernel bias x := rfl

end Network

/-- A network bundled with explicit final dimensions.  This wrapper removes
dependent casts from recursive construction proofs while retaining the exact
`Network` semantics underneath. -/
structure NetworkTo (kRows kCols inRows inCols outRows outCols : ℕ) where
  net : Network kRows kCols inRows inCols
  rows_eq : net.outRows = outRows
  cols_eq : net.outCols = outCols

namespace NetworkTo

/-- Evaluation reindexed to the explicit output rectangle. -/
def eval {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : NetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) : Image outRows outCols :=
  fun i j ↦ net.net.eval x
    ⟨i, by simpa [net.rows_eq] using i.isLt⟩
    ⟨j, by simpa [net.cols_eq] using j.isLt⟩

/-- The depth-zero typed network. -/
def nil (rows cols kRows kCols : ℕ) :
    NetworkTo kRows kCols rows cols rows cols :=
  ⟨Network.nil rows cols, rfl, rfl⟩

/-- Prepend one actual convolution/ReLU layer to a typed tail network. -/
def cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    (tail : NetworkTo kRows kCols (rows + kRows - 1) (cols + kCols - 1)
      outRows outCols) :
    NetworkTo kRows kCols rows cols outRows outCols :=
  ⟨Network.cons kernel bias tail.net, tail.rows_eq, tail.cols_eq⟩

def single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1)) :
    NetworkTo kRows kCols rows cols
      (rows + kRows - 1) (cols + kCols - 1) :=
  cons kernel bias (nil _ _ kRows kCols)

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ} (x : Image rows cols) :
    (nil rows cols kRows kCols).eval x = x := by
  funext i j
  rfl

@[simp] theorem eval_cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    (tail : NetworkTo kRows kCols (rows + kRows - 1) (cols + kCols - 1)
      outRows outCols) (x : Image rows cols) :
    (cons kernel bias tail).eval x = tail.eval (layerEval kernel bias x) := by
  funext i j
  rfl

@[simp] theorem eval_single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols)
    (bias : Image (rows + kRows - 1) (cols + kCols - 1))
    (x : Image rows cols) :
    (single kernel bias).eval x = layerEval kernel bias x := by
  rw [single, eval_cons, eval_nil]

/-- Affine readout of a typed network. -/
def realize {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : NetworkTo kRows kCols inRows inCols outRows outCols)
    (weight : Image outRows outCols) (constant : ℝ)
    (x : Image inRows inCols) : ℝ :=
  (∑ i, ∑ j, weight i j * net.eval x i j) + constant

end NetworkTo

@[simp] theorem fullConv_zero_zero {kRows kCols rows cols : ℕ}
    [NeZero kRows] [NeZero kCols]
    (w : Kernel kRows kCols) (x : Image rows cols) :
    fullConv w x 0 0 = w ⟨0, Nat.pos_of_ne_zero (NeZero.ne kRows)⟩
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne kCols)⟩ * zeroExtend x 0 0 := by
  classical
  simp only [fullConv, Nat.le_zero]
  rw [Fintype.sum_eq_single (0 : Fin kRows)]
  · rw [Fintype.sum_eq_single (0 : Fin kCols)]
    · simp
    · intro b hb
      simp [hb]
  · intro a ha
    simp [ha]

end ICM2022NumCS97
