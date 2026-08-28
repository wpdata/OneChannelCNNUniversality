import OneChannelCNNUniversality.Basic

/-!
# Shared scalar biases

This module defines the exact subclass in which every hidden layer has one
scalar bias, broadcast over all spatial positions.  It also embeds that class
into the existing position-dependent-bias semantics without changing its
evaluation.
-/

namespace OneChannelCNNUniversality

/-- The rectangular image whose entries all equal `b`. -/
def constantImage (rows cols : ℕ) (b : ℝ) : Image rows cols :=
  fun _ _ ↦ b

/-- One expansive convolution/ReLU layer with a scalar spatially shared bias. -/
def sharedLayerEval {kRows kCols rows cols : ℕ}
    (w : Kernel kRows kCols) (b : ℝ) (x : Image rows cols) :
    Image (rows + kRows - 1) (cols + kCols - 1) :=
  layerEval w (constantImage _ _ b) x

/-- A finite sequence of one-channel expansive layers with one scalar bias per layer. -/
inductive SharedBiasNetwork (kRows kCols : ℕ) : ℕ → ℕ → Type
  | nil (rows cols : ℕ) : SharedBiasNetwork kRows kCols rows cols
  | cons {rows cols : ℕ}
      (kernel : Kernel kRows kCols)
      (bias : ℝ)
      (tail : SharedBiasNetwork kRows kCols
        (rows + kRows - 1) (cols + kCols - 1)) :
      SharedBiasNetwork kRows kCols rows cols

namespace SharedBiasNetwork

/-- Regard a shared-bias network as a position-dependent-bias network. -/
def toNetwork : (net : SharedBiasNetwork kRows kCols rows cols) →
    Network kRows kCols rows cols
  | .nil r c => .nil r c
  | .cons kernel bias tail =>
      .cons kernel (constantImage _ _ bias) tail.toNetwork

/-- Number of hidden layers. -/
def depth : SharedBiasNetwork kRows kCols rows cols → ℕ
  | .nil _ _ => 0
  | .cons _ _ tail => tail.depth + 1

/-- Row count of the final feature image. -/
def outRows (net : SharedBiasNetwork kRows kCols rows cols) : ℕ :=
  net.toNetwork.outRows

/-- Column count of the final feature image. -/
def outCols (net : SharedBiasNetwork kRows kCols rows cols) : ℕ :=
  net.toNetwork.outCols

/-- Exact evaluation of all shared-bias hidden layers. -/
def eval (net : SharedBiasNetwork kRows kCols rows cols)
    (x : Image rows cols) : Image net.outRows net.outCols :=
  net.toNetwork.eval x

/-- Arbitrary affine readout of the final one-channel feature image. -/
def realize (net : SharedBiasNetwork kRows kCols rows cols)
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (x : Image rows cols) : ℝ :=
  (∑ i, ∑ j, weight i j * net.eval x i j) + constant

/-- A shared-bias network consisting of exactly one layer. -/
def single (kernel : Kernel kRows kCols) (bias : ℝ) :
    SharedBiasNetwork kRows kCols rows cols :=
  .cons kernel bias (.nil _ _)

/-- Embedding into the general semantics preserves the final feature image exactly. -/
@[simp] theorem eval_toNetwork
    (net : SharedBiasNetwork kRows kCols rows cols)
    (x : Image rows cols) : net.toNetwork.eval x = net.eval x := rfl

/-- The embedding preserves the final row dimension definitionally. -/
@[simp] theorem outRows_toNetwork
    (net : SharedBiasNetwork kRows kCols rows cols) :
    net.toNetwork.outRows = net.outRows := rfl

/-- The embedding preserves the final column dimension definitionally. -/
@[simp] theorem outCols_toNetwork
    (net : SharedBiasNetwork kRows kCols rows cols) :
    net.toNetwork.outCols = net.outCols := rfl

/-- The embedding preserves every affine readout exactly. -/
@[simp] theorem realize_toNetwork
    (net : SharedBiasNetwork kRows kCols rows cols)
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (x : Image rows cols) :
    net.toNetwork.realize weight constant x = net.realize weight constant x := rfl

end SharedBiasNetwork

/-- A shared-bias network bundled with explicit final dimensions.  This is
the scalar-bias analogue of `NetworkTo` and keeps recursive constructions
free of dependent casts. -/
structure SharedBiasNetworkTo
    (kRows kCols inRows inCols outRows outCols : ℕ) where
  net : SharedBiasNetwork kRows kCols inRows inCols
  rows_eq : net.outRows = outRows
  cols_eq : net.outCols = outCols

namespace SharedBiasNetworkTo

/-- Evaluation reindexed to the explicit output rectangle. -/
def eval {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) : Image outRows outCols :=
  fun i j ↦ net.net.eval x
    ⟨i, by simpa [net.rows_eq] using i.isLt⟩
    ⟨j, by simpa [net.cols_eq] using j.isLt⟩

/-- The depth-zero explicitly typed shared-bias network. -/
def nil (rows cols kRows kCols : ℕ) :
    SharedBiasNetworkTo kRows kCols rows cols rows cols :=
  ⟨SharedBiasNetwork.nil rows cols, rfl, rfl⟩

/-- Prepend one genuine scalar-bias convolution/ReLU layer. -/
def cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols) (bias : ℝ)
    (tail : SharedBiasNetworkTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols) :
    SharedBiasNetworkTo kRows kCols rows cols outRows outCols :=
  ⟨SharedBiasNetwork.cons kernel bias tail.net, tail.rows_eq, tail.cols_eq⟩

/-- A single explicitly typed shared-bias layer. -/
def single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols) (bias : ℝ) :
    SharedBiasNetworkTo kRows kCols rows cols
      (rows + kRows - 1) (cols + kCols - 1) :=
  cons kernel bias (nil _ _ kRows kCols)

@[simp] theorem eval_nil {kRows kCols rows cols : ℕ}
    (x : Image rows cols) :
    (nil rows cols kRows kCols).eval x = x := by
  funext i j
  rfl

@[simp] theorem eval_cons {kRows kCols rows cols outRows outCols : ℕ}
    (kernel : Kernel kRows kCols) (bias : ℝ)
    (tail : SharedBiasNetworkTo kRows kCols
      (rows + kRows - 1) (cols + kCols - 1) outRows outCols)
    (x : Image rows cols) :
    (cons kernel bias tail).eval x = tail.eval (sharedLayerEval kernel bias x) := by
  funext i j
  rfl

@[simp] theorem eval_single {kRows kCols rows cols : ℕ}
    (kernel : Kernel kRows kCols) (bias : ℝ) (x : Image rows cols) :
    (single kernel bias).eval x = sharedLayerEval kernel bias x := by
  rw [single, eval_cons, eval_nil]

end SharedBiasNetworkTo
end OneChannelCNNUniversality
