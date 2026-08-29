import OneChannelCNNUniversality.SharedBiasSeedTransport

open OneChannelCNNUniversality

example {rows cols : ℕ} {x y z : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast (x + z) (y + z) r s := by
  exact hxy.add_right z

example {rows cols : ℕ} (c : ℝ) :
    SharedBiasNetworkTo 2 2 rows cols
      (rows + 2 - 1) (cols + 2 - 1) :=
  sharedBiasSeedLayer c

example {rows cols : ℕ} {x : Image rows cols} {c : ℝ}
    (hx : ImageNonnegative x) (hc : 0 ≤ c) :
    (sharedBiasSeedLayer c).eval x =
      fullConvImage expansiveIdentityKernel x +
        constantImage (rows + 2 - 1) (cols + 2 - 1) c := by
  exact sharedBiasSeedLayer_eval_of_nonnegative hx hc

example {rows cols : ℕ} {x : Image rows cols} {c : ℝ}
    (hx : ImageNonnegative x) (hc : 0 ≤ c)
    (i : Fin rows) (j : Fin cols) :
    (sharedBiasSeedLayer c).eval x
      (⟨i, by omega⟩ : Fin (rows + 2 - 1))
      (⟨j, by omega⟩ : Fin (cols + 2 - 1)) = x i j + c := by
  exact sharedBiasSeedLayer_original hx hc i j

example {X : Type*} [TopologicalSpace X] {K : Set X}
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) {c : ℝ} :
    ContinuousFeatureOn K (fun x ↦ (sharedBiasSeedLayer c).eval (F x)) := by
  exact SharedBiasNetworkTo.continuousFeatureOn_eval
    (sharedBiasSeedLayer c) F hF

example {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    (x : Image rows cols) (hx : ImageNonnegative x) :
    ImageNonnegative (net.eval x) := by
  exact net.eval_nonnegative_of_nonnegative_input x hx

example {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols
      inRows inCols outRows outCols)
    (x : Image inRows inCols) (hdepth : 0 < net.net.depth) :
    ImageNonnegative (net.eval x) := by
  exact net.eval_nonnegative_of_pos_depth x hdepth

example {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols)
    (c : ℝ) :
    SharedBiasNetworkTo 2 2 inRows inCols outRows outCols :=
  head.appendWithSeed c tail

example {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols)
    {x : Image inRows inCols} {c : ℝ}
    (hx : ImageNonnegative (head.eval x)) (hc : 0 ≤ c) :
    (head.appendWithSeed c tail).eval x =
      tail.eval
        (fullConvImage expansiveIdentityKernel (head.eval x) +
          constantImage (midRows + 2 - 1) (midCols + 2 - 1) c) := by
  exact SharedBiasNetworkTo.eval_appendWithSeed_of_nonnegative
    head tail hx hc

example {inRows inCols midRows midCols outRows outCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1) outRows outCols)
    (c : ℝ) :
    (head.appendWithSeed c tail).net.depth =
      head.net.depth + 1 + tail.net.depth := by
  exact SharedBiasNetworkTo.depth_appendWithSeed head c tail
