import OneChannelCNNUniversality.SharedBiasCausality

open OneChannelCNNUniversality

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (b : ℝ) (p q : ℕ) (x y : Image rows cols)
    (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (sharedLayerEval w b x) (sharedLayerEval w b y) p q := by
  exact northwestAgree_sharedLayerEval w b hxy

example {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    (p q : ℕ) (x y : Image rows cols)
    (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (net.eval x) (net.eval y) p q := by
  exact northwestAgree_sharedBiasNetwork_eval net hxy

example {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (p q : ℕ) (x y : Image inRows inCols)
    (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (net.eval x) (net.eval y) p q := by
  exact northwestAgree_sharedBiasNetworkTo_eval net hxy

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (steps p q : ℕ) (x y : Image rows cols)
    (hxy : NorthwestAgree x y p q) :
    NorthwestAgree (iterateFullConv w steps x)
      (iterateFullConv w steps y) p q := by
  exact northwestAgree_iterateFullConv w steps hxy

example {rows cols : ℕ} (rowSteps extraColSteps : ℕ)
    (x y : Image rows cols) (i : Fin rows) (j : Fin cols)
    (hxy : NorthwestAgree x y i j) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x i j =
      protectedLinearizedPascalSignal rowSteps extraColSteps y i j := by
  exact protectedLinearizedPascalSignal_eq_of_northwestAgree
    rowSteps extraColSteps i j hxy
