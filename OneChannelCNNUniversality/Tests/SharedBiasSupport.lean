import OneChannelCNNUniversality.SharedBiasSupport

open OneChannelCNNUniversality

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (fullConvImage w x) (fullConvImage w y) r s := by
  exact agreeOutsideSoutheast_fullConvImage w hxy

example {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols) (b : ℝ)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (sharedLayerEval w b x) (sharedLayerEval w b y) r s := by
  exact agreeOutsideSoutheast_sharedLayerEval w b hxy

example {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (net.eval x) (net.eval y) r s := by
  exact agreeOutsideSoutheast_sharedBiasNetwork_eval net hxy

example {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} {r s : ℕ}
    (hxy : AgreeOutsideSoutheast x y r s) :
    AgreeOutsideSoutheast (net.eval x) (net.eval y) r s := by
  exact agreeOutsideSoutheast_sharedBiasNetworkTo_eval net hxy

example {rows cols : ℕ} {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    NorthwestAgree x y r s := by
  exact hxy.northwestAgree

example {kRows kCols rows cols : ℕ}
    (net : SharedBiasNetwork kRows kCols rows cols)
    {x y : Image rows cols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast (net.eval x) (net.eval y) r s := by
  exact agreeOutsideStrictSoutheast_sharedBiasNetwork_eval net hxy

example {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    {x y : Image inRows inCols} {r s : ℕ}
    (hxy : AgreeOutsideStrictSoutheast x y r s) :
    AgreeOutsideStrictSoutheast (net.eval x) (net.eval y) r s := by
  exact agreeOutsideStrictSoutheast_sharedBiasNetworkTo_eval net hxy
