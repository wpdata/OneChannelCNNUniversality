import OneChannelCNNUniversality.SharedBiasFrontier

open OneChannelCNNUniversality

example {kRows kCols inRows inCols outRows outCols : ℕ}
    (net : SharedBiasNetworkTo kRows kCols
      inRows inCols outRows outCols)
    {x y : Image inRows inCols}
    (hroot : zeroExtend x 0 0 = zeroExtend y 0 0) :
    zeroExtend (net.eval x) 0 0 = zeroExtend (net.eval y) 0 0 := by
  exact northwestOutput_eq_of_inputRoot_eq net hroot

example {rows cols : ℕ} (hcols : 0 < cols)
    (θ : ℝ) (x : Image rows cols) :
    zeroExtend ((eastFrontierLayer (rows := rows) (cols := cols) θ).eval x)
        0 1 =
      relu (zeroExtend x 0 0 + zeroExtend x 0 1 + θ) := by
  exact eastFrontierLayer_east_eval hcols θ x

#check NorthwestRealizesOn.eq_of_inputRoot_eq
#check not_exists_northwestRealization_of_root_eq_target_ne
#check eastFrontierLayer_injectiveOn_and_east_add
