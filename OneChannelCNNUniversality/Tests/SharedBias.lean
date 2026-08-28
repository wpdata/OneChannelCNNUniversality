import OneChannelCNNUniversality.SharedBias

open OneChannelCNNUniversality

example (b : ℝ) : constantImage 2 3 b 0 0 = b := rfl

example (w : Kernel 2 2) (b : ℝ) (x : Image 1 1) :
    (SharedBiasNetwork.single w b).eval x = sharedLayerEval w b x := rfl

example (net : SharedBiasNetwork 2 2 1 1) (x : Image 1 1) :
    net.toNetwork.eval x = net.eval x := by
  exact net.eval_toNetwork x

example (net : SharedBiasNetwork 2 2 1 1)
    (weight : Image net.outRows net.outCols) (constant : ℝ)
    (x : Image 1 1) :
    net.toNetwork.realize weight constant x = net.realize weight constant x := by
  exact net.realize_toNetwork weight constant x
