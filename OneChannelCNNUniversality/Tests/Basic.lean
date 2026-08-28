import OneChannelCNNUniversality.Basic

open OneChannelCNNUniversality

example (x : Image 1 1) (w : Kernel 2 2) :
    fullConv w x 0 0 = w 0 0 * x 0 0 := by
  simp [fullConv]
