import ICM2022NumCS97.Basic

open ICM2022NumCS97

example (x : Image 1 1) (w : Kernel 2 2) :
    fullConv w x 0 0 = w 0 0 * x 0 0 := by
  simp [fullConv]
