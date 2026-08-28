import OneChannelCNNUniversality.SharedBiasGeometry

open OneChannelCNNUniversality

variable {rows cols : ℕ} {c : ℝ}

-- A zero kernel plus shared bias creates a constant positive rectangle.
example (hc : 0 ≤ c) (x : Image rows cols) :
    sharedLayerEval (0 : Kernel 2 2) c x = constantImage _ _ c := by
  exact constant_seed hc x

-- Horizontal differencing retains exactly the positive left boundary.
example (hc : 0 < c) :
    horizontalBoundarySignal rows cols c = expectedLeftBoundary rows cols c := by
  exact horizontal_boundary_signal hc

-- Vertical differencing of that boundary retains exactly its northwest corner.
example (hc : 0 < c) :
    cornerSeed rows cols c = expectedNorthwestCorner rows cols c := by
  exact corner_seed_signal hc
