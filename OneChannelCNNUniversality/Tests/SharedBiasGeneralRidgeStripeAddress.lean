import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeAddress

/-! # Regression tests for the complementary signed-stripe address -/

namespace OneChannelCNNUniversality

#check generalRidgeStripeSeedAddressImage
#check generalRidgeStripeFinalLocalAddressImage
#check generalRidgeStripeTarget
#check generalRidgeStripeFinalLocalAddress_row_one_nonneg_gap
#check generalRidgeStripeTwoCarrier_gap

/-- The smallest stripe instance has target `(1,2)` in a `4 × 5` output. -/
example : generalRidgeStripeTarget 0 =
    ((1, 2) : Fin 4 × Fin 5) := rfl

end OneChannelCNNUniversality
