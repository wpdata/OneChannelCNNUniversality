import OneChannelCNNUniversality.SharedBiasHeterogeneousCarrier

/-!
# Regression tests for heterogeneous compact carrier networks
-/

namespace OneChannelCNNUniversality

#check exists_shared_bias_bilinear_carrier
#check continuousFeatureOn_fullConvChain
#check fullConvChain_append
#check zeroExtend_fullConvChain_append
#check exists_shared_bias_carrier_layer_with_boost
#check exists_shared_bias_bilinear_prefix_with_terminal_boost
#check exists_sharedBias_select_from_unit_address_on

example {rows cols : ℕ} (x : Image rows cols) :
    fullConvChain [] x = x := by
  rfl

end OneChannelCNNUniversality
