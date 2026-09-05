import OneChannelCNNUniversality.SharedBiasNondestructiveCarrier

/-! # Regression tests for lossless nonuniform carrier generation -/

namespace OneChannelCNNUniversality

#check horizontalSharedCarrier_nonuniform
#check nondestructiveBoundaryTransform
#check nondestructiveBoundaryTransform_injective
#check exists_depthTwo_nondestructive_nonuniform_carrier_on_compact

#print axioms horizontalSharedCarrier_nonuniform
#print axioms nondestructiveBoundaryTransform_injective
#print axioms exists_depthTwo_nondestructive_nonuniform_carrier_on_compact

/-- A concrete compact-domain certificate: on `[-1,1]²`, an exact-depth-two
network generates a fixed nonuniform carrier while remaining injective. -/
example :
    ∃ (net : SharedBiasNetworkTo 2 2 1 2
          ((1 + 2 - 1) + 2 - 1) ((2 + 2 - 1) + 2 - 1))
      (carrier : Image ((1 + 2 - 1) + 2 - 1) ((2 + 2 - 1) + 2 - 1)),
      net.net.depth = 2 ∧ SpatiallyNonuniform carrier ∧
        (∀ x ∈ twoPointSymmetricBox 1,
          ∃ signal, net.eval x = signal + carrier) ∧
        Set.InjOn (fun x ↦ net.eval x) (twoPointSymmetricBox 1) := by
  obtain ⟨net, c, b, carrier, _hc, _hb, hdepth, _hcarrier,
      hnonuniform, heval, hinjective⟩ :=
    exists_depthTwo_nondestructive_nonuniform_carrier_on_compact
      (twoPointSymmetricBox 1) (twoPointSymmetricBox_compact 1) (by norm_num)
  refine ⟨net, carrier, hdepth, hnonuniform, ?_, hinjective⟩
  intro x hx
  exact ⟨nondestructiveBoundaryTransform x, heval x hx⟩

end OneChannelCNNUniversality
