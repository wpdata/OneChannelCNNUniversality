import OneChannelCNNUniversality.SharedBiasGridGateSchedule

open OneChannelCNNUniversality

#check SignedAffineGate
#check SignedAffineGate.eval
#check evalSignedAffineGateSchedule
#check exists_protectedGridGateSchedule_on_compact

example (x a₁ c₁ a₂ c₂ : ℝ) :
    evalSignedAffineGateSchedule
        [⟨a₁, c₁⟩, ⟨a₂, c₂⟩] x =
      relu (a₂ * relu (a₁ * x + c₁) + c₂) := by
  rfl
