import OneChannelCNNUniversality.SharedBiasLocalGateSchedule

open OneChannelCNNUniversality

#check weightedMixGateNetwork_gate_at
#check SignedLocalAffineGate
#check SignedLocalAffineGate.eval
#check evalSignedLocalAffineGateSchedule
#check evalSignedLocalAffineGateSchedule_congr_prefix
#check evalSignedLocalAffineGateSchedule_congr_receptiveField
#check exists_weightedMixGateSchedule_on_compact

example (gate : SignedLocalAffineGate) (state : ℕ → ℝ) (j : ℕ) :
    gate.eval state j =
      relu (gate.slope *
        (state j + if 1 ≤ j then gate.westWeight * state (j - 1) else 0) +
        gate.offset) := by
  rfl
