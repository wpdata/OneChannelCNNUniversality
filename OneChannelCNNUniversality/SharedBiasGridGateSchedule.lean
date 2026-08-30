import OneChannelCNNUniversality.SharedBiasGridGateComposition

/-!
# Arbitrary finite schedules of protected grid gates

Compactness and injectivity can be propagated through any finite list of
signed affine ReLU gates.  Each list entry contributes one protected depth-two
grid block.  The northern row evaluates the nested scalar gate schedule
pointwise, while the complete one-channel feature image remains injective.
-/

namespace OneChannelCNNUniversality

universe u

/-- The signed affine parameters of one scalar ReLU gate. -/
structure SignedAffineGate where
  slope : ℝ
  offset : ℝ

namespace SignedAffineGate

/-- Scalar evaluation of one signed affine ReLU gate. -/
def eval (gate : SignedAffineGate) (x : ℝ) : ℝ :=
  relu (gate.slope * x + gate.offset)

end SignedAffineGate

/-- Apply the head gate first and continue through the finite schedule. -/
def evalSignedAffineGateSchedule : List SignedAffineGate → ℝ → ℝ
  | [], x => x
  | gate :: schedule, x =>
      evalSignedAffineGateSchedule schedule (gate.eval x)

/-- Every finite signed affine ReLU schedule has a genuine expansive
one-channel shared-bias CNN implementation on a compact continuous image
family.  It uses exactly two layers per scalar gate, computes the nested
schedule pointwise on the original northern row, and preserves injectivity
of the complete representation. -/
theorem exists_protectedGridGateSchedule_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (schedule : List SignedAffineGate) :
    ∃ net : SharedBiasNetwork 2 2 rows cols,
      net.depth = 2 * schedule.length ∧
      (∀ x ∈ K, ∀ j : Fin cols,
        zeroExtend (net.eval (F x)) 0 j =
          evalSignedAffineGateSchedule schedule
            (zeroExtend (F x) 0 j)) ∧
      Set.InjOn (fun x ↦ net.eval (F x)) K := by
  induction schedule generalizing rows cols with
  | nil =>
      refine ⟨SharedBiasNetwork.nil rows cols, ?_, ?_, ?_⟩
      · rfl
      · intro x hx j
        rfl
      · exact hFinjective
  | cons gate schedule ih =>
      obtain ⟨M, hM, hbound⟩ :=
        exists_uniform_feature_margin hK F hF 0
      let first : SharedBiasNetworkTo 2 2 rows cols
          (rows + 2) (cols + 2) :=
        protectedGridGateNetwork gate.slope gate.offset M
      let G : X → Image (rows + 2) (cols + 2) :=
        fun x ↦ first.eval (F x)
      have hG : ContinuousFeatureOn K G := by
        exact first.continuousFeatureOn_eval F hF
      have hGinjective : Set.InjOn G K := by
        exact protectedGridGateNetwork_injectiveOn
          F gate.slope gate.offset M hM.le
          (fun x hx i j ↦ by
            have := hbound x hx i j
            simpa using this.le)
          hFinjective
      obtain ⟨tail, htailDepth, htailGate, htailInjective⟩ :=
        ih G hG hGinjective
      let net : SharedBiasNetwork 2 2 rows cols :=
        .cons expansiveIdentityKernel
          (protectedGridGateCarrier gate.slope gate.offset M)
          (.cons (protectedRowGateKernel gate.slope)
            (gate.offset - gate.slope *
              protectedGridGateCarrier gate.slope gate.offset M)
            tail)
      refine ⟨net, ?_, ?_, ?_⟩
      · change tail.depth + 1 + 1 = 2 * (schedule.length + 1)
        rw [htailDepth]
        omega
      · intro x hx j
        change zeroExtend (tail.eval (G x)) 0 j = _
        rw [htailGate x hx (⟨j, by omega⟩ : Fin (cols + 2))]
        change evalSignedAffineGateSchedule schedule
          (zeroExtend (first.eval (F x)) 0 j) = _
        rw [protectedGridGateNetwork_gate
          (F x) gate.slope gate.offset M hM.le
          (fun i j ↦ by
            have := hbound x hx i j
            simpa using this.le) j]
        rfl
      · change Set.InjOn (fun x ↦ tail.eval (G x)) K
        exact htailInjective

end OneChannelCNNUniversality
