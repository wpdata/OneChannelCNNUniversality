import OneChannelCNNUniversality.SharedBiasAffineMixGate

/-!
# Finite schedules of signed local affine gates

Each schedule entry mixes every northern-row register with its western
predecessor and then applies a signed affine ReLU.  Compactness chooses fresh
shared carriers at every stage.  The compiled genuine one-channel CNN has
exact depth three times the schedule length and keeps its complete feature
representation injective.
-/

namespace OneChannelCNNUniversality

universe u

/-- Parameters of one spatially shared local affine ReLU gate. -/
structure SignedLocalAffineGate where
  westWeight : ℝ
  slope : ℝ
  offset : ℝ

namespace SignedLocalAffineGate

/-- Evaluate one local gate on a natural-indexed row with a zero western
boundary. -/
def eval (gate : SignedLocalAffineGate) (state : ℕ → ℝ) (j : ℕ) : ℝ :=
  relu (gate.slope *
    (state j + if 1 ≤ j then gate.westWeight * state (j - 1) else 0) +
    gate.offset)

end SignedLocalAffineGate

/-- Apply the head local gate first and continue through the finite schedule. -/
def evalSignedLocalAffineGateSchedule :
    List SignedLocalAffineGate → (ℕ → ℝ) → ℕ → ℝ
  | [], state => state
  | gate :: schedule, state =>
      evalSignedLocalAffineGateSchedule schedule (gate.eval state)

/-- A local-gate schedule at coordinate `j` depends only on the input prefix
through `j`. -/
theorem evalSignedLocalAffineGateSchedule_congr_prefix
    (schedule : List SignedLocalAffineGate) {state other : ℕ → ℝ} {j : ℕ}
    (hagree : ∀ q, q ≤ j → state q = other q) :
    evalSignedLocalAffineGateSchedule schedule state j =
      evalSignedLocalAffineGateSchedule schedule other j := by
  induction schedule generalizing state other with
  | nil =>
      exact hagree j le_rfl
  | cons gate schedule ih =>
      change evalSignedLocalAffineGateSchedule schedule (gate.eval state) j =
        evalSignedLocalAffineGateSchedule schedule (gate.eval other) j
      apply ih
      intro q hq
      unfold SignedLocalAffineGate.eval
      rw [hagree q hq]
      by_cases hwest : 1 ≤ q
      · simp only [hwest, if_true]
        rw [hagree (q - 1) (by omega)]
      · simp only [hwest, if_false]

/-- A schedule of length `L` has western receptive radius at most `L`: its
value at `j` depends only on the interval from `j - L` through `j`. -/
theorem evalSignedLocalAffineGateSchedule_congr_receptiveField
    (schedule : List SignedLocalAffineGate) {state other : ℕ → ℝ} {j : ℕ}
    (hagree : ∀ q, j - schedule.length ≤ q → q ≤ j →
      state q = other q) :
    evalSignedLocalAffineGateSchedule schedule state j =
      evalSignedLocalAffineGateSchedule schedule other j := by
  induction schedule generalizing state other with
  | nil =>
      exact hagree j (by simp) le_rfl
  | cons gate schedule ih =>
      simp only [List.length_cons] at hagree
      change evalSignedLocalAffineGateSchedule schedule (gate.eval state) j =
        evalSignedLocalAffineGateSchedule schedule (gate.eval other) j
      apply ih
      intro q hqLower hqUpper
      unfold SignedLocalAffineGate.eval
      rw [hagree q (by omega) hqUpper]
      by_cases hwest : 1 ≤ q
      · simp only [hwest, if_true]
        rw [hagree (q - 1) (by omega) (by omega)]
      · simp only [hwest, if_false]

/-- Every finite local signed-affine schedule has a genuine expansive
one-channel shared-bias CNN implementation on a compact continuous image
family.  Each local gate contributes exactly three layers, the original
northern row obeys the corresponding causal local recurrence, and the full
feature image remains injective. -/
theorem exists_weightedMixGateSchedule_on_compact
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (schedule : List SignedLocalAffineGate) :
    ∃ net : SharedBiasNetwork 2 2 rows cols,
      net.depth = 3 * schedule.length ∧
      (∀ x ∈ K, ∀ j : Fin cols,
        zeroExtend (net.eval (F x)) 0 j =
          evalSignedLocalAffineGateSchedule schedule
            (fun q ↦ zeroExtend (F x) 0 q) j) ∧
      Set.InjOn (fun x ↦ net.eval (F x)) K := by
  induction schedule generalizing rows cols with
  | nil =>
      refine ⟨SharedBiasNetwork.nil rows cols, ?_, ?_, ?_⟩
      · rfl
      · intro x hx j
        rfl
      · exact hFinjective
  | cons gate schedule ih =>
      obtain ⟨b, hb, hlinear⟩ :=
        exists_shared_bias_linearization hK F hF
          (horizontalWeightedKernel gate.westWeight)
      let mix : SharedBiasNetworkTo 2 2 rows cols
          (rows + 2 - 1) (cols + 2 - 1) :=
        weightedMixLayer gate.westWeight b
      let mixed : X → Image (rows + 2 - 1) (cols + 2 - 1) :=
        fun x ↦ mix.eval (F x)
      have hmixed : ContinuousFeatureOn K mixed := by
        exact mix.continuousFeatureOn_eval F hF
      obtain ⟨M, hM, hbound⟩ :=
        exists_uniform_feature_margin hK mixed hmixed 0
      let first : SharedBiasNetworkTo 2 2 rows cols
          (rows + 2 - 1 + 2) (cols + 2 - 1 + 2) :=
        weightedMixGateNetwork gate.westWeight b gate.slope gate.offset M
      let G : X → Image (rows + 2 - 1 + 2) (cols + 2 - 1 + 2) :=
        fun x ↦ first.eval (F x)
      have hG : ContinuousFeatureOn K G := by
        exact first.continuousFeatureOn_eval F hF
      have hGinjective : Set.InjOn G K := by
        exact weightedMixGateNetwork_injectiveOn
          F gate.westWeight b gate.slope gate.offset M
          (fun x hx p q ↦ by
            rw [weightedMixLayer, SharedBiasNetworkTo.eval_single]
            exact hlinear x hx p q)
          hM.le
          (fun x hx i j ↦ by
            have := hbound x hx i j
            simpa [mixed, mix] using this.le)
          hFinjective
      obtain ⟨tail, htailDepth, htailGate, htailInjective⟩ :=
        ih G hG hGinjective
      let corrected : ℝ := gate.offset - gate.slope * b
      let carrier : ℝ :=
        protectedGridGateCarrier gate.slope corrected M
      let net : SharedBiasNetwork 2 2 rows cols :=
        .cons (horizontalWeightedKernel gate.westWeight) b
          (.cons expansiveIdentityKernel carrier
            (.cons (protectedRowGateKernel gate.slope)
              (corrected - gate.slope * carrier) tail))
      refine ⟨net, ?_, ?_, ?_⟩
      · change tail.depth + 1 + 1 + 1 = 3 * (schedule.length + 1)
        rw [htailDepth]
        omega
      · intro x hx j
        have htail := htailGate x hx
          (⟨j, by omega⟩ : Fin (cols + 2 - 1 + 2))
        change zeroExtend (tail.eval (G x)) 0 j = _
        rw [htail]
        apply evalSignedLocalAffineGateSchedule_congr_prefix
        intro q hq
        have hqcols : q < cols := lt_of_le_of_lt hq j.isLt
        have hfirst := weightedMixGateNetwork_gate_at
          (F x) gate.westWeight b gate.slope gate.offset M
          (fun p q ↦ by
            rw [weightedMixLayer, SharedBiasNetworkTo.eval_single]
            exact hlinear x hx p q)
          hM.le
          (fun i j ↦ by
            have := hbound x hx i j
            simpa [mixed, mix] using this.le)
          (⟨q, hqcols⟩ : Fin cols)
        simpa [G, first, SignedLocalAffineGate.eval] using hfirst
      · change Set.InjOn (fun x ↦ tail.eval (G x)) K
        exact htailInjective

end OneChannelCNNUniversality
