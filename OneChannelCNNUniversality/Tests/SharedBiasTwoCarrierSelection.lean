import OneChannelCNNUniversality.SharedBiasTwoCarrierSelection

/-!
# Regression tests for complementary two-carrier selection
-/

namespace OneChannelCNNUniversality

#check twoCarrierPreactivation
#check exists_twoCarrierSelectiveActivation_on
#check exists_twoCarrierSelectiveActivation_on_with_seed_lower_bound

/-- A singleton protected set exercises the normalized target branch. -/
example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (signal : X → Image 1 1)
    (hSignal : ContinuousFeatureOn K signal)
    (seed localCarrier : Image 1 1) (theta D : ℝ) :
    ∃ c t : ℝ, 0 < c ∧ 0 < t ∧
      ∀ x ∈ K,
        relu (twoCarrierPreactivation
          (signal x) seed localCarrier (0, 0) theta c t 0 0) =
          relu (signal x 0 0 + theta) := by
  obtain ⟨c, t, hc, ht, hselect⟩ :=
    exists_twoCarrierSelectiveActivation_on hK signal hSignal
      seed localCarrier (fun _ _ ↦ True) (0, 0) theta D (by
        intro p q hpq hne
        exfalso
        exact hne (Subsingleton.elim _ _))
  exact ⟨c, t, hc, ht, by
    intro x hx
    simpa using hselect x hx 0 0 trivial⟩

/-- A genuine three-column regression exercises both complementary gap
branches and the prescribed lower bound on the seed scale. -/
example {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (signal : X → Image 1 3)
    (hSignal : ContinuousFeatureOn K signal) (theta : ℝ) :
    ∃ c t : ℝ, 17 ≤ c ∧ 0 < c ∧ 0 < t ∧
      ∀ x ∈ K, ∀ p q,
        relu (twoCarrierPreactivation (signal x)
          (fun _ q ↦ if q = (0 : Fin 3) then 1 else 0)
          (fun _ q ↦ if q = (2 : Fin 3) then 2 else 0)
          (0, 1) theta c t p q) =
        if (p, q) = ((0, 1) : Fin 1 × Fin 3) then
          relu (signal x p q + theta)
        else twoCarrierPreactivation (signal x)
          (fun _ q ↦ if q = (0 : Fin 3) then 1 else 0)
          (fun _ q ↦ if q = (2 : Fin 3) then 2 else 0)
          (0, 1) theta c t p q := by
  obtain ⟨c, t, hcMin, hc, ht, hselect⟩ :=
    exists_twoCarrierSelectiveActivation_on_with_seed_lower_bound
      hK signal hSignal
        (fun _ q ↦ if q = (0 : Fin 3) then 1 else 0)
        (fun _ q ↦ if q = (2 : Fin 3) then 2 else 0)
        (fun _ _ ↦ True) (0, 1) theta 0 17 (by
          intro p q hpq hne
          have hp : p = 0 := Subsingleton.elim _ _
          subst p
          fin_cases q <;> simp_all)
  exact ⟨c, t, hcMin, hc, ht, fun x hx p q ↦
    hselect x hx p q trivial⟩

end OneChannelCNNUniversality
