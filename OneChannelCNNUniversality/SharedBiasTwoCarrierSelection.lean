import OneChannelCNNUniversality.SharedBiasSelection

/-!
# Compact selection from two complementary carriers

One carrier need not separate a target from every protected coordinate.  It
is enough to have two complementary directions: a seed carrier with a unit
gap on one class, and a local carrier with a two-unit gap on the remaining
class.  The seed carrier is allowed a fixed deficit `D` on the second class.

Compactness supplies a uniform signal margin.  Scaling the seed carrier by
that margin and then scaling the local carrier to cover both the margin and
the possible seed deficit gives an exact shared-bias ReLU mask.
-/

namespace OneChannelCNNUniversality

open Set

/-- Affine preactivation formed from a variable signal, two fixed spatial
carriers, and the unique scalar bias that normalizes the target to `theta`. -/
noncomputable def twoCarrierPreactivation {rows cols : ℕ}
    (signal seedCarrier localCarrier : Image rows cols)
    (target : Fin rows × Fin cols) (theta c t : ℝ)
    (p : Fin rows) (q : Fin cols) : ℝ :=
  signal p q + c * seedCarrier p q + t * localCarrier p q +
    (theta - c * seedCarrier target.1 target.2 -
      t * localCarrier target.1 target.2)

/-- Exact compact selector from two complementary address directions.

For every protected non-target coordinate, either the seed direction has a
unit gap and the local direction is nondecreasing, or the seed direction is
no worse than `-D` and the local direction has a two-unit gap.  The target
formula is asserted when the target itself belongs to `protect`. -/
theorem exists_twoCarrierSelectiveActivation_on
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (seedCarrier localCarrier : Image rows cols)
    (protect : Fin rows → Fin cols → Prop)
    (target : Fin rows × Fin cols) (theta D : ℝ)
    (hgap : ∀ p q, protect p q → (p, q) ≠ target →
      (1 ≤ seedCarrier p q - seedCarrier target.1 target.2 ∧
          0 ≤ localCarrier p q - localCarrier target.1 target.2) ∨
        (-D ≤ seedCarrier p q - seedCarrier target.1 target.2 ∧
          2 ≤ localCarrier p q - localCarrier target.1 target.2)) :
    ∃ c t : ℝ, 0 < c ∧ 0 < t ∧
      ∀ x ∈ K, ∀ p q, protect p q →
        relu (twoCarrierPreactivation
          (signal x) seedCarrier localCarrier target theta c t p q) =
          if (p, q) = target then relu (signal x p q + theta)
          else twoCarrierPreactivation
            (signal x) seedCarrier localCarrier target theta c t p q := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  let t : ℝ := (M + M * max D 0) / 2
  have ht : 0 < t := by
    dsimp [t]
    have hmax : 0 ≤ max D 0 := le_max_right D 0
    positivity
  refine ⟨M, t, hM, ht, ?_⟩
  intro x hx p q hpq
  by_cases heq : (p, q) = target
  · rw [if_pos heq]
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    congr 1
    simp [twoCarrierPreactivation]
  · rw [if_neg heq]
    apply relu_of_nonneg
    have hsignal : -M < signal x p q + theta := by
      exact neg_lt_of_abs_lt (hbound x hx p q)
    have hrearrange :
        twoCarrierPreactivation
            (signal x) seedCarrier localCarrier target theta M t p q =
          (signal x p q + theta) +
            M * (seedCarrier p q - seedCarrier target.1 target.2) +
            t * (localCarrier p q - localCarrier target.1 target.2) := by
      simp only [twoCarrierPreactivation]
      ring
    rw [hrearrange]
    rcases hgap p q hpq heq with hfirst | hsecond
    · have hseed :
          M ≤ M * (seedCarrier p q - seedCarrier target.1 target.2) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hfirst.1 hM.le
      have hlocal :
          0 ≤ t * (localCarrier p q - localCarrier target.1 target.2) :=
        mul_nonneg ht.le hfirst.2
      linarith
    · have hseed :
          M * (-D) ≤
            M * (seedCarrier p q - seedCarrier target.1 target.2) :=
        mul_le_mul_of_nonneg_left hsecond.1 hM.le
      have hlocal :
          t * 2 ≤
            t * (localCarrier p q - localCarrier target.1 target.2) :=
        mul_le_mul_of_nonneg_left hsecond.2 ht.le
      have hD : M * D ≤ M * max D 0 := by
        exact mul_le_mul_of_nonneg_left (le_max_left D 0) hM.le
      have htformula : t * 2 = M + M * max D 0 := by
        dsimp [t]
        ring
      linarith

/-- The same two-carrier selector with an arbitrary prescribed lower bound
on the seed-carrier scale.  Enlarging that scale only improves the first
gap class; the local-carrier scale is enlarged simultaneously to absorb the
possible seed deficit on the second class.  This monotone interface is what
allows the terminal selector to reuse a seed scale already chosen to keep
all preceding ReLU layers linear. -/
theorem exists_twoCarrierSelectiveActivation_on_with_seed_lower_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols : ℕ} (signal : X → Image rows cols)
    (hSignal : ContinuousFeatureOn K signal)
    (seedCarrier localCarrier : Image rows cols)
    (protect : Fin rows → Fin cols → Prop)
    (target : Fin rows × Fin cols) (theta D cMin : ℝ)
    (hgap : ∀ p q, protect p q → (p, q) ≠ target →
      (1 ≤ seedCarrier p q - seedCarrier target.1 target.2 ∧
          0 ≤ localCarrier p q - localCarrier target.1 target.2) ∨
        (-D ≤ seedCarrier p q - seedCarrier target.1 target.2 ∧
          2 ≤ localCarrier p q - localCarrier target.1 target.2)) :
    ∃ c t : ℝ, cMin ≤ c ∧ 0 < c ∧ 0 < t ∧
      ∀ x ∈ K, ∀ p q, protect p q →
        relu (twoCarrierPreactivation
          (signal x) seedCarrier localCarrier target theta c t p q) =
          if (p, q) = target then relu (signal x p q + theta)
          else twoCarrierPreactivation
            (signal x) seedCarrier localCarrier target theta c t p q := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_feature_margin hK signal hSignal theta
  let c : ℝ := max M cMin
  have hMc : M ≤ c := le_max_left _ _
  have hcMin : cMin ≤ c := le_max_right _ _
  have hc : 0 < c := hM.trans_le hMc
  let t : ℝ := (M + c * max D 0) / 2
  have ht : 0 < t := by
    dsimp [t]
    have hmax : 0 ≤ max D 0 := le_max_right D 0
    positivity
  refine ⟨c, t, hcMin, hc, ht, ?_⟩
  intro x hx p q hpq
  by_cases heq : (p, q) = target
  · rw [if_pos heq]
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    congr 1
    simp [twoCarrierPreactivation]
  · rw [if_neg heq]
    apply relu_of_nonneg
    have hsignal : -M < signal x p q + theta := by
      exact neg_lt_of_abs_lt (hbound x hx p q)
    have hrearrange :
        twoCarrierPreactivation
            (signal x) seedCarrier localCarrier target theta c t p q =
          (signal x p q + theta) +
            c * (seedCarrier p q - seedCarrier target.1 target.2) +
            t * (localCarrier p q - localCarrier target.1 target.2) := by
      simp only [twoCarrierPreactivation]
      ring
    rw [hrearrange]
    rcases hgap p q hpq heq with hfirst | hsecond
    · have hseed :
          c ≤ c * (seedCarrier p q - seedCarrier target.1 target.2) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hfirst.1 hc.le
      have hlocal :
          0 ≤ t * (localCarrier p q - localCarrier target.1 target.2) :=
        mul_nonneg ht.le hfirst.2
      linarith
    · have hseed :
          c * (-D) ≤
            c * (seedCarrier p q - seedCarrier target.1 target.2) :=
        mul_le_mul_of_nonneg_left hsecond.1 hc.le
      have hlocal :
          t * 2 ≤
            t * (localCarrier p q - localCarrier target.1 target.2) :=
        mul_le_mul_of_nonneg_left hsecond.2 ht.le
      have hD : c * D ≤ c * max D 0 := by
        exact mul_le_mul_of_nonneg_left (le_max_left D 0) hc.le
      have htformula : t * 2 = M + c * max D 0 := by
        dsimp [t]
        ring
      linarith

end OneChannelCNNUniversality
