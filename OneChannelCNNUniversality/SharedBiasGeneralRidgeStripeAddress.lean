import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeSeedAddress
import OneChannelCNNUniversality.SharedBiasGeneralRidgeStripeFinalAddress

/-!
# Complementary northern-two-row addresses for the signed stripe

The complete identity-seed address supplies horizontal uniqueness on row
one, while the final-factor local address supplies northern and endpoint
separation.  This file embeds both algebraic addresses into the final output
rectangle and proves exactly the two-class gap hypothesis consumed by
`SharedBiasTwoCarrierSelection`.

Only rows zero and one are protected.  Values assigned farther south are
irrelevant to the theorem and are set to zero.
-/

namespace OneChannelCNNUniversality

/-- Complete-chain seed address embedded in the final stripe rectangle. -/
noncomputable def generalRidgeStripeSeedAddressImage {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) :=
  fun p q ↦
    if (p : ℕ) = 0 then
      generalRidgeStripeSeedAddressRowZero w T q
    else if (p : ℕ) = 1 then
      generalRidgeStripeSeedAddressRowOne w T q
    else 0

/-- Final-factor local address embedded in the same rectangle. -/
noncomputable def generalRidgeStripeFinalLocalAddressImage {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) :
    Image (n + 4) (2 * (n + 2) + 1) :=
  fun p q ↦
    if (p : ℕ) ≤ 1 then
      generalRidgeStripeFinalLocalAddress w T p q
    else 0

/-- The protected target of the complete signed stripe block. -/
def generalRidgeStripeTarget (n : ℕ) :
    Fin (n + 4) × Fin (2 * (n + 2) + 1) :=
  (⟨1, by omega⟩, ⟨n + 2, by omega⟩)

@[simp] theorem generalRidgeStripeSeedAddressImage_row_zero {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (q : Fin (2 * (n + 2) + 1)) :
    generalRidgeStripeSeedAddressImage w T 0 q =
      generalRidgeStripeSeedAddressRowZero w T q := by
  simp [generalRidgeStripeSeedAddressImage]

@[simp] theorem generalRidgeStripeSeedAddressImage_row_one {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (q : Fin (2 * (n + 2) + 1)) :
    generalRidgeStripeSeedAddressImage w T 1 q =
      generalRidgeStripeSeedAddressRowOne w T q := by
  simp [generalRidgeStripeSeedAddressImage]

@[simp] theorem generalRidgeStripeFinalLocalAddressImage_north {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (p : Fin (n + 4)) (hp : (p : ℕ) ≤ 1)
    (q : Fin (2 * (n + 2) + 1)) :
    generalRidgeStripeFinalLocalAddressImage w T p q =
      generalRidgeStripeFinalLocalAddress w T p q := by
  simp [generalRidgeStripeFinalLocalAddressImage, hp]

/-- On row one the local direction never decreases relative to the target:
it has a two-unit gap at the endpoints and is flat in the interior. -/
theorem generalRidgeStripeFinalLocalAddress_row_one_nonneg_gap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (q : ℕ) (hq : q ≤ 2 * (n + 2)) :
    0 ≤ generalRidgeStripeFinalLocalAddress w T 1 q -
      generalRidgeStripeFinalLocalAddress w T 1 (n + 2) := by
  by_cases hleft : q = 0
  · subst q
    linarith [generalRidgeStripeFinalLocalAddress_row_one_left_gap w T hT]
  · by_cases hright : q = 2 * (n + 2)
    · subst q
      linarith [generalRidgeStripeFinalLocalAddress_row_one_right_gap w T hT]
    · have hq0 : 1 ≤ q := by omega
      have hq1 : q < 2 * (n + 2) := by omega
      rw [generalRidgeStripeFinalLocalAddress_row_one_interior
        w T q hq0 hq1]
      linarith

/-- The complete seed and local addresses satisfy the complementary gap
condition required for compact two-carrier ReLU selection. -/
theorem generalRidgeStripeTwoCarrier_gap {n : ℕ}
    (w : Fin (n + 2) → ℝ) (T : ℝ)
    (hT : generalRidgeStripeSeedAddressThreshold w ≤ T)
    (p : Fin (n + 4)) (q : Fin (2 * (n + 2) + 1))
    (hp : (p : ℕ) ≤ 1)
    (hne : (p, q) ≠ generalRidgeStripeTarget n) :
    (1 ≤ generalRidgeStripeSeedAddressImage w T p q -
          generalRidgeStripeSeedAddressImage w T
            (generalRidgeStripeTarget n).1
            (generalRidgeStripeTarget n).2 ∧
        0 ≤ generalRidgeStripeFinalLocalAddressImage w T p q -
          generalRidgeStripeFinalLocalAddressImage w T
            (generalRidgeStripeTarget n).1
            (generalRidgeStripeTarget n).2) ∨
      (-generalRidgeStripeSeedBTarget w ≤
          generalRidgeStripeSeedAddressImage w T p q -
            generalRidgeStripeSeedAddressImage w T
              (generalRidgeStripeTarget n).1
              (generalRidgeStripeTarget n).2 ∧
        2 ≤ generalRidgeStripeFinalLocalAddressImage w T p q -
          generalRidgeStripeFinalLocalAddressImage w T
            (generalRidgeStripeTarget n).1
            (generalRidgeStripeTarget n).2) := by
  have hthreshold := generalRidgeStripeSeedAddressThreshold_one_le w
  have hTone : 1 ≤ T := hthreshold.trans hT
  have hp_cases : (p : ℕ) = 0 ∨ (p : ℕ) = 1 := by omega
  rcases hp_cases with hp0 | hp1
  · right
    have hpEq : p = (0 : Fin (n + 4)) := Fin.ext hp0
    subst p
    constructor
    · simpa [generalRidgeStripeTarget] using
        generalRidgeStripeSeedAddress_north_lower_bound w T hTone (q : ℕ)
    · simpa [generalRidgeStripeTarget] using
        generalRidgeStripeFinalLocalAddress_row_zero_gap
          w T hTone (q : ℕ) (by omega)
  · left
    have hpEq : p = (1 : Fin (n + 4)) := Fin.ext hp1
    subst p
    have hqne : (q : ℕ) ≠ n + 2 := by
      intro hq
      apply hne
      rw [generalRidgeStripeTarget]
      congr 1
      exact Fin.ext hq
    constructor
    · simpa [generalRidgeStripeTarget] using
        generalRidgeStripeSeedAddress_row_one_gap_of_threshold
          w T hT (q : ℕ) (by omega) hqne
    · simpa [generalRidgeStripeTarget] using
        generalRidgeStripeFinalLocalAddress_row_one_nonneg_gap
          w T hTone (q : ℕ) (by omega)

end OneChannelCNNUniversality
