import OneChannelCNNUniversality.SharedBiasGeneralRidgePolynomial

/-!
# A separated allocation for arbitrary-width ridge carriers

For every depth `d ≥ 2`, this file selects two distinct factor slots.  The
first slot receives the target leading coefficient plus a positive scale, and
the last slot receives the negative of that scale.  Thus the allocation still
sums to the target leading coefficient, while the last lower factor has a
uniformly negative response at `X = 1`.

Writing `β` for the last Lagrange coefficient, the scale is

\[
  T=\frac{|\beta|+d+2}{d+1}.
\]

Since the last nodal factor is `X + d`, its allocated lower factor at `X = 1`
is exactly

\[
  \beta-T(d+1)=\beta-|\beta|-(d+2)\leq -(d+2).
\]

The statements here are algebraic preparation for a shared-bias carrier
construction.  They do not by themselves prove that every ReLU layer follows
its intended linear branch.
-/

open scoped BigOperators Polynomial

namespace OneChannelCNNUniversality

open Polynomial

/-- The last factor slot at any depth `d ≥ 2`. -/
def generalRidgeLastIndex {d : ℕ} (hd : 2 ≤ d) : Fin d :=
  ⟨d - 1, by omega⟩

/-- The first factor slot at any depth `d ≥ 2`. -/
def generalRidgeFirstIndex {d : ℕ} (hd : 2 ≤ d) : Fin d :=
  ⟨0, by omega⟩

theorem generalRidgeFirstIndex_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (i : Fin d) :
    i = generalRidgeFirstIndex hd ↔ (i : ℕ) = 0 := by
  constructor
  · intro h
    simpa [generalRidgeFirstIndex] using congrArg Fin.val h
  · intro h
    apply Fin.ext
    simpa [generalRidgeFirstIndex]

theorem generalRidgeLastIndex_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (i : Fin d) :
    i = generalRidgeLastIndex hd ↔ (i : ℕ) = d - 1 := by
  constructor
  · intro h
    simpa [generalRidgeLastIndex] using congrArg Fin.val h
  · intro h
    apply Fin.ext
    simpa [generalRidgeLastIndex]

@[simp] theorem generalRidgeLastIndex_val {d : ℕ} (hd : 2 ≤ d) :
    (generalRidgeLastIndex hd : ℕ) = d - 1 := rfl

/-- At depth at least two, the first and last allocation slots are distinct. -/
@[simp] theorem generalRidgeLastIndex_ne_first {d : ℕ} (hd : 2 ≤ d) :
    generalRidgeLastIndex hd ≠ generalRidgeFirstIndex hd := by
  intro h
  have hval := congrArg Fin.val h
  change d - 1 = 0 at hval
  omega

/-- Positive scale used to separate the last carrier response. -/
noncomputable def generalRidgeCarrierScale {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) : ℝ :=
  (|generalRidgeBeta w (generalRidgeLastIndex hd)| + (d : ℝ) + 2) /
    ((d : ℝ) + 1)

theorem generalRidgeCarrierScale_pos {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    0 < generalRidgeCarrierScale hd w := by
  rw [generalRidgeCarrierScale]
  positivity

theorem generalRidgeCarrierScale_mul_succ {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    generalRidgeCarrierScale hd w * ((d : ℝ) + 1) =
      |generalRidgeBeta w (generalRidgeLastIndex hd)| + (d : ℝ) + 2 := by
  rw [generalRidgeCarrierScale]
  field_simp

/--
Put `w₀ + T` in the first slot, `-T` in the last slot, and zero elsewhere.
-/
noncomputable def generalRidgeSeparatedAllocation {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i ↦
    if i = generalRidgeFirstIndex hd then w 0 + generalRidgeCarrierScale hd w
    else if i = generalRidgeLastIndex hd then -generalRidgeCarrierScale hd w
    else 0

@[simp] theorem generalRidgeSeparatedAllocation_zero {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    generalRidgeSeparatedAllocation hd w (generalRidgeFirstIndex hd) =
      w 0 + generalRidgeCarrierScale hd w := by
  simp [generalRidgeSeparatedAllocation]

@[simp] theorem generalRidgeSeparatedAllocation_last {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    generalRidgeSeparatedAllocation hd w (generalRidgeLastIndex hd) =
      -generalRidgeCarrierScale hd w := by
  simp [generalRidgeSeparatedAllocation, generalRidgeLastIndex_ne_first hd]

/-- The separated allocation preserves the required total `w₀`. -/
theorem generalRidgeSeparatedAllocation_sum {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    ∑ i : Fin d, generalRidgeSeparatedAllocation hd w i = w 0 := by
  classical
  calc
    ∑ i : Fin d, generalRidgeSeparatedAllocation hd w i =
        ∑ i : Fin d, (
          (if i = generalRidgeFirstIndex hd then
              w 0 + generalRidgeCarrierScale hd w else 0) +
            (if i = generalRidgeLastIndex hd then
              -generalRidgeCarrierScale hd w else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hfirst : i = generalRidgeFirstIndex hd
        · subst i
          simp [generalRidgeSeparatedAllocation,
            (generalRidgeLastIndex_ne_first hd).symm]
        · by_cases hlast : i = generalRidgeLastIndex hd
          · simp [generalRidgeSeparatedAllocation, hlast]
          · simp [generalRidgeSeparatedAllocation, hfirst, hlast]
    _ = w 0 := by
      rw [Finset.sum_add_distrib]
      simp

/-- The last horizontal factor is exactly `X + d`. -/
theorem generalRidgeLastNodalFactor_eval {d : ℕ} (hd : 2 ≤ d) (q : ℝ) :
    (generalRidgeNodalFactor (generalRidgeLastIndex hd)).eval q = q + d := by
  simp [generalRidgeNodalFactor, generalRidgeLastIndex,
    Nat.sub_add_cancel (by omega : 1 ≤ d)]

/-- At the north origin, the last horizontal factor has response exactly `d`. -/
theorem generalRidgeLastNodalFactor_eval_zero {d : ℕ} (hd : 2 ≤ d) :
    (generalRidgeNodalFactor (generalRidgeLastIndex hd)).eval 0 = d := by
  simpa using generalRidgeLastNodalFactor_eval hd 0

/-- On every nonnegative north coordinate, the last factor response is at least `d`. -/
theorem generalRidgeLastNodalFactor_eval_ge_depth {d : ℕ} (hd : 2 ≤ d)
    {q : ℝ} (hq : 0 ≤ q) :
    (d : ℝ) ≤ (generalRidgeNodalFactor (generalRidgeLastIndex hd)).eval q := by
  rw [generalRidgeLastNodalFactor_eval hd q]
  linarith

/-- Exact separated response of the last lower factor at `X = 1`. -/
theorem generalRidgeSeparatedLastLowerFactor_eval_one {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    (generalRidgeLowerFactor w (generalRidgeSeparatedAllocation hd w)
        (generalRidgeLastIndex hd)).eval 1 =
      generalRidgeBeta w (generalRidgeLastIndex hd) -
        |generalRidgeBeta w (generalRidgeLastIndex hd)| - ((d : ℝ) + 2) := by
  rw [generalRidgeLowerFactor]
  simp only [eval_add, eval_C, eval_mul]
  rw [generalRidgeSeparatedAllocation_last]
  rw [generalRidgeLastNodalFactor_eval hd 1]
  rw [show (1 : ℝ) + d = d + 1 by ring]
  rw [neg_mul, generalRidgeCarrierScale_mul_succ]
  ring

/-- The last lower factor is uniformly at most `-(d+2)` at `X = 1`. -/
theorem generalRidgeSeparatedLastLowerFactor_eval_one_le {d : ℕ} (hd : 2 ≤ d)
    (w : Fin (d + 1) → ℝ) :
    (generalRidgeLowerFactor w (generalRidgeSeparatedAllocation hd w)
        (generalRidgeLastIndex hd)).eval 1 ≤ -((d : ℝ) + 2) := by
  rw [generalRidgeSeparatedLastLowerFactor_eval_one hd w]
  have hβ := le_abs_self (generalRidgeBeta w (generalRidgeLastIndex hd))
  linarith

end OneChannelCNNUniversality
