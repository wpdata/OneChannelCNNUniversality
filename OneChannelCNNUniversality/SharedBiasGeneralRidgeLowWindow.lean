import OneChannelCNNUniversality.SharedBiasGeneralRidgePolynomial

/-!
# Finite-window inversion for sequential ridge blocks

If a polynomial `H` has nonzero constant coefficient, then its coercion to a
formal power series is a unit.  Truncating `R H⁻¹` after degree `d` gives a
polynomial `U` of degree at most `d` satisfying

\[
  [X^j](UH)=[X^j]R,\qquad 0\le j\le d.
\]

Only the requested low-order window is matched; no global polynomial inverse
is claimed.  This triangular algebra is the correction mechanism needed when
a later ridge block must cancel the known affine transport of earlier blocks.
-/

namespace OneChannelCNNUniversality

open Polynomial

/-- Truncate the formal-power-series quotient `R / H` to degrees at most
`d`. -/
noncomputable def generalRidgeLowWindowMultiplier
    (d : ℕ) (H R : ℝ[X]) : ℝ[X] :=
  PowerSeries.trunc (d + 1)
    ((R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹)

/-- The truncated multiplier has the requested degree budget. -/
theorem generalRidgeLowWindowMultiplier_natDegree_le
    (d : ℕ) (H R : ℝ[X]) :
    (generalRidgeLowWindowMultiplier d H R).natDegree ≤ d := by
  exact Nat.lt_succ_iff.mp
    (PowerSeries.natDegree_trunc_lt
      ((R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹) d)

/-- Multiplication by `H` recovers every coefficient of `R` through degree
`d`, provided the constant coefficient of `H` is nonzero. -/
theorem generalRidgeLowWindowMultiplier_coeff_mul
    (d : ℕ) (H R : ℝ[X]) (hH0 : H.coeff 0 ≠ 0)
    (j : ℕ) (hj : j ≤ d) :
    (generalRidgeLowWindowMultiplier d H R * H).coeff j = R.coeff j := by
  let quotient : PowerSeries ℝ :=
    (R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹
  have hconstant : PowerSeries.constantCoeff (H : PowerSeries ℝ) ≠ 0 := by
    simpa using hH0
  calc
    (generalRidgeLowWindowMultiplier d H R * H).coeff j =
        PowerSeries.coeff j
          ((generalRidgeLowWindowMultiplier d H R : PowerSeries ℝ) *
            (H : PowerSeries ℝ)) := by
      rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
      simp only [Polynomial.coeff_coe]
    _ = PowerSeries.coeff j (quotient * (H : PowerSeries ℝ)) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxleft : x.1 ≤ j := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        omega
      rw [generalRidgeLowWindowMultiplier]
      change
        PowerSeries.coeff x.1
            (PowerSeries.trunc (d + 1)
              ((R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹)) *
            PowerSeries.coeff x.2 (H : PowerSeries ℝ) =
          PowerSeries.coeff x.1
              ((R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹) *
            PowerSeries.coeff x.2 (H : PowerSeries ℝ)
      rw [Polynomial.coeff_coe]
      rw [PowerSeries.coeff_trunc, if_pos (by omega)]
    _ = R.coeff j := by
      change PowerSeries.coeff j
          (((R : PowerSeries ℝ) * (H : PowerSeries ℝ)⁻¹) *
            (H : PowerSeries ℝ)) = R.coeff j
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ hconstant, mul_one]
      simp

/-- Existential interface for the finite triangular inverse. -/
theorem exists_generalRidgeLowWindowMultiplier
    (d : ℕ) (H R : ℝ[X]) (hH0 : H.coeff 0 ≠ 0) :
    ∃ U : ℝ[X], U.natDegree ≤ d ∧
      ∀ j ≤ d, (U * H).coeff j = R.coeff j := by
  refine ⟨generalRidgeLowWindowMultiplier d H R,
    generalRidgeLowWindowMultiplier_natDegree_le d H R, ?_⟩
  intro j hj
  exact generalRidgeLowWindowMultiplier_coeff_mul d H R hH0 j hj

end OneChannelCNNUniversality
