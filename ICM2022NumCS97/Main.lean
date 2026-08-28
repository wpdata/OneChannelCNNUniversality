import ICM2022NumCS97.Simulation

/-!
# Universal approximation by two-dimensional one-channel CNNs

This module combines the lattice Stone--Weierstrass density theorem with the
exact compiler from finite lattice expressions to the original expansive
single-channel ReLU convolutional-network semantics.
-/

namespace ICM2022NumCS97

/--
Universal approximation for the exact two-dimensional expansive
single-channel ReLU CNN model.

For every positive finite input rectangle, every fixed convolution-kernel
rectangle having at least two rows and two columns, every compact input set,
every continuous real-valued target on that set, and every positive error
tolerance, there is a finite-depth one-channel network with that fixed kernel
shape and an affine readout whose uniform error is below the tolerance.
-/
theorem twoDimensional_oneChannel_universal_approximation
    {kRows kCols d₁ d₂ : ℕ}
    (hkRows : 2 ≤ kRows) (hkCols : 2 ≤ kCols)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {K : Set (Image d₁ d₂)} (hK : IsCompact K)
    (f : C(K, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (outRows outCols : ℕ)
      (net : NetworkTo kRows kCols d₁ d₂ outRows outCols)
      (weight : Image outRows outCols) (constant : ℝ),
      ∀ x : K, |net.realize weight constant x.1 - f x| < epsilon := by
  obtain ⟨e, he⟩ :=
    encodedLatticeExpr_dense_on_compact hd₁ hd₂ hK f hepsilon
  obtain ⟨net, weight, constant, hnet⟩ :=
    exists_network_realizing_latticeExpr
      hkRows hkCols hd₁ hd₂ hK e
  refine ⟨latticeOutRows kRows d₁ d₂ e,
    latticeOutCols kCols d₁ d₂ e,
    net, weight, constant, ?_⟩
  intro x
  rw [hnet x.1 x.2]
  exact he x

end ICM2022NumCS97
