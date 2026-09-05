import OneChannelCNNUniversality.SharedBias

/-!
# A one-layer obstruction for shared-bias carrier initialization

Consider a one-row, two-column input and one expansive `2 × 2` layer.
The southern output row has three entries.  Before ReLU they are

\[
  w_{10}x_0+b,\qquad
  w_{10}x_1+w_{11}x_0+b,\qquad
  w_{11}x_1+b.
\]

If this whole row is independent of the arbitrary real input, the two
southern kernel coefficients must vanish.  The row is then spatially
constant, with every entry equal to `relu b`.  Thus one shared-bias layer
cannot initialize a nonuniform input-independent carrier on these three
sites.
-/

namespace OneChannelCNNUniversality

/-- A one-row, two-column input with prescribed entries. -/
def twoPointRowInput (x₀ x₁ : ℝ) : Image 1 2 :=
  fun _ j ↦ if (j : ℕ) = 0 then x₀ else x₁

/-- The left entry of the southern output row before ReLU. -/
theorem fullConv_twoPointRowInput_south_left
    (w : Kernel 2 2) (x₀ x₁ : ℝ) :
    fullConv w (twoPointRowInput x₀ x₁) 1 0 =
      w (1 : Fin 2) (0 : Fin 2) * x₀ := by
  norm_num [fullConv, twoPointRowInput, zeroExtend, Fin.sum_univ_succ]

/-- The middle entry of the southern output row before ReLU. -/
theorem fullConv_twoPointRowInput_south_middle
    (w : Kernel 2 2) (x₀ x₁ : ℝ) :
    fullConv w (twoPointRowInput x₀ x₁) 1 1 =
      w (1 : Fin 2) (0 : Fin 2) * x₁ +
        w (1 : Fin 2) (1 : Fin 2) * x₀ := by
  norm_num [fullConv, twoPointRowInput, zeroExtend, Fin.sum_univ_succ]

/-- The right entry of the southern output row before ReLU. -/
theorem fullConv_twoPointRowInput_south_right
    (w : Kernel 2 2) (x₀ x₁ : ℝ) :
    fullConv w (twoPointRowInput x₀ x₁) 1 2 =
      w (1 : Fin 2) (1 : Fin 2) * x₁ := by
  norm_num [fullConv, twoPointRowInput, zeroExtend, Fin.sum_univ_succ]

/-- A ReLU of an affine function on all of `ℝ` can be constant only when
its slope vanishes. -/
theorem slope_eq_zero_of_relu_affine_constant (a b c : ℝ)
    (hconstant : ∀ x : ℝ, relu (a * x + b) = c) :
    a = 0 := by
  by_contra ha
  have hzero := hconstant (-b / a)
  have hone := hconstant ((1 - b) / a)
  have hargZero : a * (-b / a) + b = 0 := by
    field_simp
    ring
  have hargOne : a * ((1 - b) / a) + b = 1 := by
    field_simp
    ring
  rw [hargZero] at hzero
  rw [hargOne] at hone
  norm_num [relu] at hzero hone
  linarith

/-- If all three southern outputs of one shared-bias layer are independent
of the arbitrary two-entry input, both kernel coefficients that reach that
row are zero. -/
theorem oneLayer_south_constant_kernel_zero
    (w : Kernel 2 2) (b : ℝ) (c : Fin 3 → ℝ)
    (hconstant : ∀ x₀ x₁ q,
      sharedLayerEval w b (twoPointRowInput x₀ x₁)
          (1 : Fin 2) q = c q) :
    w (1 : Fin 2) (0 : Fin 2) = 0 ∧
      w (1 : Fin 2) (1 : Fin 2) = 0 := by
  constructor
  · apply slope_eq_zero_of_relu_affine_constant
      (w (1 : Fin 2) (0 : Fin 2)) b (c (0 : Fin 3))
    intro x₀
    have h := hconstant x₀ 0 (0 : Fin 3)
    simpa [sharedLayerEval, layerEval, constantImage,
      fullConv_twoPointRowInput_south_left] using h
  · apply slope_eq_zero_of_relu_affine_constant
      (w (1 : Fin 2) (1 : Fin 2)) b (c (2 : Fin 3))
    intro x₁
    have h := hconstant 0 x₁ (2 : Fin 3)
    simpa [sharedLayerEval, layerEval, constantImage,
      fullConv_twoPointRowInput_south_right] using h

/-- Under the same input-independence hypothesis, the southern output row
is exactly the constant row `relu b`. -/
theorem oneLayer_south_constant_eq_relu_bias
    (w : Kernel 2 2) (b : ℝ) (c : Fin 3 → ℝ)
    (hconstant : ∀ x₀ x₁ q,
      sharedLayerEval w b (twoPointRowInput x₀ x₁)
          (1 : Fin 2) q = c q) :
    ∀ x₀ x₁ q,
      sharedLayerEval w b (twoPointRowInput x₀ x₁)
          (1 : Fin 2) q = relu b := by
  rcases oneLayer_south_constant_kernel_zero w b c hconstant with ⟨hleft, hright⟩
  intro x₀ x₁ q
  fin_cases q
  · simp [sharedLayerEval, layerEval, constantImage,
      fullConv_twoPointRowInput_south_left, hleft]
  · simp [sharedLayerEval, layerEval, constantImage,
      fullConv_twoPointRowInput_south_middle, hleft, hright]
  · simp [sharedLayerEval, layerEval, constantImage,
      fullConv_twoPointRowInput_south_right, hright]

/-- No single expansive `2 × 2` layer with a shared scalar bias can
produce a southern row that is both independent of every real input and
nonuniform across its three spatial sites. -/
theorem not_oneLayer_south_nonuniform_inputIndependent
    (w : Kernel 2 2) (b : ℝ) :
    ¬ ∃ c : Fin 3 → ℝ,
      (∃ q₁ q₂, c q₁ ≠ c q₂) ∧
        ∀ x₀ x₁ q,
          sharedLayerEval w b (twoPointRowInput x₀ x₁)
              (1 : Fin 2) q = c q := by
  rintro ⟨c, ⟨q₁, q₂, hne⟩, hconstant⟩
  have heval := oneLayer_south_constant_eq_relu_bias w b c hconstant
  apply hne
  calc
    c q₁ = sharedLayerEval w b (twoPointRowInput 0 0)
        (1 : Fin 2) q₁ := (hconstant 0 0 q₁).symm
    _ = relu b := heval 0 0 q₁
    _ = sharedLayerEval w b (twoPointRowInput 0 0)
        (1 : Fin 2) q₂ := (heval 0 0 q₂).symm
    _ = c q₂ := hconstant 0 0 q₂

/-- On any input domain containing the zero image, an input-independent
southern row must equal the spatially constant row `relu b`.  Unlike the
global theorem above, this conclusion needs no interior or size assumption
on the domain. -/
theorem oneLayer_south_constant_on_zero_mem_eq_relu_bias
    (K : Set (Image 1 2)) (hzero : (0 : Image 1 2) ∈ K)
    (w : Kernel 2 2) (b : ℝ) (c : Fin 3 → ℝ)
    (hconstant : ∀ x ∈ K, ∀ q,
      sharedLayerEval w b x (1 : Fin 2) q = c q) :
    ∀ q, c q = relu b := by
  intro q
  calc
    c q = sharedLayerEval w b (0 : Image 1 2)
        (1 : Fin 2) q := (hconstant 0 hzero q).symm
    _ = relu b := by
      simp [sharedLayerEval, layerEval, constantImage]

/-- Consequently, a single shared-bias layer cannot produce a spatially
nonuniform southern carrier that is input-independent on a domain containing
the zero image. -/
theorem not_oneLayer_south_nonuniform_inputIndependent_on_zero_mem
    (K : Set (Image 1 2)) (hzero : (0 : Image 1 2) ∈ K)
    (w : Kernel 2 2) (b : ℝ) :
    ¬ ∃ c : Fin 3 → ℝ,
      (∃ q₁ q₂, c q₁ ≠ c q₂) ∧
        ∀ x ∈ K, ∀ q,
          sharedLayerEval w b x (1 : Fin 2) q = c q := by
  rintro ⟨c, ⟨q₁, q₂, hne⟩, hconstant⟩
  have heq := oneLayer_south_constant_on_zero_mem_eq_relu_bias
    K hzero w b c hconstant
  apply hne
  calc
    c q₁ = relu b := heq q₁
    _ = c q₂ := (heq q₂).symm

/-- The coordinatewise symmetric box `[-M,M]²` for the two input
registers. -/
def twoPointSymmetricBox (M : ℝ) : Set (Image 1 2) :=
  Set.Icc (constantImage 1 2 (-M)) (constantImage 1 2 M)

/-- Every finite symmetric two-point box is compact. -/
theorem twoPointSymmetricBox_compact (M : ℝ) :
    IsCompact (twoPointSymmetricBox M) :=
  isCompact_Icc

/-- A nonempty symmetric box contains the zero image. -/
theorem twoPointSymmetricBox_zero_mem (M : ℝ) (hM : 0 ≤ M) :
    (0 : Image 1 2) ∈ twoPointSymmetricBox M := by
  constructor <;> intro i j <;> simp [constantImage] <;>
    linarith

/-- On the compact symmetric input box `[-M,M]²`, no single shared-bias
layer has a southern row that is simultaneously input-independent and
spatially nonuniform. -/
theorem not_oneLayer_south_nonuniform_inputIndependent_on_symmetricBox
    (M : ℝ) (hM : 0 ≤ M) (w : Kernel 2 2) (b : ℝ) :
    ¬ ∃ c : Fin 3 → ℝ,
      (∃ q₁ q₂, c q₁ ≠ c q₂) ∧
        ∀ x ∈ twoPointSymmetricBox M, ∀ q,
          sharedLayerEval w b x (1 : Fin 2) q = c q := by
  exact not_oneLayer_south_nonuniform_inputIndependent_on_zero_mem
    (twoPointSymmetricBox M) (twoPointSymmetricBox_zero_mem M hM) w b

end OneChannelCNNUniversality
