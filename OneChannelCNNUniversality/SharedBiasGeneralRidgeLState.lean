import OneChannelCNNUniversality.SharedBiasGeneralRidgeNetwork
import OneChannelCNNUniversality.SharedBiasChainLayout
import OneChannelCNNUniversality.SharedBiasSeedTransport

/-!
# An input-length monotone state for an arbitrary-width ridge

The first `d + 1` northern coordinates of the general-ridge output already
form an injective triangular code.  Together with the ridge target immediately
south of their eastern endpoint, they occupy a southeast-monotone `L`-shaped
chain of length `d + 2`.  Thus the full northern fringe is not needed to
retain both the input code and the nonlinear ridge.

This file extracts that logical state without claiming that the coordinate
restriction itself is a convolutional layer.
-/

namespace OneChannelCNNUniversality

open Set

/-- Embed a northern code coordinate into the `L`-state index type. -/
def generalRidgeLCodeIndex {n : ℕ} (q : Fin (n + 3)) : Fin (n + 4) :=
  ⟨q, by omega⟩

/-- The final `L`-state index, reserved for the nonlinear ridge. -/
def generalRidgeLTerminalIndex (n : ℕ) : Fin (n + 4) :=
  ⟨n + 3, by omega⟩

/-- The first `n + 3` sites run east along the northern row; the final site
turns one step south onto the arbitrary-width ridge target. -/
def generalRidgeLLayout (n : ℕ) :
    Fin (n + 4) →
      Fin (n + 3) × Fin (2 * (n + 2) + 1) :=
  fun t ↦
    if ht : (t : ℕ) < n + 3 then
      (⟨0, by omega⟩, ⟨t, by omega⟩)
    else
      (⟨1, by omega⟩, ⟨n + 2, by omega⟩)

/-- A northern code index is sent to the matching northern output site. -/
@[simp] theorem generalRidgeLLayout_code {n : ℕ} (q : Fin (n + 3)) :
    generalRidgeLLayout n (generalRidgeLCodeIndex q) =
      (⟨0, by omega⟩, ⟨q, by omega⟩) := by
  simp [generalRidgeLLayout, generalRidgeLCodeIndex]

/-- The terminal logical index is the southern ridge coordinate. -/
@[simp] theorem generalRidgeLLayout_terminal (n : ℕ) :
    generalRidgeLLayout n (generalRidgeLTerminalIndex n) =
      (⟨1, by omega⟩, ⟨n + 2, by omega⟩) := by
  simp [generalRidgeLLayout, generalRidgeLTerminalIndex]

/-- The `L`-layout is monotone in the southeast product order. -/
theorem generalRidgeLLayout_southeastMonotone (n : ℕ) :
    SoutheastMonotoneLayout (generalRidgeLLayout n) := by
  intro a b hab
  unfold generalRidgeLLayout southeastProtected
  split_ifs with ha hb
  · exact ⟨le_rfl, hab⟩
  · change (0 : ℕ) ≤ 1 ∧ (a : ℕ) ≤ n + 2
    omega
  · exfalso
    have haLt := a.isLt
    have hbLt := b.isLt
    omega
  · exact ⟨le_rfl, le_rfl⟩

/-- Distinct logical indices occupy distinct sites of the `L`-layout. -/
theorem generalRidgeLLayout_injective (n : ℕ) :
    Function.Injective (generalRidgeLLayout n) := by
  intro a b hab
  by_cases ha : (a : ℕ) < n + 3
  · by_cases hb : (b : ℕ) < n + 3
    · have hcol := congrArg (fun z ↦ (z.2 : ℕ)) hab
      simp [generalRidgeLLayout, ha, hb] at hcol
      exact Fin.ext hcol
    · have hrow := congrArg (fun z ↦ (z.1 : ℕ)) hab
      simp [generalRidgeLLayout, ha, hb] at hrow
  · by_cases hb : (b : ℕ) < n + 3
    · have hrow := congrArg (fun z ↦ (z.1 : ℕ)) hab
      simp [generalRidgeLLayout, ha, hb] at hrow
    · apply Fin.ext
      have haLt := a.isLt
      have hbLt := b.isLt
      omega

/-- Restrict a general-ridge output to its compact northern-code-plus-ridge
`L`-state. -/
def generalRidgeLState (n : ℕ)
    (z : Image (n + 3) (2 * (n + 2) + 1)) : Image 1 (n + 4) :=
  fun _ t ↦ z (generalRidgeLLayout n t).1 (generalRidgeLLayout n t).2

/-- Reading a code index from the logical state reads the corresponding
northern output coordinate. -/
@[simp] theorem generalRidgeLState_code (n : ℕ)
    (z : Image (n + 3) (2 * (n + 2) + 1)) (q : Fin (n + 3)) :
    generalRidgeLState n z 0 (generalRidgeLCodeIndex q) =
      zeroExtend z 0 q := by
  rw [generalRidgeLState, generalRidgeLLayout_code]
  exact (zeroExtend_of_lt z (by omega) (by omega)).symm

/-- Reading the last logical index reads the exact ridge target. -/
@[simp] theorem generalRidgeLState_terminal (n : ℕ)
    (z : Image (n + 3) (2 * (n + 2) + 1)) :
    generalRidgeLState n z 0 (generalRidgeLTerminalIndex n) =
      zeroExtend z 1 (n + 2) := by
  rw [generalRidgeLState, generalRidgeLLayout_terminal]
  exact (zeroExtend_of_lt z (by omega) (by omega)).symm

/-- The input-length northern prefix of the pure general-ridge convolution. -/
noncomputable def generalRidgeNorthPrefix {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ)
    (x : Image 1 (d + 1)) : Image 1 (d + 1) :=
  fun _ q ↦ zeroExtend (generalRidgeFullConv w η x) 0 q

private def NorthPrefixEq {rows cols : ℕ} (limit : ℕ)
    (x y : Image rows cols) : Prop :=
  ∀ q, q < limit → zeroExtend x 0 q = zeroExtend y 0 q

private theorem northPrefixEq_of_fullConv_factor
    {rows cols limit : ℕ} (f : BilinearKernelFactor)
    (hf : f.a0 ≠ 0) {x y : Image rows cols}
    (hout : NorthPrefixEq limit
      (fullConvImage f.kernel x) (fullConvImage f.kernel y)) :
    NorthPrefixEq limit x y := by
  intro q hq
  induction q with
  | zero =>
      have hzero := hout 0 hq
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat,
        fullConv_bilinearKernel_nat] at hzero
      norm_num at hzero
      exact hzero.resolve_right hf
  | succ q ih =>
      have hsucc := hout (q + 1) hq
      rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
        BilinearKernelFactor.kernel, fullConv_bilinearKernel_nat,
        fullConv_bilinearKernel_nat] at hsucc
      simp [show 1 ≤ q + 1 by omega,
        show ¬1 ≤ (0 : ℕ) by omega] at hsucc
      have hprev := ih (by omega)
      rw [hprev] at hsucc
      apply mul_left_cancel₀ hf
      linarith

private theorem northPrefixEq_of_fullConvChain
    (fs : List BilinearKernelFactor)
    (hfs : ∀ f ∈ fs, f.a0 ≠ 0)
    {rows cols limit : ℕ} {x y : Image rows cols}
    (hout : NorthPrefixEq limit (fullConvChain fs x) (fullConvChain fs y)) :
    NorthPrefixEq limit x y := by
  induction fs generalizing rows cols with
  | nil => exact hout
  | cons f fs ih =>
      have hf : f.a0 ≠ 0 := hfs f (by simp)
      have htail : NorthPrefixEq limit
          (fullConvImage f.kernel x) (fullConvImage f.kernel y) := by
        apply ih
        · intro g hg
          exact hfs g (by simp [hg])
        · exact hout
      exact northPrefixEq_of_fullConv_factor f hf htail

/-- The first `d + 1` northern coordinates already recover the complete
`1 × (d + 1)` input.  The remaining northern expansion fringe is not
needed for injectivity. -/
theorem generalRidgeNorthPrefix_injective {d : ℕ}
    (w : Fin (d + 1) → ℝ) (η : Fin d → ℝ) :
    Function.Injective (generalRidgeNorthPrefix w η) := by
  intro x y hxy
  have hout : NorthPrefixEq (d + 1)
      (generalRidgeFullConv w η x) (generalRidgeFullConv w η y) := by
    intro q hq
    have hentry := congrFun (congrFun hxy (⟨0, by omega⟩ : Fin 1))
      (⟨q, hq⟩ : Fin (d + 1))
    exact hentry
  have hnonzero : ∀ f ∈ generalRidgeFactorList w η, f.a0 ≠ 0 := by
    rw [generalRidgeFactorList, List.forall_mem_ofFn_iff]
    intro i
    change (((i : ℕ) + 1 : ℕ) : ℝ) ≠ 0
    positivity
  have hin : NorthPrefixEq (d + 1) x y := by
    apply northPrefixEq_of_fullConvChain
      (generalRidgeFactorList w η) hnonzero
    simpa [generalRidgeFullConv] using hout
  funext i j
  fin_cases i
  have hentry := hin j j.isLt
  rw [zeroExtend_of_lt x (by omega) j.isLt,
    zeroExtend_of_lt y (by omega) j.isLt] at hentry
  exact hentry

/-- The arbitrary-width ridge network contains a continuous, injective
logical `L`-state.  Its northern prefix is the pure triangular code plus a
fixed offset, and its terminal coordinate is the requested affine ReLU
ridge exactly. -/
theorem exists_generalRidgeLState_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 3))
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (w : Fin (n + 3) → ℝ) (gamma : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 (n + 3)
          (n + 3) (2 * (n + 2) + 1))
      (offset : Image (n + 3) (2 * (n + 2) + 1)),
      net.net.depth = n + 2 ∧
        ContinuousFeatureOn K
          (fun x ↦ generalRidgeLState n (net.eval (F x))) ∧
        Set.InjOn
          (fun x ↦ generalRidgeLState n (net.eval (F x))) K ∧
        ∀ x ∈ K,
          generalRidgeLState n (net.eval (F x)) 0
              (generalRidgeLTerminalIndex n) =
            relu ((∑ j : Fin (n + 3), w j * F x 0 j) + gamma) ∧
          ∀ q : Fin (n + 3),
            generalRidgeLState n (net.eval (F x)) 0
                (generalRidgeLCodeIndex q) =
              zeroExtend
                  (generalRidgeFullConv w
                    (generalRidgeSeparatedAllocation (by omega) w) (F x))
                  0 q +
                zeroExtend offset 0 q := by
  obtain ⟨net, offset, hdepth, hbehavior⟩ :=
    exists_protectedGeneralRidgeNetwork_behavior_on_compact
      hK F hF w gamma
  let η := generalRidgeSeparatedAllocation (d := n + 2) (by omega) w
  have hstateContinuous : ContinuousFeatureOn K
      (fun x ↦ generalRidgeLState n (net.eval (F x))) := by
    have hnetContinuous := net.continuousFeatureOn_eval F hF
    intro i t
    simpa [generalRidgeLState] using
      hnetContinuous (generalRidgeLLayout n t).1
        (generalRidgeLLayout n t).2
  have hstateInjective : Set.InjOn
      (fun x ↦ generalRidgeLState n (net.eval (F x))) K := by
    intro x hx y hy hxy
    apply hFinjective hx hy
    apply generalRidgeNorthPrefix_injective w η
    funext i q
    fin_cases i
    have hstate := congrFun
      (congrFun hxy (⟨0, by omega⟩ : Fin 1))
      (generalRidgeLCodeIndex q)
    change generalRidgeLState n (net.eval (F x)) 0
        (generalRidgeLCodeIndex q) =
      generalRidgeLState n (net.eval (F y)) 0
        (generalRidgeLCodeIndex q) at hstate
    rw [generalRidgeLState_code, generalRidgeLState_code] at hstate
    let qout : Fin (2 * (n + 2) + 1) := ⟨q, by omega⟩
    have hxNorth := (hbehavior x hx).2 qout
    have hyNorth := (hbehavior y hy).2 qout
    change zeroExtend (net.eval (F x)) 0 q =
      zeroExtend (net.eval (F y)) 0 q at hstate
    change zeroExtend (generalRidgeFullConv w η (F x)) 0 q =
      zeroExtend (generalRidgeFullConv w η (F y)) 0 q
    change zeroExtend (net.eval (F x)) 0 q =
        zeroExtend (generalRidgeFullConv w η (F x)) 0 q +
          zeroExtend offset 0 q at hxNorth
    change zeroExtend (net.eval (F y)) 0 q =
        zeroExtend (generalRidgeFullConv w η (F y)) 0 q +
          zeroExtend offset 0 q at hyNorth
    linarith
  refine ⟨net, offset, hdepth, hstateContinuous, hstateInjective, ?_⟩
  intro x hx
  constructor
  · rw [generalRidgeLState_terminal]
    exact (hbehavior x hx).1
  · intro q
    rw [generalRidgeLState_code]
    let qout : Fin (2 * (n + 2) + 1) := ⟨q, by omega⟩
    simpa [η, qout] using (hbehavior x hx).2 qout

end OneChannelCNNUniversality
