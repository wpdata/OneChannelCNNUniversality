import OneChannelCNNUniversality.SharedBiasHeterogeneousCarrier
import OneChannelCNNUniversality.SharedBiasRecovery

/-!
# Terminal shared-bias selection after a heterogeneous prefix

This module packages the compact carrier argument used by the arbitrary-width
ridge construction.  A heterogeneous prefix is kept in ReLU's linear branch,
and its last bias has a tunable nonnegative boost.  The final convolution sees
that boost as a fixed spatial address.  Whenever the address has a unit gap on
the protected coordinates, compactness chooses one boost scale that makes the
final shared scalar bias apply ReLU only at the target and keep every other
protected coordinate linear.
-/

namespace OneChannelCNNUniversality

open Set

/-- Address produced when the final kernel convolves a unit constant image
created after `init.length + 1` prefix layers. -/
def bilinearTerminalAddress
    {rows cols : ℕ} (init : List BilinearKernelFactor)
    (final : BilinearKernelFactor) :
    Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
  fullConvImage final.kernel
    (constantImage
      (grownSize 2 rows init.length + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1) 1)

/-- Pure formal signal after `init`, one penultimate factor, and one final
factor. -/
def bilinearTerminalPureSignal
    (init : List BilinearKernelFactor)
    (penultimate final : BilinearKernelFactor)
    {rows cols : ℕ} (x : Image rows cols) :
    Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
  fullConvImage final.kernel
    (fullConvImage penultimate.kernel (fullConvChain init x))

/-- Convolution of a constant image scales the convolution of the unit
constant image. -/
theorem fullConv_constantImage_eq_mul_unit
    {kRows kCols rows cols : ℕ} (w : Kernel kRows kCols)
    (c : ℝ) (p : Fin (rows + kRows - 1))
    (q : Fin (cols + kCols - 1)) :
    fullConv w (constantImage rows cols c) p q =
      c * fullConv w (constantImage rows cols 1) p q := by
  have hconstant :
      constantImage rows cols c = c • constantImage rows cols 1 := by
    funext i j
    simp [constantImage]
  change fullConvImage w (constantImage rows cols c) p q =
    c * fullConvImage w (constantImage rows cols 1) p q
  rw [hconstant, fullConvImage_smul]
  rfl

/-- Compact terminal-selection compiler for two final heterogeneous factors.
The target receives `relu (pureSignal + theta)`.  Every other protected site
equals the pure signal plus one fixed offset image.  Expansion sites outside
`protect` are intentionally unconstrained. -/
theorem exists_shared_bias_bilinear_terminal_selection
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (init : List BilinearKernelFactor)
    (penultimate final : BilinearKernelFactor)
    {rows cols : ℕ} (F : X → Image rows cols)
    (hF : ContinuousFeatureOn K F)
    (protect :
      Fin (grownSize 2 rows init.length + 2 - 1 + 2 - 1) →
        Fin (grownSize 2 cols init.length + 2 - 1 + 2 - 1) → Prop)
    (target :
      Fin (grownSize 2 rows init.length + 2 - 1 + 2 - 1) ×
        Fin (grownSize 2 cols init.length + 2 - 1 + 2 - 1))
    (theta : ℝ)
    (haddress : ∀ p q, protect p q → (p, q) ≠ target →
      1 ≤ bilinearTerminalAddress (rows := rows) (cols := cols)
          init final p q -
        bilinearTerminalAddress (rows := rows) (cols := cols)
          init final target.1 target.2) :
    ∃ (net : SharedBiasNetworkTo 2 2 rows cols
          (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
          (grownSize 2 cols init.length + 2 - 1 + 2 - 1))
      (offset : Image
        (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
        (grownSize 2 cols init.length + 2 - 1 + 2 - 1)),
      net.net.depth = init.length + 2 ∧
        ∀ x ∈ K, ∀ p q, protect p q →
          net.eval (F x) p q =
            if (p, q) = target then
              relu (bilinearTerminalPureSignal init penultimate final (F x) p q +
                theta)
            else
              bilinearTerminalPureSignal init penultimate final (F x) p q +
                offset p q := by
  have hdecomp :
      ∀ x ∈ K, F x = F x + (0 : Image rows cols) := by
    intro x hx
    simp
  obtain ⟨prefixNet, _baseBias, prefixCarrier, _hbaseBias,
      hprefixDepth, hprefix⟩ :=
    exists_shared_bias_bilinear_prefix_with_terminal_boost
      hK init penultimate F F (0 : Image rows cols) hdecomp hF
  let fixedCarrier : Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
    fullConvImage final.kernel prefixCarrier
  let pureSignal : X → Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
    fun x ↦ bilinearTerminalPureSignal init penultimate final (F x)
  let signal : X → Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
    fun x ↦ pureSignal x + fixedCarrier
  let address := bilinearTerminalAddress
    (rows := rows) (cols := cols) init final
  let selectedTheta : ℝ := theta - fixedCarrier target.1 target.2
  have hinit : ContinuousFeatureOn K
      (fun x ↦ fullConvChain init (F x)) :=
    continuousFeatureOn_fullConvChain init F hF
  have hpenultimate : ContinuousFeatureOn K
      (fun x ↦ fullConvImage penultimate.kernel (fullConvChain init (F x))) := by
    intro p q
    exact continuousFeatureOn_fullConv hinit penultimate.kernel p q
  have hpure : ContinuousFeatureOn K pureSignal := by
    intro p q
    exact continuousFeatureOn_fullConv hpenultimate final.kernel p q
  have hsignal : ContinuousFeatureOn K signal := by
    intro p q
    exact (hpure p q).add continuousOn_const
  obtain ⟨scale, hscale, hselect⟩ :=
    exists_sharedBias_select_from_unit_address_on hK signal hsignal
      address protect target selectedTheta (by
        intro p q hpq hne
        exact haddress p q hpq hne)
  let finalBias : ℝ :=
    selectedTheta - scale * address target.1 target.2
  let net : SharedBiasNetworkTo 2 2 rows cols
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
    (prefixNet scale).append
      (SharedBiasNetworkTo.single final.kernel finalBias)
  let offset : Image
      (grownSize 2 rows init.length + 2 - 1 + 2 - 1)
      (grownSize 2 cols init.length + 2 - 1 + 2 - 1) :=
    fun p q ↦ fixedCarrier p q + scale * address p q + finalBias
  refine ⟨net, offset, ?_, ?_⟩
  · change ((prefixNet scale).append
      (SharedBiasNetworkTo.single final.kernel finalBias)).net.depth = _
    rw [SharedBiasNetworkTo.depth_append, hprefixDepth]
    rfl
  intro x hx p q hpq
  have hprefixEval := hprefix scale hscale.le x hx
  have hconstant :
      fullConv final.kernel
          (constantImage
            (grownSize 2 rows init.length + 2 - 1)
            (grownSize 2 cols init.length + 2 - 1) scale) p q =
        scale * address p q := by
    exact fullConv_constantImage_eq_mul_unit final.kernel scale p q
  have hpreactivation :
      fullConv final.kernel ((prefixNet scale).eval (F x)) p q + finalBias =
        signal x p q + scale * address p q +
          (selectedTheta - scale * address target.1 target.2) := by
    rw [hprefixEval, fullConv_add, fullConv_add, hconstant]
    simp only [signal, pureSignal, bilinearTerminalPureSignal, fixedCarrier,
      fullConvImage, Pi.add_apply, finalBias]
  have hselected := hselect x hx p q hpq
  change ((prefixNet scale).append
      (SharedBiasNetworkTo.single final.kernel finalBias)).eval (F x) p q = _
  rw [SharedBiasNetworkTo.eval_append, SharedBiasNetworkTo.eval_single]
  change relu
      (fullConv final.kernel ((prefixNet scale).eval (F x)) p q + finalBias) = _
  rw [hpreactivation, hselected]
  by_cases htarget : (p, q) = target
  · rw [if_pos htarget, if_pos htarget]
    have hp : p = target.1 := congrArg Prod.fst htarget
    have hq : q = target.2 := congrArg Prod.snd htarget
    subst p
    subst q
    simp only [signal, pureSignal, selectedTheta, Pi.add_apply]
    congr 1
    ring
  · rw [if_neg htarget, if_neg htarget]
    simp only [signal, pureSignal, offset, Pi.add_apply]
    ring

end OneChannelCNNUniversality
