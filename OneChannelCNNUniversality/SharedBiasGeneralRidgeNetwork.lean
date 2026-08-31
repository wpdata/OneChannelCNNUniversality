import OneChannelCNNUniversality.SharedBiasGeneralRidgeSeparation
import OneChannelCNNUniversality.SharedBiasGeneralRidgeRecovery
import OneChannelCNNUniversality.SharedBiasTerminalSelection

/-!
# Protected arbitrary-width shared-bias ridge networks

For every depth `d ≥ 2`, this file combines the separated Lagrange factor
allocation, compact heterogeneous carrier construction, terminal unit-gap
selection, and northern polynomial recovery.  The result is a genuine
depth-`d`, one-channel expansive `2 × 2` shared-bias ReLU network whose
southern target is an arbitrary affine ReLU ridge and whose complete northern
row remains an affine injective encoding of the input.

The theorem is parameterized as `d = n + 2` so the last two factors are
definitionally available.  This is an exact ridge module, not yet the final
finite-sum universal approximation compiler.
-/

namespace OneChannelCNNUniversality

open Set

/-- Reindex an image along equal row and column dimensions. -/
private def reindexImage {rows cols rows' cols' : ℕ}
    (hrows : rows = rows') (hcols : cols = cols')
    (x : Image rows cols) : Image rows' cols' :=
  fun p q ↦ x (Fin.cast hrows.symm p) (Fin.cast hcols.symm q)

private theorem zeroExtend_reindexImage {rows cols rows' cols' : ℕ}
    (hrows : rows = rows') (hcols : cols = cols')
    (x : Image rows cols) (p q : ℕ) :
    zeroExtend (reindexImage hrows hcols x) p q = zeroExtend x p q := by
  subst rows'
  subst cols'
  rfl

/-- Repackage an explicitly typed network along equal output dimensions. -/
private def reindexSharedBiasNetworkTo
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols) :
    SharedBiasNetworkTo kRows kCols inRows inCols outRows' outCols' :=
  ⟨net.net, net.rows_eq.trans hrows, net.cols_eq.trans hcols⟩

private theorem zeroExtend_reindexSharedBiasNetworkTo_eval
    {kRows kCols inRows inCols outRows outCols outRows' outCols' : ℕ}
    (hrows : outRows = outRows') (hcols : outCols = outCols')
    (net : SharedBiasNetworkTo kRows kCols inRows inCols outRows outCols)
    (x : Image inRows inCols) (p q : ℕ) :
    zeroExtend ((reindexSharedBiasNetworkTo hrows hcols net).eval x) p q =
      zeroExtend (net.eval x) p q := by
  subst outRows'
  subst outCols'
  rfl

/-- With a `2 × 2` expansive kernel, each layer adds exactly one spatial
coordinate. -/
@[simp] theorem grownSize_two_eq_add (start steps : ℕ) :
    grownSize 2 start steps = start + steps := by
  induction steps generalizing start with
  | zero => simp [grownSize]
  | succ steps ih =>
      rw [grownSize, ih]
      omega

/-- The pure terminal signal obtained from the separated prefix and final two
factors has the requested ridge value at `(1,n+2)`. -/
theorem generalRidgeTerminalPureSignal_target
    {n : ℕ} (w : Fin (n + 3) → ℝ) (x : Image 1 (n + 3)) :
    let hd : 2 ≤ n + 2 := by omega
    let η := generalRidgeSeparatedAllocation hd w
    let init := generalRidgeFactorPrefix hd w η
    let penultimate :=
      generalRidgeKernelFactor w η (generalRidgePenultimateIndex hd)
    let final := generalRidgeSeparatedLastFactor hd w
    zeroExtend
        (bilinearTerminalPureSignal init penultimate final x) 1 (n + 2) =
      ∑ j : Fin (n + 3), w j * x 0 j := by
  dsimp only
  let hd : 2 ≤ n + 2 := by omega
  let η := generalRidgeSeparatedAllocation hd w
  let init := generalRidgeFactorPrefix hd w η
  let penultimate :=
    generalRidgeKernelFactor w η (generalRidgePenultimateIndex hd)
  let final := generalRidgeSeparatedLastFactor hd w
  have hsplit :
      generalRidgeFactorList w η = init ++ [penultimate, final] := by
    simpa [init, penultimate, final, generalRidgeSeparatedLastFactor] using
      (generalRidgeFactorList_split_last_two (n := n) w η)
  calc
    zeroExtend (bilinearTerminalPureSignal init penultimate final x) 1 (n + 2) =
        zeroExtend
          (fullConvChain [penultimate, final] (fullConvChain init x))
            1 (n + 2) := rfl
    _ = zeroExtend
          (fullConvChain (init ++ [penultimate, final]) x) 1 (n + 2) :=
        (zeroExtend_fullConvChain_append init [penultimate, final]
          x 1 (n + 2)).symm
    _ = zeroExtend (generalRidgeFullConv w η x) 1 (n + 2) := by
        rw [← hsplit]
        rfl
    _ = ∑ j : Fin (n + 3), w j * x 0 j := by
        exact generalRidgeFullConv_target w η
          (generalRidgeSeparatedAllocation_sum hd w) x

/-- At every natural northern coordinate, the terminal pure signal agrees
with the full arbitrary-width ridge convolution chain. -/
theorem generalRidgeTerminalPureSignal_north
    {n : ℕ} (w : Fin (n + 3) → ℝ) (x : Image 1 (n + 3)) (q : ℕ) :
    let hd : 2 ≤ n + 2 := by omega
    let η := generalRidgeSeparatedAllocation hd w
    let init := generalRidgeFactorPrefix hd w η
    let penultimate :=
      generalRidgeKernelFactor w η (generalRidgePenultimateIndex hd)
    let final := generalRidgeSeparatedLastFactor hd w
    zeroExtend (bilinearTerminalPureSignal init penultimate final x) 0 q =
      zeroExtend (generalRidgeFullConv w η x) 0 q := by
  dsimp only
  let hd : 2 ≤ n + 2 := by omega
  let η := generalRidgeSeparatedAllocation hd w
  let init := generalRidgeFactorPrefix hd w η
  let penultimate :=
    generalRidgeKernelFactor w η (generalRidgePenultimateIndex hd)
  let final := generalRidgeSeparatedLastFactor hd w
  have hsplit :
      generalRidgeFactorList w η = init ++ [penultimate, final] := by
    simpa [init, penultimate, final, generalRidgeSeparatedLastFactor] using
      (generalRidgeFactorList_split_last_two (n := n) w η)
  calc
    zeroExtend (bilinearTerminalPureSignal init penultimate final x) 0 q =
        zeroExtend
          (fullConvChain [penultimate, final] (fullConvChain init x)) 0 q := rfl
    _ = zeroExtend
          (fullConvChain (init ++ [penultimate, final]) x) 0 q :=
        (zeroExtend_fullConvChain_append init [penultimate, final] x 0 q).symm
    _ = zeroExtend (generalRidgeFullConv w η x) 0 q := by
        rw [← hsplit]
        rfl

/-- On a compact coordinatewise-continuous family, every affine ReLU ridge
on a one-row input of arbitrary width at least three is realized by a genuine
one-channel expansive shared-bias network.  The whole northern output row is
simultaneously preserved as the pure general-ridge convolution plus one fixed
offset.  This behavior theorem needs continuity but no injectivity assumption;
injectivity is derived below. -/
theorem exists_protectedGeneralRidgeNetwork_behavior_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 3))
    (hF : ContinuousFeatureOn K F) (w : Fin (n + 3) → ℝ) (gamma : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 (n + 3)
          (n + 3) (2 * (n + 2) + 1))
      (offset : Image (n + 3) (2 * (n + 2) + 1)),
      net.net.depth = n + 2 ∧
        (∀ x ∈ K,
          zeroExtend (net.eval (F x)) 1 (n + 2) =
            relu ((∑ j : Fin (n + 3), w j * F x 0 j) + gamma) ∧
          ∀ q : Fin (2 * (n + 2) + 1),
            zeroExtend (net.eval (F x)) 0 q =
              zeroExtend
                  (generalRidgeFullConv w
                    (generalRidgeSeparatedAllocation (by omega) w) (F x)) 0 q +
                zeroExtend offset 0 q) := by
  let hd : 2 ≤ n + 2 := by omega
  let η := generalRidgeSeparatedAllocation hd w
  let init := generalRidgeFactorPrefix hd w η
  let penultimate :=
    generalRidgeKernelFactor w η (generalRidgePenultimateIndex hd)
  let final := generalRidgeSeparatedLastFactor hd w
  have hinitLength : init.length = n := by
    simp [init]
  let target :
      Fin (grownSize 2 1 init.length + 2 - 1 + 2 - 1) ×
        Fin (grownSize 2 (n + 3) init.length + 2 - 1 + 2 - 1) :=
    (⟨1, by simp [hinitLength, grownSize_two_eq_add]⟩,
      ⟨n + 2, by simp [hinitLength, grownSize_two_eq_add]⟩)
  let protect :
      Fin (grownSize 2 1 init.length + 2 - 1 + 2 - 1) →
        Fin (grownSize 2 (n + 3) init.length + 2 - 1 + 2 - 1) → Prop :=
    fun p q ↦ (p : ℕ) = 0 ∨ (p, q) = target
  have haddress : ∀ p q, protect p q → (p, q) ≠ target →
      1 ≤ bilinearTerminalAddress (rows := 1) (cols := n + 3)
            init final p q -
          bilinearTerminalAddress (rows := 1) (cols := n + 3)
            init final target.1 target.2 := by
    intro p q hpq hne
    rcases hpq with hp | htarget
    · have hp0 : p = ⟨0, by
          simp [hinitLength, grownSize_two_eq_add]⟩ := Fin.ext hp
      subst p
      let q' : Fin (2 * (n + 2) + 1) :=
        ⟨q, by
          have hq := q.isLt
          simp only [hinitLength, grownSize_two_eq_add] at hq
          omega⟩
      have hgap := generalRidgeSeparatedLastKernel_gap hd w q'
      have htargetRow : (target.1 : ℕ) = 1 := by rfl
      have htargetCol : (target.2 : ℕ) = n + 2 := by rfl
      have hqVal : (q : ℕ) = (q' : ℕ) := rfl
      have haddressRows :
          grownSize 2 1 init.length + 2 - 1 = n + 2 := by
        simp [hinitLength, grownSize_two_eq_add]
        omega
      have haddressCols :
          grownSize 2 (n + 3) init.length + 2 - 1 =
            2 * (n + 2) := by
        simp [hinitLength, grownSize_two_eq_add]
        omega
      change 1 ≤
        fullConv final.kernel
            (constantImage
              (grownSize 2 1 init.length + 2 - 1)
              (grownSize 2 (n + 3) init.length + 2 - 1) 1) 0 q -
          fullConv final.kernel
            (constantImage
              (grownSize 2 1 init.length + 2 - 1)
              (grownSize 2 (n + 3) init.length + 2 - 1) 1)
              target.1 target.2
      rw [hqVal, htargetRow, htargetCol]
      rw [haddressRows, haddressCols]
      simpa only [final, generalRidgeSeparatedLastKernel, q'] using
          (show (1 : ℝ) ≤ _ from le_trans (by norm_num) hgap)
    · exact (hne htarget).elim
  obtain ⟨rawNet, rawOffset, hdepth, hterminal⟩ :=
    exists_shared_bias_bilinear_terminal_selection hK init penultimate final
      F hF protect target gamma haddress
  have hrows :
      grownSize 2 1 init.length + 2 - 1 + 2 - 1 = n + 3 := by
    simp [hinitLength, grownSize_two_eq_add]
    omega
  have hcols :
      grownSize 2 (n + 3) init.length + 2 - 1 + 2 - 1 =
        2 * (n + 2) + 1 := by
    simp [hinitLength, grownSize_two_eq_add]
    omega
  have hbehavior :
      ∀ x ∈ K,
        zeroExtend (rawNet.eval (F x)) 1 (n + 2) =
            relu ((∑ j : Fin (n + 3), w j * F x 0 j) + gamma) ∧
          ∀ q : Fin
              (grownSize 2 (n + 3) init.length + 2 - 1 + 2 - 1),
            zeroExtend (rawNet.eval (F x)) 0 q =
              zeroExtend (generalRidgeFullConv w η (F x)) 0 q +
                zeroExtend rawOffset 0 q := by
    intro x hx
    constructor
    · have htargetProtected : protect target.1 target.2 := Or.inr rfl
      have ht := hterminal x hx target.1 target.2 htargetProtected
      rw [if_pos rfl] at ht
      have htZero :
          zeroExtend (rawNet.eval (F x)) 1 (n + 2) =
            rawNet.eval (F x) target.1 target.2 := by
        exact zeroExtend_of_lt _ target.1.isLt target.2.isLt
      rw [htZero, ht]
      congr 1
      simpa [target, init, η, penultimate, final, hd] using
        generalRidgeTerminalPureSignal_target w (F x)
    · intro q
      let p0 : Fin
          (grownSize 2 1 init.length + 2 - 1 + 2 - 1) :=
        ⟨0, by simp [hinitLength, grownSize_two_eq_add]⟩
      have hpProtected : protect p0 q := Or.inl rfl
      have hpNe : (p0, q) ≠ target := by
        intro heq
        have := congrArg (fun z ↦ (z.1 : ℕ)) heq
        simp [p0, target] at this
      have hn := hterminal x hx p0 q hpProtected
      rw [if_neg hpNe] at hn
      calc
        zeroExtend (rawNet.eval (F x)) 0 q = rawNet.eval (F x) p0 q := by
          exact zeroExtend_of_lt _ p0.isLt q.isLt
        _ = bilinearTerminalPureSignal init penultimate final (F x) p0 q +
              rawOffset p0 q := hn
        _ = zeroExtend (generalRidgeFullConv w η (F x)) 0 q +
              zeroExtend rawOffset 0 q := by
          rw [← generalRidgeTerminalPureSignal_north w (F x) q]
          rw [zeroExtend_of_lt, zeroExtend_of_lt]
  let net : SharedBiasNetworkTo 2 2 1 (n + 3)
      (n + 3) (2 * (n + 2) + 1) :=
    reindexSharedBiasNetworkTo hrows hcols rawNet
  let offset : Image (n + 3) (2 * (n + 2) + 1) :=
    reindexImage hrows hcols rawOffset
  have hnormalizedBehavior :
      ∀ x ∈ K,
        zeroExtend (net.eval (F x)) 1 (n + 2) =
            relu ((∑ j : Fin (n + 3), w j * F x 0 j) + gamma) ∧
          ∀ q : Fin (2 * (n + 2) + 1),
            zeroExtend (net.eval (F x)) 0 q =
              zeroExtend (generalRidgeFullConv w η (F x)) 0 q +
                zeroExtend offset 0 q := by
    intro x hx
    constructor
    · simpa only [net, zeroExtend_reindexSharedBiasNetworkTo_eval] using
        (hbehavior x hx).1
    · intro q
      have hq := (hbehavior x hx).2 (Fin.cast hcols.symm q)
      simpa only [net, offset,
        zeroExtend_reindexSharedBiasNetworkTo_eval,
        zeroExtend_reindexImage, Fin.val_cast] using hq
  refine ⟨net, offset, ?_, ?_⟩
  · simpa [net, reindexSharedBiasNetworkTo, hinitLength] using hdepth
  · simpa only [η, hd] using hnormalizedBehavior

/-- Injective-feature corollary of the compact arbitrary-width ridge
construction.  The construction itself needs only continuity; injectivity is
used here, and only here, together with exact recovery from the protected
northern row. -/
theorem exists_protectedGeneralRidgeNetwork_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n : ℕ} (F : X → Image 1 (n + 3))
    (hF : ContinuousFeatureOn K F) (hFinjective : Set.InjOn F K)
    (w : Fin (n + 3) → ℝ) (gamma : ℝ) :
    ∃ (net : SharedBiasNetworkTo 2 2 1 (n + 3)
          (n + 3) (2 * (n + 2) + 1))
      (offset : Image (n + 3) (2 * (n + 2) + 1)),
      net.net.depth = n + 2 ∧
        (∀ x ∈ K,
          zeroExtend (net.eval (F x)) 1 (n + 2) =
            relu ((∑ j : Fin (n + 3), w j * F x 0 j) + gamma) ∧
          ∀ q : Fin (2 * (n + 2) + 1),
            zeroExtend (net.eval (F x)) 0 q =
              zeroExtend
                  (generalRidgeFullConv w
                    (generalRidgeSeparatedAllocation (by omega) w) (F x)) 0 q +
                zeroExtend offset 0 q) ∧
        Set.InjOn (fun x ↦ net.eval (F x)) K := by
  obtain ⟨net, offset, hdepth, hbehavior⟩ :=
    exists_protectedGeneralRidgeNetwork_behavior_on_compact
      hK F hF w gamma
  refine ⟨net, offset, hdepth, hbehavior, ?_⟩
  intro x hx y hy hxy
  apply hFinjective hx hy
  apply generalRidgeFullConv_north_eq_imp_eq w
    (generalRidgeSeparatedAllocation (by omega) w)
  intro q
  let qout : Fin (2 * (n + 2) + 1) :=
    ⟨q, by
      have hq := q.isLt
      simp only [grownSize_two_eq_add] at hq
      omega⟩
  have hxNorth := (hbehavior x hx).2 qout
  have hyNorth := (hbehavior y hy).2 qout
  have hnet := congrArg (fun z ↦ zeroExtend z 0 qout) hxy
  rw [generalRidgeFullConvNorthRow_apply,
    generalRidgeFullConvNorthRow_apply]
  linarith

end OneChannelCNNUniversality
