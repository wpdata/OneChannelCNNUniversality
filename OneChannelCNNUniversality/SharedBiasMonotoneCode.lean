import OneChannelCNNUniversality.SharedBiasAdjacentCopy

/-!
# A monotone northwest code for repeated selected ReLUs

Exact duplication is needed only to initialize the first selected block.
Afterward the northwest work register may be any monotone function of a
latent scalar, provided its eastern backup is a strictly monotone function
of the same scalar.  The eastern protected output then continues to recover
the latent scalar after every selected ReLU.
-/

namespace OneChannelCNNUniversality

/-- On `K`, the northwest work coordinate and its eastern backup factor
through a common scalar code.  The work factor is monotone and the backup
factor is strictly monotone. -/
def NorthwestMonotoneCodeOn
    {X : Type*} (K : Set X) {rows cols : ℕ}
    (V : X → Image rows cols) (code : X → ℝ) : Prop :=
  ∃ rootFn eastFn : ℝ → ℝ,
    Monotone rootFn ∧ StrictMono eastFn ∧
      ∀ x ∈ K,
        zeroExtend (V x) 0 0 = rootFn (code x) ∧
        zeroExtend (V x) 0 1 = eastFn (code x)

/-- The expansive delta bridge preserves both northwest coordinates and
therefore preserves every northwest monotone code. -/
theorem NorthwestMonotoneCodeOn.expansiveIdentity
    {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {code : X → ℝ}
    (hcode : NorthwestMonotoneCodeOn K V code) :
    NorthwestMonotoneCodeOn K
      (fun x ↦ fullConvImage expansiveIdentityKernel (V x)) code := by
  obtain ⟨rootFn, eastFn, hrootMono, heastStrict, hfactor⟩ := hcode
  refine ⟨rootFn, eastFn, hrootMono, heastStrict, ?_⟩
  intro x hx
  rw [zeroExtend_fullConvImage, zeroExtend_fullConvImage,
    fullConv_expansiveIdentityKernel_nat,
    fullConv_expansiveIdentityKernel_nat]
  exact hfactor x hx

/-- A northwest monotone code depends only on the values of the feature
family on the certified set. -/
theorem NorthwestMonotoneCodeOn.of_eqOn
    {X : Type*} {K : Set X} {rows cols : ℕ}
    {V W : X → Image rows cols} {code : X → ℝ}
    (hcode : NorthwestMonotoneCodeOn K V code)
    (hVW : ∀ x ∈ K, W x = V x) :
    NorthwestMonotoneCodeOn K W code := by
  obtain ⟨rootFn, eastFn, hrootMono, heastStrict, hfactor⟩ := hcode
  refine ⟨rootFn, eastFn, hrootMono, heastStrict, ?_⟩
  intro x hx
  rw [hVW x hx]
  exact hfactor x hx

/-- The genuine adjacent-copy layer followed by the genuine delta seed
bridge initializes the monotone code with both factors equal to identity. -/
theorem northwestMonotoneCodeOn_successor_adjacentCopy
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 0 < cols)
    (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFvacant : ∀ x ∈ K, EastNeighborVacant (F x)) :
    NorthwestMonotoneCodeOn K
      (successorFeature
        (adjacentCopyLayer (rows := rows) (cols := cols)) F)
      (fun x ↦ zeroExtend (F x) 0 0) := by
  refine ⟨id, id, monotone_id, strictMono_id, ?_⟩
  intro x hx
  have hcopy := adjacentCopyLayer_eastRootDuplicate hrows hcols
    (hFnonnegative x hx) (hFvacant x hx)
  have hroot : zeroExtend
      ((adjacentCopyLayer (rows := rows) (cols := cols)).eval (F x))
      0 0 = zeroExtend (F x) 0 0 := by
    rw [adjacentCopyLayer_eval_of_nonnegative (hFnonnegative x hx),
      zeroExtend_fullConvImage,
      fullConv_horizontalAccumulationKernel_nat]
    simp
  have hsuccessor := hcopy.successorFeature
  unfold EastRootDuplicate at hsuccessor
  constructor
  · unfold successorFeature
    rw [zeroExtend_fullConvImage,
      fullConv_expansiveIdentityKernel_nat, hroot]
    rfl
  · rw [← hsuccessor]
    unfold successorFeature
    rw [zeroExtend_fullConvImage,
      fullConv_expansiveIdentityKernel_nat, hroot]
    rfl

/-- Exact northwest-root output of a bundled selector, written with natural
coordinates so it can be used directly by code invariants. -/
theorem BundledPascalGridSelectionSpec.eval_northwest_zero
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 0 < cols)
    {V : X → Image rows cols} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin rows) (⟨0, hcols⟩ : Fin cols) c b net)
    {x : X} (hx : x ∈ K) :
    zeroExtend (net.eval (V x + constantImage rows cols c)) 0 0 =
      relu (zeroExtend (V x) 0 0 + θ) := by
  let targetRow : Fin rows := ⟨0, hrows⟩
  let targetCol : Fin cols := ⟨0, hcols⟩
  have hprotected :
      southeastProtected targetRow targetCol targetRow targetCol :=
    ⟨le_rfl, le_rfl⟩
  have hs := hspec.2 x hx targetRow targetCol hprotected
  rw [if_pos rfl] at hs
  rw [protectedLinearizedPascalSignal_northwest_zero
    hrows hcols] at hs
  have houtRows : 0 < protectedSelectionSize rows rowSteps extraColSteps := by
    have hlt := original_lt_pascalStage rows extraColSteps rowSteps targetRow
    simp only [protectedSelectionSize]
    omega
  have houtCols : 0 < protectedSelectionSize cols rowSteps extraColSteps := by
    have hlt := original_lt_pascalStage cols extraColSteps rowSteps targetCol
    simp only [protectedSelectionSize]
    omega
  rw [zeroExtend_of_lt _ houtRows houtCols]
  have hroot : zeroExtend (V x) 0 0 =
      V x targetRow targetCol := by
    rw [zeroExtend_of_lt _ hrows hcols]
  simpa [targetRow, targetCol, hroot] using hs

/-- Exact eastern-backup output.  Its variable part is the previous backup
plus a nonnegative integer multiple of the previous work value. -/
theorem BundledPascalGridSelectionSpec.eval_northwest_one
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 2 ≤ cols)
    {V : X → Image rows cols} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin rows) (⟨0, by omega⟩ : Fin cols) c b net)
    {x : X} (hx : x ∈ K) :
    zeroExtend (net.eval (V x + constantImage rows cols c)) 0 1 =
      zeroExtend (V x) 0 1 +
        (extraColSteps + 1 : ℕ) * zeroExtend (V x) 0 0 +
        protectedLinearizedPascalCarrier rowSteps extraColSteps
          rows cols c b (⟨0, hrows⟩ : Fin rows)
            (⟨1, by omega⟩ : Fin cols) +
        (θ - protectedLinearizedPascalCarrier rowSteps extraColSteps
          rows cols c b (⟨0, hrows⟩ : Fin rows)
            (⟨0, by omega⟩ : Fin cols)) := by
  let targetRow : Fin rows := ⟨0, hrows⟩
  let targetCol : Fin cols := ⟨0, by omega⟩
  let backupCol : Fin cols := ⟨1, by omega⟩
  have hprotected :
      southeastProtected targetRow targetCol targetRow backupCol := by
    simp [southeastProtected, targetRow, targetCol, backupCol]
  have hs := hspec.2 x hx targetRow backupCol hprotected
  have hne : (targetRow, backupCol) ≠ (targetRow, targetCol) := by
    simp [backupCol, targetCol]
  rw [if_neg hne] at hs
  rw [protectedLinearizedPascalSignal_northwest_one
    hrows hcols] at hs
  have houtRows : 0 < protectedSelectionSize rows rowSteps extraColSteps := by
    have hlt := original_lt_pascalStage rows extraColSteps rowSteps targetRow
    simp only [protectedSelectionSize]
    omega
  have houtCols : 1 < protectedSelectionSize cols rowSteps extraColSteps := by
    have hlt := original_lt_pascalStage cols extraColSteps rowSteps backupCol
    simp only [protectedSelectionSize]
    omega
  rw [zeroExtend_of_lt _ houtRows houtCols]
  have hzero : zeroExtend (V x) 0 0 = V x targetRow targetCol := by
    rw [zeroExtend_of_lt _ hrows (by omega)]
  have hone : zeroExtend (V x) 0 1 = V x targetRow backupCol := by
    rw [zeroExtend_of_lt _ hrows (by omega)]
  simpa [targetRow, targetCol, backupCol, hzero, hone,
    add_assoc] using hs

/-- Equality of complete selector outputs recovers the selector input when
the northwest pair carries a monotone/strictly-monotone common scalar code. -/
theorem BundledPascalGridSelectionSpec.injective_on_northwestMonotoneCode
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 2 ≤ cols)
    {V : X → Image rows cols} {code : X → ℝ} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin rows) (⟨0, by omega⟩ : Fin cols) c b net)
    (hcode : NorthwestMonotoneCodeOn K V code)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (heval : net.eval (V x + constantImage rows cols c) =
      net.eval (V y + constantImage rows cols c)) :
    V x = V y := by
  obtain ⟨rootFn, eastFn, hrootMono, heastStrict, hfactor⟩ := hcode
  have heast := congrArg (fun z ↦ zeroExtend z 0 1) heval
  rw [hspec.eval_northwest_one hrows hcols hx,
    hspec.eval_northwest_one hrows hcols hy] at heast
  have hxfactor := hfactor x hx
  have hyfactor := hfactor y hy
  rw [hxfactor.1, hxfactor.2, hyfactor.1, hyfactor.2] at heast
  let combined : ℝ → ℝ := fun t ↦
    eastFn t + (extraColSteps + 1 : ℕ) * rootFn t
  have hcombined : StrictMono combined := by
    intro s t hst
    have heastlt := heastStrict hst
    have hrootle := hrootMono hst.le
    have hcoefficient : (0 : ℝ) ≤ extraColSteps + 1 := by positivity
    dsimp [combined]
    nlinarith
  have hcombinedEq : combined (code x) = combined (code y) := by
    dsimp [combined]
    linarith
  have hcodeEq : code x = code y := hcombined.injective hcombinedEq
  have hrootValue : zeroExtend (V x) 0 0 = zeroExtend (V y) 0 0 := by
    rw [hxfactor.1, hyfactor.1, hcodeEq]
  apply protectedLinearizedPascalSignal_injective rowSteps extraColSteps
  funext i j
  let targetRow : Fin rows := ⟨0, hrows⟩
  let targetCol : Fin cols := ⟨0, by omega⟩
  by_cases hroot : (i, j) = (targetRow, targetCol)
  · have hi : i = targetRow := congrArg Prod.fst hroot
    have hj : j = targetCol := congrArg Prod.snd hroot
    subst i
    subst j
    rw [protectedLinearizedPascalSignal_northwest_zero hrows (by omega),
      protectedLinearizedPascalSignal_northwest_zero hrows (by omega)]
    have hrootValue' : V x targetRow targetCol =
        V y targetRow targetCol := by
      rw [← zeroExtend_of_lt (V x) hrows (by omega),
        ← zeroExtend_of_lt (V y) hrows (by omega)]
      exact hrootValue
    exact hrootValue'
  · have hprotected : southeastProtected targetRow targetCol i j := by
      constructor
      · change (0 : ℕ) ≤ (i : ℕ)
        exact Nat.zero_le _
      · change (0 : ℕ) ≤ (j : ℕ)
        exact Nat.zero_le _
    have hxspec := hspec.2 x hx i j hprotected
    have hyspec := hspec.2 y hy i j hprotected
    have hevalij := congrFun (congrFun heval
      (⟨i, by
        have := original_lt_pascalStage rows extraColSteps rowSteps i
        simp only [protectedSelectionSize]
        omega⟩))
      (⟨j, by
        have := original_lt_pascalStage cols extraColSteps rowSteps j
        simp only [protectedSelectionSize]
        omega⟩)
    rw [hxspec, hyspec, if_neg hroot, if_neg hroot] at hevalij
    linarith

/-- One genuine selected block closes the monotone-code invariant.  The new
root factor is a ReLU of the old monotone factor; the new eastern factor is
the old strictly monotone factor plus a nonnegative multiple of the root
factor and a fixed carrier shift. -/
theorem BundledPascalGridSelectionSpec.preserves_northwestMonotoneCode
    {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 2 ≤ cols)
    {V : X → Image rows cols} {code : X → ℝ} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin rows) (⟨0, by omega⟩ : Fin cols) c b net)
    (hcode : NorthwestMonotoneCodeOn K V code) :
    NorthwestMonotoneCodeOn K
      (fun x ↦ net.eval (V x + constantImage rows cols c)) code := by
  obtain ⟨rootFn, eastFn, hrootMono, heastStrict, hfactor⟩ := hcode
  let shift : ℝ :=
    protectedLinearizedPascalCarrier rowSteps extraColSteps
      rows cols c b (⟨0, hrows⟩ : Fin rows)
        (⟨1, by omega⟩ : Fin cols) +
      (θ - protectedLinearizedPascalCarrier rowSteps extraColSteps
        rows cols c b (⟨0, hrows⟩ : Fin rows)
          (⟨0, by omega⟩ : Fin cols))
  let nextRoot : ℝ → ℝ := fun t ↦ relu (rootFn t + θ)
  let nextEast : ℝ → ℝ := fun t ↦
    eastFn t + (extraColSteps + 1 : ℕ) * rootFn t + shift
  have hnextRoot : Monotone nextRoot := by
    intro s t hst
    have hle : rootFn s + θ ≤ rootFn t + θ :=
      by linarith [hrootMono hst]
    exact max_le_max hle le_rfl
  have hnextEast : StrictMono nextEast := by
    intro s t hst
    have heastlt := heastStrict hst
    have hrootle := hrootMono hst.le
    have hcoefficient : (0 : ℝ) ≤ extraColSteps + 1 := by positivity
    dsimp [nextEast]
    nlinarith
  refine ⟨nextRoot, nextEast, hnextRoot, hnextEast, ?_⟩
  intro x hx
  have hxfactor := hfactor x hx
  constructor
  · rw [hspec.eval_northwest_zero hrows (by omega) hx, hxfactor.1]
  · rw [hspec.eval_northwest_one hrows hcols hx,
      hxfactor.1, hxfactor.2]
    dsimp [nextEast, shift]
    ring

namespace SharedBiasNetworkTo

/-- The monotone-code invariant proved for a selector is inherited by the
actual network obtained by composing that selector through a genuine seed
layer. -/
theorem appendWithSeed_preserves_northwestMonotoneCode
    {X : Type*} {K : Set X}
    {inRows inCols midRows midCols : ℕ}
    {head : SharedBiasNetworkTo 2 2
      inRows inCols midRows midCols}
    {F : X → Image inRows inCols} {code : X → ℝ}
    {θ c b : ℝ} {rowSteps extraColSteps : ℕ}
    {tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1)
      (protectedSelectionSize (midRows + 2 - 1) rowSteps extraColSteps)
      (protectedSelectionSize (midCols + 2 - 1) rowSteps extraColSteps)}
    (hrows : 0 < midRows + 2 - 1)
    (hcols : 2 ≤ midCols + 2 - 1)
    (hspec : BundledPascalGridSelectionSpec K
      (successorFeature head F) θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin (midRows + 2 - 1))
      (⟨0, by omega⟩ : Fin (midCols + 2 - 1)) c b tail)
    (hcode : NorthwestMonotoneCodeOn K
      (successorFeature head F) code)
    (heval : ∀ x ∈ K,
      (head.appendWithSeed c tail).eval (F x) =
        tail.eval
          (successorFeature head F x +
            constantImage (midRows + 2 - 1) (midCols + 2 - 1) c)) :
    NorthwestMonotoneCodeOn K
      (fun x ↦ (head.appendWithSeed c tail).eval (F x)) code := by
  apply (hspec.preserves_northwestMonotoneCode hrows hcols hcode).of_eqOn
  exact heval

/-- If the preceding network is injective on `K`, then appending a selector
whose successor feature carries a northwest monotone code preserves that
injectivity.  This statement concerns the evaluation of the genuinely
composed shared-bias CNN, not an external feature transformation. -/
theorem appendWithSeed_injectiveOn_of_northwestMonotoneCode
    {X : Type*} {K : Set X}
    {inRows inCols midRows midCols : ℕ}
    {head : SharedBiasNetworkTo 2 2
      inRows inCols midRows midCols}
    {F : X → Image inRows inCols} {code : X → ℝ}
    {θ c b : ℝ} {rowSteps extraColSteps : ℕ}
    {tail : SharedBiasNetworkTo 2 2
      (midRows + 2 - 1) (midCols + 2 - 1)
      (protectedSelectionSize (midRows + 2 - 1) rowSteps extraColSteps)
      (protectedSelectionSize (midCols + 2 - 1) rowSteps extraColSteps)}
    (hrows : 0 < midRows + 2 - 1)
    (hcols : 2 ≤ midCols + 2 - 1)
    (hspec : BundledPascalGridSelectionSpec K
      (successorFeature head F) θ rowSteps extraColSteps
      (⟨0, hrows⟩ : Fin (midRows + 2 - 1))
      (⟨0, by omega⟩ : Fin (midCols + 2 - 1)) c b tail)
    (hcode : NorthwestMonotoneCodeOn K
      (successorFeature head F) code)
    (hheadInjective : Set.InjOn (fun x ↦ head.eval (F x)) K)
    (heval : ∀ x ∈ K,
      (head.appendWithSeed c tail).eval (F x) =
        tail.eval
          (successorFeature head F x +
            constantImage (midRows + 2 - 1) (midCols + 2 - 1) c)) :
    Set.InjOn (fun x ↦ (head.appendWithSeed c tail).eval (F x)) K := by
  intro x hx y hy hfinal
  have htail :
      tail.eval
          (successorFeature head F x +
            constantImage (midRows + 2 - 1) (midCols + 2 - 1) c) =
        tail.eval
          (successorFeature head F y +
            constantImage (midRows + 2 - 1) (midCols + 2 - 1) c) := by
    rw [← heval x hx, ← heval y hy]
    exact hfinal
  have hsuccessor : successorFeature head F x =
      successorFeature head F y :=
    hspec.injective_on_northwestMonotoneCode
      hrows hcols hcode hx hy htail
  have hhead : head.eval (F x) = head.eval (F y) :=
    fullConvImage_expansiveIdentityKernel_injective hsuccessor
  exact hheadInjective hx hy hhead

end SharedBiasNetworkTo

end OneChannelCNNUniversality
