import OneChannelCNNUniversality.SharedBiasMonotoneCode

open OneChannelCNNUniversality

example {X : Type*} {K : Set X} {rows cols : ℕ}
    (hrows : 0 < rows) (hcols : 0 < cols)
    (F : X → Image rows cols)
    (hFnonnegative : ∀ x ∈ K, ImageNonnegative (F x))
    (hFvacant : ∀ x ∈ K, EastNeighborVacant (F x)) :
    NorthwestMonotoneCodeOn K
      (successorFeature
        (adjacentCopyLayer (rows := rows) (cols := cols)) F)
      (fun x ↦ zeroExtend (F x) 0 0) := by
  exact northwestMonotoneCodeOn_successor_adjacentCopy
    hrows hcols F hFnonnegative hFvacant

example {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {code : X → ℝ}
    (hcode : NorthwestMonotoneCodeOn K V code) :
    NorthwestMonotoneCodeOn K
      (fun x ↦ fullConvImage expansiveIdentityKernel (V x)) code := by
  exact hcode.expansiveIdentity

#check BundledPascalGridSelectionSpec.injective_on_northwestMonotoneCode
#check BundledPascalGridSelectionSpec.preserves_northwestMonotoneCode
#check NorthwestMonotoneCodeOn.of_eqOn
#check SharedBiasNetworkTo.appendWithSeed_preserves_northwestMonotoneCode
#check SharedBiasNetworkTo.appendWithSeed_injectiveOn_of_northwestMonotoneCode
