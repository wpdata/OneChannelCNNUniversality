import OneChannelCNNUniversality.SharedBiasRedundantRecovery

open OneChannelCNNUniversality

example {n : ℕ} (hn : 0 < n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨0, hn⟩ : Fin n) =
      x rowZero ⟨0, hn⟩ := by
  exact protectedLinearizedPascalSignal_rowZero_zero
    hn rowSteps extraColSteps x

example {n : ℕ} (hn : 2 ≤ n) (rowSteps extraColSteps : ℕ)
    (x : Image 1 n) :
    protectedLinearizedPascalSignal rowSteps extraColSteps x rowZero
        (⟨1, by omega⟩ : Fin n) =
      x rowZero ⟨1, by omega⟩ +
        (extraColSteps + 1 : ℕ) * x rowZero ⟨0, by omega⟩ := by
  exact protectedLinearizedPascalSignal_rowZero_one
    hn rowSteps extraColSteps x

example {X : Type*} {K : Set X} {n : ℕ} (hn : 2 ≤ n)
    {V : X → Image 1 n} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {net : SharedBiasNetworkTo 2 2 1 n
      (protectedSelectionSize 1 rowSteps extraColSteps)
      (protectedSelectionSize n rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      rowZero (⟨0, by omega⟩ : Fin n) c b net)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxdup : EastRootDuplicate (V x))
    (hydup : EastRootDuplicate (V y))
    (heval : net.eval (V x + constantImage 1 n c) =
      net.eval (V y + constantImage 1 n c)) :
    V x = V y := by
  exact hspec.injective_on_eastRootDuplicate
    (by omega) hn hx hy hxdup hydup heval

#check EastRootDuplicate
#check BundledPascalGridSelectionSpec.injective_on_eastRootDuplicate
