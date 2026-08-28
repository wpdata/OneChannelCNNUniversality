import OneChannelCNNUniversality.Program

open OneChannelCNNUniversality

example (rows cols kRows kCols : ℕ) (x : Image rows cols) :
    (MaskProgram.nil (kRows := kRows) (kCols := kCols) rows cols).eval x = x := by
  simp

example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {rows cols kRows kCols : ℕ}
    (program : MaskProgram kRows kCols rows cols)
    (V : X → Image rows cols) (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols program.outRows program.outCols)
      (carrier : Image program.outRows program.outCols),
      ∀ x ∈ K, net.eval (V x) = program.eval (V x) + carrier := by
  simpa using program.exists_network hK V V 0 (by simp) hV

example {kRows kCols rows cols : ℕ} (w final : Kernel kRows kCols)
    (steps : ℕ)
    (keep : Fin (grownSize kRows rows (steps + 1)) →
      Fin (grownSize kCols cols (steps + 1)) → Bool)
    (x : Image rows cols) :
    HEq ((MaskProgram.iterationsThenMask w final steps keep
      (MaskProgram.nil (kRows := kRows) (kCols := kCols) _ _)).eval x)
      (fun p q ↦ if keep p q then iterateThenConv w final steps x p q else 0) := by
  exact MaskProgram.eval_iterationsThenMask_heq w final steps keep
    (MaskProgram.nil (kRows := kRows) (kCols := kCols) _ _) x
