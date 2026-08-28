import ICM2022NumCS97.HybridProgram

open ICM2022NumCS97

example (z b : ℝ) : ActivationMode.eval (.relu b) z = relu (z + b) := rfl

example (z b : ℝ) : ActivationMode.eval (.translate b) z = z + b := rfl

example {kRows kCols rows cols : ℕ}
    (program : MaskProgram kRows kCols rows cols) (x : Image rows cols) :
    HEq ((HybridProgram.ofMaskProgram program).eval x) (program.eval x) := by
  exact HybridProgram.eval_ofMaskProgram_heq program x

example {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {kRows kCols rows cols : ℕ}
    (program : HybridProgram kRows kCols rows cols)
    (F V : X → Image rows cols) (known : Image rows cols)
    (hdecomp : ∀ x ∈ K, F x = V x + known)
    (hV : ContinuousFeatureOn K V) :
    ∃ (net : NetworkTo kRows kCols rows cols program.outRows program.outCols)
      (carrier : Image program.outRows program.outCols),
      ∀ x ∈ K, net.eval (F x) = program.eval (V x) + carrier := by
  exact program.exists_network hK F V known hdecomp hV

example {kRows kCols rows cols : ℕ}
    (first : HybridProgram kRows kCols rows cols)
    (second : HybridProgram kRows kCols first.outRows first.outCols)
    (x : Image rows cols) :
    HEq ((first.append second).eval x) (second.eval (first.eval x)) := by
  exact HybridProgram.eval_append_heq first second x

example {kRows kCols inRows inCols midRows midCols outRows outCols : ℕ}
    (first : HybridProgramTo kRows kCols inRows inCols midRows midCols)
    (second : HybridProgramTo kRows kCols midRows midCols outRows outCols)
    (x : Image inRows inCols) :
    (first.append second).eval x = second.eval (first.eval x) := by
  exact HybridProgramTo.eval_append first second x
