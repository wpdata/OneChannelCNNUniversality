import OneChannelCNNUniversality.SharedBiasFiniteRecovery

open OneChannelCNNUniversality

example {X A B : Type} {K : Set X} {F : X → A} {G : X → B}
    (step : RelativeRecoveryStep K F G) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) (hp : step.Protected x y)
    (heq : G x = G y) : F x = F y := by
  exact step.recover hx hy hp heq

example {X A B : Type} {K : Set X} {F : X → A} {G : X → B}
    (chain : RelativeRecoveryChain K F G) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) (hp : chain.Protected x y)
    (heq : G x = G y) : F x = F y := by
  exact chain.recover hx hy hp heq

example {X A : Type} {K : Set X} (F : X → A) :
    (RelativeRecoveryChain.nil (K := K) F).length = 0 := rfl

example {X A B C : Type} {K : Set X}
    {F : X → A} {G : X → B} {H : X → C}
    (step : RelativeRecoveryStep K F G)
    (tail : RelativeRecoveryChain K G H) :
    (RelativeRecoveryChain.cons step tail).length = tail.length + 1 := rfl

example {X A B C : Type} {K : Set X}
    {F : X → A} {G : X → B} {H : X → C}
    (left : RelativeRecoveryChain K F G)
    (right : RelativeRecoveryChain K G H) :
    RelativeRecoveryChain K F H :=
  left.append right

example {X A B C : Type} {K : Set X}
    {F : X → A} {G : X → B} {H : X → C}
    (left : RelativeRecoveryChain K F G)
    (right : RelativeRecoveryChain K G H) :
    (left.append right).length = left.length + right.length := by
  exact RelativeRecoveryChain.length_append left right

example {X A B C : Type} {K : Set X}
    {F : X → A} {G : X → B} {H : X → C}
    (left : RelativeRecoveryChain K F G)
    (right : RelativeRecoveryChain K G H) (x y : X) :
    (left.append right).Protected x y ↔
      left.Protected x y ∧ right.Protected x y := by
  exact RelativeRecoveryChain.protected_append_iff left right x y

example {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {targetRow : Fin rows} {targetCol : Fin cols}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      targetRow targetCol c b net) :
    RelativeRecoveryStep K V
      (fun x ↦ net.eval (V x + constantImage rows cols c)) :=
  bundledPascalSelectionRecoveryStep hspec

example {X : Type*} {K : Set X}
    {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) :
    RelativeRecoveryStep K (fun x ↦ head.eval (F x))
      (successorFeature head F) :=
  successorBridgeRecoveryStep head F

#check twoStageRecoveryChain
#check RelativeRecoveryChain.recover
