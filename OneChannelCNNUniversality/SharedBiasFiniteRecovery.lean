import OneChannelCNNUniversality.SharedBiasTwoStageRecovery

/-!
# Finite relative-recovery chains

This file separates the backward recovery argument from the changing spatial
dimensions of a sequence of expansive CNN blocks.  A recovery step relates
two feature families over the same compact parameter set, while a dependent
chain allows the codomain type to change at every step.
-/

namespace OneChannelCNNUniversality

universe u v

/-- One feature transformation whose output equality recovers input-feature
equality whenever its local protection predicate holds. -/
structure RelativeRecoveryStep {X : Type u} (K : Set X)
    {A B : Type v} (before : X → A) (after : X → B) where
  Protected : X → X → Prop
  recover : ∀ {x y : X}, x ∈ K → y ∈ K → Protected x y →
    after x = after y → before x = before y

/-- A heterogeneous finite chain of relative-recovery steps.  Intermediate
feature types may differ, which models the changing image dimensions of
expansive convolutional blocks. -/
inductive RelativeRecoveryChain {X : Type u} (K : Set X) :
    {A B : Type v} → (X → A) → (X → B) →
      Type (max (u + 1) (v + 1))
  | nil {A : Type v} (F : X → A) : RelativeRecoveryChain K F F
  | cons {A B C : Type v} {F : X → A} {G : X → B} {H : X → C}
      (step : RelativeRecoveryStep K F G)
      (tail : RelativeRecoveryChain K G H) : RelativeRecoveryChain K F H

namespace RelativeRecoveryChain

/-- All local protection predicates required along a recovery chain. -/
def Protected {X : Type u} {K : Set X} {A B : Type v}
    {F : X → A} {G : X → B} :
    RelativeRecoveryChain K F G → X → X → Prop
  | .nil _ => fun _ _ ↦ True
  | .cons step tail => fun x y ↦ step.Protected x y ∧ tail.Protected x y

/-- Number of local recovery steps in the chain. -/
def length {X : Type u} {K : Set X} {A B : Type v}
    {F : X → A} {G : X → B} : RelativeRecoveryChain K F G → ℕ
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- Concatenation of two recovery chains with a common intermediate feature
family. -/
def append {X : Type u} {K : Set X} {A B C : Type v}
    {F : X → A} {G : X → B} {H : X → C} :
    RelativeRecoveryChain K F G → RelativeRecoveryChain K G H →
      RelativeRecoveryChain K F H
  | .nil _, right => right
  | .cons step tail, right => .cons step (tail.append right)

/-- Chain length is additive under concatenation. -/
theorem length_append {X : Type u} {K : Set X} {A B C : Type v}
    {F : X → A} {G : X → B} {H : X → C}
    (left : RelativeRecoveryChain K F G)
    (right : RelativeRecoveryChain K G H) :
    (left.append right).length = left.length + right.length := by
  induction left with
  | nil => simp [append, length]
  | cons step tail ih =>
      simp only [append, length, ih]
      omega

/-- The protection obligation of a concatenation is exactly the conjunction
of the obligations of its two pieces. -/
theorem protected_append_iff
    {X : Type u} {K : Set X} {A B C : Type v}
    {F : X → A} {G : X → B} {H : X → C}
    (left : RelativeRecoveryChain K F G)
    (right : RelativeRecoveryChain K G H) (x y : X) :
    (left.append right).Protected x y ↔
      left.Protected x y ∧ right.Protected x y := by
  induction left with
  | nil => simp [append, Protected]
  | cons step tail ih =>
      simp only [append, Protected, ih]
      tauto

/-- Backward induction through any finite heterogeneous chain. -/
theorem recover {X : Type u} {K : Set X} {A B : Type v}
    {F : X → A} {G : X → B} (chain : RelativeRecoveryChain K F G)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hp : chain.Protected x y) (heq : G x = G y) : F x = F y := by
  induction chain generalizing x y with
  | nil => exact heq
  | cons step tail ih =>
      exact step.recover hx hy hp.1 (ih hx hy hp.2 heq)

end RelativeRecoveryChain

/-- A bundled protected Pascal selector, viewed only through its certified
relative-recovery interface. -/
def bundledPascalSelectionRecoveryStep
    {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols} {θ c b : ℝ}
    {rowSteps extraColSteps : ℕ}
    {targetRow : Fin rows} {targetCol : Fin cols}
    {net : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps extraColSteps)
      (protectedSelectionSize cols rowSteps extraColSteps)}
    (hspec : BundledPascalGridSelectionSpec K V θ rowSteps extraColSteps
      targetRow targetCol c b net) :
    RelativeRecoveryStep K V
      (fun x ↦ net.eval (V x + constantImage rows cols c)) where
  Protected := fun x y ↦ AgreeOutsideStrictSoutheast
    (V x) (V y) targetRow targetCol
  recover := by
    intro x y hx hy hp heq
    exact hspec.injective_on_rootPuncturedSoutheast hx hy hp heq

/-- The delta successor bridge is an unconditional recovery step because its
expansive embedding is globally injective. -/
def successorBridgeRecoveryStep
    {X : Type*} {K : Set X} {inRows inCols midRows midCols : ℕ}
    (head : SharedBiasNetworkTo 2 2 inRows inCols midRows midCols)
    (F : X → Image inRows inCols) :
    RelativeRecoveryStep K (fun x ↦ head.eval (F x))
      (successorFeature head F) where
  Protected := fun _ _ ↦ True
  recover := by
    intro x y _hx _hy _hp heq
    exact headEval_eq_of_successorFeature_eq head F heq

/-- The two-selector recovery proof packaged as a three-step heterogeneous
chain: first selector, unconditional delta bridge, second selector. -/
def twoStageRecoveryChain
    {X : Type*} {K : Set X} {rows cols : ℕ}
    {V : X → Image rows cols}
    {rowSteps₁ extraColSteps₁ rowSteps₂ extraColSteps₂ : ℕ}
    {targetRow₁ : Fin rows} {targetCol₁ : Fin cols}
    {targetRow₂ : Fin
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)}
    {targetCol₂ : Fin
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)}
    {θ₁ θ₂ c₁ b₁ c₂ b₂ : ℝ}
    {head : SharedBiasNetworkTo 2 2 rows cols
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁)
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁)}
    {tail : SharedBiasNetworkTo 2 2
      (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
      (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
      (protectedSelectionSize
        (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
        rowSteps₂ extraColSteps₂)
      (protectedSelectionSize
        (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
        rowSteps₂ extraColSteps₂)}
    (hspec₁ : BundledPascalGridSelectionSpec K V θ₁
      rowSteps₁ extraColSteps₁ targetRow₁ targetCol₁ c₁ b₁ head)
    (hspec₂ : BundledPascalGridSelectionSpec K
      (successorFeature head
        (fun z ↦ V z + constantImage rows cols c₁)) θ₂
      rowSteps₂ extraColSteps₂ targetRow₂ targetCol₂ c₂ b₂ tail) :
    RelativeRecoveryChain K V
      (fun x ↦ tail.eval
        (successorFeature head
            (fun z ↦ V z + constantImage rows cols c₁) x +
          constantImage
            (protectedSelectionSize rows rowSteps₁ extraColSteps₁ + 2 - 1)
            (protectedSelectionSize cols rowSteps₁ extraColSteps₁ + 2 - 1)
            c₂)) := by
  let F : X → Image rows cols :=
    fun z ↦ V z + constantImage rows cols c₁
  exact .cons (bundledPascalSelectionRecoveryStep hspec₁)
    (.cons (successorBridgeRecoveryStep head F)
      (.cons (bundledPascalSelectionRecoveryStep hspec₂) (.nil _)))

end OneChannelCNNUniversality
