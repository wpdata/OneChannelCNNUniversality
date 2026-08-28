import OneChannelCNNUniversality.SharedBiasRelativeInjectivity

/-!
# Monotone chain layouts for protected shared-bias scans

The southeast protection relation is a product order, not a total order.
This file records both sides of the resulting layout issue.  A genuinely
two-dimensional rectangle cannot be enumerated surjectively by one monotone
southeast chain.  On the other hand, row-major linearization gives an exact,
injective `1 × (rows * cols)` chain representation on which the protection
relation agrees with the ordinary order of indices.

The encoder here is a mathematical coordinate permutation.  Realizing that
permutation by a shared-bias CNN is a separate compilation problem.
-/

namespace OneChannelCNNUniversality

/-- A one-row chain site.  Increasing the chain index moves weakly southeast
in the product order. -/
def rowChainLayout {n : ℕ} (t : Fin n) : Fin 1 × Fin n :=
  (⟨0, by omega⟩, t)

@[simp] theorem rowChainLayout_fst {n : ℕ} (t : Fin n) :
    (rowChainLayout t).1 = ⟨0, by omega⟩ := rfl

@[simp] theorem rowChainLayout_snd {n : ℕ} (t : Fin n) :
    (rowChainLayout t).2 = t := rfl

/-- On the one-row layout, southeast protection is exactly the usual linear
index order. -/
theorem southeastProtected_rowChainLayout_iff {n : ℕ} (a b : Fin n) :
    southeastProtected (rowChainLayout a).1 (rowChainLayout a).2
      (rowChainLayout b).1 (rowChainLayout b).2 ↔ a ≤ b := by
  simp [southeastProtected, rowChainLayout]

/-- A finite layout is southeast-monotone when later linear indices are
always weakly southeast of earlier ones. -/
def SoutheastMonotoneLayout {n rows cols : ℕ}
    (layout : Fin n → Fin rows × Fin cols) : Prop :=
  ∀ a b, a ≤ b →
    southeastProtected (layout a).1 (layout a).2
      (layout b).1 (layout b).2

theorem rowChainLayout_southeastMonotone {n : ℕ} :
    SoutheastMonotoneLayout (rowChainLayout (n := n)) := by
  intro a b hab
  exact (southeastProtected_rowChainLayout_iff a b).2 hab

theorem rowChainLayout_injective {n : ℕ} :
    Function.Injective (rowChainLayout (n := n)) := by
  intro a b hab
  exact congrArg Prod.snd hab

/-- No southeast-monotone chain can cover a rectangle having at least two
rows and two columns.  The sites `(0,1)` and `(1,0)` force opposite orders. -/
theorem not_surjective_of_southeastMonotoneLayout
    {n rows cols : ℕ} (hrows : 2 ≤ rows) (hcols : 2 ≤ cols)
    (layout : Fin n → Fin rows × Fin cols)
    (hmono : SoutheastMonotoneLayout layout) :
    ¬ Function.Surjective layout := by
  intro hsurj
  let northeast : Fin rows × Fin cols :=
    (⟨0, by omega⟩, ⟨1, by omega⟩)
  let southwest : Fin rows × Fin cols :=
    (⟨1, by omega⟩, ⟨0, by omega⟩)
  obtain ⟨a, ha⟩ := hsurj northeast
  obtain ⟨b, hb⟩ := hsurj southwest
  rcases le_total a b with hab | hba
  · have hse := hmono a b hab
    rw [ha, hb] at hse
    simpa [southeastProtected, northeast, southwest] using hse
  · have hse := hmono b a hba
    rw [hb, ha] at hse
    simpa [southeastProtected, northeast, southwest] using hse

/-- Rank in the southeast product order. -/
def southeastRank {rows cols : ℕ} (p : Fin rows × Fin cols) : ℕ :=
  p.1 + p.2

theorem southeastRank_lt_size {rows cols : ℕ}
    (p : Fin rows × Fin cols) :
    southeastRank p < rows + cols - 1 := by
  unfold southeastRank
  have hpRow := p.1.isLt
  have hpCol := p.2.isLt
  omega

/-- A nontrivial southeast move strictly increases rank. -/
theorem southeastRank_strict {rows cols : ℕ}
    {p q : Fin rows × Fin cols}
    (hpq : southeastProtected p.1 p.2 q.1 q.2) (hne : p ≠ q) :
    southeastRank p < southeastRank q := by
  have hcoordinate : (p.1 : ℕ) ≠ (q.1 : ℕ) ∨
      (p.2 : ℕ) ≠ (q.2 : ℕ) := by
    by_contra h
    push_neg at h
    apply hne
    apply Prod.ext <;> apply Fin.ext
    · exact h.1
    · exact h.2
  unfold southeastRank southeastProtected at *
  omega

/-- An injective chain of `n` protected sites in a `rows × cols` rectangle
has length at most `rows + cols - 1`.  Consequently, storing `n` arbitrary
registers on one protected chain requires linear total spatial extent. -/
theorem SoutheastMonotoneLayout.length_le
    {n rows cols : ℕ} {layout : Fin n → Fin rows × Fin cols}
    (hmono : SoutheastMonotoneLayout layout)
    (hinjective : Function.Injective layout) :
    n ≤ rows + cols - 1 := by
  by_cases hn : n = 0
  · omega
  let ranked : Fin n → Fin (rows + cols - 1) := fun t ↦
    ⟨southeastRank (layout t), southeastRank_lt_size (layout t)⟩
  have hranked : StrictMono ranked := by
    intro a b hab
    apply Fin.mk_lt_mk.mpr
    apply southeastRank_strict
    · exact hmono a b hab.le
    · exact hinjective.ne hab.ne
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective ranked hranked.injective

/-- Row-major coordinate permutation from a rectangular image to a one-row
chain image. -/
def rowMajorChainEncode {rows cols : ℕ} (x : Image rows cols) :
    Image 1 (rows * cols) :=
  fun _ t ↦
    let ij := (finProdFinEquiv (m := rows) (n := cols)).symm t
    x ij.1 ij.2

/-- The inverse coordinate permutation from a one-row chain image back to a
rectangle. -/
def rowMajorChainDecode (rows cols : ℕ) (x : Image 1 (rows * cols)) :
    Image rows cols :=
  fun i j ↦ x ⟨0, by omega⟩
    (finProdFinEquiv (m := rows) (n := cols) (i, j))

@[simp] theorem rowMajorChainDecode_encode {rows cols : ℕ}
    (x : Image rows cols) :
    rowMajorChainDecode rows cols (rowMajorChainEncode x) = x := by
  funext i j
  simp [rowMajorChainDecode, rowMajorChainEncode]

/-- Row-major chain encoding loses no feature information. -/
theorem rowMajorChainEncode_injective {rows cols : ℕ} :
    Function.Injective
      (rowMajorChainEncode (rows := rows) (cols := cols)) := by
  intro x y hxy
  have := congrArg (rowMajorChainDecode rows cols) hxy
  simpa using this

end OneChannelCNNUniversality
