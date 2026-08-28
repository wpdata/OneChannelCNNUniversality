import ICM2022NumCS97.Register

/-!
# Collision-free southeast routing geometry

Masters lie on a grid with gap at least three.  Temporary copies leave a
master diagonally, move east on the offset row, and then move south in a
column strictly beyond the master rectangle.  These elementary predicates
are independent of the real values stored in the registers.
-/

namespace ICM2022NumCS97

abbrev Site := ℕ × ℕ

/-- Two aligned sites leave at least `gap` empty lattice spacing in their
common row or column. -/
def corridorClear (gap : ℕ) (p q : Site) : Prop :=
  (p.1 = q.1 ∧ p.2 + gap ≤ q.2) ∨
  (p.2 = q.2 ∧ p.1 + gap ≤ q.1)

instance (gap : ℕ) (p q : Site) : Decidable (corridorClear gap p q) :=
  inferInstanceAs (Decidable
    ((p.1 = q.1 ∧ p.2 + gap ≤ q.2) ∨ (p.2 = q.2 ∧ p.1 + gap ≤ q.1)))

def eastPath (p : Site) (steps : ℕ) : List Site :=
  p :: (List.range steps).map (fun t ↦ (p.1, p.2 + (t + 1)))

def southPath (p : Site) (steps : ℕ) : List Site :=
  p :: (List.range steps).map (fun t ↦ (p.1 + (t + 1), p.2))

@[simp] theorem eastPath_head (p : Site) (steps : ℕ) :
    (eastPath p steps).head? = some p := rfl

@[simp] theorem southPath_head (p : Site) (steps : ℕ) :
    (southPath p steps).head? = some p := rfl

theorem mem_eastPath_iff (p r : Site) (steps : ℕ) :
    r ∈ eastPath p steps ↔ r.1 = p.1 ∧ ∃ t ≤ steps, r.2 = p.2 + t := by
  simp only [eastPath, List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨rfl, 0, by omega, by simp⟩
    · exact ⟨rfl, t + 1, by omega, rfl⟩
  · rintro ⟨hr, t, ht, hc⟩
    rcases t with _ | t
    · left
      apply Prod.ext <;> simp_all
    · right
      refine ⟨t, by omega, ?_⟩
      apply Prod.ext <;> simp_all

theorem mem_southPath_iff (p r : Site) (steps : ℕ) :
    r ∈ southPath p steps ↔ r.2 = p.2 ∧ ∃ t ≤ steps, r.1 = p.1 + t := by
  simp only [southPath, List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨rfl, 0, by omega, by simp⟩
    · exact ⟨rfl, t + 1, by omega, rfl⟩
  · rintro ⟨hc, t, ht, hr⟩
    rcases t with _ | t
    · left
      apply Prod.ext <;> simp_all
    · right
      refine ⟨t, by omega, ?_⟩
      apply Prod.ext <;> simp_all

/-- An offset row `3i+1` contains no gap-three master row. -/
theorem offset_row_not_master (i r : ℕ) : 3 * i + 1 ≠ 3 * r := by omega

/-- A master strictly southeast predecessor cannot occur one diagonal step
behind another gap-three master. -/
theorem master_no_diagonal_predecessor (i j r c : ℕ) :
    (3 * i + 1, 3 * j + 1) ≠ (3 * r, 3 * c) := by
  intro h
  have := congrArg Prod.fst h
  omega

/-- Distinct gap-three masters are never a single east/south/diagonal step
apart, the precise no-crosstalk condition for the three routing kernels. -/
theorem masters_not_one_step_apart (i j r c : ℕ)
    (_hneq : (i, j) ≠ (r, c)) :
    (3 * i, 3 * j) ≠ (3 * r + 1, 3 * c) ∧
    (3 * i, 3 * j) ≠ (3 * r, 3 * c + 1) ∧
    (3 * i, 3 * j) ≠ (3 * r + 1, 3 * c + 1) := by
  constructor
  · intro h
    have := congrArg Prod.fst h
    omega
  constructor
  · intro h
    have := congrArg Prod.snd h
    omega
  · intro h
    have := congrArg Prod.fst h
    omega

end ICM2022NumCS97
