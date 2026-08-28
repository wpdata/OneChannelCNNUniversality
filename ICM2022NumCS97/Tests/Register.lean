import ICM2022NumCS97.Register
import ICM2022NumCS97.Routing

open ICM2022NumCS97

example (x : Image 2 2) :
    fullConv (deltaKernel (1 : Fin 2) (1 : Fin 2) (1 : ℝ)) x 1 1 = x 0 0 := by
  simp [fullConv_deltaKernel]

example (x : Image 2 2) (a : ℝ) (p q : ℕ) :
    fullConv (twoTapKernel (0 : Fin 2) (0 : Fin 2)
      (1 : Fin 2) (1 : Fin 2) a) x p q =
      zeroExtend x p q +
        (if 1 ≤ p ∧ 1 ≤ q then a * zeroExtend x (p - 1) (q - 1) else 0) := by
  simpa using fullConv_twoTapKernel
    (x := x) (baseRow := (0 : Fin 2)) (baseCol := (0 : Fin 2))
      (shiftRow := (1 : Fin 2)) (shiftCol := (1 : Fin 2)) (a := a) (p := p) (q := q)

example (x : Image 3 3) (a : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hempty : zeroExtend x p q = 0) :
    fullConv (twoTapKernel (0 : Fin 2) (0 : Fin 2)
      (1 : Fin 2) (1 : Fin 2) a) x p q =
        a * zeroExtend x (p - 1) (q - 1) :=
  twoTap_move_to_empty x a p q hp hq hempty

example : corridorClear 3 (0, 0) (0, 3) := by decide
example : corridorClear 3 (0, 0) (3, 0) := by decide
