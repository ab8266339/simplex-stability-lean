import SimplexFull.GeometryAlgebra
import Mathlib.Tactic.LinearCombination

namespace SimplexFull.Geometry

theorem square_shell_hessian_identity
    (m A B C N R E0 E1 : ℝ) (hm : 3 ≤ m)
    (hN : N = 4 * ((m - 1) / m) * E0 + 2 * E1)
    (hR : R = (m - 2) * E1) :
    -m * C / 2 * (N - 2 * R / m) + A * N - 2 * (C - B) * R =
      4 * ((((m - 1) / m) * A - (m - 1) * C / 2) * E0 +
        ((A + (m - 2) * B) / 2 - (m - 1) * C / 2) * E1) := by
  rw [hN, hR]
  have hb := WeakSimplexGeometry.hessian_reduction_identity m A B C E0 E1 hm
  dsimp only at hb
  linear_combination 4 * hb

theorem square_shell_hessian_pos
    (m A B C N R E0 E1 : ℝ) (hm : 3 ≤ m)
    (hN : N = 4 * ((m - 1) / m) * E0 + 2 * E1)
    (hR : R = (m - 2) * E1)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE : 0 < E0 + E1)
    (hg0 : 0 < (m - 1) / m * A - (m - 1) * C / 2)
    (hg1 : 0 < (A + (m - 2) * B) / 2 - (m - 1) * C / 2) :
    0 < -m * C / 2 * (N - 2 * R / m) + A * N - 2 * (C - B) * R := by
  rw [square_shell_hessian_identity m A B C N R E0 E1 hm hN hR]
  have hp := WeakSimplexGeometry.hessian_quadratic_pos m A B C E0 E1 hm hE0 hE1 hE hg0 hg1
  have hi := WeakSimplexGeometry.hessian_reduction_identity m A B C E0 E1 hm
  dsimp only at hp hi
  rw [hi] at hp
  exact mul_pos (by norm_num) hp

#print axioms square_shell_hessian_identity
#print axioms square_shell_hessian_pos
end SimplexFull.Geometry