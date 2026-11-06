import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-
Algebraic certificates for the Section 11 Hessian reduction.
Real identities only: no geometric Hessian and no Gaussian integrals.
-/

noncomputable section

namespace WeakSimplexGeometry

theorem hessian_reduction_identity
    (m A B C E0 E1 : ℝ) (hm : (3 : ℝ) ≤ m) :
    let alpha := (m - 1) / m;
    let N := 4 * alpha * E0 + 2 * E1;
    let R := (m - 2) * E1;
    -m * C / 8 * (N - 2 * R / m) + A / 4 * N - (C - B) / 2 * R
      =
      (alpha * A - (m - 1) * C / 2) * E0
        + ((A + (m - 2) * B) / 2 - (m - 1) * C / 2) * E1 := by
  dsimp only
  have hm_ne : m ≠ 0 := by
    apply ne_of_gt
    linarith
  field_simp [hm_ne]
  ring

theorem hessian_quadratic_pos
    (m A B C E0 E1 : ℝ) (hm : (3 : ℝ) ≤ m)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE : 0 < E0 + E1)
    (hGap0 : 0 < (m - 1) / m * A - (m - 1) * C / 2)
    (hGap1 : 0 < (A + (m - 2) * B) / 2 - (m - 1) * C / 2) :
    0 <
      (let alpha := (m - 1) / m;
        let N := 4 * alpha * E0 + 2 * E1;
        let R := (m - 2) * E1;
        -m * C / 8 * (N - 2 * R / m) + A / 4 * N - (C - B) / 2 * R) := by
  have hId := hessian_reduction_identity m A B C E0 E1 hm
  dsimp only at hId
  dsimp only
  rw [hId]
  by_cases hE0eq : E0 = 0
  · have hE1pos : 0 < E1 := by
      rw [hE0eq, zero_add] at hE
      exact hE
    have hpos : 0 < ((A + (m - 2) * B) / 2 - (m - 1) * C / 2) * E1 := by
      positivity
    rw [hE0eq, mul_zero, zero_add]
    exact hpos
  · have hE0pos : 0 < E0 := lt_of_le_of_ne hE0 (Ne.symm hE0eq)
    have hpos : 0 < ((m - 1) / m * A - (m - 1) * C / 2) * E0 := by
      positivity
    have hnn : 0 ≤ ((A + (m - 2) * B) / 2 - (m - 1) * C / 2) * E1 := by
      positivity
    linarith

theorem hessian_quadratic_pos_m3
    (A B C E1 : ℝ) (hE1 : 0 < E1)
    (hGap1 : 0 < (A + ((3 : ℝ) - 2) * B) / 2 - ((3 : ℝ) - 1) * C / 2) :
    0 <
      (let alpha := ((3 : ℝ) - 1) / 3;
        let N := 4 * alpha * (0 : ℝ) + 2 * E1;
        let R := ((3 : ℝ) - 2) * E1;
        -(3 : ℝ) * C / 8 * (N - 2 * R / 3) + A / 4 * N - (C - B) / 2 * R) := by
  have hId := hessian_reduction_identity (3 : ℝ) A B C 0 E1 le_rfl
  dsimp only at hId
  dsimp only
  rw [hId]
  rw [mul_zero, zero_add]
  have hpos : 0 < ((A + ((3 : ℝ) - 2) * B) / 2 - ((3 : ℝ) - 1) * C / 2) * E1 := by
    positivity
  exact hpos

theorem shell_scalar_relations
    (m rho : ℝ) (hm : 0 < m) (h0 : 0 ≤ rho ^ 2) (h1 : rho ^ 2 < 2 * m) :
    let kappa := 1 - rho ^ 2 / (2 * m);
    0 < kappa ∧
      2 * m * (1 - kappa) = rho ^ 2 ∧
      kappa ^ 2 - 1 = -rho ^ 2 / m + rho ^ 4 / (4 * m ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have hd : (0 : ℝ) < 2 * m := by positivity
    have hq : rho ^ 2 / (2 * m) < 1 :=
      (div_lt_iff₀ hd).2 (by simpa using h1)
    linarith
  · have hm_ne : m ≠ 0 := ne_of_gt hm
    field_simp [hm_ne]
    ring
  · have hm_ne : m ≠ 0 := ne_of_gt hm
    field_simp [hm_ne]
    ring

#print axioms hessian_reduction_identity
#print axioms hessian_quadratic_pos
#print axioms hessian_quadratic_pos_m3
#print axioms shell_scalar_relations
#check hessian_reduction_identity
#check hessian_quadratic_pos
#check hessian_quadratic_pos_m3
#check shell_scalar_relations

end WeakSimplexGeometry
