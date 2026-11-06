import SimplexFull.ShapeHessian
import SimplexFull.ActualShell
import SimplexFull.CovarianceCoefficients
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
open SimplexFull.Covariance
lemma shellQuadratic_raw_identity {m : ℕ} (hm : m ≠ 0) (A B C : ℝ) (D : shellSpace m) :
    shellQuadratic m A B C D = (A-(m:ℝ)*C/2)*shellN D+(2*B-C)*shellR D := by
  unfold shellQuadratic
  have hmR : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp [hmR]
  ring
lemma norm_sq_le_shellN {m : ℕ} (hm : m ≠ 0) (D : shellSpace m) : ‖D‖^2 ≤ shellN D := by
  obtain ⟨_,hPD,hDP,htr⟩ := shell_facts D
  have hf := frobSq_centered_tracefree hm (shell_centered hm hPD hDP) htr
  have hn : frobSq (D:ShapeMatrix m) ≤ shellN D := by
    rw [hf]
    exact sub_le_self _ (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg m))
      (rowSumSq_nonneg _))
  exact (l2_opNorm_sq_le_frobSq (D:ShapeMatrix m)).trans hn
theorem gaussian_shell_coercive_m4 {m : ℕ} (hm : 4 ≤ m) {mu : ℝ} (hmu : 0 < mu)
    (hgap : (m:ℝ)/2 < a m mu) :
    ∃ gamma > 0, ∀ D : shellSpace m, gamma*‖D‖^2 ≤
      shellQuadratic m (gaussianA m mu) (gaussianB m mu) (gaussianC m mu) D := by
  let gamma := gaussianA m mu-(m:ℝ)*gaussianC m mu/2
  have hg : 0 < gamma := gaussian_raw_gap0_pos (by omega) hmu hgap
  refine ⟨gamma,hg,?_⟩
  intro D
  rw [shellQuadratic_raw_identity (by omega)]
  have h1 := mul_le_mul_of_nonneg_left (norm_sq_le_shellN (by omega) D) hg.le
  have h2 : 0 ≤ (2*gaussianB m mu-gaussianC m mu)*shellR D :=
    mul_nonneg (gaussian_twoB_subC_pos hm hmu).le (rowSumSq_nonneg (shellB D))
  exact h1.trans (le_add_of_nonneg_right h2)
#print axioms gaussian_shell_coercive_m4
lemma shellR_eq_half_shellN_m3 (D : shellSpace 3) : shellR D = shellN D/2 := by
  have hn := shell_hN (m:=3) (by decide) D
  have hr := shell_hR (m:=3) (by decide) D
  rw [shellE0_eq_zero_m3, mul_zero, zero_add] at hn
  norm_num at hr
  linarith
lemma shellQuadratic_m3_identity (A B C : ℝ) (D : shellSpace 3) :
    shellQuadratic 3 A B C D = (A+B-2*C)*shellN D := by
  rw [shellQuadratic_raw_identity (by decide), shellR_eq_half_shellN_m3]
  norm_num
  ring
theorem gaussian_shell_coercive_m3 {mu : ℝ} (hmu : 0 < mu) (hgap : 2 < a 3 mu+b 3 mu) :
    ∃ gamma > 0, ∀ D : shellSpace 3, gamma*‖D‖^2 ≤
      shellQuadratic 3 (gaussianA 3 mu) (gaussianB 3 mu) (gaussianC 3 mu) D := by
  let gamma := gaussianA 3 mu+gaussianB 3 mu-2*gaussianC 3 mu
  have hg : 0 < gamma := gaussian_triangle_gap_pos hmu hgap
  refine ⟨gamma,hg,?_⟩
  intro D
  rw [shellQuadratic_m3_identity]
  exact mul_le_mul_of_nonneg_left (norm_sq_le_shellN (by decide) D) hg.le
#print axioms gaussian_shell_coercive_m3
end SimplexFull.Geometry