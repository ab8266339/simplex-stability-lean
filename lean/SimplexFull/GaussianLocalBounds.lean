import SimplexFull.GaussianDensity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator RealInnerProductSpace Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

theorem quad_eq_inner (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    quad M x = inner ℝ x (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M x) := by
  rw [Matrix.inner_toEuclideanCLM, quad_eq_dotProduct]

theorem quad_abs_le_norm (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : |quad M x| ≤ ‖M‖*‖x‖^2 := by
  calc
    |quad M x| = |inner ℝ x (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M x)| := by rw [quad_eq_inner]
    _ ≤ ‖x‖*‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M‖*‖x‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) M).le_opNorm x) (norm_nonneg x)
    _ = ‖M‖*‖x‖^2 := by rw [Matrix.cstar_norm_def]; ring

theorem quad_inv_lower_of_close {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : ‖R⁻¹-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    (1/2)*‖x‖^2 ≤ quad R⁻¹ x := by
  have he : R⁻¹ = 1+(R⁻¹-1) := by
    simpa only [add_comm] using (sub_add_cancel R⁻¹ (1 : Matrix (Fin m) (Fin m) ℝ)).symm
  have heq := congrArg (fun M => quad M x) he
  rw [quad_add, quad_one] at heq
  have hn := neg_le_of_abs_le (quad_abs_le_norm (R⁻¹-1) x)
  have hp := mul_le_mul_of_nonneg_right hR (sq_nonneg ‖x‖)
  linarith

def rhoPrefactor (R : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (Real.sqrt ((2*Real.pi)^m*R.det))⁻¹

theorem rhoPrefactor_nonneg (R : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ rhoPrefactor R := by
  unfold rhoPrefactor
  positivity

theorem rho_nonneg (R : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ rho R x := by
  exact mul_nonneg (rhoPrefactor_nonneg R) (Real.exp_pos _).le


theorem continuousAt_rhoPrefactor_one :
    ContinuousAt (rhoPrefactor : Matrix (Fin m) (Fin m) ℝ → ℝ) 1 := by
  have hc : Continuous (fun R : Matrix (Fin m) (Fin m) ℝ =>
      Real.sqrt ((2*Real.pi)^m*R.det)) :=
    (continuous_const.mul continuous_id.matrix_det).sqrt
  have hn : Real.sqrt ((2*Real.pi)^m*(1 : Matrix (Fin m) (Fin m) ℝ).det) ≠ 0 := by
    rw [Matrix.det_one, mul_one]
    exact (Real.sqrt_pos.2 (pow_pos (mul_pos (by norm_num) Real.pi_pos) m)).ne'
  exact hc.continuousAt.inv₀ hn

theorem continuousAt_matrixInverse_one :
    ContinuousAt (fun R : Matrix (Fin m) (Fin m) ℝ => R⁻¹) 1 := by
  apply continuousAt_matrix_inv
  rw [Matrix.det_one]
  have he : (Ring.inverse : ℝ → ℝ) = fun x => x⁻¹ := by
    funext x
    exact Ring.inverse_eq_inv x
  rw [he]
  exact continuousAt_inv₀ (by norm_num : (1:ℝ) ≠ 0)

theorem exists_local_rho_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
      ∀ R : Matrix (Fin m) (Fin m) ℝ, ‖R-1‖ < ε →
      ∀ x : EuclideanSpace ℝ (Fin m),
        |rho R x| ≤ C*Real.exp (-‖x‖^2/4) := by
  have hi : Tendsto (fun R : Matrix (Fin m) (Fin m) ℝ => ‖R⁻¹-1‖)
      (𝓝 1) (𝓝 0) := by
    have hh := ((continuousAt_matrixInverse_one (m := m)).sub (continuousAt_const (y := (1 : Matrix (Fin m) (Fin m) ℝ)))).norm.tendsto
    simpa only [matrix_inv_one, sub_self, norm_zero] using hh
  have hiv : ∀ᶠ R : Matrix (Fin m) (Fin m) ℝ in 𝓝 1, ‖R⁻¹-1‖ < 1/2 :=
    hi.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
  let C : ℝ := rhoPrefactor (1 : Matrix (Fin m) (Fin m) ℝ)+1
  have hC : 0 < C := by
    dsimp [C]
    linarith [rhoPrefactor_nonneg (1 : Matrix (Fin m) (Fin m) ℝ)]
  have hpv : ∀ᶠ R : Matrix (Fin m) (Fin m) ℝ in 𝓝 1, rhoPrefactor R < C :=
    continuousAt_rhoPrefactor_one.tendsto.eventually
      (eventually_lt_nhds (by dsimp [C]; linarith))
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp (hiv.and hpv)
  refine ⟨ε, hε, C, hC, ?_⟩
  intro R hR x
  have hh := hb (by simpa only [dist_eq_norm] using hR)
  have hq := quad_inv_lower_of_close hh.1.le x
  have he : Real.exp (-quad R⁻¹ x/2) ≤ Real.exp (-‖x‖^2/4) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (rho_nonneg R x)]
  exact mul_le_mul hh.2.le he (Real.exp_pos _).le hC.le

#print axioms exists_local_rho_bound


theorem quad_lower_of_close {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    (1/2)*‖x‖^2 ≤ quad M x := by
  have he : M = 1+(M-1) := by
    simpa only [add_comm] using (sub_add_cancel M (1 : Matrix (Fin m) (Fin m) ℝ)).symm
  have heq := congrArg (fun A => quad A x) he
  rw [quad_add, quad_one] at heq
  have hn := neg_le_of_abs_le (quad_abs_le_norm (M-1) x)
  have hp := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖x‖)
  linarith

theorem exp_quad_le_gaussian_of_close {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ‖M-1‖ ≤ 1/2) (x : EuclideanSpace ℝ (Fin m)) :
    Real.exp (-quad M x/2) ≤ Real.exp (-‖x‖^2/4) := by
  apply Real.exp_le_exp.mpr
  linarith [quad_lower_of_close hM x]

#print axioms quad_lower_of_close
end SimplexFull.Covariance