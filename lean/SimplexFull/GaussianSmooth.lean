import SimplexFull.PrecisionGaussian
noncomputable section
open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Covariance
variable {m : ℕ} [NeZero m]
def rhoExpectation (lam : ℝ) (R : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ x, Real.exp (lam * maxCoord x) * rho R x

theorem rhoExpectation_eq_precision (lam : ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    rhoExpectation lam R = rhoPrefactor R * precisionIntegral lam R⁻¹ := by
  unfold rhoExpectation precisionIntegral
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [rho, rhoPrefactor, precisionKernel, precisionLinear, _root_.smul_apply,
    smul_eq_mul, quadCLM_apply]
  rw [show (-1/2 : ℝ) * quad R⁻¹ x = -quad R⁻¹ x/2 by ring]
  ring

theorem contDiffAt_matrixInverse_one :
    ContDiffAt ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => R⁻¹) 1 := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Units.val_one] using
    contDiffAt_ringInverse ℝ (1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)

theorem contDiffAt_rhoPrefactor_one :
    ContDiffAt ℝ ⊤ (rhoPrefactor : Matrix (Fin m) (Fin m) ℝ → ℝ) 1 := by
  have hbase : 0 < (2*Real.pi)^m := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  have harg : (2*Real.pi)^m*(1 : Matrix (Fin m) (Fin m) ℝ).det ≠ 0 := by
    simpa using ne_of_gt hbase
  have hs : Real.sqrt ((2*Real.pi)^m*(1 : Matrix (Fin m) (Fin m) ℝ).det) ≠ 0 := by
    simpa using (Real.sqrt_pos.mpr hbase).ne'
  exact ((contDiff_const.mul contDiff_det).contDiffAt.sqrt harg).inv hs

theorem contDiffAt_precisionIntegral_one (lam : ℝ) :
    ContDiffAt ℝ 2 (precisionIntegral (m := m) lam) 1 :=
  (contDiffOn_precisionIntegral lam).contDiffAt (Metric.ball_mem_nhds 1 (by norm_num))

theorem contDiffAt_rhoExpectation_one (lam : ℝ) :
    ContDiffAt ℝ 2 (rhoExpectation (m := m) lam) 1 := by
  have hJ : ContDiffAt ℝ 2 (precisionIntegral (m := m) lam)
      ((1 : Matrix (Fin m) (Fin m) ℝ)⁻¹) := by
    simpa only [matrix_inv_one] using contDiffAt_precisionIntegral_one (m := m) lam
  have heq : rhoExpectation (m := m) lam = fun R => rhoPrefactor R * precisionIntegral lam R⁻¹ :=
    funext (rhoExpectation_eq_precision lam)
  rw [heq]
  exact (contDiffAt_rhoPrefactor_one.of_le (by simp)).mul
    (hJ.comp 1 (contDiffAt_matrixInverse_one.of_le (by simp)))
#print axioms contDiffAt_rhoExpectation_one
end SimplexFull.Covariance

