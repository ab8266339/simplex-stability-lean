import SimplexFull.ShellStationarity
import SimplexFull.ShellConvexity
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
theorem exists_shellLoss_quadratic_min (hm : 2 ≤ m) (mu : ℝ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ H : shellSpace m, c * ‖H‖^2 ≤
      fderiv ℝ (fderiv ℝ (shellLoss (m:=m) mu)) (0,0) (0,H) (0,H)) :
    ∃ eps > 0, ∃ delta > 0, ∀ tau : ℝ, |tau| < eps → ∀ D : shellSpace m, ‖D‖ < delta →
      shellLoss (m:=m) mu (tau,0) + (c/4)*‖D‖^2 ≤ shellLoss (m:=m) mu (tau,D) ∧
      (shellLoss (m:=m) mu (tau,D) = shellLoss (m:=m) mu (tau,0) ↔ D = 0) := by
  obtain ⟨U,hUn,hUd⟩ := (contDiffAt_shellLoss_zero (m:=m) mu).contDiffOn le_rfl (by norm_num)
  obtain ⟨V,hVU,hVo,h0V⟩ := mem_nhds_iff.mp hUn
  have hVd : ContDiffOn ℝ 2 (shellLoss (m:=m) mu) V := hUd.mono hVU
  obtain ⟨eps,heps,hs⟩ := exists_shellLoss_stationary hm mu
  have hcrit : ∀ᶠ tau : ℝ in 𝓝 0, ∀ H : shellSpace m,
      fderiv ℝ (shellLoss (m:=m) mu) (tau,0) (0,H) = 0 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) heps] with tau htau
    exact hs tau (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using htau)
  exact Convexity.exists_local_quadratic_min hVo h0V hVd hc hcoer hcrit
#print axioms exists_shellLoss_quadratic_min
end SimplexFull.Geometry