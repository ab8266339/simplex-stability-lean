import SimplexFull.ShellRegularity
import SimplexFull.CenteredSqrt
import SimplexFull.GaussianSmooth
import SimplexFull.ShellSymmetry
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Geometry
variable {m : ℕ} [NeZero m]
def extendedLoss (mu : ℝ) (R : ShapeMatrix m) : ℝ :=
  Real.exp (-mu^2/2)/(m:ℝ) * (Covariance.rhoExpectation (m:=m) mu 1 - Covariance.rhoExpectation (m:=m) mu R)
def shellLoss (mu : ℝ) (p : ℝ × shellSpace m) : ℝ :=
  extendedLoss mu (shellCovarianceOnSpace m p.1 p.2)
lemma shellCovariance_zero : shellCovariance m 0 0 = 1 := by
  have hP : centering m * centering m = centering m := centering_idempotent (NeZero.ne m)
  simp only [shellCovariance, squareShellC, chartKappa, zero_div, sub_zero, one_smul, add_zero,
    hP, sub_self]
  ext i j
  simp [shellLift]
lemma contDiffAt_extendedLoss_one (mu : ℝ) : ContDiffAt ℝ 2 (extendedLoss (m:=m) mu) 1 := by
  exact contDiffAt_const.mul (contDiffAt_const.sub (Covariance.contDiffAt_rhoExpectation_one (m:=m) mu))
lemma contDiffAt_shellLoss_zero (mu : ℝ) : ContDiffAt ℝ 2 (shellLoss (m:=m) mu) 0 := by
  have hbase : shellCovarianceOnSpace m (0:ℝ) (0:shellSpace m) = 1 :=
    shellCovariance_zero
  have hL : ContDiffAt ℝ 2 (extendedLoss (m:=m) mu)
      (shellCovarianceOnSpace m (0:ℝ) (0:shellSpace m)) := by
    rw [hbase]
    exact contDiffAt_extendedLoss_one mu
  have hS : ContDiffAt ℝ 2 (fun p : ℝ × shellSpace m => shellCovarianceOnSpace m p.1 p.2) 0 :=
    (contDiff_shellCovarianceOnSpace m).contDiffAt.of_le (by simp)
  exact hL.comp (0 : ℝ × shellSpace m) hS
#print axioms contDiffAt_shellLoss_zero
end SimplexFull.Geometry