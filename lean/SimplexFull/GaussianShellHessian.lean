import SimplexFull.GaussianShellAlgebra
import SimplexFull.ShellHessianChain
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
open SimplexFull.Covariance
variable {m : ℕ} [NeZero m]
theorem gaussian_shell_hessian (hm : 2 ≤ m) {mu : ℝ} (hmu : 0 < mu) (D : shellSpace m) :
    fderiv ℝ (fderiv ℝ (shellLoss (m:=m) mu)) (0,0) (0,D) (0,D) =
      2*shellQuadratic m (gaussianA m mu) (gaussianB m mu) (gaussianC m mu) D := by
  rw [shellLoss_hessian_sqChart, fderiv_extendedLoss_shell_acceleration hm hmu D]
  have hs := second_fderiv_extendedLoss_one_coefficient hm hmu (shellB_isSymm D)
    (shellB_zeroDiagonal D) (entrySum_shellB (NeZero.ne m) D)
  change fderiv ℝ (fderiv ℝ (extendedLoss (m:=m) mu)) 1
    (uncompress (D : ShapeMatrix m)) (uncompress (D : ShapeMatrix m)) = _ at hs
  rw [hs]
  exact shell_hessian_coefficient_algebra _ _ _ D
#print axioms gaussian_shell_hessian
theorem gaussian_shell_hessian_gaps (hm : 3 ≤ m) {mu : ℝ} (hmu : 0 < mu) (D : shellSpace m) :
    fderiv ℝ (fderiv ℝ (shellLoss (m:=m) mu)) (0,0) (0,D) (0,D) =
      8*gaussianC m mu*((WeakSimplexPilot.L0 (m:ℝ) (a m mu)-WeakSimplexPilot.Lp (m:ℝ))*shellE0 D+
      (WeakSimplexPilot.L1 (m:ℝ) (a m mu) (b m mu)-WeakSimplexPilot.Lp (m:ℝ))*shellE1 D) := by
  rw [gaussian_shell_hessian (by omega) hmu, shellQuadratic_identity hm]
  unfold gaussianA gaussianB WeakSimplexPilot.L0 WeakSimplexPilot.L1 WeakSimplexPilot.Lp
  ring
#print axioms gaussian_shell_hessian_gaps
end SimplexFull.Geometry

