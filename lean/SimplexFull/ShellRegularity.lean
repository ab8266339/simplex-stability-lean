import SimplexFull.Shell
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace SimplexFull.Geometry
theorem contDiff_shellCovariance_submodule (m : ℕ) (S : Submodule ℝ (ShapeMatrix m)) :
    ContDiff ℝ ⊤ (fun p : ℝ × S => shellCovariance m p.1 p.2) := by
  have hD : ContDiff ℝ ⊤ (fun p : ℝ × S => (p.2 : ShapeMatrix m)) :=
    S.subtypeL.contDiff.comp contDiff_snd
  have hT : ContDiff ℝ ⊤ (fun p : ℝ × S => chartKappa m p.1 • centering m + (p.2 : ShapeMatrix m)) :=
    (((contDiff_chartKappa m).comp contDiff_fst).smul contDiff_const).add hD
  have hC : ContDiff ℝ ⊤ (fun p : ℝ × S => squareShellC m p.1 p.2) :=
    (hT.mul hT).sub contDiff_const
  exact contDiff_const.add ((contDiff_shellLift m).comp hC)
theorem contDiff_shellCovarianceOnSpace (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × shellSpace m => shellCovarianceOnSpace m p.1 p.2) :=
  contDiff_shellCovariance_submodule m (shellSpace m)
#print axioms contDiff_shellCovarianceOnSpace
end SimplexFull.Geometry