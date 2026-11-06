import SimplexFull.GaussianCoefficientIntegrals
import SimplexFull.GaussianSecondDifferentiation
import SimplexFull.ShellObjective
import SimplexFull.CovarianceCoefficients
import SimplexFull.GaussianPolynomial
noncomputable section
open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Topology
namespace SimplexFull.Covariance
variable {m : ℕ} [NeZero m]

theorem hasFDerivAt_extendedLoss_one (mu : ℝ) :
    HasFDerivAt (Geometry.extendedLoss (m := m) mu)
      ((-Real.exp (-mu^2/2)/(m:ℝ)) • fderiv ℝ (rhoExpectation mu) 1) 1 := by
  have hf := ((contDiffAt_rhoExpectation_one (m := m) mu).differentiableAt
    (by simp : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have he := ((hasFDerivAt_const (rhoExpectation (m := m) mu 1) (1 : Matrix (Fin m) (Fin m) ℝ)).sub hf).const_mul
    (Real.exp (-mu^2/2)/(m:ℝ))
  convert! he using 1
  ext A
  simp
  ring

theorem fderiv_extendedLoss_one_integral (mu : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (fderiv ℝ (Geometry.extendedLoss (m := m) mu) 1) A =
      (-Real.exp (-mu^2/2)/(m:ℝ)) *
        ∫ x, Real.exp (mu*maxCoord x)*rho 1 x*(quad A x-A.trace)/2 := by
  rw [(hasFDerivAt_extendedLoss_one mu).fderiv, _root_.smul_apply, smul_eq_mul,
    fderiv_rhoExpectation_one]

theorem fderiv_extendedLoss_one_zeroDiagonal (mu : ℝ) {A : Matrix (Fin m) (Fin m) ℝ}
    (hZ : Geometry.zeroDiagonal A) :
    (fderiv ℝ (Geometry.extendedLoss (m := m) mu) 1) A =
      (-Real.exp (-mu^2/2)/(m:ℝ)) * ∫ x, Real.exp (mu*maxCoord x)*firstDensityCoeff A x := by
  have ht : A.trace = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Geometry.zeroDiagonal_apply hZ, Finset.sum_const_zero]
  rw [fderiv_extendedLoss_one_integral, ht]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by unfold firstDensityCoeff; ring
#print axioms fderiv_extendedLoss_one_zeroDiagonal


theorem fderiv_extendedLoss_one_coefficient (hm : 2 ≤ m) {mu : ℝ} (hmu : 0 < mu)
    {A : Matrix (Fin m) (Fin m) ℝ} (hZ : Geometry.zeroDiagonal A) :
    (fderiv ℝ (Geometry.extendedLoss (m := m) mu) 1) A =
      gaussianC m mu * Geometry.halfEntrySum A := by
  rw [fderiv_extendedLoss_one_zeroDiagonal mu hZ,
    integral_exp_max_firstDensityCoeff hmu hm hZ]
  unfold gaussianC gaussianScale
  ring
#print axioms fderiv_extendedLoss_one_coefficient



local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ →L[ℝ] (Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ)) := ContinuousLinearMap.toNormedSpace

theorem hasFDerivAt_extendedLoss_of_diff (mu : ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hf : DifferentiableAt ℝ (rhoExpectation mu) R) :
    HasFDerivAt (Geometry.extendedLoss (m := m) mu)
      ((-Real.exp (-mu^2/2)/(m:ℝ)) • fderiv ℝ (rhoExpectation mu) R) R := by
  have he := ((hasFDerivAt_const (rhoExpectation (m := m) mu 1) R).sub hf.hasFDerivAt).const_mul
    (Real.exp (-mu^2/2)/(m:ℝ))
  convert! he using 1
  ext A
  simp
  ring

theorem second_fderiv_extendedLoss_one (mu : ℝ) (A B : Matrix (Fin m) (Fin m) ℝ) :
    (fderiv ℝ (fderiv ℝ (Geometry.extendedLoss (m := m) mu)) 1) A B =
      (-Real.exp (-mu^2/2)/(m:ℝ)) * (fderiv ℝ (fderiv ℝ (rhoExpectation mu)) 1) A B := by
  have hc : ContDiffAt ℝ 1 (fderiv ℝ (rhoExpectation (m := m) mu)) 1 :=
    (contDiffAt_rhoExpectation_one mu).fderiv_right (by norm_num)
  have hd := (hc.differentiableAt (by simp : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hk := hd.const_smul (-Real.exp (-mu^2/2)/(m:ℝ))
  have heq : fderiv ℝ (Geometry.extendedLoss (m := m) mu) =ᶠ[𝓝 1]
      (fun R => (-Real.exp (-mu^2/2)/(m:ℝ)) • fderiv ℝ (rhoExpectation mu) R) := by
    filter_upwards [(contDiffAt_rhoExpectation_one (m := m) mu).eventually (by simp)] with R hR
    exact (hasFDerivAt_extendedLoss_of_diff mu R (hR.differentiableAt (by simp))).fderiv
  have he := hk.congr_of_eventuallyEq heq
  rw [he.fderiv]
  simp
#print axioms second_fderiv_extendedLoss_one
theorem second_fderiv_extendedLoss_one_coefficient (hm : 2 ≤ m) {mu : ℝ} (hmu : 0 < mu)
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) (hZ : Geometry.zeroDiagonal A)
    (hT : Geometry.entrySum A=0) :
    (fderiv ℝ (fderiv ℝ (Geometry.extendedLoss (m := m) mu)) 1) A A =
      gaussianA m mu/2*Geometry.frobSq A-(gaussianC m mu-gaussianB m mu)*Geometry.rowSumSq A := by
  have htr : A.trace=0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Geometry.zeroDiagonal_apply hZ, Finset.sum_const_zero]
  rw [second_fderiv_extendedLoss_one, second_fderiv_rhoExpectation_one_trace_zero mu A htr,
    integral_exp_max_secondDensityCoeff_entrySum_zero hmu hm hA hZ hT]
  unfold gaussianA gaussianB gaussianC gaussianScale
  ring
#print axioms second_fderiv_extendedLoss_one_coefficient
end SimplexFull.Covariance

