import SimplexFull.GaussianDensityLaw
import SimplexFull.Decoder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace SimplexFull.Covariance

variable {m : ℕ}

theorem rho_nonneg_all (R : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : 0 ≤ rho R x := by
  unfold rho
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem integral_withDensity_rho (R : Matrix (Fin m) (Fin m) ℝ)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal (rho R x)) =
      ∫ x, rho R x * f x := by
  have hm : Measurable (fun x => ENNReal.ofReal (rho R x)) :=
    (continuous_rho R).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_ofReal (rho_nonneg_all R _), smul_eq_mul]

theorem integrable_withDensity_rho_iff (R : Matrix (Fin m) (Fin m) ℝ)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    Integrable f (volume.withDensity (fun x => ENNReal.ofReal (rho R x))) ↔
      Integrable (fun x => rho R x * f x) := by
  have hm : Measurable (fun x => ENNReal.ofReal (rho R x)) :=
    (continuous_rho R).measurable.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (rho_nonneg_all R _), smul_eq_mul]

theorem integral_stdGaussian_eq_rho_one (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin m)) =
      ∫ x, rho (1 : Matrix (Fin m) (Fin m) ℝ) x * f x := by
  rw [stdGaussian_eq_withDensity_rho_one, integral_withDensity_rho]

set_option pp.fullNames true in
#print axioms integral_withDensity_rho
set_option pp.fullNames true in
#print axioms integrable_withDensity_rho_iff
set_option pp.fullNames true in
#print axioms integral_stdGaussian_eq_rho_one


theorem integral_multivariateGaussian_eq_rho (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∫ x, f x ∂multivariateGaussian 0 R = ∫ x, rho R x * f x := by
  rw [multivariateGaussian_eq_withDensity_rho R hR, integral_withDensity_rho]

theorem integrable_multivariateGaussian_iff_rho (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    Integrable f (multivariateGaussian 0 R) ↔
      Integrable (fun x => rho R x * f x) := by
  rw [multivariateGaussian_eq_withDensity_rho R hR, integrable_withDensity_rho_iff]

theorem integral_rho_eq_one (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef) :
    ∫ x, rho R x = 1 := by
  have hi := integral_multivariateGaussian_eq_rho R hR (fun _ => 1)
  simpa using hi.symm

theorem integrable_rho_posDef (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef) :
    Integrable (rho R) :=
  integrable_of_integral_eq_one (integral_rho_eq_one R hR)

theorem integrable_exp_maxCoord_rho [NeZero m] (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (lam : ℝ) :
    Integrable (fun x => rho R x * Real.exp (lam * maxCoord x)) :=
  (integrable_multivariateGaussian_iff_rho R hR _).mp
    (integrable_exp_mul_maxCoord R hR.posSemidef lam)

theorem decodingSuccess_eq_rho_integral [NeZero m] (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (lam : ℝ) :
    decodingSuccess R lam =
      Real.exp (-(lam ^ 2) / 2) / (m : ℝ) *
        ∫ x, rho R x * Real.exp (lam * maxCoord x) := by
  rw [decodingSuccess, integral_multivariateGaussian_eq_rho R hR]

set_option pp.fullNames true
#print axioms integral_multivariateGaussian_eq_rho
#print axioms integrable_multivariateGaussian_iff_rho
#print axioms integral_rho_eq_one
#print axioms integrable_rho_posDef
#print axioms integrable_exp_maxCoord_rho
#print axioms decodingSuccess_eq_rho_integral

end SimplexFull.Covariance
