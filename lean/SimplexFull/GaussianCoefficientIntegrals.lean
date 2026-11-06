import SimplexFull.OrthantCoefficients
import SimplexFull.CovarianceCoefficients
import SimplexFull.LayerCake

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SimplexFull.Covariance
open SimplexFull.Geometry
variable {m : ℕ} [NeZero m]

theorem integral_exp_max_firstDensityCoeff {mu : ℝ} (hmu : 0 < mu) (hm : 2 ≤ m)
    {A : Matrix (Fin m) (Fin m) ℝ} (hZ : zeroDiagonal A) :
    (∫ x, Real.exp (mu*maxCoord x)*firstDensityCoeff A x) =
      -mu*normalizer m mu*halfEntrySum A := by
  have hh := integral_exp_max_eq_neg_integral_orthant
    (continuous_firstDensityCoeff A).measurable hmu (integrable_firstDensityCoeff A)
    (integral_firstDensityCoeff_zero hZ) (integrable_exp_max_firstDensityCoeff mu A)
  have he : ∀ c : ℝ, Real.exp (mu*c)*(∫ x in {x | ∀ i, x i ≤ c}, firstDensityCoeff A x) =
      tiltWeight m mu c*halfEntrySum A := by
    intro c
    change Real.exp (mu*c)*(∫ x in orthantIic c, firstDensityCoeff A x) = _
    rw [integral_orthant_firstDensityCoeff_zeroDiagonal hm hZ c]
    unfold tiltWeight
    ring
  simp_rw [he] at hh
  rw [integral_mul_const] at hh
  simpa only [normalizer, mul_assoc] using hh

#print axioms integral_exp_max_firstDensityCoeff

theorem integral_tiltWeight_mul (m : ℕ) (mu : ℝ) (f : ℝ → ℝ) :
    (∫ c, tiltWeight m mu c*f c) = normalizer m mu*tiltedMoment m mu f := by
  have hz := (normalizer_pos m mu).ne'
  have he : (fun c => tiltWeight m mu c*f c) = fun c => f c*tiltWeight m mu c := by
    funext c; ring
  rw [he]
  unfold tiltedMoment
  field_simp

theorem integral_tiltWeight_quadratic (m : ℕ) (mu F R : ℝ) :
    (∫ c, tiltWeight m mu c*((h c)^2*F/4-q c*h c*R/2)) =
      normalizer m mu*(a m mu*F/4-(1-b m mu)*R/2) := by
  have he : (fun c => tiltWeight m mu c*((h c)^2*F/4-q c*h c*R/2)) =
      fun c => ((h c)^2*tiltWeight m mu c)*(F/4)-
        (tiltWeight m mu c-sigma c*tiltWeight m mu c)*(R/2) := by
    funext c
    unfold sigma
    ring
  have h1 := (gm_integrable_hsq m mu).mul_const (F/4)
  have h2 : Integrable (fun c => (tiltWeight m mu c-sigma c*tiltWeight m mu c)*(R/2)) := by
    simpa only [Pi.sub_apply] using
      ((integrable_tiltWeight m mu).sub (gm_integrable_sigma m mu)).mul_const (R/2)
  rw [he, integral_sub h1 h2, integral_mul_const, integral_mul_const,
    integral_sub (integrable_tiltWeight m mu) (gm_integrable_sigma m mu)]
  have ha : (∫ c, (h c)^2*tiltWeight m mu c) = normalizer m mu*a m mu := by
    unfold a tiltedMoment
    have hz := (normalizer_pos m mu).ne'
    field_simp
  have hb : (∫ c, sigma c*tiltWeight m mu c) = normalizer m mu*b m mu := by
    unfold b tiltedMoment
    have hz := (normalizer_pos m mu).ne'
    field_simp
  rw [ha, hb]
  change _ = normalizer m mu*(a m mu*F/4-(1-b m mu)*R/2)
  dsimp [normalizer] at *
  ring

#print axioms integral_tiltWeight_quadratic

theorem integral_exp_max_secondDensityCoeff_entrySum_zero {mu : ℝ} (hmu : 0 < mu)
    (hm : 2 ≤ m) {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) (hZ : zeroDiagonal A) (hT : entrySum A=0) :
    (∫ x, Real.exp (mu*maxCoord x)*secondDensityCoeff A x) =
      -mu*normalizer m mu*(a m mu*frobSq A/4-(1-b m mu)*rowSumSq A/2) := by
  have hh := integral_exp_max_eq_neg_integral_orthant
    (continuous_secondDensityCoeff A).measurable hmu (integrable_secondDensityCoeff A)
    (integral_secondDensityCoeff_zero hA hZ) (integrable_exp_max_secondDensityCoeff mu A)
  have he : ∀ c : ℝ, Real.exp (mu*c)*(∫ x in {x | ∀ i, x i ≤ c}, secondDensityCoeff A x) =
      tiltWeight m mu c*((h c)^2*frobSq A/4-q c*h c*rowSumSq A/2) := by
    intro c
    change Real.exp (mu*c)*(∫ x in orthantIic c, secondDensityCoeff A x) = _
    rw [integral_orthant_secondDensityCoeff_factor hm hA hZ c, hT]
    unfold tiltWeight
    ring
  simp_rw [he] at hh
  rw [integral_tiltWeight_quadratic] at hh
  simpa only [mul_assoc] using hh

#print axioms integral_exp_max_secondDensityCoeff_entrySum_zero
end SimplexFull.Covariance