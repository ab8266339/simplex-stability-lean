import SimplexFull.GaussianDomination
import SimplexFull.GaussianLocalBounds

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SimplexFull.Covariance
variable {m : ℕ} [NeZero m]

theorem integrable_exp_max_rho_one_mul_of_bound (lam : ℝ) (n : ℕ)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : Continuous f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C*‖x‖^n) :
    Integrable (fun x => Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*f x) := by
  let K : ℝ := (Real.sqrt ((2*Real.pi)^m))⁻¹
  have hd := (integrable_norm_pow_exp_max_mul_gaussian (m := m) n lam
    (by norm_num : (0:ℝ)<1/2)).const_mul (C*K)
  have hc : Continuous (fun x => Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*f x) :=
    ((Real.continuous_exp.comp (continuous_const.mul SimplexFull.continuous_maxCoord)).mul (continuous_rho 1)).mul hf
  apply hd.mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (rho_nonneg 1 x)]
  calc
    Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*|f x|
        ≤ Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*(C*‖x‖^n) :=
      mul_le_mul_of_nonneg_left (hb x) (mul_nonneg (Real.exp_pos _).le (rho_nonneg 1 x))
    _ = C*K*(‖x‖^n*Real.exp (lam*SimplexFull.maxCoord x)*Real.exp (-(1/2)*‖x‖^2)) := by
      rw [rho_one]
      have he : -‖x‖^2/2 = -(1/2)*‖x‖^2 := by ring
      rw [he]
      dsimp [K]
      ring

theorem integrable_exp_max_rho_one (lam : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x) := by
  simpa using integrable_exp_max_rho_one_mul_of_bound lam 0 (f := fun _ => 1)
    continuous_const 1 (by intro x; norm_num)

theorem integrable_exp_max_rho_one_mul_quad (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x => Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*quad A x) :=
  integrable_exp_max_rho_one_mul_of_bound lam 2 (contDiff_quad A).continuous ‖A‖
    (quad_abs_le_norm A)

theorem integrable_exp_max_rho_one_mul_quad_sq (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x => Real.exp (lam*SimplexFull.maxCoord x)*rho 1 x*(quad A x)^2) := by
  apply integrable_exp_max_rho_one_mul_of_bound lam 4 ((contDiff_quad A).continuous.pow 2) (‖A‖^2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh := mul_self_le_mul_self (abs_nonneg (quad A x)) (quad_abs_le_norm A x)
  nlinarith [sq_abs (quad A x)]

def firstDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  rho 1 x*(quad A x/2)

def secondDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  rho 1 x*(Matrix.trace (A*A)/4+(quad A x)^2/8-quad (A*A) x/2)

theorem integrable_exp_max_firstDensityCoeff (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x => Real.exp (lam*SimplexFull.maxCoord x)*firstDensityCoeff A x) := by
  have hh := (integrable_exp_max_rho_one_mul_quad lam A).div_const 2
  convert hh using 1
  ext x
  simp only [firstDensityCoeff]
  ring

theorem integrable_exp_max_secondDensityCoeff (lam : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x => Real.exp (lam*SimplexFull.maxCoord x)*secondDensityCoeff A x) := by
  have hh := (((integrable_exp_max_rho_one (m := m) lam).mul_const (Matrix.trace (A*A)/4)).add
    ((integrable_exp_max_rho_one_mul_quad_sq lam A).div_const 8)).sub
    ((integrable_exp_max_rho_one_mul_quad lam (A*A)).div_const 2)
  convert hh using 1
  ext x
  simp only [secondDensityCoeff, Pi.add_apply, Pi.sub_apply]
  ring

theorem integrable_firstDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (firstDensityCoeff A) := by
  simpa using integrable_exp_max_firstDensityCoeff 0 A

theorem integrable_secondDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (secondDensityCoeff A) := by
  simpa using integrable_exp_max_secondDensityCoeff 0 A

theorem continuous_firstDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (firstDensityCoeff A) :=
  (continuous_rho 1).mul ((contDiff_quad A).continuous.div_const 2)

theorem continuous_secondDensityCoeff (A : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (secondDensityCoeff A) :=
  (continuous_rho 1).mul ((continuous_const.add (((contDiff_quad A).continuous.pow 2).div_const 8)).sub
    ((contDiff_quad (A*A)).continuous.div_const 2))

#print axioms integrable_exp_max_firstDensityCoeff
#print axioms integrable_exp_max_secondDensityCoeff
end SimplexFull.Covariance