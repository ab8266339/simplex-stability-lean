import SimplexFull.GaussianBase
import SimplexFull.Tilted
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
open MeasureTheory Set Real
namespace SimplexFull

/-- At the benchmark parameters the tilted weight is `phi^2 Phi^2`. -/
theorem tiltWeight_four_zero (c : ℝ) :
    tiltWeight 4 0 c = phi c ^ 2 * Phi c ^ 2 := by
  simp [tiltWeight, zero_mul, exp_zero, one_mul]

/-- `q h phi^2 Phi^2` expands to the two monomials used in the integration by parts. -/
theorem qh_mul_phi_sq_Phi_sq (c : ℝ) :
    q c * h c * phi c ^ 2 * Phi c ^ 2 =
      c * phi c ^ 3 * Phi c + phi c ^ 4 := by
  have hPhi : Phi c ≠ 0 := (Phi_pos c).ne'
  rw [h, q]
  calc
    (phi c / Phi c) * (c + phi c / Phi c) * phi c ^ 2 * Phi c ^ 2 =
        ((c * phi c * Phi c + phi c ^ 2) / Phi c ^ 2) * phi c ^ 2 * Phi c ^ 2 := by
          field_simp [hPhi]
    _ = (c * phi c * Phi c + phi c ^ 2) * phi c ^ 2 := by
          field_simp [hPhi]
    _ = c * phi c ^ 3 * Phi c + phi c ^ 4 := by ring

/-- Pointwise form of `sigma * phi^2 * Phi^2` at `m = 4`, `mu = 0`. -/
theorem sigma_mul_phi_sq_Phi_sq (c : ℝ) :
    sigma c * phi c ^ 2 * Phi c ^ 2 =
      phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c - phi c ^ 4 := by
  have hq := qh_mul_phi_sq_Phi_sq c
  unfold sigma
  calc
    (1 - q c * h c) * phi c ^ 2 * Phi c ^ 2 =
        phi c ^ 2 * Phi c ^ 2 - q c * h c * phi c ^ 2 * Phi c ^ 2 := by ring
    _ = phi c ^ 2 * Phi c ^ 2 - (c * phi c ^ 3 * Phi c + phi c ^ 4) := by rw [hq]
    _ = phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c - phi c ^ 4 := by ring

theorem phi_even (t : ℝ) : phi (-t) = phi t := by
  rw [phi_eq_exp, phi_eq_exp, neg_sq]

theorem phi_pow_four (c : ℝ) :
    phi c ^ 4 = ((√(2 * π))⁻¹) ^ 4 * exp (-(2 : ℝ) * c ^ 2) := by
  rw [phi_eq_exp, mul_pow]
  congr 1
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring

theorem inv_sqrt_two_pi_pow_four :
    ((√(2 * π))⁻¹) ^ 4 = 1 / (4 * π ^ 2) := by
  have hnonneg : (0 : ℝ) ≤ 2 * π := by positivity
  calc
    ((√(2 * π))⁻¹) ^ 4 = ((√(2 * π)) ^ 4)⁻¹ := by rw [inv_pow]
    _ = ((2 * π) ^ 2)⁻¹ := by
      congr 1
      rw [show (√(2 * π)) ^ 4 = ((√(2 * π)) ^ 2) ^ 2 by ring, sq_sqrt hnonneg]
    _ = (4 * π ^ 2)⁻¹ := by congr 1; ring
    _ = 1 / (4 * π ^ 2) := by rw [inv_eq_one_div]

theorem pi_pow_two_eq_rpow_mul_sqrt :
    π ^ 2 = π ^ ((3 : ℝ) / 2) * √π := by
  calc
    π ^ 2 = π ^ (2 : ℝ) := by rw [← rpow_two]
    _ = π ^ ((3 : ℝ) / 2 + (1 : ℝ) / 2) := by
      conv_lhs => rw [show (2 : ℝ) = (3 : ℝ) / 2 + (1 : ℝ) / 2 by norm_num]
    _ = π ^ ((3 : ℝ) / 2) * π ^ ((1 : ℝ) / 2) := by rw [rpow_add pi_pos]
    _ = π ^ ((3 : ℝ) / 2) * √π := by rw [← sqrt_eq_rpow]

/-- `I_4 = ∫ phi^4 = 1 / (4 √2 π^(3/2))`. -/
theorem integral_phi_four :
    ∫ c : ℝ, phi c ^ 4 = 1 / (4 * √2 * π ^ ((3 : ℝ) / 2)) := by
  simp_rw [phi_pow_four, integral_const_mul, integral_gaussian]
  rw [inv_sqrt_two_pi_pow_four, sqrt_div pi_nonneg (2 : ℝ), pi_pow_two_eq_rpow_mul_sqrt]
  field_simp

theorem phi_pow_exp (n : ℕ) (c : ℝ) :
    phi c ^ n = ((√(2 * π))⁻¹) ^ n * exp (-((n : ℝ) / 2) * c ^ 2) := by
  rw [phi_eq_exp, mul_pow]
  congr 1
  rw [← exp_nat_mul]
  congr 1
  ring

theorem inv_sqrt_two_pi_sq :
    ((√(2 * π))⁻¹) ^ 2 = 1 / (2 * π) := by
  have hnonneg : (0 : ℝ) ≤ 2 * π := by positivity
  calc
    ((√(2 * π))⁻¹) ^ 2 = ((√(2 * π)) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (2 * π)⁻¹ := by rw [sq_sqrt hnonneg]
    _ = 1 / (2 * π) := by rw [inv_eq_one_div]

theorem phi_sq_eq (c : ℝ) :
    phi c ^ 2 = (1 / (2 * π)) * exp (-(1 : ℝ) * c ^ 2) := by
  rw [phi_pow_exp 2, inv_sqrt_two_pi_sq]
  congr 1
  congr 1
  ring

theorem integral_phi_sq :
    ∫ c : ℝ, phi c ^ 2 = 1 / (2 * √π) := by
  simp_rw [phi_sq_eq, integral_const_mul, integral_gaussian, div_one]
  have hsq : √π ^ 2 = π := sq_sqrt pi_nonneg
  calc
    (1 / (2 * π)) * √π = √π / (2 * π) := by ring
    _ = √π / (2 * √π ^ 2) := congr_arg (fun t => √π / (2 * t)) hsq.symm
    _ = 1 / (2 * √π) := by field_simp

theorem phi_pow_three (c : ℝ) :
    phi c ^ 3 = (1 / ((2 * π) * √(2 * π))) * exp (-((3 : ℝ) / 2) * c ^ 2) := by
  have hsqrt : (0 : ℝ) ≤ 2 * π := by positivity
  have hden : ((√(2 * π))⁻¹) ^ 3 = 1 / ((2 * π) * √(2 * π)) := by
    calc
      ((√(2 * π))⁻¹) ^ 3 = ((√(2 * π)) ^ 3)⁻¹ := by rw [inv_pow]
      _ = (√(2 * π) ^ 2 * √(2 * π))⁻¹ := by ring
      _ = ((2 * π) * √(2 * π))⁻¹ := by rw [sq_sqrt hsqrt]
      _ = 1 / ((2 * π) * √(2 * π)) := by rw [inv_eq_one_div]
  calc
    phi c ^ 3 = ((√(2 * π))⁻¹) ^ 3 * exp (-((3 : ℝ) / 2) * c ^ 2) := phi_pow_exp 3 c
    _ = (1 / ((2 * π) * √(2 * π))) * exp (-((3 : ℝ) / 2) * c ^ 2) := by rw [hden]

theorem integral_phi_three :
    ∫ c : ℝ, phi c ^ 3 = 1 / (2 * π * √3) := by
  simp_rw [phi_pow_three, integral_const_mul, integral_gaussian]
  have harg : (π : ℝ) / ((3 : ℝ) / 2) = (2 * π) / 3 := by
    rw [div_eq_mul_inv, inv_div]
    ring
  rw [harg, sqrt_div (by positivity : (0 : ℝ) ≤ 2 * π) 3]
  field_simp

theorem integrable_phi_sq : Integrable (fun c : ℝ => phi c ^ 2) := by
  rw [show (fun c : ℝ => phi c ^ 2) =
      fun c => (1 / (2 * π)) * exp (-(1 : ℝ) * c ^ 2) from funext phi_sq_eq]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _

theorem integrable_phi_three : Integrable (fun c : ℝ => phi c ^ 3) := by
  rw [show (fun c : ℝ => phi c ^ 3) =
      fun c => (1 / ((2 * π) * √(2 * π))) * exp (-((3 : ℝ) / 2) * c ^ 2) from
        funext phi_pow_three]
  exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 3 / 2)).const_mul _

theorem integrable_phi_four : Integrable (fun c : ℝ => phi c ^ 4) := by
  have hfun : (fun c : ℝ => phi c ^ 4) =
      fun c => ((√(2 * π))⁻¹) ^ 4 * exp (-(2 : ℝ) * c ^ 2) :=
    funext phi_pow_four
  rw [hfun]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2)).const_mul _

theorem integrable_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * exp (-b * x ^ 2)) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < (2 : ℝ))

theorem hasDerivAt_id_mul_gaussian (b x : ℝ) :
    HasDerivAt (fun t => t * exp (-b * t ^ 2))
      ((1 - 2 * b * x ^ 2) * exp (-b * x ^ 2)) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hexp : HasDerivAt (fun t => exp (-b * t ^ 2))
      (exp (-b * x ^ 2) * (-b * (2 * x))) x :=
    (hpow.const_mul (-b)).exp
  have hmul := (hasDerivAt_id x).mul hexp
  refine hmul.congr_deriv ?_
  simp only [id_eq]
  ring

theorem integrable_deriv_id_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1 - 2 * b * x ^ 2) * exp (-b * x ^ 2)) := by
  have hfun : (fun x : ℝ => (1 - 2 * b * x ^ 2) * exp (-b * x ^ 2)) =
      fun x => exp (-b * x ^ 2) - (2 * b) * (x ^ 2 * exp (-b * x ^ 2)) := by
    funext x
    ring
  rw [hfun]
  exact (integrable_exp_neg_mul_sq hb).sub
    ((integrable_sq_mul_exp_neg_mul_sq hb).const_mul (2 * b))

theorem integral_id_gaussian_deriv_eq_zero {b : ℝ} (hb : 0 < b) :
    ∫ x, (1 - 2 * b * x ^ 2) * exp (-b * x ^ 2) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (fun x => hasDerivAt_id_mul_gaussian b x)
    (integrable_deriv_id_gaussian hb) (integrable_mul_exp_neg_mul_sq hb)

theorem integral_sq_gaussian {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * exp (-b * x ^ 2) = √(π / b) / (2 * b) := by
  have hzero := integral_id_gaussian_deriv_eq_zero hb
  have hfun : (fun x : ℝ => (1 - 2 * b * x ^ 2) * exp (-b * x ^ 2)) =
      fun x => exp (-b * x ^ 2) - (2 * b) * (x ^ 2 * exp (-b * x ^ 2)) := by
    funext x
    ring
  rw [hfun, integral_sub (integrable_exp_neg_mul_sq hb)
      ((integrable_sq_mul_exp_neg_mul_sq hb).const_mul (2 * b)),
    integral_const_mul, integral_gaussian] at hzero
  rw [eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linarith

theorem integral_sq_phi_sq :
    ∫ c : ℝ, c ^ 2 * phi c ^ 2 = 1 / (4 * √π) := by
  have hpt : ∀ c, c ^ 2 * phi c ^ 2 =
      (1 / (2 * π)) * (c ^ 2 * exp (-(1 : ℝ) * c ^ 2)) := by
    intro c
    rw [phi_sq_eq]
    ring
  simp_rw [hpt, integral_const_mul, integral_sq_gaussian (by norm_num : (0 : ℝ) < 1)]
  simp only [div_one, mul_one]
  have hsq : √π ^ 2 = π := sq_sqrt pi_nonneg
  calc
    (1 / (2 * π)) * (√π / 2) = √π / (4 * π) := by ring
    _ = √π / (4 * √π ^ 2) := congr_arg (fun t => √π / (4 * t)) hsq.symm
    _ = 1 / (4 * √π) := by field_simp

theorem integral_comp_neg (g : ℝ → ℝ) : ∫ x, g (-x) = ∫ x, g x := by
  have h₁ : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) (volume : Measure ℝ) :=
    ⟨measurable_neg, Measure.map_neg_eq_self (volume : Measure ℝ)⟩
  simpa using h₁.integral_comp (Homeomorph.neg ℝ).measurableEmbedding g

theorem integral_odd_eq_zero {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have hneg := integral_comp_neg g
  rw [integral_congr_ae (ae_of_all _ hodd), integral_neg] at hneg
  linarith

theorem tail_phi_eq_Phi_neg (c : ℝ) : ∫ x in Ioi c, phi x = Phi (-c) := by
  unfold Phi
  rw [← integral_comp_neg_Ioi c phi]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [phi_even]

theorem Phi_add_Phi_neg (c : ℝ) : Phi c + Phi (-c) = 1 := by
  have hsum : Phi c + ∫ x in Ioi c, phi x = 1 := by
    simpa [Phi, integral_phi_eq_one] using
      intervalIntegral.integral_Iic_add_Ioi (f := phi) (b := c)
        integrable_phi.integrableOn integrable_phi.integrableOn
  simpa [tail_phi_eq_Phi_neg] using hsum

theorem phi_sq_Phi_sub_half_odd (x : ℝ) :
    phi (-x) ^ 2 * (Phi (-x) - 1 / 2) = -(phi x ^ 2 * (Phi x - 1 / 2)) := by
  have hneg : Phi (-x) = 1 - Phi x := by
    have h := Phi_add_Phi_neg x
    linarith
  rw [phi_even, hneg]
  ring

theorem abs_Phi_sub_half_le (c : ℝ) : |Phi c - 1 / 2| ≤ 1 / 2 := by
  rw [abs_le]
  constructor <;> linarith [Phi_pos c, Phi_lt_one c]

theorem hasDerivAt_phi_pow_three (x : ℝ) :
    HasDerivAt (fun t => phi t ^ 3) (-(3 : ℝ) * x * phi x ^ 3) x := by
  refine ((hasDerivAt_phi x).pow 3).congr_deriv ?_
  ring

theorem hasDerivAt_phi3_mul_Phi (x : ℝ) :
    HasDerivAt (fun t => phi t ^ 3 * Phi t)
      (-(3 : ℝ) * x * phi x ^ 3 * Phi x + phi x ^ 4) x := by
  refine ((hasDerivAt_phi_pow_three x).mul (hasDerivAt_Phi x)).congr_deriv ?_
  ring

theorem integrable_abs_mul_phi_three :
    Integrable (fun x : ℝ => |x| * phi x ^ 3) := by
  have hpt : (fun x : ℝ => |x| * phi x ^ 3) =
      fun x => (1 / ((2 * π) * √(2 * π))) * (|x| * exp (-((3 : ℝ) / 2) * x ^ 2)) := by
    funext x
    rw [phi_pow_three]
    ring
  have habs : Integrable (fun x : ℝ => |x| * exp (-((3 : ℝ) / 2) * x ^ 2)) := by
    simpa [abs_mul, abs_of_pos (exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq (by positivity : (0 : ℝ) < 3 / 2)).abs
  rw [hpt]
  exact habs.const_mul _

theorem integrable_id_phi3_Phi :
    Integrable (fun x : ℝ => x * phi x ^ 3 * Phi x) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x * phi x ^ 3 * Phi x) := by
    refine (continuous_id.mul ((continuous_phi.pow 3).mul continuous_Phi)).aestronglyMeasurable.congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply, id_eq]
    ring
  refine integrable_abs_mul_phi_three.mono' hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (phi_nonneg x) 3),
    abs_of_pos (Phi_pos x)]
  have hle : Phi x ≤ 1 := (Phi_lt_one x).le
  calc
    |x| * phi x ^ 3 * Phi x ≤ |x| * phi x ^ 3 * 1 :=
      mul_le_mul_of_nonneg_left hle (mul_nonneg (abs_nonneg x) (pow_nonneg (phi_nonneg x) 3))
    _ = |x| * phi x ^ 3 := by ring

theorem integrable_phi3_mul_Phi : Integrable (fun x : ℝ => phi x ^ 3 * Phi x) := by
  refine integrable_phi_three.mono'
    ((continuous_phi.pow 3).mul continuous_Phi).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (phi_nonneg x) 3) (Phi_pos x).le)]
  exact mul_le_of_le_one_right (pow_nonneg (phi_nonneg x) 3) (Phi_lt_one x).le

theorem integrable_phi3_Phi_deriv :
    Integrable (fun x : ℝ => -(3 : ℝ) * x * phi x ^ 3 * Phi x + phi x ^ 4) := by
  have hfun : (fun x : ℝ => -(3 : ℝ) * x * phi x ^ 3 * Phi x + phi x ^ 4) =
      fun x => phi x ^ 4 + (-(3 : ℝ)) * (x * phi x ^ 3 * Phi x) := by
    funext x
    ring
  rw [hfun]
  exact integrable_phi_four.add (integrable_id_phi3_Phi.const_mul (-(3 : ℝ)))

theorem integral_id_phi3_Phi :
    ∫ x, x * phi x ^ 3 * Phi x = (1 / 3) * ∫ x, phi x ^ 4 := by
  have hzero : ∫ x, -(3 : ℝ) * x * phi x ^ 3 * Phi x + phi x ^ 4 = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable (fun x => hasDerivAt_phi3_mul_Phi x)
      integrable_phi3_Phi_deriv integrable_phi3_mul_Phi
  have hfun : (fun x : ℝ => -(3 : ℝ) * x * phi x ^ 3 * Phi x + phi x ^ 4) =
      fun x => phi x ^ 4 - 3 * (x * phi x ^ 3 * Phi x) := by
    funext x
    ring
  rw [hfun, integral_sub integrable_phi_four (integrable_id_phi3_Phi.const_mul 3),
    integral_const_mul] at hzero
  have hmul : 3 * ∫ x, x * phi x ^ 3 * Phi x = ∫ x, phi x ^ 4 := by linarith
  rw [← hmul]
  ring

theorem hasDerivAt_phi_sq (x : ℝ) :
    HasDerivAt (fun t => phi t ^ 2) (-(2 : ℝ) * x * phi x ^ 2) x := by
  refine ((hasDerivAt_phi x).pow 2).congr_deriv ?_
  ring

theorem hasDerivAt_phi_sq_mul_Phi_sub (x : ℝ) :
    HasDerivAt (fun t => phi t ^ 2 * (Phi t - 1 / 2))
      (-(2 : ℝ) * x * phi x ^ 2 * (Phi x - 1 / 2) + phi x ^ 3) x := by
  refine ((hasDerivAt_phi_sq x).mul ((hasDerivAt_Phi x).sub_const (1 / 2))).congr_deriv ?_
  ring

theorem integrable_abs_mul_phi_sq :
    Integrable (fun x : ℝ => |x| * phi x ^ 2) := by
  have hpt : (fun x : ℝ => |x| * phi x ^ 2) =
      fun x => (1 / (2 * π)) * (|x| * exp (-(1 : ℝ) * x ^ 2)) := by
    funext x
    rw [phi_sq_eq]
    ring
  have habs : Integrable (fun x : ℝ => |x| * exp (-(1 : ℝ) * x ^ 2)) := by
    simpa [abs_mul, abs_of_pos (exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).abs
  rw [hpt]
  exact habs.const_mul _

theorem integrable_phi_sq_Phi_sub :
    Integrable (fun x : ℝ => phi x ^ 2 * (Phi x - 1 / 2)) := by
  refine (integrable_phi_sq.const_mul (1 / 2)).mono'
    ((continuous_phi.pow 2).mul (continuous_Phi.sub continuous_const)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (phi_nonneg x) 2)]
  calc
    phi x ^ 2 * |Phi x - 1 / 2| ≤ phi x ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (abs_Phi_sub_half_le x) (pow_nonneg (phi_nonneg x) 2)
    _ = (1 / 2) * phi x ^ 2 := by ring

theorem integrable_id_phi_sq_Phi_sub :
    Integrable (fun x : ℝ => x * phi x ^ 2 * (Phi x - 1 / 2)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x * phi x ^ 2 * (Phi x - 1 / 2)) := by
    let subPhi : ℝ → ℝ := fun x => Phi x - 1 / 2
    have hsub : Continuous subPhi := continuous_Phi.sub continuous_const
    refine (continuous_id.mul ((continuous_phi.pow 2).mul hsub)).aestronglyMeasurable.congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply, id_eq, subPhi]
    ring
  refine (integrable_abs_mul_phi_sq.const_mul (1 / 2)).mono' hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (phi_nonneg x) 2)]
  calc
    |x| * phi x ^ 2 * |Phi x - 1 / 2| ≤ |x| * phi x ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (abs_Phi_sub_half_le x)
        (mul_nonneg (abs_nonneg x) (pow_nonneg (phi_nonneg x) 2))
    _ = (1 / 2) * (|x| * phi x ^ 2) := by ring

theorem integrable_phi_sq_Phi_sub_sq :
    Integrable (fun x : ℝ => phi x ^ 2 * (Phi x - 1 / 2) ^ 2) := by
  refine (integrable_phi_sq.const_mul (1 / 4)).mono'
    ((continuous_phi.pow 2).mul ((continuous_Phi.sub continuous_const).pow 2)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (phi_nonneg x) 2),
    abs_of_nonneg (sq_nonneg (Phi x - 1 / 2))]
  have hsq : (Phi x - 1 / 2) ^ 2 ≤ (1 / 2) ^ 2 := by
    have habs := abs_Phi_sub_half_le x
    have := mul_le_mul habs habs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa [sq, abs_mul] using this
  calc
    phi x ^ 2 * (Phi x - 1 / 2) ^ 2 ≤ phi x ^ 2 * (1 / 4) := by
      have : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
      rw [this] at hsq
      exact mul_le_mul_of_nonneg_left hsq (pow_nonneg (phi_nonneg x) 2)
    _ = (1 / 4) * phi x ^ 2 := by ring

theorem integrable_phi_sq_Phi_sub_deriv :
    Integrable (fun x : ℝ =>
      -(2 : ℝ) * x * phi x ^ 2 * (Phi x - 1 / 2) + phi x ^ 3) := by
  have hfun : (fun x : ℝ => -(2 : ℝ) * x * phi x ^ 2 * (Phi x - 1 / 2) + phi x ^ 3) =
      fun x => phi x ^ 3 + (-(2 : ℝ)) * (x * phi x ^ 2 * (Phi x - 1 / 2)) := by
    funext x
    ring
  rw [hfun]
  exact integrable_phi_three.add (integrable_id_phi_sq_Phi_sub.const_mul (-(2 : ℝ)))

theorem integral_id_phi_sq_Phi_sub :
    ∫ x, x * phi x ^ 2 * (Phi x - 1 / 2) = (1 / 2) * ∫ x, phi x ^ 3 := by
  have hzero : ∫ x, -(2 : ℝ) * x * phi x ^ 2 * (Phi x - 1 / 2) + phi x ^ 3 = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable (fun x => hasDerivAt_phi_sq_mul_Phi_sub x)
      integrable_phi_sq_Phi_sub_deriv integrable_phi_sq_Phi_sub
  have hfun : (fun x : ℝ => -(2 : ℝ) * x * phi x ^ 2 * (Phi x - 1 / 2) + phi x ^ 3) =
      fun x => phi x ^ 3 - 2 * (x * phi x ^ 2 * (Phi x - 1 / 2)) := by
    funext x
    ring
  rw [hfun, integral_sub integrable_phi_three (integrable_id_phi_sq_Phi_sub.const_mul 2),
    integral_const_mul] at hzero
  have hmul : 2 * ∫ x, x * phi x ^ 2 * (Phi x - 1 / 2) = ∫ x, phi x ^ 3 := by linarith
  rw [← hmul]
  ring

theorem integral_phi_sq_Phi_sub_eq_zero :
    ∫ x, phi x ^ 2 * (Phi x - 1 / 2) = 0 :=
  integral_odd_eq_zero phi_sq_Phi_sub_half_odd

theorem integral_phi_sq_Phi_sq_decompose :
    ∫ c, phi c ^ 2 * Phi c ^ 2 =
      (∫ c, phi c ^ 2 * (Phi c - 1 / 2) ^ 2) + 1 / (8 * √π) := by
  set f := fun c : ℝ => phi c ^ 2 * (Phi c - 1 / 2) ^ 2
  set g := fun c : ℝ => phi c ^ 2 * (Phi c - 1 / 2)
  set h := fun c : ℝ => (1 / 4) * phi c ^ 2
  have hf : Integrable f := integrable_phi_sq_Phi_sub_sq
  have hg : Integrable g := integrable_phi_sq_Phi_sub
  have hh : Integrable h := integrable_phi_sq.const_mul (1 / 4)
  have hpt : (fun c => phi c ^ 2 * Phi c ^ 2) = fun c => f c + g c + h c := by
    funext c
    simp only [f, g, h]
    ring
  rw [hpt]
  have hform : ∫ c, f c + g c + h c = ∫ c, (f + g) c + h c := by
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    simp [Pi.add_apply]
  rw [hform, integral_add (hf.add hg) hh]
  have hform2 : ∫ c, (f + g) c = ∫ c, f c + g c := by
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    simp [Pi.add_apply]
  rw [hform2, integral_add hf hg, integral_phi_sq_Phi_sub_eq_zero, add_zero]
  have hrhs : ∫ c, phi c ^ 2 * (Phi c - 1 / 2) ^ 2 = ∫ c, f c := by
    simp [f]
  rw [hrhs]
  have hhval : ∫ c, h c = (1 / 4) * ∫ c, phi c ^ 2 := by
    simp [h, integral_const_mul]
  rw [hhval, integral_phi_sq]
  ring

theorem integral_three {u v w : ℝ → ℝ}
    (hu : Integrable u) (hv : Integrable v) (hw : Integrable w) :
    ∫ x, u x + v x + w x = (∫ x, u x) + (∫ x, v x) + (∫ x, w x) := by
  have h1 : ∫ x, u x + v x + w x = ∫ x, (u + v) x + w x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [Pi.add_apply]
  have h2 : ∫ x, (u + v) x = ∫ x, u x + v x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [Pi.add_apply]
  rw [h1, integral_add (hu.add hv) hw, h2, integral_add hu hv]

theorem integrable_sq_phi_sq : Integrable (fun c : ℝ => c ^ 2 * phi c ^ 2) := by
  have hpt : (fun c : ℝ => c ^ 2 * phi c ^ 2) =
      fun c => (1 / (2 * π)) * (c ^ 2 * exp (-(1 : ℝ) * c ^ 2)) := by
    funext c
    rw [phi_sq_eq]
    ring
  rw [hpt]
  exact (integrable_sq_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _

theorem integrable_phi_sq_Phi_sq : Integrable (fun c : ℝ => phi c ^ 2 * Phi c ^ 2) := by
  refine integrable_phi_sq.mono'
    ((continuous_phi.pow 2).mul (continuous_Phi.pow 2)).aestronglyMeasurable
    (ae_of_all _ fun c => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (phi_nonneg c) 2) (sq_nonneg (Phi c)))]
  exact mul_le_of_le_one_right (pow_nonneg (phi_nonneg c) 2)
    (pow_le_one₀ (Phi_pos c).le (Phi_lt_one c).le)

theorem sigma_tilt_four_eq (c : ℝ) :
    sigma c * tiltWeight 4 0 c =
      phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c - phi c ^ 4 := by
  rw [tiltWeight_four_zero]
  calc
    sigma c * (phi c ^ 2 * Phi c ^ 2) = sigma c * phi c ^ 2 * Phi c ^ 2 := by ring
    _ = phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c - phi c ^ 4 :=
      sigma_mul_phi_sq_Phi_sq c

theorem integrable_sigma_tilt_four :
    Integrable (fun c : ℝ => sigma c * tiltWeight 4 0 c) := by
  have hfun : (fun c : ℝ => sigma c * tiltWeight 4 0 c) =
      fun c => (phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c) - phi c ^ 4 := by
    funext c
    rw [sigma_tilt_four_eq]
  rw [hfun]
  exact (integrable_phi_sq_Phi_sq.sub integrable_id_phi3_Phi).sub integrable_phi_four

theorem normalizer_four_zero :
    normalizer 4 0 = ∫ c, phi c ^ 2 * Phi c ^ 2 := by
  unfold normalizer
  simp_rw [tiltWeight_four_zero]

theorem pi_rpow_three_halves : π ^ ((3 : ℝ) / 2) = π * √π := by
  have hs : √π ≠ 0 := by positivity
  apply mul_left_cancel₀ hs
  have hsq : √π * √π = π := by
    rw [← sq]
    exact sq_sqrt pi_nonneg
  calc
    √π * π ^ ((3 : ℝ) / 2) = π ^ ((3 : ℝ) / 2) * √π := by ring
    _ = π ^ 2 := pi_pow_two_eq_rpow_mul_sqrt.symm
    _ = π * π := by ring
    _ = π * (√π * √π) := by rw [hsq]
    _ = √π * (π * √π) := by ring

theorem cross_sq_lower :
    1 / (12 * π ^ ((3 : ℝ) / 2)) ≤ ∫ x, phi x ^ 2 * (Phi x - 1 / 2) ^ 2 := by
  set A := ∫ x, x ^ 2 * phi x ^ 2
  set B := ∫ x, x * phi x ^ 2 * (Phi x - 1 / 2)
  set C := ∫ x, phi x ^ 2 * (Phi x - 1 / 2) ^ 2
  have hA : A = 1 / (4 * √π) := integral_sq_phi_sq
  have hB : B = (1 / 2) * ∫ x, phi x ^ 3 := integral_id_phi_sq_Phi_sub
  have hApos : 0 < A := by rw [hA]; positivity
  set t : ℝ := B / A
  let u : ℝ → ℝ := fun x => phi x ^ 2 * (Phi x - 1 / 2) ^ 2
  let v : ℝ → ℝ := fun x => (-(2 * t)) * (x * phi x ^ 2 * (Phi x - 1 / 2))
  let w : ℝ → ℝ := fun x => t ^ 2 * (x ^ 2 * phi x ^ 2)
  have hu : Integrable u := integrable_phi_sq_Phi_sub_sq
  have hv : Integrable v := integrable_id_phi_sq_Phi_sub.const_mul (-(2 * t))
  have hw : Integrable w := integrable_sq_phi_sq.const_mul (t ^ 2)
  have hsq : (fun x => (phi x * (Phi x - 1 / 2) - t * (x * phi x)) ^ 2) =
      fun x => u x + v x + w x := by
    funext x
    simp only [u, v, w]
    ring
  have hint : Integrable (fun x => (phi x * (Phi x - 1 / 2) - t * (x * phi x)) ^ 2) := by
    rw [hsq]
    exact (hu.add hv).add hw
  have hnn : 0 ≤ ∫ x, (phi x * (Phi x - 1 / 2) - t * (x * phi x)) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x, (phi x * (Phi x - 1 / 2) - t * (x * phi x)) ^ 2 =
      (∫ x, u x) + (∫ x, v x) + (∫ x, w x) := by
    rw [hsq]
    exact integral_three hu hv hw
  have hC : (∫ x, u x) = C := by simp [u, C]
  have hBv : (∫ x, v x) = (-(2 * t)) * B := by
    simp only [v]
    rw [integral_const_mul]
  have hAw : (∫ x, w x) = t ^ 2 * A := by
    simp [w, A, integral_const_mul]
  have hquad : 0 ≤ C - 2 * t * B + t ^ 2 * A := by
    rw [hexp, hC, hBv, hAw] at hnn
    linarith
  have hmin : C - 2 * t * B + t ^ 2 * A = C - B ^ 2 / A := by
    simp only [t]
    field_simp [hApos.ne']
    ring
  have hle : B ^ 2 / A ≤ C := by linarith
  have hval : B ^ 2 / A = 1 / (12 * π ^ ((3 : ℝ) / 2)) := by
    rw [hA, hB, integral_phi_three, pi_rpow_three_halves]
    field_simp
    rw [sq_sqrt pi_nonneg, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  linarith

theorem normalizer_four_zero_lower :
    1 / (8 * √π) + 1 / (12 * π ^ ((3 : ℝ) / 2)) ≤ normalizer 4 0 := by
  rw [normalizer_four_zero, integral_phi_sq_Phi_sq_decompose]
  linarith [cross_sq_lower]

theorem sqrt_two_lt_seventeen_div_twelve : √2 < (17 : ℝ) / 12 := by
  rw [sqrt_lt' (by norm_num : (0 : ℝ) < 17 / 12)]
  norm_num

theorem eight_sqrt_two_lt_three_pi_add_two : 8 * √2 < 3 * π + 2 := by
  have hsqrt : 8 * √2 < 34 / 3 := by
    calc
      8 * √2 < 8 * (17 / 12) :=
        mul_lt_mul_of_pos_left sqrt_two_lt_seventeen_div_twelve (by norm_num)
      _ = 34 / 3 := by norm_num
  have hpi : 34 / 3 < 3 * π + 2 := by
    have hbound : (3.14 : ℝ) < π := pi_gt_d2
    have hnum : 34 / 3 < 3 * (3.14 : ℝ) + 2 := by norm_num
    linarith
  linarith

theorem b_four_zero_formula :
    b 4 0 = 1 - 4 * (∫ c, phi c ^ 4) / (3 * normalizer 4 0) := by
  have hfun : (fun c => sigma c * tiltWeight 4 0 c) =
      fun c => (phi c ^ 2 * Phi c ^ 2 - c * phi c ^ 3 * Phi c) - phi c ^ 4 := by
    funext c
    rw [sigma_tilt_four_eq]
  have hnum : ∫ c, sigma c * tiltWeight 4 0 c =
      (∫ c, phi c ^ 2 * Phi c ^ 2) - (∫ c, c * phi c ^ 3 * Phi c) - ∫ c, phi c ^ 4 := by
    have hpt : (fun c => sigma c * tiltWeight 4 0 c) =
        fun c => phi c ^ 2 * Phi c ^ 2 + (-1) * (c * phi c ^ 3 * Phi c) + (-1) * phi c ^ 4 := by
      funext c
      rw [sigma_tilt_four_eq]
      ring
    rw [hpt, integral_three integrable_phi_sq_Phi_sq (integrable_id_phi3_Phi.const_mul (-1))
        (integrable_phi_four.const_mul (-1)), integral_const_mul, integral_const_mul]
    ring
  unfold b tiltedMoment
  rw [hnum, normalizer_four_zero, integral_id_phi3_Phi]
  have hJ : (∫ c, phi c ^ 2 * Phi c ^ 2) ≠ 0 := by
    rw [← normalizer_four_zero]
    exact (normalizer_pos 4 0).ne'
  field_simp [hJ]
  ring

theorem benchmark_ratio_le :
    4 * (∫ c, phi c ^ 4) / (3 * normalizer 4 0) ≤ 4 * √2 / (3 * π + 2) := by
  set J := normalizer 4 0
  set I : ℝ := ∫ c, phi c ^ 4
  set L : ℝ := 1 / (8 * √π) + 1 / (12 * π ^ ((3 : ℝ) / 2))
  have hJ : L ≤ J := normalizer_four_zero_lower
  have hLpos : 0 < L := by
    unfold L
    positivity
  have hI : I = 1 / (4 * √2 * π ^ ((3 : ℝ) / 2)) := integral_phi_four
  have hle : 4 * I / (3 * J) ≤ 4 * I / (3 * L) := by
    refine div_le_div_of_nonneg_left ?_ ?_ ?_
    · have : 0 < I := by rw [hI]; positivity
      positivity
    · positivity
    · linarith
  have harith : 4 * I / (3 * L) = 4 * √2 / (3 * π + 2) := by
    rw [hI]
    unfold L
    rw [pi_rpow_three_halves]
    field_simp
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  linarith

theorem four_sqrt_two_ratio_lt_half : 4 * √2 / (3 * π + 2) < 1 / 2 := by
  have hden : 0 < 3 * π + 2 := by linarith [pi_pos]
  rw [div_lt_iff₀ hden]
  linarith [eight_sqrt_two_lt_three_pi_add_two]

theorem b4_zero_gt_half : (1 : ℝ) / 2 < b 4 0 := by
  linarith [b_four_zero_formula, benchmark_ratio_le, four_sqrt_two_ratio_lt_half]

#print axioms tiltWeight_four_zero
#print axioms qh_mul_phi_sq_Phi_sq
#print axioms sigma_mul_phi_sq_Phi_sq
#print axioms phi_even
#print axioms phi_pow_four
#print axioms integral_phi_four
#print axioms integrable_phi_four
#print axioms integral_phi_sq
#print axioms integral_phi_three
#print axioms integral_sq_gaussian
#print axioms integral_sq_phi_sq
#print axioms Phi_add_Phi_neg
#print axioms integral_id_phi3_Phi
#print axioms integral_id_phi_sq_Phi_sub
#print axioms integral_phi_sq_Phi_sq_decompose
#print axioms cross_sq_lower
#print axioms b_four_zero_formula
#print axioms benchmark_ratio_le
#print axioms b4_zero_gt_half

end SimplexFull
