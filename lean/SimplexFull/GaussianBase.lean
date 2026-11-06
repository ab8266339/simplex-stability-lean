import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory Set Real Function
open scoped Real
namespace SimplexFull

def phi (x : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 x
def Phi (c : ℝ) : ℝ := ∫ x in Iic c, phi x
def q (c : ℝ) : ℝ := phi c / Phi c
def h (c : ℝ) : ℝ := c + q c
def sigma (c : ℝ) : ℝ := 1 - q c * h c
def F (c : ℝ) : ℝ := h c ^ 2 - sigma c
def D (c : ℝ) : ℝ := sigma c + sigma c ^ 2 - (1 - sigma c) * h c ^ 2

theorem phi_pos (x : ℝ) : 0 < phi x :=
  ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero

theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := (phi_pos x).le

theorem integrable_phi : Integrable phi :=
  ProbabilityTheory.integrable_gaussianPDFReal 0 1

theorem integral_phi_eq_one : (∫ x, phi x) = 1 :=
  ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero

theorem continuous_phi : Continuous phi := by
  unfold phi ProbabilityTheory.gaussianPDFReal
  fun_prop

theorem phi_eq_exp (t : ℝ) : phi t = (√(2 * π))⁻¹ * exp (-(t ^ 2) / 2) := by
  unfold phi ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero, mul_one]

theorem hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hhalf : HasDerivAt (fun t : ℝ => -(t ^ 2) / 2) (-x) x := by
    have hmul : HasDerivAt (fun t : ℝ => (-(1 / 2 : ℝ)) * t ^ 2)
        ((-(1 / 2 : ℝ)) * (2 * x)) x :=
      hsq.const_mul (-(1 / 2))
    exact (hmul.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by ring)
  have hexp : HasDerivAt (fun t : ℝ => exp (-(t ^ 2) / 2))
      (exp (-(x ^ 2) / 2) * -x) x :=
    hhalf.exp
  have hscaled : HasDerivAt (fun t : ℝ => (√(2 * π))⁻¹ * exp (-(t ^ 2) / 2))
      ((√(2 * π))⁻¹ * (exp (-(x ^ 2) / 2) * -x)) x :=
    hexp.const_mul ((√(2 * π))⁻¹)
  exact (hscaled.congr_deriv (by rw [phi_eq_exp]; ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall phi_eq_exp)

theorem Phi_pos (c : ℝ) : 0 < Phi c := by
  unfold Phi
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun _ => phi_nonneg _)
    integrable_phi.integrableOn]
  have hsupp : support phi = univ := by
    ext x
    simp [mem_support, (phi_pos x).ne']
  rw [hsupp, univ_inter, Real.volume_Iic]
  exact ENNReal.zero_lt_top

theorem Phi_lt_one (c : ℝ) : Phi c < 1 := by
  have htail : 0 < ∫ x in Ioi c, phi x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun _ => phi_nonneg _)
      integrable_phi.integrableOn]
    have hsupp : support phi = univ := by
      ext x
      simp [mem_support, (phi_pos x).ne']
    rw [hsupp, univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have hsum : Phi c + ∫ x in Ioi c, phi x = 1 := by
    simpa [Phi, integral_phi_eq_one] using
      intervalIntegral.integral_Iic_add_Ioi (f := phi) (b := c)
        integrable_phi.integrableOn integrable_phi.integrableOn
  linarith

theorem Phi_eq_add_interval (c : ℝ) :
    Phi c = Phi 0 + ∫ x in (0 : ℝ)..c, phi x := by
  have h := intervalIntegral.integral_Iic_sub_Iic (f := phi) (a := (0 : ℝ)) (b := c)
    integrable_phi.integrableOn integrable_phi.integrableOn
  simpa [Phi, sub_eq_iff_eq_add'] using h

theorem hasDerivAt_Phi (c : ℝ) : HasDerivAt Phi (phi c) c := by
  have hsum : HasDerivAt ((fun _ : ℝ => Phi 0) + fun u => ∫ x in (0 : ℝ)..u, phi x)
      (0 + phi c) c :=
    (hasDerivAt_const c (Phi 0)).add
      ((continuous_phi.integral_hasStrictDerivAt (0 : ℝ) c).hasDerivAt)
  have hderiv : HasDerivAt (fun t => Phi 0 + ∫ x in (0 : ℝ)..t, phi x) (phi c) c :=
    (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv
      (zero_add (phi c))
  exact hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall Phi_eq_add_interval)

theorem continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.mpr fun c => (hasDerivAt_Phi c).continuousAt

end SimplexFull