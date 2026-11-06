import SimplexFull.GaussianBase
import SimplexFull.Mills
import SimplexFull.GaussianDensity
import SimplexFull.Decoder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian orthant moments

Actual Lebesgue integrals of coordinate monomials of `phi` on `(-∞, c]`, then products over the
orthant `{x | maxCoord x ≤ c}`. The covariance Hessian coefficient is assembled from these
moments. Parameter derivatives of the density are not proved here.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace SimplexFull

/-! ### One-dimensional tail moments -/

lemma neg_sq_div_two (x : ℝ) : -(x ^ 2) / 2 = -(1 / 2) * x ^ 2 := by
  rw [div_eq_mul_inv]
  have h2 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [h2]
  ring

lemma tendsto_phi_atBot_zero : Tendsto phi atBot (𝓝 0) := by
  have hcomp : Tendsto (phi ∘ Neg.neg) atBot (𝓝 0) :=
    tendsto_phi_atTop_zero.comp tendsto_neg_atBot_atTop
  have heq : phi ∘ Neg.neg = phi := funext fun x => phi_neg_basic x
  exact heq ▸ hcomp

lemma tendsto_id_mul_phi_atTop_zero : Tendsto (fun x : ℝ => x * phi x) atTop (𝓝 0) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hexp : Tendsto (fun x : ℝ => exp (-x)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hsqrt : Tendsto ((fun y : ℝ => √y) ∘ fun x => exp (-x)) atTop (𝓝 0) := by
    have hcomp := (continuous_sqrt.tendsto (0 : ℝ)).comp hexp
    simpa [Real.sqrt_zero] using hcomp
  have heq : (fun x : ℝ => exp (-(1 / 2) * x)) =
      (fun y : ℝ => √y) ∘ fun x => exp (-x) := by
    ext x
    rw [Function.comp_apply, Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hhalf : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) :=
    heq ▸ hsqrt
  have hlittle :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (1 : ℝ)).tendsto_zero_of_tendsto hhalf
  have hmul : (fun x : ℝ => x * phi x) =
      fun x => (√(2 * π))⁻¹ * (x ^ (1 : ℝ) * exp (-(1 / 2) * x ^ 2)) := by
    ext x
    rw [phi_eq_exp, rpow_one, ← neg_sq_div_two]
    ring
  rw [hmul]
  simpa using hlittle.const_mul ((√(2 * π))⁻¹)

lemma tendsto_id_mul_phi_atBot_zero : Tendsto (fun x : ℝ => x * phi x) atBot (𝓝 0) := by
  have hcomp : Tendsto (fun x : ℝ => (-x) * phi (-x)) atBot (𝓝 0) :=
    tendsto_id_mul_phi_atTop_zero.comp tendsto_neg_atBot_atTop
  have hneg : Tendsto (fun x : ℝ => -((-x) * phi (-x))) atBot (𝓝 0) := by
    simpa using hcomp.neg
  have heq : (fun x : ℝ => -((-x) * phi (-x))) = fun x => x * phi x := by
    ext x
    rw [phi_neg_basic x]
    ring
  exact heq ▸ hneg

lemma integrable_pow_mul_phi (n : ℕ) : Integrable (fun x : ℝ => x ^ n * phi x) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hs : -1 < (n : ℝ) := lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)
  have hint := integrable_rpow_mul_exp_neg_mul_sq hb hs
  have hfun : (fun x : ℝ => x ^ n * phi x) =
      fun x => (√(2 * π))⁻¹ * (x ^ (n : ℝ) * exp (-(1 / 2) * x ^ 2)) := by
    ext x
    rw [phi_eq_exp, ← rpow_natCast x n, ← neg_sq_div_two]
    ring
  rw [hfun]
  exact hint.const_mul ((√(2 * π))⁻¹)

lemma integrable_id_mul_phi : Integrable (fun x : ℝ => x * phi x) := by
  simpa [pow_one] using integrable_pow_mul_phi 1

lemma integrable_sq_mul_phi : Integrable (fun x : ℝ => x ^ 2 * phi x) :=
  integrable_pow_mul_phi 2

lemma hasDerivAt_neg_phi (x : ℝ) : HasDerivAt (fun t => -phi t) (x * phi x) x := by
  refine (hasDerivAt_phi x).neg.congr_deriv ?_
  ring

lemma hasDerivAt_id_mul_phi (x : ℝ) :
    HasDerivAt (fun t => t * phi t) ((1 - x ^ 2) * phi x) x := by
  refine ((hasDerivAt_id x).mul (hasDerivAt_phi x)).congr_deriv ?_
  simp only [id_eq, one_mul]
  ring

/-- `∫_{(-∞, c]} x φ(x) dx = -φ(c)`. -/
theorem integral_Iic_id_mul_phi (c : ℝ) :
    ∫ x in Iic c, x * phi x = -phi c := by
  have hderiv : ∀ x ∈ Iic c, HasDerivAt (fun t => -phi t) (x * phi x) x :=
    fun x _ => hasDerivAt_neg_phi x
  have hint : IntegrableOn (fun x => x * phi x) (Iic c) := integrable_id_mul_phi.integrableOn
  have htend : Tendsto (fun t => -phi t) atBot (𝓝 0) := by
    simpa using tendsto_phi_atBot_zero.neg
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := c) (f := fun t => -phi t)
    (f' := fun x => x * phi x) (m := (0 : ℝ)) hderiv hint htend
  simpa using h

/-- `∫_{(-∞, c]} (1 - x²) φ(x) dx = c φ(c)`, from `(x φ)' = (1 - x²) φ` and `x φ(x) → 0`. -/
theorem integral_Iic_one_sub_sq_mul_phi (c : ℝ) :
    ∫ x in Iic c, (1 - x ^ 2) * phi x = c * phi c := by
  have hderiv : ∀ x ∈ Iic c, HasDerivAt (fun t => t * phi t) ((1 - x ^ 2) * phi x) x :=
    fun x _ => hasDerivAt_id_mul_phi x
  have hint : IntegrableOn (fun x => (1 - x ^ 2) * phi x) (Iic c) := by
    have hfun : (fun x : ℝ => (1 - x ^ 2) * phi x) = fun x => phi x - x ^ 2 * phi x := by
      ext x
      ring
    rw [hfun]
    exact (integrable_phi.sub integrable_sq_mul_phi).integrableOn
  have htend : Tendsto (fun t => t * phi t) atBot (𝓝 (0 : ℝ)) := tendsto_id_mul_phi_atBot_zero
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := c) (f := fun t => t * phi t)
    (f' := fun x => (1 - x ^ 2) * phi x) (m := (0 : ℝ)) hderiv hint htend
  simpa using h

/-- `∫_{(-∞, c]} x² φ(x) dx = Φ(c) - c φ(c)`. -/
theorem integral_Iic_sq_mul_phi (c : ℝ) :
    ∫ x in Iic c, x ^ 2 * phi x = Phi c - c * phi c := by
  have hsplit : ∫ x in Iic c, phi x - x ^ 2 * phi x =
      (∫ x in Iic c, phi x) - ∫ x in Iic c, x ^ 2 * phi x :=
    integral_sub (μ := volume.restrict (Iic c)) integrable_phi.integrableOn
      integrable_sq_mul_phi.integrableOn
  have hfun : (fun x : ℝ => (1 - x ^ 2) * phi x) = fun x => phi x - x ^ 2 * phi x := by
    ext x
    ring
  have hftc := integral_Iic_one_sub_sq_mul_phi c
  rw [hfun, hsplit] at hftc
  have hPhi : ∫ x in Iic c, phi x = Phi c := rfl
  rw [hPhi] at hftc
  linarith

#print axioms integral_Iic_id_mul_phi
#print axioms integral_Iic_sq_mul_phi

end SimplexFull
