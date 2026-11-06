import SimplexFull.GlobalBivariateCalculus
import SimplexFull.GlobalRectangleQuantitative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open MeasureTheory Set Real Filter ProbabilityTheory WeakSimplex
open scoped Topology Interval ENNReal
namespace SimplexFull.GlobalBivariate

theorem Phi_monotone : Monotone Phi := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_Phi x).differentiableAt)
  intro x
  rw [(hasDerivAt_Phi x).deriv]
  exact phi_nonneg x

theorem gaussianReal_Icc_eq_Phi (l u : ℝ) (hlu : l≤u) :
    gaussianReal 0 1 (Icc l u) = ENNReal.ofReal (Phi u-Phi l) := by
  rw [gaussianReal_apply_eq_integral _ one_ne_zero]
  congr 1
  change (∫ x in Icc l u, phi x) = Phi u-Phi l
  change (∫ x in Icc l u, phi x) = (∫ x in Iic u, phi x)-(∫ x in Iic l, phi x)
  rw [intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn integrable_phi.integrableOn]
  rw [intervalIntegral.integral_of_le hlu,restrict_Ioc_eq_restrict_Icc]

theorem shifted_conditional_mass {r : ℝ} (hr : |r|<1) {a : ℝ} (ha : 0≤a) (t : ℝ) :
    gaussianReal 0 (1-r^2).toNNReal {x | x+t*r ∈ Icc (-a) a} =
      ENNReal.ofReal (Phi (z r a t)-Phi (z r (-a) t)) := by
  have hs := sd_pos hr
  have hs2 := sd_sq hr
  have hmap : (gaussianReal 0 1).map (fun x => sd r*x) =
      gaussianReal 0 (1-r^2).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.toNNReal_of_nonneg (by nlinarith [sq_nonneg (sd r)] : 0≤1-r^2),hs2]
  have hmset : MeasurableSet {x : ℝ | x+t*r ∈ Icc (-a) a} :=
    measurableSet_Icc.preimage (by fun_prop)
  rw [←hmap,Measure.map_apply (by fun_prop) hmset]
  have hset : (fun x => sd r*x) ⁻¹' {x | x+t*r ∈ Icc (-a) a} =
      Icc (z r (-a) t) (z r a t) := by
    ext x
    simp only [mem_preimage,mem_setOf_eq,mem_Icc,z,div_le_iff₀ hs,le_div_iff₀ hs]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith
  rw [hset,gaussianReal_Icc_eq_Phi]
  unfold z
  exact div_le_div_of_nonneg_right (by linarith) hs.le

theorem pair_probability_eq_rectangleIntegral
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.PosSemidef)
    (hdiag : ∀ i,R i i=1) (r : Fin 2→ℝ) (hr : ∀ i,0≤r i)
    (hcorr : |R 0 1|<1) :
    (multivariateGaussian (0 : Coord 2) R (symmetricRectangle r)).toReal =
      rectangleIntegral (R 0 1) (r 0) (r 1) := by
  rw [GlobalRectangle.pair_rectangle_eq_conditional hR hdiag]
  simp_rw [shifted_conditional_mass hcorr (hr 0)]
  let f : ℝ→ℝ := fun t => Phi (z (R 0 1) (r 0) t)-Phi (z (R 0 1) (-r 0) t)
  have hnn (t : ℝ) : 0≤f t := by
    apply sub_nonneg.mpr
    apply Phi_monotone
    unfold z
    exact div_le_div_of_nonneg_right (by linarith [hr 0]) (sd_pos hcorr).le
  have hf : Continuous f := by
    dsimp [f,z]
    exact (continuous_Phi.comp (by fun_prop)).sub (continuous_Phi.comp (by fun_prop))
  change (∫⁻ t in Icc (-r 1) (r 1), ENNReal.ofReal (f t) ∂gaussianReal 0 1).toReal = _
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hf.aestronglyMeasurable]
  rw [← integral_indicator measurableSet_Icc,integral_gaussianReal_eq_integral_smul one_ne_zero]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • (Icc (-r 1) (r 1)).indicator f x) =
      (Icc (-r 1) (r 1)).indicator (conditional (R 0 1) (r 0)) := by
    ext x
    by_cases hx : x ∈ Icc (-r 1) (r 1)
    · simp [Set.indicator_of_mem hx,f,conditional,phi,mul_comm]
    · simp [Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Icc]
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le (by linarith [hr 1]),restrict_Ioc_eq_restrict_Icc]

#print axioms pair_probability_eq_rectangleIntegral
end SimplexFull.GlobalBivariate

namespace SimplexFull.GlobalBivariate

theorem rectangleIntegral_zero (a b : ℝ) :
    rectangleIntegral 0 a b = (Phi a-Phi (-a))*(Phi b-Phi (-b)) := by
  unfold rectangleIntegral conditional z sd
  simp only [zero_pow (by norm_num : 2≠0),sub_zero,Real.sqrt_one,zero_mul,div_one]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact (intervalIntegral.integral_Iic_sub_Iic (f := phi) (a := -b) (b := b)
    integrable_phi.integrableOn integrable_phi.integrableOn).symm

theorem rectangleIntegral_zero_eq_product {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    rectangleIntegral 0 a b =
      (gaussianReal 0 1 (Icc (-a) a)*gaussianReal 0 1 (Icc (-b) b)).toReal := by
  rw [rectangleIntegral_zero,ENNReal.toReal_mul,
    gaussianReal_Icc_eq_Phi (-a) a (by linarith),
    gaussianReal_Icc_eq_Phi (-b) b (by linarith),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (Phi_monotone (by linarith : -a≤a))),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (Phi_monotone (by linarith : -b≤b)))]

#print axioms rectangleIntegral_zero_eq_product
end SimplexFull.GlobalBivariate
