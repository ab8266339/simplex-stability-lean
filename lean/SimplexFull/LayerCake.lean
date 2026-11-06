import SimplexFull.Decoder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
noncomputable section
open MeasureTheory Set Filter
namespace SimplexFull
variable {X : Type*} [MeasurableSpace X] {nu : Measure X} [SFinite nu]
private def tailKernel (u g : X → ℝ) (a : ℝ) (z : X × ℝ) : ℝ :=
  if z.2 < u z.1 then Real.exp (a * z.2) * g z.1 else 0
private theorem tailKernel_section_integrable (u g : X → ℝ) {a : ℝ}
    (ha : 0 < a) (x : X) : Integrable (fun c => tailKernel u g a (x,c)) := by
  have hi := (integrableOn_exp_mul_Iic ha (u x)).mono_set Iio_subset_Iic_self
  convert! IntegrableOn.integrable_indicator (hi.mul_const (g x)) measurableSet_Iio using 1

private theorem tailKernel_section_integral (u g : X → ℝ) {a : ℝ}
    (ha : 0 < a) (x : X) :
    (∫ c, tailKernel u g a (x,c)) = Real.exp (a * u x) / a * g x := by
  change (∫ c, (Iio (u x)).indicator (fun c => Real.exp (a*c)*g x) c) = _
  rw [integral_indicator measurableSet_Iio, integral_mul_const, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic ha]
private theorem tailKernel_section_norm (u g : X → ℝ) {a : ℝ}
    (ha : 0 < a) (x : X) :
    (∫ c, ‖tailKernel u g a (x,c)‖) = ‖Real.exp (a * u x) * g x‖ / a := by
  have heq : (fun c => ‖tailKernel u g a (x,c)‖) =
      fun c => tailKernel u (fun y => ‖g y‖) a (x,c) := by
    funext c
    simp [tailKernel, apply_ite norm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [heq, tailKernel_section_integral u (fun y => ‖g y‖) ha]
  simp [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_mul_eq_mul_div]

private theorem tailKernel_integrable {u g : X → ℝ} (hu : Measurable u)
    (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun x => Real.exp (a * u x) * g x) nu) :
    Integrable (tailKernel u g a) (nu.prod volume) := by
  have hm : Measurable (tailKernel u g a) := by
    unfold tailKernel
    exact Measurable.ite (measurableSet_lt measurable_snd (hu.comp measurable_fst))
      ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
        (hg.comp measurable_fst)) measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall (tailKernel_section_integrable u g ha)
  · simpa only [tailKernel_section_norm u g ha] using hint.norm.div_const a

theorem integral_exp_comp_eq_integral_tail {u g : X → ℝ}
    (hu : Measurable u) (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun x => Real.exp (a * u x) * g x) nu) :
    (∫ x, Real.exp (a * u x) * g x ∂nu) =
      a * ∫ c, Real.exp (a * c) * (∫ x in {x | c < u x}, g x ∂nu) := by
  have hi := tailKernel_integrable hu hg ha hint
  have hf := integral_integral_swap (f := fun x c => tailKernel u g a (x,c)) hi
  have hleft : (∫ x, ∫ c, tailKernel u g a (x,c) ∂volume ∂nu) =
      (∫ x, Real.exp (a * u x) * g x ∂nu) / a := by
    simp_rw [tailKernel_section_integral u g ha, div_mul_eq_mul_div]
    simpa only [div_eq_mul_inv] using integral_mul_const a⁻¹ (fun x => Real.exp (a * u x) * g x)
  have hright : (∫ c, ∫ x, tailKernel u g a (x,c) ∂nu ∂volume) =
      ∫ c, Real.exp (a*c) * (∫ x in {x | c < u x}, g x ∂nu) := by
    congr 1; funext c
    change (∫ x, {x | c < u x}.indicator (fun x => Real.exp (a*c)*g x) x ∂nu) = _
    rw [integral_indicator (measurableSet_lt measurable_const hu), integral_const_mul]
  rw [hleft, hright] at hf
  exact (div_eq_iff (ne_of_gt ha)).mp hf |>.trans (mul_comm _ _)


theorem integral_exp_comp_eq_neg_integral_sublevel {u g : X → ℝ}
    (hu : Measurable u) (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hgi : Integrable g nu) (hzero : (∫ x, g x ∂nu) = 0)
    (hint : Integrable (fun x => Real.exp (a * u x) * g x) nu) :
    (∫ x, Real.exp (a * u x) * g x ∂nu) =
      -a * ∫ c, Real.exp (a*c) * (∫ x in {x | u x ≤ c}, g x ∂nu) := by
  rw [integral_exp_comp_eq_integral_tail hu hg ha hint]
  have heq (c : ℝ) : (∫ x in {x | c < u x}, g x ∂nu) =
      -(∫ x in {x | u x ≤ c}, g x ∂nu) := by
    have hs := integral_add_compl (s := {x | u x ≤ c}) (measurableSet_le hu measurable_const) hgi
    have hcompl : {x | u x ≤ c}ᶜ = {x | c < u x} := by ext x; simp
    rw [hcompl, hzero] at hs
    linarith
  simp_rw [heq, mul_neg, integral_neg]
  ring

#print axioms integral_exp_comp_eq_integral_tail
#print axioms integral_exp_comp_eq_neg_integral_sublevel



theorem integrable_exp_mul_integral_sublevel {u g : X → ℝ}
    (hu : Measurable u) (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hgi : Integrable g nu) (hzero : (∫ x, g x ∂nu) = 0)
    (hint : Integrable (fun x => Real.exp (a * u x) * g x) nu) :
    Integrable (fun c => Real.exp (a*c) * (∫ x in {x | u x ≤ c}, g x ∂nu)) := by
  have hi := (tailKernel_integrable hu hg ha hint).integral_prod_right.neg
  convert! hi using 1
  funext c
  have hs := integral_add_compl (s := {x | u x ≤ c})
    (measurableSet_le hu measurable_const) hgi
  have hcompl : {x | u x ≤ c}ᶜ = {x | c < u x} := by ext x; simp
  rw [hcompl, hzero] at hs
  have htail : (∫ x, tailKernel u g a (x,c) ∂nu) =
      Real.exp (a*c) * (∫ x in {x | c < u x}, g x ∂nu) := by
    change (∫ x, {x | c < u x}.indicator (fun x => Real.exp (a*c)*g x) x ∂nu) = _
    rw [integral_indicator (measurableSet_lt measurable_const hu), integral_const_mul]
  change Real.exp (a*c) * (∫ x in {x | u x ≤ c}, g x ∂nu) = -(∫ x, tailKernel u g a (x,c) ∂nu)
  rw [htail]
  linear_combination Real.exp (a*c) * hs

theorem maxCoord_le_iff {m : ℕ} [NeZero m]
    (x : EuclideanSpace ℝ (Fin m)) (c : ℝ) :
    maxCoord x ≤ c ↔ ∀ i, x i ≤ c := by
  simp [maxCoord, Finset.sup'_le_iff]

theorem integral_exp_max_eq_neg_integral_orthant {m : ℕ} [NeZero m]
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : Measurable g) {a : ℝ} (ha : 0 < a)
    (hgi : Integrable g) (hzero : (∫ x, g x) = 0)
    (hint : Integrable (fun x => Real.exp (a * maxCoord x) * g x)) :
    (∫ x, Real.exp (a * maxCoord x) * g x) =
      -a * ∫ c, Real.exp (a*c) * (∫ x in {x | ∀ i, x i ≤ c}, g x) := by
  simpa only [maxCoord_le_iff] using
    integral_exp_comp_eq_neg_integral_sublevel measurable_maxCoord hg ha hgi hzero hint
#print axioms integrable_exp_mul_integral_sublevel
#print axioms integral_exp_max_eq_neg_integral_orthant
end SimplexFull


