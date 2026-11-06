import SimplexFull.LayerCake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter
namespace SimplexFull.GlobalTail

def centeredTailKernel {X : Type*} (f : X → ℝ) (p : X × ℝ) : ℝ :=
  (if p.2 < f p.1 then 1 else 0) - (if p.2 < 0 then 1 else 0)

theorem centeredTailKernel_section {X : Type*} (f : X → ℝ) (x : X) :
    (fun t => centeredTailKernel f (x,t)) =
      (Ico 0 (f x)).indicator (fun _ => (1 : ℝ)) -
        (Ico (f x) 0).indicator (fun _ => (1 : ℝ)) := by
  funext t
  by_cases ht : t < 0 <;> by_cases hf : t < f x
  · simp [centeredTailKernel, Set.indicator, ht, hf, not_le_of_gt ht, not_le_of_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, not_le_of_gt ht, le_of_not_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, le_of_not_gt ht, not_le_of_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, le_of_not_gt ht, le_of_not_gt hf]

theorem integrable_indicator_Ico (a b : ℝ) :
    Integrable ((Ico a b).indicator (fun _ : ℝ => (1 : ℝ))) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact (continuous_const.integrableOn_Icc).mono_set Ico_subset_Icc_self

theorem centeredTailKernel_integrable_section {X : Type*} (f : X → ℝ) (x : X) :
    Integrable (fun t => centeredTailKernel f (x,t)) := by
  rw [centeredTailKernel_section]
  exact (integrable_indicator_Ico 0 (f x)).sub (integrable_indicator_Ico (f x) 0)

theorem centeredTailKernel_integral_section {X : Type*} (f : X → ℝ) (x : X) :
    (∫ t, centeredTailKernel f (x,t)) = f x := by
  rw [centeredTailKernel_section]
  change (∫ t, (Ico 0 (f x)).indicator (fun _ : ℝ => (1 : ℝ)) t -
    (Ico (f x) 0).indicator (fun _ : ℝ => (1 : ℝ)) t) = f x
  rw [integral_sub (integrable_indicator_Ico _ _)
    (integrable_indicator_Ico _ _), integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ico]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ico]
  by_cases hx : 0 ≤ f x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hf : f x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hf, max_eq_left (neg_nonneg.mpr hf)]


theorem centeredTailKernel_norm_section {X : Type*} (f : X → ℝ) (x : X) :
    (fun t => ‖centeredTailKernel f (x,t)‖) =
      (Ico 0 (f x)).indicator (fun _ => (1 : ℝ)) +
        (Ico (f x) 0).indicator (fun _ => (1 : ℝ)) := by
  funext t
  by_cases ht : t < 0 <;> by_cases hf : t < f x
  · simp [centeredTailKernel, Set.indicator, ht, hf, not_le_of_gt ht, not_le_of_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, not_le_of_gt ht, le_of_not_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, le_of_not_gt ht, not_le_of_gt hf]
  · simp [centeredTailKernel, Set.indicator, ht, hf, le_of_not_gt ht, le_of_not_gt hf]

theorem centeredTailKernel_integral_norm {X : Type*} (f : X → ℝ) (x : X) :
    (∫ t, ‖centeredTailKernel f (x,t)‖) = ‖f x‖ := by
  rw [centeredTailKernel_norm_section]
  change (∫ t, (Ico 0 (f x)).indicator (fun _ : ℝ => (1 : ℝ)) t +
    (Ico (f x) 0).indicator (fun _ : ℝ => (1 : ℝ)) t) = ‖f x‖
  rw [integral_add (integrable_indicator_Ico _ _) (integrable_indicator_Ico _ _),
    integral_indicator measurableSet_Ico, integral_indicator measurableSet_Ico]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ico, Real.norm_eq_abs]
  by_cases hx : 0 ≤ f x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  · have hf : f x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hf, max_eq_left (neg_nonneg.mpr hf), abs_of_nonpos hf]

variable {X : Type*} [MeasurableSpace X] {mu : Measure X} [SFinite mu]

theorem centeredTailKernel_measurable {f : X → ℝ} (hf : Measurable f) :
    Measurable (centeredTailKernel f) := by
  unfold centeredTailKernel
  exact (Measurable.ite (measurableSet_lt measurable_snd (hf.comp measurable_fst))
    measurable_const measurable_const).sub
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const)
    measurable_const measurable_const)

theorem centeredTailKernel_integrable {f : X → ℝ}
    (hf : Measurable f) (hi : Integrable f mu) :
    Integrable (centeredTailKernel f) (mu.prod volume) := by
  apply (integrable_prod_iff (centeredTailKernel_measurable hf).aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall (centeredTailKernel_integrable_section f)
  · simpa only [centeredTailKernel_integral_norm] using hi.norm

theorem integral_centeredTailKernel {f : X → ℝ}
    (hf : Measurable f) (hi : Integrable f mu) :
    (∫ t, ∫ x, centeredTailKernel f (x,t) ∂mu) = ∫ x, f x ∂mu := by
  have hs := integral_integral_swap (f := fun x t => centeredTailKernel f (x,t))
    (centeredTailKernel_integrable hf hi)
  simpa only [centeredTailKernel_integral_section] using hs.symm


theorem centeredTailKernel_integral_left [IsProbabilityMeasure mu]
    {f : X → ℝ} (hf : Measurable f) (t : ℝ) :
    (∫ x, centeredTailKernel f (x,t) ∂mu) =
      1 - mu.real {x | f x ≤ t} - (if t < 0 then 1 else 0) := by
  have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  have hi : Integrable (({x | t < f x} : Set X).indicator (fun _ => (1 : ℝ))) mu :=
    (integrable_const (1 : ℝ)).indicator hs
  change (∫ x, ({x | t < f x} : Set X).indicator (fun _ => (1 : ℝ)) x -
    (if t < 0 then 1 else 0) ∂mu) = _
  rw [integral_sub hi (integrable_const _), integral_indicator hs]
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ, one_mul, measureReal_restrict_apply_univ]
  have hc : {x | t < f x} = {x | f x ≤ t}ᶜ := by ext x; simp
  rw [hc, probReal_compl_eq_one_sub (measurableSet_le hf measurable_const)]

theorem integrable_cdf_gap [IsProbabilityMeasure mu]
    {nu : Measure X} [IsProbabilityMeasure nu] {f : X → ℝ}
    (hf : Measurable f) (hm : Integrable f mu) (hn : Integrable f nu) :
    Integrable (fun t => mu.real {x | f x ≤ t} - nu.real {x | f x ≤ t}) := by
  have him := (centeredTailKernel_integrable hf hm).integral_prod_right
  have hin := (centeredTailKernel_integrable hf hn).integral_prod_right
  have hi := hin.sub him
  convert hi using 1
  funext t
  simp only [Pi.sub_apply]
  rw [centeredTailKernel_integral_left hf t, centeredTailKernel_integral_left hf t]
  ring

theorem integral_sub_eq_integral_cdf_gap [IsProbabilityMeasure mu]
    {nu : Measure X} [IsProbabilityMeasure nu] {f : X → ℝ}
    (hf : Measurable f) (hm : Integrable f mu) (hn : Integrable f nu) :
    (∫ x, f x ∂nu) - (∫ x, f x ∂mu) =
      ∫ t, mu.real {x | f x ≤ t} - nu.real {x | f x ≤ t} := by
  rw [← integral_centeredTailKernel hf hn, ← integral_centeredTailKernel hf hm,
    ← integral_sub (centeredTailKernel_integrable hf hn).integral_prod_right
      (centeredTailKernel_integrable hf hm).integral_prod_right]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [centeredTailKernel_integral_left hf t, centeredTailKernel_integral_left hf t]
  ring

#print axioms centeredTailKernel_integrable
#print axioms integral_centeredTailKernel
#print axioms integrable_cdf_gap
#print axioms integral_sub_eq_integral_cdf_gap
end SimplexFull.GlobalTail
