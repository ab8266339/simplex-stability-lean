import SimplexFull.GlobalTailMean
import Mathlib.Tactic
noncomputable section
open MeasureTheory Set
namespace SimplexFull.GlobalTail

theorem integral_ge_const_on_interval {g : Real → Real} (hg : Integrable g)
    (hn : ∀ t, 0 ≤ g t) {A l r : Real} (hlr : l ≤ r)
    (hl : ∀ t ∈ Icc l r, A ≤ g t) : (r-l)*A ≤ ∫ t, g t := by
  have hi : Integrable ((Icc l r).indicator (fun _ => A)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hle : ∀ t, (Icc l r).indicator (fun _ => A) t ≤ g t := by
    intro t
    by_cases ht : t ∈ Icc l r
    · simpa [ht] using hl t ht
    · simpa [ht] using hn t
  have hb := integral_mono hi hg hle
  rw [integral_indicator measurableSet_Icc, setIntegral_const] at hb
  simpa [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hlr)] using hb

theorem exp_sublevel_eq {X : Type*} (f : X → Real) {a t : Real}
    (ha : 0<a) (ht : 0<t) :
    {x | Real.exp (a*f x) ≤ t} = {x | f x ≤ Real.log t/a} := by
  ext x
  simp only [mem_setOf_eq, ← Real.le_log_iff_exp_le ht]
  rw [le_div_iff₀ ha, mul_comm]

theorem exp_sublevel_empty {X : Type*} (f : X → Real) {a t : Real}
    (ht : t≤0) : {x | Real.exp (a*f x) ≤ t} = ∅ := by
  ext x
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact not_le.mpr (lt_of_le_of_lt ht (Real.exp_pos _))

theorem exp_integral_difference_ge_of_cdf_gap
    {X : Type*} [MeasurableSpace X] {mu nu : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {f : X → Real}
    (hf : Measurable f) {a : Real} (ha : 0<a)
    (hm : Integrable (fun x => Real.exp (a*f x)) mu)
    (hn : Integrable (fun x => Real.exp (a*f x)) nu)
    (hdom : ∀ t, nu.real {x | f x ≤ t} ≤ mu.real {x | f x ≤ t})
    {A : Real} (hl : ∀ t ∈ Icc (0:Real) 1,
      A ≤ mu.real {x | f x ≤ t}-nu.real {x | f x ≤ t}) :
    A*(Real.exp a-1) ≤
      (∫ x, Real.exp (a*f x) ∂nu)-(∫ x, Real.exp (a*f x) ∂mu) := by
  have he : Measurable (fun x => Real.exp (a*f x)) :=
    Real.measurable_exp.comp (measurable_const.mul hf)
  rw [integral_sub_eq_integral_cdf_gap he hm hn, mul_comm]
  apply integral_ge_const_on_interval (integrable_cdf_gap he hm hn)
  · intro t
    by_cases ht : 0<t
    · rw [exp_sublevel_eq f ha ht]
      exact sub_nonneg.mpr (hdom _)
    · rw [exp_sublevel_empty f (le_of_not_gt ht)]
      simp
  · exact Real.one_le_exp_iff.mpr ha.le
  · intro t ht
    have htpos : 0<t := lt_of_lt_of_le (by norm_num) ht.1
    rw [exp_sublevel_eq f ha htpos]
    apply hl
    constructor
    · exact div_nonneg (Real.log_nonneg ht.1) ha.le
    · rw [div_le_one ha]
      exact (Real.log_le_iff_le_exp htpos).mpr ht.2

#print axioms exp_integral_difference_ge_of_cdf_gap
end SimplexFull.GlobalTail
