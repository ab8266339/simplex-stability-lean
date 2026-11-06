import SimplexFull.GlobalTailMean
import SimplexFull.GlobalMeanWidthBase
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
namespace SimplexFull.GlobalTail

theorem integral_ge_const_of_unit_interval {g : ℝ → ℝ} (hg : Integrable g)
    (hn : ∀ t, 0 ≤ g t) {A : ℝ} (hA : 0 ≤ A)
    (hl : ∀ t ∈ Icc (0 : ℝ) 1, A ≤ g t) : A ≤ ∫ t, g t := by
  have hi : Integrable ((Icc (0 : ℝ) 1).indicator (fun _ => A)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hle : ∀ t, (Icc (0 : ℝ) 1).indicator (fun _ => A) t ≤ g t := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simpa [ht] using hl t ht
    · simpa [ht] using hn t
  have hb := integral_mono hi hg hle
  rw [integral_indicator measurableSet_Icc, setIntegral_const] at hb
  simpa using hb

theorem integral_difference_ge_of_cdf_gap
    {X : Type*} [MeasurableSpace X] {mu nu : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {f : X → ℝ}
    (hf : Measurable f) (hm : Integrable f mu) (hn : Integrable f nu)
    (hdom : ∀ t, nu.real {x | f x ≤ t} ≤ mu.real {x | f x ≤ t})
    {A : ℝ} (hA : 0 ≤ A)
    (hl : ∀ t ∈ Icc (0 : ℝ) 1,
      A ≤ mu.real {x | f x ≤ t} - nu.real {x | f x ≤ t}) :
    A ≤ (∫ x, f x ∂nu) - (∫ x, f x ∂mu) := by
  rw [integral_sub_eq_integral_cdf_gap hf hm hn]
  exact integral_ge_const_of_unit_interval (integrable_cdf_gap hf hm hn)
    (fun t => sub_nonneg.mpr (hdom t)) hA hl

variable {m : ℕ} [NeZero m]

theorem gaussianMaxMean_gap_eq_integral
    (R S : Matrix (Fin m) (Fin m) ℝ) :
    gaussianMaxMean S - gaussianMaxMean R =
      ∫ t, (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R).real
        {x | maxCoord x ≤ t} -
        (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).real
        {x | maxCoord x ≤ t} :=
  integral_sub_eq_integral_cdf_gap measurable_maxCoord
    (integrable_maxCoord_mvg R) (integrable_maxCoord_mvg S)

theorem gaussianMaxMean_gap_ge_of_cdf
    (R S : Matrix (Fin m) (Fin m) ℝ)
    (hdom : ∀ t,
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).real
        {x | maxCoord x ≤ t} ≤
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R).real
        {x | maxCoord x ≤ t})
    {A : ℝ} (hA : 0 ≤ A)
    (hl : ∀ t ∈ Icc (0 : ℝ) 1,
      A ≤ (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) R).real
        {x | maxCoord x ≤ t} -
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).real
        {x | maxCoord x ≤ t}) :
    A ≤ gaussianMaxMean S - gaussianMaxMean R :=
  integral_difference_ge_of_cdf_gap measurable_maxCoord
    (integrable_maxCoord_mvg R) (integrable_maxCoord_mvg S) hdom hA hl

#print axioms integral_difference_ge_of_cdf_gap
#print axioms gaussianMaxMean_gap_eq_integral
#print axioms gaussianMaxMean_gap_ge_of_cdf
end SimplexFull.GlobalTail
