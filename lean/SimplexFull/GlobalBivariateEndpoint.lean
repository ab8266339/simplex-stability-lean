import SimplexFull.GlobalBivariateProbability
import SimplexFull.GeometryBase
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Real WeakSimplex
open scoped ENNReal
namespace SimplexFull.GlobalBivariate

theorem pair_endpoint_mass {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (r : Fin 2 → ℝ) (hr : ∀ i, 0 ≤ r i) (hcorr : |R 0 1| = 1) :
    (multivariateGaussian (0 : Coord 2) R (symmetricRectangle r)).toReal =
      (gaussianReal 0 1 (Icc (-(min (r 0) (r 1))) (min (r 0) (r 1)))).toReal := by
  have hs : (R 0 1)^2 = 1 := by
    nlinarith [sq_abs (R 0 1)]
  rw [GlobalRectangle.pair_rectangle_eq_conditional hR hdiag]
  simp_rw [hs, sub_self, Real.toNNReal_zero, gaussianReal_zero_var]
  have he : (fun t : ℝ => Measure.dirac (0 : ℝ)
      {z | z + t * R 0 1 ∈ Icc (-r 0) (r 0)}) =
      (Icc (-r 0) (r 0)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    have hm : t * R 0 1 ∈ Icc (-r 0) (r 0) ↔ t ∈ Icc (-r 0) (r 0) := by
      simp only [mem_Icc, ← abs_le, abs_mul, hcorr, mul_one]
    have hms : MeasurableSet {z : ℝ | z + t * R 0 1 ∈ Icc (-r 0) (r 0)} := (measurable_id.add_const (t * R 0 1)) measurableSet_Icc
    rw [Measure.dirac_apply' _ hms]
    by_cases ht : t ∈ Icc (-r 0) (r 0)
    · have hz : (0:ℝ) ∈ {z | z+t*R 0 1 ∈ Icc (-r 0) (r 0)} := by
        simpa only [mem_setOf_eq, zero_add] using hm.mpr ht
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem ht]
      rfl
    · have hz : (0:ℝ) ∉ {z | z+t*R 0 1 ∈ Icc (-r 0) (r 0)} := by
        simpa only [mem_setOf_eq, zero_add] using mt hm.mp ht
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem ht]
  rw [he, lintegral_indicator measurableSet_Icc, lintegral_one]
  have hset : Icc (-r 0) (r 0) ∩ Icc (-r 1) (r 1) =
      Icc (-(min (r 0) (r 1))) (min (r 0) (r 1)) := by
    ext t
    simp only [mem_inter_iff, mem_Icc]
    by_cases h : r 0 ≤ r 1
    · rw [min_eq_left h]
      constructor
      · exact fun hh => hh.1
      · intro hh
        exact ⟨hh, ⟨by linarith [hh.1], by linarith [hh.2]⟩⟩
    · rw [min_eq_right (le_of_not_ge h)]
      constructor
      · exact fun hh => hh.2
      · intro hh
        exact ⟨⟨by linarith [hh.1], by linarith [hh.2]⟩, hh⟩
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.restrict_apply measurableSet_Icc, hset]

theorem pair_rectangle_le_slab {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (r : Fin 2 → ℝ) (i : Fin 2) :
    multivariateGaussian (0 : Coord 2) R (symmetricRectangle r) ≤
      gaussianReal 0 1 (Icc (-r i) (r i)) := by
  have hm : MeasurePreserving (fun x : Coord 2 => x i)
      (multivariateGaussian 0 R) (gaussianReal 0 1) := by
    simpa [hdiag i] using measurePreserving_eval_multivariateGaussian
      (μ := (0 : Coord 2)) hR (i := i)
  calc
    _ ≤ multivariateGaussian (0 : Coord 2) R
        ((fun x : Coord 2 => x i) ⁻¹' Icc (-r i) (r i)) := by
      apply measure_mono
      intro x hx
      exact hx i
    _ = _ := by rw [← hm.map_eq, Measure.map_apply hm.measurable measurableSet_Icc]

theorem pair_rectangle_le_min_slab {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin 2 → ℝ) :
    multivariateGaussian (0 : Coord 2) R (symmetricRectangle r) ≤
      gaussianReal 0 1 (Icc (-(min (r 0) (r 1))) (min (r 0) (r 1))) := by
  by_cases h : r 0 ≤ r 1
  · simpa only [min_eq_left h] using pair_rectangle_le_slab hR hdiag r 0
  · simpa only [min_eq_right (le_of_not_ge h)] using pair_rectangle_le_slab hR hdiag r 1

def halfCovariance : Matrix (Fin 2) (Fin 2) ℝ :=
  (1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    (1/2 : ℝ) • Geometry.onesMatrix 2

theorem halfCovariance_psd : halfCovariance.PosSemidef := by
  have ho : (Geometry.onesMatrix 2).PosSemidef := by
    convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 => (1 : ℝ)) using 1 <;>
      ext i j <;> simp [Geometry.onesMatrix, Matrix.vecMulVec]
  exact (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1/2)).add
    (ho.smul (by norm_num : (0 : ℝ) ≤ 1/2))

theorem halfCovariance_diag (i : Fin 2) : halfCovariance i i = 1 := by
  norm_num [halfCovariance, Geometry.onesMatrix, Matrix.one_apply]

theorem rectangleIntegral_half_le_min_slab (r : Fin 2 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    rectangleIntegral (1/2) (r 0) (r 1) ≤
      (gaussianReal 0 1 (Icc (-(min (r 0) (r 1))) (min (r 0) (r 1)))).toReal := by
  have hcorr : |halfCovariance 0 1| < 1 := by
    norm_num [halfCovariance, Geometry.onesMatrix, Matrix.one_apply]
  have he := pair_probability_eq_rectangleIntegral halfCovariance_psd halfCovariance_diag r hr hcorr
  have hc : halfCovariance 0 1 = 1/2 := by
    norm_num [halfCovariance, Geometry.onesMatrix, Matrix.one_apply]
  rw [hc] at he
  rw [← he]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (pair_rectangle_le_min_slab halfCovariance_psd halfCovariance_diag r)

#print axioms pair_endpoint_mass
#print axioms rectangleIntegral_half_le_min_slab
end SimplexFull.GlobalBivariate
