import SimplexFull.GlobalComparisonDoubling
import SimplexFull.GlobalRectangleBound
import SimplexFull.GlobalComparisonProduct
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison
open Rotation

theorem weighted_rectangle_gap {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (weights radii : Fin m → ℝ)
    (g : Fin m → ℝ → ℝ)
    (hg : ∀ i x, g i x = weights i * (Icc (-radii i) (radii i)).indicator (1 : ℝ → ℝ) x) :
    (∫ x, ∏ i, g i (x i) ∂multivariateGaussian (0 : Coord m) R) -
      (∏ i, ∫ x, g i x ∂gaussianReal 0 1) =
    (∏ i, weights i) *
      ((multivariateGaussian (0 : Coord m) R (symmetricRectangle radii)).toReal -
        (∏ i, gaussianReal 0 1 (Icc (-radii i) (radii i))).toReal) := by
  classical
  have hleft : (∏ i, ∫ v, g i v ∂gaussianReal 0 1) =
      (∏ i, weights i) * ∏ i, (gaussianReal 0 1).real (Icc (-radii i) (radii i)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp_rw [hg i]
    rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
  have hright : (∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) R) =
      (∏ i, weights i) * (multivariateGaussian (0 : Coord m) R).real (symmetricRectangle radii) := by
    rw [← integral_indicator_one (measurableSet_symmetricRectangle radii), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hg, Finset.prod_mul_distrib]
    congr 1
    by_cases hv : v ∈ symmetricRectangle radii
    · rw [Set.indicator_of_mem hv]
      refine Finset.prod_eq_one fun i _ => ?_
      simp [Set.indicator_of_mem (hv i)]
    · rw [Set.indicator_of_notMem hv]
      simp only [symmetricRectangle, Set.mem_setOf_eq, not_forall] at hv
      obtain ⟨i, hi⟩ := hv
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Set.indicator_of_notMem hi])
  rw [hleft, hright, ENNReal.toReal_prod]
  simp only [Measure.real]
  ring

def normalizedTilt (a b M : ℝ) (x : ℝ) : ℝ := M⁻¹ * tiltedHalfLine a b x

theorem normalizedTilt_measurable (a b M : ℝ) : Measurable (normalizedTilt a b M) :=
  (measurable_tiltedHalfLine _ _).const_mul _
theorem normalizedTilt_nonneg {a b M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 ≤ normalizedTilt a b M x :=
  mul_nonneg (inv_pos.mpr hM).le (tiltedHalfLine_nonneg _ _ _)
theorem normalizedTilt_bounded {a b M : ℝ} (ha : 0 ≤ a) :
    Bornology.IsBounded (range (normalizedTilt a b M)) :=
  SimplexUniqueness.Deficit.isBounded_range_const_mul (isBounded_range_tiltedHalfLine ha) _

theorem normalizedTilt_factor (a b M u v : ℝ) :
    fixedAverageFactor (normalizedTilt a b M) u v =
      M⁻¹^2 * Real.exp (Real.sqrt 2*a*u) *
        (Icc (-(Real.sqrt 2*b-u)) (Real.sqrt 2*b-u)).indicator (1 : ℝ → ℝ) v :=
  SimplexUniqueness.Deficit.fixedAverageFactor_tilted a b M u v

theorem normalizedTilt_D_integral {a b M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) (u : ℝ) :
    normalizedSelfConvolution (normalizedTilt a b M) u =
      ∫ v, fixedAverageFactor (normalizedTilt a b M) u v ∂gaussianReal 0 1 :=
  (integral_fixedAverageFactor_eq_normalizedSelfConvolution
    (normalizedTilt_measurable _ _ _) (normalizedTilt_nonneg hM)
    (normalizedTilt_bounded ha) u).symm

theorem tilt_gap_formula {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (a b M : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hM : ∀ i, 0 < M i) (u : Coord m) :
    (∫ v, ∏ i, fixedAverageFactor (normalizedTilt (a i) (b i) (M i)) (u i) (v i)
      ∂multivariateGaussian (0 : Coord m) R) -
      (∏ i, normalizedSelfConvolution (normalizedTilt (a i) (b i) (M i)) (u i)) =
    (∏ i, (M i)⁻¹^2 * Real.exp (Real.sqrt 2*a i*u i)) *
      ((multivariateGaussian (0 : Coord m) R
        (symmetricRectangle (fun i => Real.sqrt 2*b i-u i))).toReal -
      (∏ i, gaussianReal 0 1 (Icc (-(Real.sqrt 2*b i-u i)) (Real.sqrt 2*b i-u i))).toReal) := by
  simp_rw [normalizedTilt_D_integral (ha _) (hM _)]
  exact weighted_rectangle_gap _ _ _ _ (fun i v => normalizedTilt_factor _ _ _ _ _)

theorem tilt_gap_nonneg {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsCorrelation R) (hne : R ≠ 1) (a b M : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hM : ∀ i, 0 < M i) (u : Coord m) :
    0 ≤ (∫ v, ∏ i, fixedAverageFactor (normalizedTilt (a i) (b i) (M i)) (u i) (v i)
      ∂multivariateGaussian (0 : Coord m) R) -
      (∏ i, normalizedSelfConvolution (normalizedTilt (a i) (b i) (M i)) (u i)) := by
  apply sub_nonneg.mpr
  simp_rw [normalizedTilt_D_integral (ha _) (hM _)]
  exact SimplexUniqueness.Deficit.indicator_product_ge R hR hne
    (fun i => (M i)⁻¹^2 * Real.exp (Real.sqrt 2*a i*u i))
    (fun i => Real.sqrt 2*b i-u i)
    (fun i => mul_pos (sq_pos_of_pos (inv_pos.mpr (hM i))) (Real.exp_pos _))
    _ (fun i v => normalizedTilt_factor _ _ _ _ _)

#print axioms tilt_gap_formula
#print axioms tilt_gap_nonneg
end SimplexFull.GlobalComparison
