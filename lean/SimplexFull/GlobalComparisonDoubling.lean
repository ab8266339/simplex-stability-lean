import SimplexFull.GlobalComparisonRotation
noncomputable section
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators
namespace SimplexFull.GlobalComparison.Rotation

/-- Actual Gaussian rotation and Fubini identity; covariance may be singular. -/
theorem doubling_identity {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i))) :
    (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R)^2 -
    (∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
       ∂multivariateGaussian (0 : Coord m) R) =
    ∫ u, ((∫ v, ∏ i, fixedAverageFactor (h i) (u i) (v i)
       ∂multivariateGaussian (0 : Coord m) R) -
       ∏ i, normalizedSelfConvolution (h i) (u i))
       ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let μ : Measure (Coord m) := multivariateGaussian (0 : Coord m) R
  let rot : Coord m × Coord m →L[ℝ] Coord m × Coord m :=
    ContinuousLinearMap.rotation (-(Real.pi / 4))
  let original : Coord m × Coord m → ℝ := fun p ↦
    coordProduct h p.1 * coordProduct h p.2
  let transformed : Coord m → ℝ := fun u ↦
    ∏ i, normalizedSelfConvolution (h i) (u i)
  have hcoord_int : Integrable (coordProduct h) μ := by
    exact integrable_coord_product h hh_meas hh_bounded
  have horiginal_int : Integrable original (μ.prod μ) := by
    exact hcoord_int.mul_prod hcoord_int
  have horiginal_meas : Measurable original := by
    exact ((measurable_coordProduct h hh_meas).comp measurable_fst).mul
      ((measurable_coordProduct h hh_meas).comp measurable_snd)
  have hrot_map : (μ.prod μ).map rot = μ.prod μ := by
    simpa only [μ, rot] using multivariateGaussian_prod_rotation R
  have hrot_pres : MeasurePreserving rot (μ.prod μ) (μ.prod μ) :=
    ⟨rot.measurable, hrot_map⟩
  have hsum_int : Integrable (sumDifferenceProduct h) (μ.prod μ) := by
    have hcomp := hrot_pres.integrable_comp_of_integrable horiginal_int
    have heq : sumDifferenceProduct h = original ∘ rot := by
      funext p
      simpa only [Function.comp_apply, original, rot] using
        sumDifferenceProduct_eq_rotated h p
    rw [heq]
    exact hcomp
  have htransformed_int : Integrable transformed μ := by
    exact integrable_coord_product
      (fun i ↦ normalizedSelfConvolution (h i))
      (fun i ↦ measurable_normalizedSelfConvolution (hh_meas i))
      (fun i ↦ isBounded_range_normalizedSelfConvolution
        (hh_nonneg i) (hh_bounded i))
  have hiterated_int :
      Integrable (fun u ↦ ∫ v, sumDifferenceProduct h (u, v) ∂μ) μ :=
    hsum_int.integral_prod_left
  have hrotate_integral :
      (∫ p, original p ∂μ.prod μ) =
        ∫ p, sumDifferenceProduct h p ∂μ.prod μ := by
    calc
      (∫ p, original p ∂μ.prod μ) =
          ∫ p, original p ∂Measure.map rot (μ.prod μ) := by rw [hrot_map]
      _ = ∫ p, original (rot p) ∂μ.prod μ :=
        integral_map_of_stronglyMeasurable rot.measurable
          horiginal_meas.stronglyMeasurable
      _ = ∫ p, sumDifferenceProduct h p ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with p
        exact (sumDifferenceProduct_eq_rotated h p).symm
  have hiterated :
      (∫ u, ∫ v, sumDifferenceProduct h (u,v) ∂μ ∂μ) =
      (∫ x, coordProduct h x ∂μ)^2 := by
    rw [← integral_prod (sumDifferenceProduct h) hsum_int, ← hrotate_integral]
    dsimp [original]
    rw [integral_prod_mul]
    ring
  change (∫ x, coordProduct h x ∂μ)^2 - (∫ u, transformed u ∂μ) =
    ∫ u, ((∫ v, sumDifferenceProduct h (u,v) ∂μ)-transformed u) ∂μ
  rw [integral_sub hiterated_int htransformed_int, hiterated]

/-- Integrating a pointwise quantitative rectangle deficit on a measurable box. -/
theorem doubling_lower_of_indicator {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (E : Set (Coord m)) (hE : MeasurableSet E) (C : ℝ)
    (hgap : ∀ u, E.indicator (fun _ => C) u ≤
      (∫ v, ∏ i, fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) R) -
      ∏ i, normalizedSelfConvolution (h i) (u i)) :
    (multivariateGaussian (0 : Coord m) R).real E * C ≤
      (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R)^2 -
      ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R := by
  classical
  let μ := multivariateGaussian (0 : Coord m) R
  have hi : Integrable (coordProduct h) μ := integrable_coord_product h hh_meas hh_bounded
  have hr : MeasurePreserving
      (ContinuousLinearMap.rotation (-(Real.pi/4)) : Coord m × Coord m →L[ℝ] Coord m × Coord m)
      (μ.prod μ) (μ.prod μ) :=
    ⟨ContinuousLinearMap.measurable _, multivariateGaussian_prod_rotation R⟩
  have hs : Integrable (sumDifferenceProduct h) (μ.prod μ) := by
    have ht := hr.integrable_comp_of_integrable (hi.mul_prod hi)
    convert ht using 1
    funext p
    exact sumDifferenceProduct_eq_rotated h p
  have hi2 : Integrable (fun u : Coord m => ∏ i, normalizedSelfConvolution (h i) (u i)) μ :=
    integrable_coord_product _ (fun i => measurable_normalizedSelfConvolution (hh_meas i))
      (fun i => isBounded_range_normalizedSelfConvolution (hh_nonneg i) (hh_bounded i))
  have hd := hs.integral_prod_left.sub hi2
  have he := (integrable_const C : Integrable (fun _ : Coord m => C) μ).indicator hE
  have hle := integral_mono he hd hgap
  rw [doubling_identity R h hh_meas hh_nonneg hh_bounded]
  simpa only [integral_indicator hE, integral_const, smul_eq_mul, Measure.real,
    μ, sumDifferenceProduct, Measure.restrict_apply_univ, Pi.sub_apply] using hle

#print axioms doubling_identity
#print axioms doubling_lower_of_indicator
end SimplexFull.GlobalComparison.Rotation
