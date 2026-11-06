import SimplexUniquenessLean.StrictRectangle
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Strict product inequality for truncated exponentials

Lemma 2 of the paper (Section V-B). For a correlation matrix `S ≠ I` and
centered truncated exponential factors `f_i(z) = e^{a_i z} 1_{(-∞, b_i]}(z)`
with `a_i > 0`, `b_i > 0`, the Gaussian product expectation strictly exceeds
the product of the one-dimensional masses.

Proof route. The non-strict rotation argument of Mulgund (`SumDifference.lean`) shows
`(∫ ∏ h_i dμ_S)² ≥ ∫ ∏ D h_i dμ_S` for the normalized self-convolution `D`; here the same
argument is rerun with the pointwise comparison kept, and strictness is read off on the
positive-mass set where all the fixed-average factors are indicators of symmetric intervals
of positive radius (Lemma 1, `symmetricRectangle_gt_iid`).
-/

noncomputable section

namespace SimplexUniqueness

open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators

namespace Deficit

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/SumDifference.lean, MIT
private def coordProduct {m : ℕ} (h : Fin m → ℝ → ℝ) (x : Coord m) : ℝ :=
  ∏ i, h i (x i)

private def fixedAverageFactor
    (h : ℝ → ℝ) (u v : ℝ) : ℝ :=
  h ((u + v) / Real.sqrt 2) * h ((u - v) / Real.sqrt 2)

private theorem measurable_fixedAverageFactor
    {h : ℝ → ℝ} (hh : Measurable h) (u : ℝ) :
    Measurable (fixedAverageFactor h u) := by
  exact (hh.comp ((measurable_const.add measurable_id).div_const _)).mul
    (hh.comp ((measurable_const.sub measurable_id).div_const _))

private theorem fixedAverageFactor_nonneg
    {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (u v : ℝ) :
    0 ≤ fixedAverageFactor h u v :=
  mul_nonneg (hh _) (hh _)

private theorem fixedAverageFactor_even
    (h : ℝ → ℝ) (u : ℝ) : Function.Even (fixedAverageFactor h u) := by
  intro v
  have hplus : (u + -v) / Real.sqrt 2 = (u - v) / Real.sqrt 2 := by ring
  have hminus : (u - -v) / Real.sqrt 2 = (u + v) / Real.sqrt 2 := by ring
  simp only [fixedAverageFactor, hplus, hminus, mul_comm]

private theorem isLogConcave_comp_add_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u + v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u + x) / Real.sqrt 2) ((u + y) / Real.sqrt 2)
  have harg : t * ((u + x) / Real.sqrt 2) +
      (1 - t) * ((u + y) / Real.sqrt 2) =
        (u + (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

private theorem isLogConcave_comp_sub_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u - v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u - x) / Real.sqrt 2) ((u - y) / Real.sqrt 2)
  have harg : t * ((u - x) / Real.sqrt 2) +
      (1 - t) * ((u - y) / Real.sqrt 2) =
        (u - (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

private theorem isLogConcave_fixedAverageFactor
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) (u : ℝ) :
    IsLogConcave (fun v ↦ ENNReal.ofReal (fixedAverageFactor h u v)) := by
  have hplus := isLogConcave_comp_add_const_div_sqrtTwo hh_lc u
  have hminus := isLogConcave_comp_sub_const_div_sqrtTwo hh_lc u
  convert hplus.mul hminus using 1
  funext v
  exact ENNReal.ofReal_mul (hh_nonneg _)

private theorem exists_norm_bound_of_isBounded_range
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

private theorem isBounded_range_fixedAverageFactor
    {h : ℝ → ℝ} (hh : Bornology.IsBounded (Set.range h)) (u : ℝ) :
    Bornology.IsBounded (Set.range (fixedAverageFactor h u)) := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range hh
  apply (Metric.isBounded_closedBall :
    Bornology.IsBounded (Metric.closedBall (0 : ℝ) (C ^ 2))).subset
  rintro z ⟨v, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [fixedAverageFactor, norm_mul, pow_two]
  have hC_nonneg : 0 ≤ C := (norm_nonneg (h 0)).trans (hC 0)
  exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC_nonneg

private theorem integrable_of_measurable_isBounded_range
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf_meas : Measurable f) (hf_bounded : Bornology.IsBounded (Set.range f)) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_isBounded_range hf_bounded
  let x₀ : X := Classical.choice inferInstance
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f x₀)).trans (hC x₀)
  refine Integrable.mono' (integrable_const C) hf_meas.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [abs_of_nonneg hC_nonneg] using hC x

private theorem integral_fixedAverageFactor_eq_normalizedSelfConvolution
    {h : ℝ → ℝ} (hh_meas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_bounded : Bornology.IsBounded (Set.range h)) (u : ℝ) :
    (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) =
      normalizedSelfConvolution h u := by
  have hfixed_meas := measurable_fixedAverageFactor hh_meas u
  have hfixed_nonneg : ∀ v, 0 ≤ fixedAverageFactor h u v :=
    fixedAverageFactor_nonneg hh_nonneg u
  have hfixed_int : Integrable (fixedAverageFactor h u) (gaussianReal 0 1) :=
    integrable_of_measurable_isBounded_range hfixed_meas
      (isBounded_range_fixedAverageFactor hh_bounded u)
  rw [normalizedSelfConvolution]
  change (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) =
    (∫⁻ v, ENNReal.ofReal (h ((u + v) / Real.sqrt 2)) *
      ENNReal.ofReal (h ((u - v) / Real.sqrt 2)) ∂gaussianReal 0 1).toReal
  have hlintegral :
      (∫⁻ v, ENNReal.ofReal (h ((u + v) / Real.sqrt 2)) *
          ENNReal.ofReal (h ((u - v) / Real.sqrt 2)) ∂gaussianReal 0 1) =
        ENNReal.ofReal (∫ v, fixedAverageFactor h u v ∂gaussianReal 0 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfixed_int
      (Filter.Eventually.of_forall hfixed_nonneg)]
    apply lintegral_congr
    intro v
    exact (ENNReal.ofReal_mul (hh_nonneg _)).symm
  rw [hlintegral, ENNReal.toReal_ofReal (integral_nonneg hfixed_nonneg)]

private theorem integrable_coord_product
    {m : ℕ} {μ : Measure (Coord m)} [IsFiniteMeasure μ]
    (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i))) :
    Integrable (fun x : Coord m ↦ ∏ i, h i (x i)) μ := by
  classical
  choose C hC using fun i ↦ exists_norm_bound_of_isBounded_range (hh_bounded i)
  have hcoord_meas (i : Fin m) : Measurable (fun x : Coord m ↦ h i (x i)) :=
    (hh_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable
  have hcoord_bound (i : Fin m) : ∀ x : Coord m, ‖h i (x i)‖ ≤ C i :=
    fun x ↦ hC i (x i)
  have hproduct_int_finset (s : Finset (Fin m)) :
      Integrable (fun x : Coord m ↦ ∏ i ∈ s, h i (x i)) μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
        have hmul := hs.bdd_mul (hcoord_meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall (hcoord_bound i))
        simpa [Finset.prod_insert hi] using hmul
  simpa using hproduct_int_finset Finset.univ

private theorem measurable_coordProduct
    {m : ℕ} (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) :
    Measurable (coordProduct h) := by
  classical
  exact Finset.measurable_prod Finset.univ fun i _ ↦
    (hh_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

private theorem rotation_neg_pi_div_four_apply {m : ℕ} (p : Coord m × Coord m) :
    ContinuousLinearMap.rotation (-(Real.pi / 4)) p =
      ((Real.sqrt 2)⁻¹ • (p.1 - p.2), (Real.sqrt 2)⁻¹ • (p.1 + p.2)) := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hcoef : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    field_simp [ne_of_gt hsqrt_pos]
    nlinarith
  simp only [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.cos_pi_div_four,
    Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg, hcoef]
  apply Prod.ext
  · module
  · module

private theorem multivariateGaussian_prod_rotation {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) :
    ((multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R)).map
      (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
      (multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R) := by
  apply IsGaussian.map_rotation_eq_self
  simp

private def sumDifferenceProduct {m : ℕ}
    (h : Fin m → ℝ → ℝ) (p : Coord m × Coord m) : ℝ :=
  ∏ i, fixedAverageFactor (h i) (p.1 i) (p.2 i)

private theorem sumDifferenceProduct_eq_rotated {m : ℕ}
    (h : Fin m → ℝ → ℝ) (p : Coord m × Coord m) :
    sumDifferenceProduct h p =
      coordProduct h (ContinuousLinearMap.rotation (-(Real.pi / 4)) p).1 *
        coordProduct h (ContinuousLinearMap.rotation (-(Real.pi / 4)) p).2 := by
  classical
  rw [rotation_neg_pi_div_four_apply]
  simp only [sumDifferenceProduct, fixedAverageFactor, coordProduct, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hsub : (Real.sqrt 2)⁻¹ * (p.1 i - p.2 i) =
      (p.1 i - p.2 i) / Real.sqrt 2 := by
    rw [div_eq_mul_inv, mul_comm]
  have hadd : (Real.sqrt 2)⁻¹ * (p.1 i + p.2 i) =
      (p.1 i + p.2 i) / Real.sqrt 2 := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hsub, hadd, mul_comm]

private theorem fixedAverage_pointwise_deficit
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x))) (u : Coord m) :
    (∏ i, normalizedSelfConvolution (h i) (u i)) ≤
      ∫ v, sumDifferenceProduct h (u, v)
        ∂multivariateGaussian (0 : Coord m) R := by
  let g : Fin m → ℝ → ℝ := fun i ↦ fixedAverageFactor (h i) (u i)
  have hmain := even_logConcave_product_of_posDef R hR hdiag g
    (fun i ↦ measurable_fixedAverageFactor (hh_meas i) (u i))
    (fun i ↦ fixedAverageFactor_nonneg (hh_nonneg i) (u i))
    (fun i ↦ isBounded_range_fixedAverageFactor (hh_bounded i) (u i))
    (fun i ↦ fixedAverageFactor_even (h i) (u i))
    (fun i ↦ isLogConcave_fixedAverageFactor (hh_nonneg i) (hh_lc i) (u i))
  calc
    (∏ i, normalizedSelfConvolution (h i) (u i)) =
        ∏ i, ∫ v, g i v ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (integral_fixedAverageFactor_eq_normalizedSelfConvolution
        (hh_meas i) (hh_nonneg i) (hh_bounded i) (u i)).symm
    _ ≤ ∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) R := hmain
    _ = ∫ v, sumDifferenceProduct h (u, v)
          ∂multivariateGaussian (0 : Coord m) R := by rfl


-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/SumDifference.lean, MIT
/-- Strict version of the normalized self-convolution deficit inequality for an arbitrary
covariance matrix `R`: if the pointwise comparison holds everywhere and is strict on a set of
positive Gaussian mass, the global one is strict. No definiteness of `R` is needed here. -/
theorem product_deficit_strict_of_le
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (E : Set (Coord m)) (hE : 0 < multivariateGaussian (0 : Coord m) R E)
    (hle : ∀ u : Coord m, (∏ i, normalizedSelfConvolution (h i) (u i)) ≤
      ∫ v, ∏ i, fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) R)
    (hstrict : ∀ u ∈ E, (∏ i, normalizedSelfConvolution (h i) (u i)) <
      ∫ v, ∏ i, fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) R) :
    (∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R) <
      (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) ^ 2 := by
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
  have hpointwise (u : Coord m) :
      transformed u ≤ ∫ v, sumDifferenceProduct h (u, v) ∂μ := by
    simpa only [transformed, μ, sumDifferenceProduct] using hle u
  have hdelta_int : Integrable
      (fun u ↦ (∫ v, sumDifferenceProduct h (u, v) ∂μ) - transformed u) μ :=
    hiterated_int.sub htransformed_int
  have hdelta_nonneg :
      0 ≤ fun u ↦ (∫ v, sumDifferenceProduct h (u, v) ∂μ) - transformed u :=
    fun u ↦ sub_nonneg.2 (hpointwise u)
  have hdelta_pos :
      0 < ∫ u, ((∫ v, sumDifferenceProduct h (u, v) ∂μ) - transformed u) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hdelta_nonneg hdelta_int]
    refine lt_of_lt_of_le hE (measure_mono ?_)
    intro u hu
    rw [Function.mem_support]
    exact (sub_pos.2 (hstrict u hu)).ne'
  have hmono :
      (∫ u, transformed u ∂μ) <
        ∫ u, ∫ v, sumDifferenceProduct h (u, v) ∂μ ∂μ := by
    rw [integral_sub hiterated_int htransformed_int] at hdelta_pos
    linarith
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
  calc
    (∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R) = ∫ u, transformed u ∂μ := rfl
    _ < ∫ u, ∫ v, sumDifferenceProduct h (u, v) ∂μ ∂μ := hmono
    _ = ∫ p, sumDifferenceProduct h p ∂μ.prod μ :=
      (integral_prod (sumDifferenceProduct h) hsum_int).symm
    _ = ∫ p, original p ∂μ.prod μ := hrotate_integral.symm
    _ = (∫ x, coordProduct h x ∂μ) ^ 2 := by
      rw [integral_prod_mul]
      ring
    _ = (∫ x, ∏ i, h i (x i)
        ∂multivariateGaussian (0 : Coord m) R) ^ 2 := rfl

/-- Strict version of the normalized self-convolution deficit inequality: if the pointwise
comparison is strict on a set of positive Gaussian mass, the global one is strict. -/
theorem product_deficit_strict
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef)
    (hdiag : ∀ i, R i i = 1) (h : Fin m → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) (hh_nonneg : ∀ i x, 0 ≤ h i x)
    (hh_bounded : ∀ i, Bornology.IsBounded (Set.range (h i)))
    (hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x)))
    (E : Set (Coord m)) (hE : 0 < multivariateGaussian (0 : Coord m) R E)
    (hstrict : ∀ u ∈ E, (∏ i, normalizedSelfConvolution (h i) (u i)) <
      ∫ v, ∏ i, fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) R) :
    (∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R) <
      (∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) R) ^ 2 :=
  product_deficit_strict_of_le R h hh_meas hh_nonneg hh_bounded E hE
    (fun u ↦ fixedAverage_pointwise_deficit R hR hdiag h hh_meas hh_nonneg hh_bounded hh_lc u)
    hstrict

/-- If every factor is a positive constant times the indicator of a symmetric interval of
positive radius, the correlated product strictly exceeds the product of masses. -/
theorem indicator_product_gt
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S) (hne : S ≠ 1)
    (c ρ : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hρ : ∀ i, 0 < ρ i) (g : Fin m → ℝ → ℝ)
    (hg : ∀ i v, g i v = c i * (Icc (-ρ i) (ρ i)).indicator (1 : ℝ → ℝ) v) :
    (∏ i, ∫ v, g i v ∂gaussianReal 0 1) <
      ∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) S := by
  classical
  have hleft : (∏ i, ∫ v, g i v ∂gaussianReal 0 1) =
      (∏ i, c i) * ∏ i, (gaussianReal 0 1).real (Icc (-ρ i) (ρ i)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp_rw [hg i]
    rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
  have hright : (∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) S) =
      (∏ i, c i) * (multivariateGaussian (0 : Coord m) S).real (symmetricRectangle ρ) := by
    rw [← integral_indicator_one (measurableSet_symmetricRectangle ρ), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only [hg, Finset.prod_mul_distrib]
    congr 1
    by_cases hv : v ∈ symmetricRectangle ρ
    · rw [Set.indicator_of_mem hv]
      refine Finset.prod_eq_one fun i _ ↦ ?_
      simp [Set.indicator_of_mem (hv i)]
    · rw [Set.indicator_of_notMem hv]
      simp only [symmetricRectangle, Set.mem_setOf_eq, not_forall] at hv
      obtain ⟨i, hi⟩ := hv
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Set.indicator_of_notMem hi])
  rw [hleft, hright]
  refine mul_lt_mul_of_pos_left ?_ (Finset.prod_pos fun i _ ↦ hc i)
  have hlt := symmetricRectangle_gt_iid S hS hne ρ hρ
  have hfin : multivariateGaussian (0 : Coord m) S (symmetricRectangle ρ) ≠ ∞ :=
    measure_ne_top _ _
  have := (ENNReal.toReal_lt_toReal (ne_top_of_lt hlt) hfin).2 hlt
  simpa [Measure.real, ENNReal.toReal_prod] using this

/-- Non-strict form of `indicator_product_gt`, valid for arbitrary real radii. -/
theorem indicator_product_ge
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S) (hne : S ≠ 1)
    (c ρ : Fin m → ℝ) (hc : ∀ i, 0 < c i) (g : Fin m → ℝ → ℝ)
    (hg : ∀ i v, g i v = c i * (Icc (-ρ i) (ρ i)).indicator (1 : ℝ → ℝ) v) :
    (∏ i, ∫ v, g i v ∂gaussianReal 0 1) ≤
      ∫ v, ∏ i, g i (v i) ∂multivariateGaussian (0 : Coord m) S := by
  classical
  by_cases hpos : ∀ i, 0 < ρ i
  · exact (indicator_product_gt S hS hne c ρ hc hpos g hg).le
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
    have h0 : ∫ v, g i v ∂gaussianReal 0 1 = 0 := by
      simp_rw [hg i]
      rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
      have hsub : Icc (-ρ i) (ρ i) ⊆ {0} := by
        intro x hx
        have h1 := hx.1
        have h2 := hx.2
        simp only [Set.mem_singleton_iff]
        linarith
      have hnull : (gaussianReal 0 1) (Icc (-ρ i) (ρ i)) = 0 :=
        measure_mono_null hsub (measure_singleton 0)
      rw [measureReal_def, hnull, ENNReal.toReal_zero, mul_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    refine integral_nonneg fun v ↦ Finset.prod_nonneg fun j _ ↦ ?_
    rw [hg j]
    exact mul_nonneg (hc j).le (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

/-- The fixed-average factor of a normalized truncated exponential is a constant times the
indicator of a symmetric interval. -/
theorem fixedAverageFactor_tilted (a b M u v : ℝ) :
    fixedAverageFactor (fun x ↦ M⁻¹ * tiltedHalfLine a b x) u v =
      (M⁻¹ ^ 2 * Real.exp (Real.sqrt 2 * a * u)) *
        (Icc (-(Real.sqrt 2 * b - u)) (Real.sqrt 2 * b - u)).indicator (1 : ℝ → ℝ) v := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e1 : (u + v) / Real.sqrt 2 ≤ b ↔ v ≤ Real.sqrt 2 * b - u := by
    rw [div_le_iff₀ hs]
    constructor <;> intro h <;> linarith [mul_comm b (Real.sqrt 2)]
  have e2 : (u - v) / Real.sqrt 2 ≤ b ↔ -(Real.sqrt 2 * b - u) ≤ v := by
    rw [div_le_iff₀ hs]
    constructor <;> intro h <;> linarith [mul_comm b (Real.sqrt 2)]
  have hexp : a * ((u + v) / Real.sqrt 2) + a * ((u - v) / Real.sqrt 2) =
      Real.sqrt 2 * a * u := by
    have h : (u + v) / Real.sqrt 2 + (u - v) / Real.sqrt 2 = Real.sqrt 2 * u := by
      rw [← add_div, div_eq_iff hs.ne']
      rw [mul_right_comm, hs2]
      ring
    rw [← mul_add, h]
    ring
  unfold fixedAverageFactor tiltedHalfLine
  beta_reduce
  by_cases h1 : v ≤ Real.sqrt 2 * b - u <;> by_cases h2 : -(Real.sqrt 2 * b - u) ≤ v
  · have hm : v ∈ Icc (-(Real.sqrt 2 * b - u)) (Real.sqrt 2 * b - u) := ⟨h2, h1⟩
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show (u + v) / Real.sqrt 2 ∈ Iic b from
      e1.2 h1), Set.indicator_of_mem (show (u - v) / Real.sqrt 2 ∈ Iic b from e2.2 h2)]
    simp only [Pi.one_apply]
    calc M⁻¹ * Real.exp (a * ((u + v) / Real.sqrt 2)) *
          (M⁻¹ * Real.exp (a * ((u - v) / Real.sqrt 2)))
        = M⁻¹ ^ 2 * Real.exp (a * ((u + v) / Real.sqrt 2) + a * ((u - v) / Real.sqrt 2)) := by
          rw [Real.exp_add]; ring
      _ = _ := by rw [hexp]; ring
  all_goals
    have hm : v ∉ Icc (-(Real.sqrt 2 * b - u)) (Real.sqrt 2 * b - u) := by
      intro hv; first | exact h1 hv.2 | exact h2 hv.1
    rw [Set.indicator_of_notMem hm]
  · have : (u - v) / Real.sqrt 2 ∉ Iic b := fun h ↦ h2 (e2.1 h)
    rw [Set.indicator_of_notMem this]; simp
  · have : (u + v) / Real.sqrt 2 ∉ Iic b := fun h ↦ h1 (e1.1 h)
    rw [Set.indicator_of_notMem this]; simp
  · have : (u + v) / Real.sqrt 2 ∉ Iic b := fun h ↦ h1 (e1.1 h)
    rw [Set.indicator_of_notMem this]; simp

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/CenteredProduct.lean, MIT
theorem isBounded_range_const_mul
    {f : ℝ → ℝ} (hf : Bornology.IsBounded (Set.range f)) (a : ℝ) :
    Bornology.IsBounded (Set.range (fun x ↦ a * f x)) := by
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖a‖ * C, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC _ (Set.mem_range_self x)) (norm_nonneg a)

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/CenteredProduct.lean, MIT
theorem isLogConcave_const_mul_of_nonneg
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IsLogConcave (fun x ↦ ENNReal.ofReal (f x))) :
    IsLogConcave (fun x ↦ ENNReal.ofReal (a * f x)) := by
  have h := (isLogConcave_const (E := ℝ) (ENNReal.ofReal a)).mul hf
  convert h using 1
  funext x
  exact ENNReal.ofReal_mul ha

/-- The Gaussian mass of a symmetric interval, as a function of the (possibly negative) radius. -/
theorem measureReal_Icc_neg_gaussian (ρ : ℝ) :
    (gaussianReal 0 1).real (Icc (-ρ) ρ) =
      normalCDF (max ρ 0) - normalCDF (-max ρ 0) := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hIic : ∀ x, (gaussianReal 0 1).real (Iic x) = normalCDF x := fun x ↦ by
    rw [measureReal_def, ← normalCDF_eq_measure_Iic, ENNReal.toReal_ofReal (normalCDF_pos x).le]
  by_cases hρ : ρ < 0
  · rw [Set.Icc_eq_empty (by linarith), max_eq_right hρ.le]
    simp
  · push Not at hρ
    rw [max_eq_left hρ]
    have hset : Icc (-ρ) ρ = Iic ρ \ Iio (-ρ) := by
      ext x
      simp only [Set.mem_Icc, Set.mem_sdiff, Set.mem_Iic, Set.mem_Iio, not_lt]
      tauto
    have hsub : Iio (-ρ) ⊆ Iic ρ := fun x hx ↦ by
      simp only [Set.mem_Iio, Set.mem_Iic] at hx ⊢
      linarith
    rw [hset, measureReal_sdiff hsub measurableSet_Iio (measure_ne_top _ _),
      hIic, measureReal_congr Iio_ae_eq_Iic, hIic]

theorem continuous_normalCDF : Continuous normalCDF :=
  continuous_iff_continuousAt.2 fun x ↦ (hasDerivAt_normalCDF x).continuousAt

/-- The normalized self-convolution of a normalized truncated exponential is continuous. -/
theorem continuous_normalizedSelfConvolution_tilted (a b M : ℝ) (ha : 0 ≤ a) (hM : 0 < M) :
    Continuous (normalizedSelfConvolution (fun x ↦ M⁻¹ * tiltedHalfLine a b x)) := by
  have hmeas : Measurable (fun x ↦ M⁻¹ * tiltedHalfLine a b x) :=
    (measurable_tiltedHalfLine _ _).const_mul _
  have hnn : ∀ x, 0 ≤ M⁻¹ * tiltedHalfLine a b x := fun x ↦
    mul_nonneg (inv_pos.2 hM).le (tiltedHalfLine_nonneg _ _ _)
  have hbdd : Bornology.IsBounded (Set.range (fun x ↦ M⁻¹ * tiltedHalfLine a b x)) :=
    isBounded_range_const_mul (isBounded_range_tiltedHalfLine ha) _
  have heq : normalizedSelfConvolution (fun x ↦ M⁻¹ * tiltedHalfLine a b x) =
      fun u ↦ (M⁻¹ ^ 2 * Real.exp (Real.sqrt 2 * a * u)) *
        (normalCDF (max (Real.sqrt 2 * b - u) 0) - normalCDF (-max (Real.sqrt 2 * b - u) 0)) := by
    funext u
    rw [← integral_fixedAverageFactor_eq_normalizedSelfConvolution hmeas hnn hbdd]
    simp_rw [fixedAverageFactor_tilted]
    rw [integral_const_mul, integral_indicator_one measurableSet_Icc,
      measureReal_Icc_neg_gaussian]
  rw [heq]
  have hc := continuous_normalCDF
  fun_prop

end Deficit

namespace Regularize

open Filter
open scoped InnerProductSpace Topology

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Orthant/Singular.lean, MIT
private def gaussianRegularizationMap {m : ℕ} (ε : ℝ) :
    Coord m × Coord m → Coord m :=
  fun p ↦ Real.sqrt (1 - ε) • p.1 + Real.sqrt ε • p.2

private def weightedSumCLM {m : ℕ} (a b : ℝ) :
    Coord m × Coord m →L[ℝ] Coord m :=
  a • ContinuousLinearMap.fst ℝ (Coord m) (Coord m) +
    b • ContinuousLinearMap.snd ℝ (Coord m) (Coord m)

@[simp]
private theorem weightedSumCLM_apply {m : ℕ} (a b : ℝ) (p : Coord m × Coord m) :
    weightedSumCLM a b p = a • p.1 + b • p.2 := by
  rfl

private theorem covariance_weightedCoords
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (a b : ℝ) (i j : Fin m) :
    cov[fun p : Coord m × Coord m ↦ a * p.1 i + b * p.2 i,
        fun p : Coord m × Coord m ↦ a * p.1 j + b * p.2 j;
        (multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))] =
      a ^ 2 * R i j + b ^ 2 * if i = j then 1 else 0 := by
  let μ := multivariateGaussian (0 : Coord m) R
  let ν := stdGaussian (Coord m)
  have hRi : MemLp (fun x : Coord m ↦ x i) 2 μ := by
    simpa [μ] using IsGaussian.memLp_dual μ (EuclideanSpace.proj i) 2 (by simp)
  have hRj : MemLp (fun x : Coord m ↦ x j) 2 μ := by
    simpa [μ] using IsGaussian.memLp_dual μ (EuclideanSpace.proj j) 2 (by simp)
  have hZi : MemLp (fun x : Coord m ↦ x i) 2 ν := by
    simpa [ν] using IsGaussian.memLp_dual ν (EuclideanSpace.proj i) 2 (by simp)
  have hZj : MemLp (fun x : Coord m ↦ x j) 2 ν := by
    simpa [ν] using IsGaussian.memLp_dual ν (EuclideanSpace.proj j) 2 (by simp)
  have hRia : MemLp (fun p : Coord m × Coord m ↦ a * p.1 i) 2 (μ.prod ν) :=
    (hRi.comp_fst ν).const_mul a
  have hRja : MemLp (fun p : Coord m × Coord m ↦ a * p.1 j) 2 (μ.prod ν) :=
    (hRj.comp_fst ν).const_mul a
  have hZib : MemLp (fun p : Coord m × Coord m ↦ b * p.2 i) 2 (μ.prod ν) :=
    (hZi.comp_snd μ).const_mul b
  have hZjb : MemLp (fun p : Coord m × Coord m ↦ b * p.2 j) 2 (μ.prod ν) :=
    (hZj.comp_snd μ).const_mul b
  have hRR :
      cov[fun p : Coord m × Coord m ↦ p.1 i, fun p ↦ p.1 j; μ.prod ν] =
        cov[fun x : Coord m ↦ x i, fun x ↦ x j; μ] := by
    exact (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp
      (f := fun x : Coord m ↦ x i) (g := fun x : Coord m ↦ x j)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hZZ :
      cov[fun p : Coord m × Coord m ↦ p.2 i, fun p ↦ p.2 j; μ.prod ν] =
        cov[fun x : Coord m ↦ x i, fun x ↦ x j; ν] := by
    exact (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp
      (f := fun x : Coord m ↦ x i) (g := fun x : Coord m ↦ x j)
      (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  have hRZ :
      cov[fun p : Coord m × Coord m ↦ p.1 i, fun p ↦ p.2 j; μ.prod ν] = 0 :=
    covariance_fst_snd_prod hRi hZj
  have hZR :
      cov[fun p : Coord m × Coord m ↦ p.2 i, fun p ↦ p.1 j; μ.prod ν] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hRj hZi
  have hcovR : cov[fun x : Coord m ↦ x i, fun x ↦ x j; μ] = R i j := by
    exact covariance_eval_multivariateGaussian hR i j
  have hcovOne :
      cov[fun x : Coord m ↦ x i, fun x ↦ x j; ν] =
        if i = j then 1 else 0 := by
    change cov[fun x : Coord m ↦ x i, fun x ↦ x j; stdGaussian (Coord m)] = _
    rw [← multivariateGaussian_zero_one]
    rw [covariance_eval_multivariateGaussian Matrix.PosSemidef.one]
    exact Matrix.one_apply
  change cov[(fun p : Coord m × Coord m ↦ a * p.1 i) +
        (fun p ↦ b * p.2 i),
      (fun p ↦ a * p.1 j) + (fun p ↦ b * p.2 j); μ.prod ν] = _
  rw [covariance_add_left hRia hZib (hRja.add hZjb),
    covariance_add_right hRia hRja hZjb,
    covariance_add_right hZib hRja hZjb]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    hRR, hZZ, hRZ, hZR, hcovR, hcovOne]
  ring

private theorem map_weightedGaussianSum
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) (a b : ℝ) :
    Measure.map (fun p : Coord m × Coord m ↦ a • p.1 + b • p.2)
        ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) =
      multivariateGaussian (0 : Coord m)
        (a ^ 2 • R + b ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  have hS :
      (a ^ 2 • R + b ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    (hR.smul (sq_nonneg a)).add (Matrix.PosSemidef.one.smul (sq_nonneg b))
  change Measure.map (weightedSumCLM a b)
      ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) = _
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · have hInt :
          Integrable (fun x : Coord m × Coord m ↦ x)
            ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) := by
        exact IsGaussian.integrable_fun_id
      rw [← (weightedSumCLM a b).integral_comp_comm hInt]
      rw [integral_continuousLinearMap_prod]
      · simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
          weightedSumCLM_apply, smul_zero, zero_add, add_zero]
        rw [integral_smul, integral_smul, integral_id_multivariateGaussian,
          integral_id_stdGaussian]
        simp
      · exact IsGaussian.integrable_fun_id
      · exact IsGaussian.integrable_fun_id
    · exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hi :
        (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis i) u) ∘
            weightedSumCLM a b =
          fun p : Coord m × Coord m ↦ a * p.1 i + b * p.2 i := by
      ext p
      simp [PiLp.inner_apply]
    have hj :
        (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis j) u) ∘
            weightedSumCLM a b =
          fun p : Coord m × Coord m ↦ a * p.1 j + b * p.2 j := by
      ext p
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_weightedCoords R hR a b i j,
      covarianceBilin_multivariateGaussian hS]
    simp [Matrix.one_apply]
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

private theorem map_gaussianRegularization_eq_multivariateGaussian
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef)
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    Measure.map (gaussianRegularizationMap ε)
        ((multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))) =
      multivariateGaussian (0 : Coord m) ((1 - ε) • R + ε • 1) := by
  change Measure.map
      (fun p : Coord m × Coord m ↦
        Real.sqrt (1 - ε) • p.1 + Real.sqrt ε • p.2) _ = _
  simpa only [Real.sq_sqrt (sub_nonneg.mpr hε₁),
    Real.sq_sqrt hε₀] using
    map_weightedGaussianSum R hR (Real.sqrt (1 - ε)) (Real.sqrt ε)

private def regularizationEpsilon (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

private theorem regularizationEpsilon_pos (n : ℕ) :
    0 < regularizationEpsilon n := by
  simp only [regularizationEpsilon]
  positivity

private theorem regularizationEpsilon_lt_one (n : ℕ) :
    regularizationEpsilon n < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

private theorem tendsto_regularizationEpsilon :
    Tendsto regularizationEpsilon atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  change Tendsto ((fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) ∘ fun n ↦ n + 1) atTop (nhds 0)
  exact h.comp (tendsto_add_atTop_nat 1)

private theorem tendsto_gaussianRegularizationMap
    {m : ℕ} (p : Coord m × Coord m) :
    Tendsto (fun n ↦ gaussianRegularizationMap (regularizationEpsilon n) p)
      atTop (nhds p.1) := by
  have hsqrtOne :
      Tendsto (fun n ↦ Real.sqrt (1 - regularizationEpsilon n)) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using (hone.sub tendsto_regularizationEpsilon).sqrt
  have hsqrtZero :
      Tendsto (fun n ↦ Real.sqrt (regularizationEpsilon n)) atTop (nhds 0) := by
    simpa using tendsto_regularizationEpsilon.sqrt
  simpa [gaussianRegularizationMap] using
    (hsqrtOne.smul_const p.1).add (hsqrtZero.smul_const p.2)

private theorem tendstoInDistribution_regularized_multivariateGaussian
    {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosSemidef) :
    TendstoInDistribution (fun _ : ℕ ↦ id) atTop id
      (fun n ↦ multivariateGaussian (0 : Coord m)
        ((1 - (1 / 2 : ℝ) ^ (n + 1)) • R + (1 / 2 : ℝ) ^ (n + 1) • 1))
      (multivariateGaussian (0 : Coord m) R) := by
  let P := (multivariateGaussian (0 : Coord m) R).prod (stdGaussian (Coord m))
  have hcouple : TendstoInDistribution
      (fun n ↦ gaussianRegularizationMap (regularizationEpsilon n)) atTop Prod.fst
      (fun _ ↦ P) P := by
    apply tendstoInDistribution_of_ae_tendsto
    · exact fun n ↦
        (weightedSumCLM (Real.sqrt (1 - regularizationEpsilon n))
          (Real.sqrt (regularizationEpsilon n))).measurable.aemeasurable
    · exact measurable_fst.aemeasurable
    · exact Filter.Eventually.of_forall tendsto_gaussianRegularizationMap
  have hlaw (n : ℕ) :
      P.map (gaussianRegularizationMap (regularizationEpsilon n)) =
        multivariateGaussian (0 : Coord m)
          ((1 - regularizationEpsilon n) • R + regularizationEpsilon n • 1) := by
    dsimp only [P]
    exact map_gaussianRegularization_eq_multivariateGaussian R hR _
      (regularizationEpsilon_pos n).le (regularizationEpsilon_lt_one n).le
  have hfstLaw : P.map Prod.fst = multivariateGaussian (0 : Coord m) R := by
    dsimp only [P]
    exact measurePreserving_fst.map_eq
  refine ⟨fun _ ↦ measurable_id.aemeasurable, measurable_id.aemeasurable, ?_⟩
  have ht := hcouple.tendsto
  simp only [hlaw, hfstLaw] at ht
  simpa only [Measure.map_id, regularizationEpsilon] using ht

/-- A lower bound on `∫ F dμ_{S_ε}` for the regularized covariances `S_ε`, `ε = 2^{-(n+1)}`,
passes to the limit `μ_S` for every bounded continuous `F`. -/
theorem le_integral_of_regularized {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (F : Coord m → ℝ) (hF : Continuous F) (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) (c : ℝ)
    (h : ∀ n : ℕ, c ≤ ∫ x, F x ∂multivariateGaussian (0 : Coord m)
      ((1 - (1 / 2 : ℝ) ^ (n + 1)) • S + (1 / 2 : ℝ) ^ (n + 1) • 1)) :
    c ≤ ∫ x, F x ∂multivariateGaussian (0 : Coord m) S := by
  have hconv := tendstoInDistribution_regularized_multivariateGaussian S hS
  have ht := hconv.tendsto
  simp only [Measure.map_id] at ht
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at ht
  have hb := ht (BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (C + C) (fun x y ↦ by
    have h1 := hC x
    have h2 := hC y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [Real.norm_eq_abs] at h1 h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith))
  exact ge_of_tendsto hb (Filter.Eventually.of_forall h)

end Regularize

/-- Lemma 2 (strict product inequality). Singular `S` is allowed. -/
theorem tiltedHalfLine_product_gt
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S) (hne : S ≠ 1)
    (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcent : ∀ i, ∫ x, x * tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1 = 0) :
    (∏ i, ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1) <
      ∫ x, ∏ i, tiltedHalfLine (a i) (b i) (x i) ∂multivariateGaussian (0 : Coord m) S := by
  classical
  let M : Fin m → ℝ := fun i ↦ ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1
  have hM : ∀ i, 0 < M i := by
    intro i
    have h := integral_tiltedHalfLine (a := a i) (s := b i - a i) (ha i).le
    rw [sub_add_cancel] at h
    show 0 < ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1
    rw [h]
    exact mul_pos (Real.exp_pos _) (normalCDF_pos _)
  let h : Fin m → ℝ → ℝ := fun i x ↦ (M i)⁻¹ * tiltedHalfLine (a i) (b i) x
  have hh_meas : ∀ i, Measurable (h i) := fun i ↦
    (measurable_tiltedHalfLine _ _).const_mul _
  have hh_nonneg : ∀ i x, 0 ≤ h i x := fun i x ↦
    mul_nonneg (inv_pos.2 (hM i)).le (tiltedHalfLine_nonneg _ _ _)
  have hh_bdd : ∀ i, Bornology.IsBounded (Set.range (h i)) := fun i ↦
    Deficit.isBounded_range_const_mul (isBounded_range_tiltedHalfLine (ha i).le) _
  have hh_lc : ∀ i, IsLogConcave (fun x ↦ ENNReal.ofReal (h i x)) := fun i ↦
    Deficit.isLogConcave_const_mul_of_nonneg (inv_pos.2 (hM i)).le
      (isLogConcave_tiltedHalfLine _ _)
  have hh_mass : ∀ i, ∫ x, h i x ∂gaussianReal 0 1 = 1 := by
    intro i
    simp only [h]
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (hM i).ne'
  have hh_bary : ∀ i, ∫ x, x * h i x ∂gaussianReal 0 1 = 0 := by
    intro i
    simp only [h]
    simp_rw [mul_left_comm _ (M i)⁻¹]
    rw [integral_const_mul, hcent i, mul_zero]
  have hDc : ∀ i, Continuous (normalizedSelfConvolution (h i)) := fun i ↦
    Deficit.continuous_normalizedSelfConvolution_tilted (a i) (b i) (M i) (ha i).le (hM i)
  have hDbdd : ∀ i, Bornology.IsBounded (Set.range (normalizedSelfConvolution (h i))) := fun i ↦
    isBounded_range_normalizedSelfConvolution (hh_nonneg i) (hh_bdd i)
  choose C hC using fun i ↦ Deficit.exists_norm_bound_of_isBounded_range (hDbdd i)
  -- the self-convolutions are admissible for the centered product inequality
  have hQ1pd : ∀ R : Matrix (Fin m) (Fin m) ℝ, R.PosDef → (∀ i, R i i = 1) →
      1 ≤ ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
        ∂multivariateGaussian (0 : Coord m) R := by
    intro R hpd hdiag
    have hc := centered_product_of_posDef R hpd hdiag (fun i ↦ normalizedSelfConvolution (h i))
      (fun i ↦ measurable_normalizedSelfConvolution (hh_meas i))
      (fun i x ↦ normalizedSelfConvolution_nonneg _ _)
      (fun i ↦ isBounded_range_normalizedSelfConvolution (hh_nonneg i) (hh_bdd i))
      (fun i ↦ isLogConcave_normalizedSelfConvolution (hh_meas i) (hh_nonneg i) (hh_bdd i)
        (hh_lc i))
      (fun i ↦ by
        rw [integral_normalizedSelfConvolution_eq_one (hh_meas i) (hh_nonneg i) (hh_bdd i)
          (hh_mass i)]
        exact one_pos)
      (fun i ↦ integral_mul_normalizedSelfConvolution_eq_zero (hh_meas i) (hh_nonneg i)
        (hh_bdd i) (hh_mass i) (hh_bary i))
    simpa [integral_normalizedSelfConvolution_eq_one (hh_meas _) (hh_nonneg _) (hh_bdd _)
      (hh_mass _)] using hc
  -- regularize `S` to positive-definite correlation matrices and pass to the limit
  have hQ1 : 1 ≤ ∫ u, ∏ i, normalizedSelfConvolution (h i) (u i)
      ∂multivariateGaussian (0 : Coord m) S := by
    refine Regularize.le_integral_of_regularized S hS.1
      (fun u ↦ ∏ i, normalizedSelfConvolution (h i) (u i))
      (continuous_finsetProd _ fun i _ ↦ (hDc i).comp (EuclideanSpace.proj i).continuous)
      (∏ i, |C i|) ?_ 1 ?_
    · intro u
      rw [Real.norm_eq_abs, Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
      exact (hC i (u i)).trans (le_abs_self _)
    · intro n
      have hε0 : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
      have hε1 : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      refine hQ1pd _ ?_ ?_
      · exact Matrix.PosDef.posSemidef_add (hS.1.smul (by linarith))
          (Matrix.PosDef.one.smul hε0)
      · intro i
        simp [Matrix.add_apply, hS.2 i]
  -- strictness on the box `{|u_i| ≤ b_i}`
  have hE : 0 < multivariateGaussian (0 : Coord m) S (symmetricRectangle b) :=
    lt_of_le_of_lt zero_le (symmetricRectangle_gt_iid S hS hne b hb)
  have hsqrt : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  have hconv : ∀ u : Coord m, (∏ i, normalizedSelfConvolution (h i) (u i)) =
      ∏ i, ∫ v, Deficit.fixedAverageFactor (h i) (u i) v ∂gaussianReal 0 1 := fun u ↦
    Finset.prod_congr rfl fun i _ ↦
      (Deficit.integral_fixedAverageFactor_eq_normalizedSelfConvolution (hh_meas i)
        (hh_nonneg i) (hh_bdd i) (u i)).symm
  have hle : ∀ u : Coord m, (∏ i, normalizedSelfConvolution (h i) (u i)) ≤
      ∫ v, ∏ i, Deficit.fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) S := by
    intro u
    rw [hconv u]
    exact Deficit.indicator_product_ge S hS hne
      (fun i ↦ (M i)⁻¹ ^ 2 * Real.exp (Real.sqrt 2 * a i * u i))
      (fun i ↦ Real.sqrt 2 * b i - u i)
      (fun i ↦ mul_pos (pow_pos (inv_pos.2 (hM i)) 2) (Real.exp_pos _))
      (fun i ↦ Deficit.fixedAverageFactor (h i) (u i))
      (fun i v ↦ Deficit.fixedAverageFactor_tilted (a i) (b i) (M i) (u i) v)
  have hstrict : ∀ u ∈ symmetricRectangle b, (∏ i, normalizedSelfConvolution (h i) (u i)) <
      ∫ v, ∏ i, Deficit.fixedAverageFactor (h i) (u i) (v i)
        ∂multivariateGaussian (0 : Coord m) S := by
    intro u hu
    have hρ : ∀ i, 0 < Real.sqrt 2 * b i - u i := fun i ↦ by
      have := (hu i).2
      nlinarith [hb i]
    rw [hconv u]
    exact Deficit.indicator_product_gt S hS hne
      (fun i ↦ (M i)⁻¹ ^ 2 * Real.exp (Real.sqrt 2 * a i * u i))
      (fun i ↦ Real.sqrt 2 * b i - u i)
      (fun i ↦ mul_pos (pow_pos (inv_pos.2 (hM i)) 2) (Real.exp_pos _)) hρ
      (fun i ↦ Deficit.fixedAverageFactor (h i) (u i))
      (fun i v ↦ Deficit.fixedAverageFactor_tilted (a i) (b i) (M i) (u i) v)
  have hdef := Deficit.product_deficit_strict_of_le S h hh_meas hh_nonneg hh_bdd
    (symmetricRectangle b) hE hle hstrict
  have hQ0_nonneg : 0 ≤ ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) S :=
    integral_nonneg fun x ↦ Finset.prod_nonneg fun i _ ↦ hh_nonneg i _
  have hQ0 : 1 < ∫ x, ∏ i, h i (x i) ∂multivariateGaussian (0 : Coord m) S := by
    by_contra hcon
    have hle := not_lt.1 hcon
    nlinarith
  have hfac : (fun x : Coord m ↦ ∏ i, tiltedHalfLine (a i) (b i) (x i)) =
      fun x ↦ (∏ i, M i) * ∏ i, h i (x i) := by
    funext x
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp only [h]
    rw [mul_inv_cancel_left₀ (hM i).ne']
  have hMpos : 0 < ∏ i, M i := Finset.prod_pos fun i _ ↦ hM i
  rw [hfac, integral_const_mul]
  calc (∏ i, M i) = (∏ i, M i) * 1 := (mul_one _).symm
    _ < _ := mul_lt_mul_of_pos_left hQ0 hMpos

/-- Lemma 2 (strict product inequality), positive-definite case. -/
theorem tiltedHalfLine_product_gt_of_posDef
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S) (hpd : S.PosDef)
    (hne : S ≠ 1)
    (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcent : ∀ i, ∫ x, x * tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1 = 0) :
    (∏ i, ∫ x, tiltedHalfLine (a i) (b i) x ∂gaussianReal 0 1) <
      ∫ x, ∏ i, tiltedHalfLine (a i) (b i) (x i) ∂multivariateGaussian (0 : Coord m) S :=
  have _ := hpd
  tiltedHalfLine_product_gt S hS hne a b ha hb hcent

end SimplexUniqueness
