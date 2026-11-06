import SimplexFull.GlobalComparisonDefs
noncomputable section
namespace SimplexFull.GlobalComparison.Rotation
open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal Matrix BigOperators

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/SumDifference.lean, MIT
def coordProduct {m : ℕ} (h : Fin m → ℝ → ℝ) (x : Coord m) : ℝ :=
  ∏ i, h i (x i)

def fixedAverageFactor
    (h : ℝ → ℝ) (u v : ℝ) : ℝ :=
  h ((u + v) / Real.sqrt 2) * h ((u - v) / Real.sqrt 2)

theorem measurable_fixedAverageFactor
    {h : ℝ → ℝ} (hh : Measurable h) (u : ℝ) :
    Measurable (fixedAverageFactor h u) := by
  exact (hh.comp ((measurable_const.add measurable_id).div_const _)).mul
    (hh.comp ((measurable_const.sub measurable_id).div_const _))

theorem fixedAverageFactor_nonneg
    {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (u v : ℝ) :
    0 ≤ fixedAverageFactor h u v :=
  mul_nonneg (hh _) (hh _)

theorem fixedAverageFactor_even
    (h : ℝ → ℝ) (u : ℝ) : Function.Even (fixedAverageFactor h u) := by
  intro v
  have hplus : (u + -v) / Real.sqrt 2 = (u - v) / Real.sqrt 2 := by ring
  have hminus : (u - -v) / Real.sqrt 2 = (u + v) / Real.sqrt 2 := by ring
  simp only [fixedAverageFactor, hplus, hminus, mul_comm]

theorem isLogConcave_comp_add_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u + v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u + x) / Real.sqrt 2) ((u + y) / Real.sqrt 2)
  have harg : t * ((u + x) / Real.sqrt 2) +
      (1 - t) * ((u + y) / Real.sqrt 2) =
        (u + (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

theorem isLogConcave_comp_sub_const_div_sqrtTwo
    {h : ℝ → ℝ≥0∞} (hh : IsLogConcave h) (u : ℝ) :
    IsLogConcave (fun v ↦ h ((u - v) / Real.sqrt 2)) := by
  intro t ht_pos ht_lt x y
  have hmain := hh ht_pos ht_lt ((u - x) / Real.sqrt 2) ((u - y) / Real.sqrt 2)
  have harg : t * ((u - x) / Real.sqrt 2) +
      (1 - t) * ((u - y) / Real.sqrt 2) =
        (u - (t * x + (1 - t) * y)) / Real.sqrt 2 := by ring
  simpa only [smul_eq_mul, harg] using hmain

theorem isLogConcave_fixedAverageFactor
    {h : ℝ → ℝ} (hh_nonneg : ∀ x, 0 ≤ h x)
    (hh_lc : IsLogConcave (fun x ↦ ENNReal.ofReal (h x))) (u : ℝ) :
    IsLogConcave (fun v ↦ ENNReal.ofReal (fixedAverageFactor h u v)) := by
  have hplus := isLogConcave_comp_add_const_div_sqrtTwo hh_lc u
  have hminus := isLogConcave_comp_sub_const_div_sqrtTwo hh_lc u
  convert hplus.mul hminus using 1
  funext v
  exact ENNReal.ofReal_mul (hh_nonneg _)

theorem exists_norm_bound_of_isBounded_range
    {X : Type*} {f : X → ℝ} (hf : Bornology.IsBounded (Set.range f)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hf
  refine ⟨C, fun x ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hC (Set.mem_range_self x)

theorem isBounded_range_fixedAverageFactor
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

theorem integrable_of_measurable_isBounded_range
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

theorem integral_fixedAverageFactor_eq_normalizedSelfConvolution
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

theorem integrable_coord_product
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

theorem measurable_coordProduct
    {m : ℕ} (h : Fin m → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i)) :
    Measurable (coordProduct h) := by
  classical
  exact Finset.measurable_prod Finset.univ fun i _ ↦
    (hh_meas i).comp (EuclideanSpace.proj (𝕜 := ℝ) i).measurable

theorem rotation_neg_pi_div_four_apply {m : ℕ} (p : Coord m × Coord m) :
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

theorem multivariateGaussian_prod_rotation {m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) :
    ((multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R)).map
      (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
      (multivariateGaussian (0 : Coord m) R).prod
        (multivariateGaussian (0 : Coord m) R) := by
  apply IsGaussian.map_rotation_eq_self
  simp

def sumDifferenceProduct {m : ℕ}
    (h : Fin m → ℝ → ℝ) (p : Coord m × Coord m) : ℝ :=
  ∏ i, fixedAverageFactor (h i) (p.1 i) (p.2 i)

theorem sumDifferenceProduct_eq_rotated {m : ℕ}
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


end SimplexFull.GlobalComparison.Rotation
