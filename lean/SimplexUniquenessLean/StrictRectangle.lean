import WeakSimplexConjectureLean

/-!
# Strict symmetric rectangle inequality

Lemma 1 of the paper (Section V-A): a strict form of the Šidák–Khatri
rectangle inequality. If `V ∼ N(0, S)` with unit diagonal and `S ≠ I`,
possibly singular, then for all finite positive radii
`P {|V_i| ≤ r_i ∀ i} > ∏ P {|Z| ≤ r_i}`.

Proof route. A one-slab peeling step (Šidák's inequality for a single coordinate), valid for
positive-semidefinite covariance, gives the non-strict grouping inequality
`P(rect) ≥ P(pair block) * ∏_{k ≠ i, j} P{|Z| ≤ r_k}`; the strict gain is obtained for the
bivariate block `(V_i, V_j)` with nonzero correlation. Since the peeling step already holds for
singular matrices, no regularization limit is required.
-/

noncomputable section

namespace SimplexUniqueness

open MeasureTheory Set WeakSimplex ProbabilityTheory
open scoped ENNReal NNReal Matrix BigOperators MatrixOrder

namespace Peel

-- Adapted from weak-simplex-conjecture-lean (Mulgund), Product/SymmetricRectangle.lean, MIT
private def symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (-r i) (r i)}

private theorem measurableSet_symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) :
    MeasurableSet (symmetricRectanglePi r) := by
  rw [symmetricRectanglePi, Set.setOf_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Icc.preimage (measurable_pi_apply i)

private theorem convex_symmetricRectangle {m : ℕ} (r : Fin m → ℝ) :
    Convex ℝ (symmetricRectangle r) := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Icc (-r i) (r i)) (hx i) (hy i) ha hb hab
  simpa using hi

private theorem convex_symmetricRectanglePi {m : ℕ} (r : Fin m → ℝ) :
    Convex ℝ (symmetricRectanglePi r) := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Icc (-r i) (r i)) (hx i) (hy i) ha hb hab
  simpa using hi

private theorem neg_mem_symmetricRectanglePi_iff
    {m : ℕ} {r : Fin m → ℝ} {x : Fin m → ℝ} :
    -x ∈ symmetricRectanglePi r ↔ x ∈ symmetricRectanglePi r := by
  constructor <;> intro hx i <;> constructor
  · simpa using neg_le_neg (hx i).2
  · simpa using neg_le_neg (hx i).1
  · simpa using neg_le_neg (hx i).2
  · simpa using neg_le_neg (hx i).1

private theorem neg_mem_symmetricRectangle_iff {m : ℕ} {r : Fin m → ℝ} {x : Coord m} :
    -x ∈ symmetricRectangle r ↔ x ∈ symmetricRectangle r := by
  constructor
  · intro hx i
    constructor
    · have := (hx i).2
      simpa using (neg_le_neg this)
    · have := (hx i).1
      simpa using (neg_le_neg this)
  · intro hx i
    constructor
    · have := (hx i).2
      simpa using (neg_le_neg this)
    · have := (hx i).1
      simpa using (neg_le_neg this)

private def gaussianShiftCLM {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (b : Fin n → ℝ) : (ℝ × (Fin k → ℝ)) →L[ℝ] (Fin n → ℝ) :=
  L.comp (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ)) +
    (ContinuousLinearMap.fst ℝ ℝ (Fin k → ℝ)).smulRight b

private theorem convexIndicator_neg_eq
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_neg : ∀ x, -x ∈ C ↔ x ∈ C) (x : Fin n → ℝ) :
    convexIndicator C (-x) = convexIndicator C x := by
  by_cases hx : x ∈ C
  · have hnx : -x ∈ C := (hC_neg x).2 hx
    simp [convexIndicator, hx, hnx]
  · have hnx : -x ∉ C := fun h ↦ hx ((hC_neg x).1 h)
    simp [convexIndicator, hx, hnx]

private def gaussianKernelOne (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(x ^ 2) / 2))

private theorem measurable_gaussianKernelOne : Measurable gaussianKernelOne := by
  exact ((continuous_id.pow 2).neg.div_const 2).rexp.measurable.ennreal_ofReal

private theorem isLogConcave_gaussianKernelOne : IsLogConcave gaussianKernelOne := by
  intro t ht_pos ht_lt x y
  rw [gaussianKernelOne, gaussianKernelOne, gaussianKernelOne,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simp only [smul_eq_mul]
  have hrem : 0 ≤ t * (1 - t) * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg ht_pos.le (sub_nonneg.mpr ht_lt.le)) (sq_nonneg _)
  nlinarith

private theorem gaussianPDF_zero_one_eq_const_mul_kernel (x : ℝ) :
    gaussianPDF 0 1 x =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * gaussianKernelOne x := by
  rw [gaussianPDF, gaussianPDFReal_def, gaussianKernelOne]
  norm_num

private theorem isLogConcave_gaussianPDF_zero_one : IsLogConcave (gaussianPDF 0 1) := by
  have hEq : gaussianPDF 0 1 = fun x ↦
      ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * gaussianKernelOne x := by
    funext x
    exact gaussianPDF_zero_one_eq_const_mul_kernel x
  rw [hEq]
  change IsLogConcave
    ((fun _ : ℝ ↦ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹) * gaussianKernelOne)
  exact (isLogConcave_const (E := ℝ)
    (ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹)).mul isLogConcave_gaussianKernelOne

private theorem isLogConcave_finset_prod
    {ι E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset ι) {f : ι → E → ℝ≥0∞}
    (hf : ∀ i ∈ s, IsLogConcave (f i)) :
    IsLogConcave (fun x ↦ ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isLogConcave_const (E := E) 1)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      change IsLogConcave (f i * fun x ↦ ∏ j ∈ s, f j x)
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

private theorem isLogConcave_piGaussianDensity {m : ℕ} :
    IsLogConcave (fun x : Fin m → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
  apply isLogConcave_finset_prod Finset.univ
  intro i hi t ht_pos ht_lt x y
  simpa using isLogConcave_gaussianPDF_zero_one ht_pos ht_lt (x i) (y i)

private def piGaussianDensity {m : ℕ} (x : Fin m → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

private theorem measurable_piGaussianDensity {m : ℕ} :
    Measurable (piGaussianDensity (m := m)) := by
  exact Finset.measurable_prod _ fun i _ ↦
    (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

private theorem isLogConcave_piGaussianDensity' {m : ℕ} :
    IsLogConcave (piGaussianDensity (m := m)) :=
  isLogConcave_piGaussianDensity

@[simp]
private theorem gaussianPDF_zero_one_neg (x : ℝ) : gaussianPDF 0 1 (-x) = gaussianPDF 0 1 x := by
  simp [gaussianPDF, gaussianPDFReal_def]

@[simp]
private theorem piGaussianDensity_neg {m : ℕ} (x : Fin m → ℝ) :
    piGaussianDensity (-x) = piGaussianDensity x := by
  simp [piGaussianDensity]

private def piGaussianShiftMass {k n : ℕ}
    (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (C : Set (Fin n → ℝ)) (b : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x

private theorem measurable_isLogConcave_piGaussianShiftMass
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C) (hC_conv : Convex ℝ C)
    (b : Fin n → ℝ) :
    Measurable (piGaussianShiftMass L C b) ∧ IsLogConcave (piGaussianShiftMass L C b) := by
  change Measurable (fun t ↦
      ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x) ∧
    IsLogConcave (fun t ↦
      ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x)
  let F : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun t x ↦
    convexIndicator C (L x + t • b) * piGaussianDensity x
  have hF_meas : Measurable (Function.uncurry F) :=
    ((measurable_convexIndicator hC_meas).comp (gaussianShiftCLM L b).measurable).mul
      (measurable_piGaussianDensity.comp measurable_snd)
  have hF_lc : IsLogConcave (fun p : ℝ × (Fin k → ℝ) ↦ F p.1 p.2) :=
    ((isLogConcave_convexIndicator hC_conv).comp_affineMap
      (gaussianShiftCLM L b).toLinearMap.toAffineMap).mul
        (isLogConcave_piGaussianDensity'.comp_affineMap
          (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ)).toLinearMap.toAffineMap)
  simpa only [F] using measurable_isLogConcave_lintegral_right hF_meas hF_lc

private theorem piGaussianShiftMass_even
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C)
    (hC_neg : ∀ x, -x ∈ C ↔ x ∈ C) (b : Fin n → ℝ) (t : ℝ) :
    piGaussianShiftMass L C b (-t) = piGaussianShiftMass L C b t := by
  let f : (Fin k → ℝ) → ℝ≥0∞ := fun x ↦
    convexIndicator C (L x + (-t) • b) * piGaussianDensity x
  have hf : Measurable f :=
    ((measurable_convexIndicator hC_meas).comp (L.measurable.add_const ((-t) • b))).mul
      measurable_piGaussianDensity
  have hneg := Measure.measurePreserving_neg (volume : Measure (Fin k → ℝ))
  change (∫⁻ x, f x) =
    ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x
  calc
    (∫⁻ x, f x) = ∫⁻ x, f (-x) := (hneg.lintegral_comp hf).symm
    _ = ∫⁻ x, convexIndicator C (L x + t • b) * piGaussianDensity x := by
      apply lintegral_congr
      intro x
      have harg : L (-x) + (-t) • b = -(L x + t • b) := by simp [add_comm]
      simp only [f, harg, convexIndicator_neg_eq hC_neg, piGaussianDensity_neg]

private theorem piGaussianShiftMass_eq_measure
    {k n : ℕ} (L : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC_meas : MeasurableSet C)
    (b : Fin n → ℝ) (t : ℝ)
    (hpi : Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity piGaussianDensity) :
    piGaussianShiftMass L C b t =
      Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) {x | L x + t • b ∈ C} := by
  have hS : MeasurableSet {x | L x + t • b ∈ C} :=
    (L.measurable.add_const (t • b)) hC_meas
  rw [piGaussianShiftMass, hpi, withDensity_apply piGaussianDensity hS,
    ← lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : L x + t • b ∈ C
  · simp [convexIndicator, hx]
  · simp [convexIndicator, hx]

private def regressionResidualCLM {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Coord (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    EuclideanSpace.proj (Fin.castSucc i) -
      R (Fin.castSucc i) (Fin.last n) • EuclideanSpace.proj (Fin.last n)

private def regressionSlope {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin n → ℝ :=
  fun i ↦ R (Fin.castSucc i) (Fin.last n)

private def regressionLastCLM {n : ℕ} : Coord (n + 1) →L[ℝ] (Unit → ℝ) :=
  ContinuousLinearMap.pi fun _ ↦ EuclideanSpace.proj (Fin.last n)

private def firstFunCLM {n : ℕ} : Coord (n + 1) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ EuclideanSpace.proj (Fin.castSucc i)

private def firstCoordCLM {n : ℕ} : Coord (n + 1) →L[ℝ] Coord n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp firstFunCLM

@[simp]
private theorem firstCoordCLM_apply {n : ℕ} (x : Coord (n + 1)) (i : Fin n) :
    firstCoordCLM x i = x (Fin.castSucc i) :=
  rfl

private theorem regression_reconstruct_first {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Coord (n + 1)) :
    regressionResidualCLM R x + x (Fin.last n) • regressionSlope R = firstFunCLM x := by
  ext i
  simp [regressionResidualCLM, regressionSlope, firstFunCLM]
  ring

private theorem mem_symmetricRectangle_succ_iff
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r : Fin (n + 1) → ℝ) (x : Coord (n + 1)) :
    x ∈ symmetricRectangle r ↔
      regressionResidualCLM R x + x (Fin.last n) • regressionSlope R ∈
          symmetricRectanglePi (fun i ↦ r (Fin.castSucc i)) ∧
        x (Fin.last n) ∈ Set.Icc (-r (Fin.last n)) (r (Fin.last n)) := by
  rw [regression_reconstruct_first]
  change (∀ i, x i ∈ Set.Icc (-r i) (r i)) ↔
    (∀ i : Fin n, x (Fin.castSucc i) ∈
      Set.Icc (-r (Fin.castSucc i)) (r (Fin.castSucc i))) ∧
      x (Fin.last n) ∈ Set.Icc (-r (Fin.last n)) (r (Fin.last n))
  exact Fin.forall_fin_succ'

private theorem map_firstCoord_multivariateGaussian_zero
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) :
    Measure.map firstCoordCLM (multivariateGaussian (0 : Coord (n + 1)) R) =
      multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
    · simp
    · exact IsGaussian.integrable_id
        (μ := multivariateGaussian (0 : Coord (n + 1)) R)
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hi : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) u) ∘
        firstCoordCLM = fun u : Coord (n + 1) ↦ u (Fin.castSucc i) := by
      ext u
      simp [PiLp.inner_apply]
    have hj : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j) u) ∘
        firstCoordCLM = fun u : Coord (n + 1) ↦ u (Fin.castSucc j) := by
      ext u
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix Fin.castSucc)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

private def multivariateGaussianSourceCLM {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] Coord (n + 1) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt R)).comp
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap

private def regressionSourceCLM {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (regressionResidualCLM R).comp (multivariateGaussianSourceCLM R)

private theorem map_regressionResidual_multivariateGaussian_zero
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Measure.map (regressionResidualCLM R)
      (multivariateGaussian (0 : Coord (n + 1)) R) =
    Measure.map (regressionSourceCLM R)
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) := by
  rw [multivariateGaussian]
  simp only [zero_add]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

private def regressionShiftMass {n : ℕ}
    (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Measure.map (regressionResidualCLM R)
    (multivariateGaussian (0 : Coord (n + 1)) R))
      {y | y + t • regressionSlope R ∈ symmetricRectanglePi r}

private theorem regressionShiftMass_eq_piGaussianShiftMass
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (t : ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    regressionShiftMass R r t =
      piGaussianShiftMass (regressionSourceCLM R) (symmetricRectanglePi r)
        (regressionSlope R) t := by
  have hS : MeasurableSet {y | y + t • regressionSlope R ∈ symmetricRectanglePi r} :=
    (measurable_id.add_const (t • regressionSlope R))
      (measurableSet_symmetricRectanglePi r)
  rw [regressionShiftMass, map_regressionResidual_multivariateGaussian_zero R,
    Measure.map_apply (regressionSourceCLM R).measurable hS]
  exact (piGaussianShiftMass_eq_measure (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r) (regressionSlope R) t hpi).symm

private theorem measurable_isLogConcave_regressionShiftMass
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    Measurable (regressionShiftMass R r) ∧ IsLogConcave (regressionShiftMass R r) := by
  have heq : regressionShiftMass R r =
      piGaussianShiftMass (regressionSourceCLM R) (symmetricRectanglePi r)
        (regressionSlope R) := by
    funext t
    exact regressionShiftMass_eq_piGaussianShiftMass R r t hpi
  rw [heq]
  exact measurable_isLogConcave_piGaussianShiftMass (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r) (convex_symmetricRectanglePi r)
    (regressionSlope R)

private theorem regressionShiftMass_even
    {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (r : Fin n → ℝ)
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity)
    (t : ℝ) : regressionShiftMass R r (-t) = regressionShiftMass R r t := by
  rw [regressionShiftMass_eq_piGaussianShiftMass R r (-t) hpi,
    regressionShiftMass_eq_piGaussianShiftMass R r t hpi]
  exact piGaussianShiftMass_even (regressionSourceCLM R)
    (measurableSet_symmetricRectanglePi r)
    (fun x ↦ neg_mem_symmetricRectanglePi_iff) (regressionSlope R) t

private theorem prod_shift_inter_eq_setLIntegral
    {n : ℕ} (ν : Measure (Fin n → ℝ)) [SFinite ν] (γ : Measure ℝ) [SFinite γ]
    {C : Set (Fin n → ℝ)} (hC : MeasurableSet C) (b : Fin n → ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ν.prod γ {p | p.1 + p.2 • b ∈ C ∧ p.2 ∈ A} =
      ∫⁻ t in A, ν {y | y + t • b ∈ C} ∂γ := by
  have hshift : Measurable (fun p : (Fin n → ℝ) × ℝ ↦ p.1 + p.2 • b) := by
    fun_prop
  have hS : MeasurableSet {p : (Fin n → ℝ) × ℝ |
      p.1 + p.2 • b ∈ C ∧ p.2 ∈ A} :=
    (hC.preimage hshift).inter (hA.preimage measurable_snd)
  rw [Measure.prod_apply_symm hS, ← lintegral_indicator hA]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ A
  · rw [Set.indicator_of_mem ht]
    congr 1
    ext y
    simp [ht]
  · rw [Set.indicator_of_notMem ht]
    simp [ht]

private theorem regressionResidual_indep_last
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    IndepFun (regressionResidualCLM R) regressionLastCLM
      (multivariateGaussian (0 : Coord (n + 1)) R) := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  have hId : HasGaussianLaw (id : Coord (n + 1) → Coord (n + 1)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hPair := hId.map ((regressionResidualCLM R).prod regressionLastCLM)
  apply hPair.indepFun_of_covariance_eval
  intro i j
  have hcoord (k : Fin (n + 1)) : MemLp (fun x : Coord (n + 1) ↦ x k) 2 μ := by
    simpa only [Function.comp_id, EuclideanSpace.coe_proj] using
      (hId.map (EuclideanSpace.proj k)).memLp_two
  change cov[
      (fun x : Coord (n + 1) ↦
        x (Fin.castSucc i) - R (Fin.castSucc i) (Fin.last n) * x (Fin.last n)),
      (fun x : Coord (n + 1) ↦ x (Fin.last n)); μ] = 0
  rw [covariance_fun_sub_left (hcoord _) ((hcoord _).const_mul _) (hcoord _),
    covariance_const_mul_left, covariance_eval_multivariateGaussian hR,
    covariance_eval_multivariateGaussian hR, hdiag]
  ring

private theorem regressionResidual_indep_lastScalar
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    IndepFun (regressionResidualCLM R) (fun x : Coord (n + 1) ↦ x (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) := by
  have h := (regressionResidual_indep_last hR hdiag).comp
    measurable_id (measurable_pi_apply ())
  simpa [Function.comp_def, regressionLastCLM] using h

private theorem map_last_multivariateGaussian_zero
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    Measure.map (fun x : Coord (n + 1) ↦ x (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) = gaussianReal 0 1 := by
  have h := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord (n + 1))) hR (i := Fin.last n)).map_eq
  simpa [hdiag] using h

private theorem map_regressionResidual_last_eq_prod
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    Measure.map
      (fun x : Coord (n + 1) ↦ (regressionResidualCLM R x, x (Fin.last n)))
      (multivariateGaussian (0 : Coord (n + 1)) R) =
    (Measure.map (regressionResidualCLM R)
      (multivariateGaussian (0 : Coord (n + 1)) R)).prod (gaussianReal 0 1) := by
  have h := (regressionResidual_indep_lastScalar hR hdiag).map_prod_eq_prod_map_map
    (regressionResidualCLM R).measurable.aemeasurable
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable.aemeasurable
  have hlast : Measure.map (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n))
      (multivariateGaussian (0 : Coord (n + 1)) R) = gaussianReal 0 1 := by
    simpa only [EuclideanSpace.coe_proj] using
      map_last_multivariateGaussian_zero hR hdiag
  rw [hlast] at h
  simpa only [EuclideanSpace.coe_proj] using h

private theorem multivariateGaussian_symmetricRectangle_eq_setLIntegral_regressionShiftMass
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin (n + 1) → ℝ) :
    multivariateGaussian (0 : Coord (n + 1)) R (symmetricRectangle r) =
      ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
        regressionShiftMass R (fun i ↦ r (Fin.castSucc i)) t ∂gaussianReal 0 1 := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  let ν := Measure.map (regressionResidualCLM R) μ
  let A := Set.Icc (-r (Fin.last n)) (r (Fin.last n))
  let C := symmetricRectanglePi (fun i : Fin n ↦ r (Fin.castSucc i))
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ A}
  let J : Coord (n + 1) → (Fin n → ℝ) × ℝ := fun x ↦
    (regressionResidualCLM R x, x (Fin.last n))
  have hJ : Measurable J := by
    exact (regressionResidualCLM R).measurable.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable
  have hS : MeasurableSet S := by
    exact ((measurableSet_symmetricRectanglePi _).preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage measurable_snd)
  have hpre : J ⁻¹' S = symmetricRectangle r := by
    ext x
    simpa only [J, S, C, A, Set.mem_preimage, Set.mem_setOf_eq] using
      (mem_symmetricRectangle_succ_iff R r x).symm
  calc
    μ (symmetricRectangle r) = μ (J ⁻¹' S) := by rw [hpre]
    _ = Measure.map J μ S := (Measure.map_apply hJ hS).symm
    _ = ν.prod (gaussianReal 0 1) S := by
      simpa only [μ, ν, J] using congrArg
        (fun m : Measure ((Fin n → ℝ) × ℝ) ↦ m S)
        (map_regressionResidual_last_eq_prod hR hdiag)
    _ = ∫⁻ t in A, ν {y | y + t • regressionSlope R ∈ C} ∂gaussianReal 0 1 := by
      exact prod_shift_inter_eq_setLIntegral ν (gaussianReal 0 1)
        (measurableSet_symmetricRectanglePi _) (regressionSlope R) measurableSet_Icc
    _ = ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
        regressionShiftMass R (fun i ↦ r (Fin.castSucc i)) t ∂gaussianReal 0 1 := by
      rfl

private theorem lintegral_regressionShiftMass_eq_marginal_symmetricRectangle
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin n → ℝ) :
    (∫⁻ t, regressionShiftMass R r t ∂gaussianReal 0 1) =
      multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc)
        (symmetricRectangle r) := by
  let μ := multivariateGaussian (0 : Coord (n + 1)) R
  let ν := Measure.map (regressionResidualCLM R) μ
  let C := symmetricRectanglePi r
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 + p.2 • regressionSlope R ∈ C}
  let J : Coord (n + 1) → (Fin n → ℝ) × ℝ := fun x ↦
    (regressionResidualCLM R x, x (Fin.last n))
  have hJ : Measurable J := by
    exact (regressionResidualCLM R).measurable.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable
  have hS : MeasurableSet S := by
    exact (measurableSet_symmetricRectanglePi _).preimage (by fun_prop)
  have hpre : J ⁻¹' S = firstCoordCLM ⁻¹' symmetricRectangle r := by
    ext x
    change regressionResidualCLM R x + x (Fin.last n) • regressionSlope R ∈
        symmetricRectanglePi r ↔ firstCoordCLM x ∈ symmetricRectangle r
    rw [regression_reconstruct_first]
    rfl
  have hSuniv :
      {p : (Fin n → ℝ) × ℝ |
          p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ Set.univ} = S := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true, S]
  calc
    (∫⁻ t, regressionShiftMass R r t ∂gaussianReal 0 1) =
        ∫⁻ t in Set.univ, ν {y | y + t • regressionSlope R ∈ C}
          ∂gaussianReal 0 1 := by
      simp only [Measure.restrict_univ, regressionShiftMass, ν, μ, C]
    _ = ν.prod (gaussianReal 0 1)
        {p | p.1 + p.2 • regressionSlope R ∈ C ∧ p.2 ∈ Set.univ} := by
      exact (prod_shift_inter_eq_setLIntegral ν (gaussianReal 0 1)
        (measurableSet_symmetricRectanglePi _) (regressionSlope R)
        MeasurableSet.univ).symm
    _ = ν.prod (gaussianReal 0 1) S := by rw [hSuniv]
    _ = Measure.map J μ S := by
      simpa only [μ, ν, J] using congrArg
        (fun m : Measure ((Fin n → ℝ) × ℝ) ↦ m S)
        (map_regressionResidual_last_eq_prod hR hdiag).symm
    _ = μ (J ⁻¹' S) := Measure.map_apply hJ hS
    _ = μ (firstCoordCLM ⁻¹' symmetricRectangle r) := by rw [hpre]
    _ = Measure.map firstCoordCLM μ (symmetricRectangle r) :=
      (Measure.map_apply firstCoordCLM.measurable
        (measurableSet_symmetricRectangle r)).symm
    _ = multivariateGaussian (0 : Coord n)
        (R.submatrix Fin.castSucc Fin.castSucc) (symmetricRectangle r) := by
      simpa only [μ] using congrArg
        (fun m : Measure (Coord n) ↦ m (symmetricRectangle r))
        (map_firstCoord_multivariateGaussian_zero hR)

private theorem measure_mul_lintegral_le_setLIntegral_of_threshold
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) {q : α → ℝ≥0∞} (hq : Measurable q)
    {c : ℝ≥0∞} (hinside : ∀ x ∈ A, c ≤ q x)
    (houtside : ∀ x ∉ A, q x ≤ c) :
    μ A * (∫⁻ x, q x ∂μ) ≤ ∫⁻ x in A, q x ∂μ := by
  have hI : c * μ A ≤ ∫⁻ x in A, q x ∂μ := by
    simpa using setLIntegral_mono hq hinside
  have hJ : (∫⁻ x in Aᶜ, q x ∂μ) ≤ c * μ Aᶜ := by
    simpa using setLIntegral_mono measurable_const
      (fun x hx ↦ houtside x (by simpa using hx))
  rw [← lintegral_add_compl q hA]
  calc
    μ A * ((∫⁻ x in A, q x ∂μ) + ∫⁻ x in Aᶜ, q x ∂μ) =
        μ A * (∫⁻ x in A, q x ∂μ) + μ A * (∫⁻ x in Aᶜ, q x ∂μ) :=
      mul_add _ _ _
    _ ≤ μ A * (∫⁻ x in A, q x ∂μ) + μ A * (c * μ Aᶜ) := by
      gcongr
    _ = μ A * (∫⁻ x in A, q x ∂μ) + (c * μ A) * μ Aᶜ := by
      ac_rfl
    _ ≤ μ A * (∫⁻ x in A, q x ∂μ) + (∫⁻ x in A, q x ∂μ) * μ Aᶜ := by
      gcongr
    _ = (∫⁻ x in A, q x ∂μ) * (μ A + μ Aᶜ) := by
      rw [mul_add]
      ac_rfl
    _ = ∫⁻ x in A, q x ∂μ := by
      rw [measure_add_measure_compl hA, measure_univ, mul_one]

private theorem antitoneOn_nonneg_of_even_logConcave
    {q : ℝ → ℝ≥0∞} (hq : IsLogConcave q) (heven : ∀ x, q (-x) = q x) :
    AntitoneOn q (Set.Ici 0) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simp [hxy']
  have hxy_strict : x < y := lt_of_le_of_ne hxy hxy'
  have hy_pos : 0 < y := lt_of_le_of_lt hx hxy_strict
  let a : ℝ := (1 + x / y) / 2
  have hratio_nonneg : 0 ≤ x / y := div_nonneg hx hy_pos.le
  have hratio_lt : x / y < 1 := (div_lt_one hy_pos).mpr hxy_strict
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_lt : a < 1 := by
    dsimp [a]
    linarith
  have hcomb : a • y + (1 - a) • (-y) = x := by
    dsimp [a]
    field_simp [ne_of_gt hy_pos]
    all_goals ring
  have h := hq ha_pos ha_lt y (-y)
  rw [heven] at h
  have hpow : q y ^ a * q y ^ (1 - a) = q y := by
    rw [← ENNReal.rpow_add_of_nonneg a (1 - a) ha_pos.le (sub_nonneg.mpr ha_lt.le)]
    norm_num
  rw [hpow, hcomb] at h
  exact h

private theorem measure_Icc_mul_lintegral_le_setLIntegral_of_even_logConcave
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ → ℝ≥0∞}
    (hq_meas : Measurable q) (hq_lc : IsLogConcave q)
    (hq_even : ∀ x, q (-x) = q x) {r : ℝ} (hr : 0 ≤ r) :
    μ (Set.Icc (-r) r) * (∫⁻ x, q x ∂μ) ≤
      ∫⁻ x in Set.Icc (-r) r, q x ∂μ := by
  have hanti := antitoneOn_nonneg_of_even_logConcave hq_lc hq_even
  have habs (x : ℝ) : q |x| = q x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos (le_of_not_ge hx), hq_even]
  apply measure_mul_lintegral_le_setLIntegral_of_threshold μ measurableSet_Icc hq_meas
    (c := q r)
  · intro x hx
    rw [← habs x]
    exact hanti (abs_nonneg x) hr ((abs_le).2 hx)
  · intro x hx
    rw [← habs x]
    have hnot : ¬ |x| ≤ r := fun h ↦ hx ((abs_le).1 h)
    exact hanti hr (abs_nonneg x) (lt_of_not_ge hnot).le

private theorem symmetricRectangle_step
    {n : ℕ} {R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (r : Fin (n + 1) → ℝ) (hrlast : 0 ≤ r (Fin.last n))
    (hpi : Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      (volume : Measure (Fin (n + 1) → ℝ)).withDensity piGaussianDensity) :
    gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
        multivariateGaussian (0 : Coord n) (R.submatrix Fin.castSucc Fin.castSucc)
          (symmetricRectangle (fun i ↦ r (Fin.castSucc i))) ≤
      multivariateGaussian (0 : Coord (n + 1)) R (symmetricRectangle r) := by
  let q := regressionShiftMass R (fun i ↦ r (Fin.castSucc i))
  have hq := measurable_isLogConcave_regressionShiftMass R
    (fun i ↦ r (Fin.castSucc i)) hpi
  have hineq := measure_Icc_mul_lintegral_le_setLIntegral_of_even_logConcave
    (gaussianReal 0 1) hq.1 hq.2
      (regressionShiftMass_even R (fun i ↦ r (Fin.castSucc i)) hpi) hrlast
  change gaussianReal 0 1 (Set.Icc (-r (Fin.last n)) (r (Fin.last n))) *
      (∫⁻ t, q t ∂gaussianReal 0 1) ≤
        ∫⁻ t in Set.Icc (-r (Fin.last n)) (r (Fin.last n)),
          q t ∂gaussianReal 0 1 at hineq
  rw [lintegral_regressionShiftMass_eq_marginal_symmetricRectangle hR hdiag] at hineq
  rw [← multivariateGaussian_symmetricRectangle_eq_setLIntegral_regressionShiftMass
    hR hdiag r] at hineq
  exact hineq

/-- The product Gaussian measure on `Fin k → ℝ` has the product-pdf density. -/
private theorem pi_gaussianReal_eq_withDensity_piGaussianDensity (k : ℕ) :
    Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity piGaussianDensity := by
  change Measure.pi (fun _ : Fin k ↦ gaussianReal 0 1) =
    (volume : Measure (Fin k → ℝ)).withDensity (fun x ↦ ∏ i, gaussianPDF 0 1 (x i))
  exact WeakSimplex.Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity

/-- Strict form of the threshold inequality: if `q ≥ c` on `A`, `q ≤ c` off `A`, and `q`
differs from `c` on a set of positive measure, then `μ A * ∫ q < ∫_A q`. -/
private theorem measure_mul_lintegral_lt_setLIntegral_of_threshold
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) {q : α → ℝ≥0∞} (hq : Measurable q)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hinside : ∀ x ∈ A, c ≤ q x) (houtside : ∀ x ∉ A, q x ≤ c)
    (hfin : ∫⁻ x, q x ∂μ ≠ ∞) (hA0 : μ A ≠ 0) (hAc0 : μ Aᶜ ≠ 0)
    (hstrict : μ (A ∩ {x | c < q x}) ≠ 0 ∨ μ (Aᶜ ∩ {x | q x < c}) ≠ 0) :
    μ A * (∫⁻ x, q x ∂μ) < ∫⁻ x in A, q x ∂μ := by
  have ha : ∫⁻ x in A, q x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
  have hI : c * μ A ≤ ∫⁻ x in A, q x ∂μ := by
    simpa using setLIntegral_mono hq hinside
  have hJ : (∫⁻ x in Aᶜ, q x ∂μ) ≤ c * μ Aᶜ := by
    simpa using setLIntegral_mono measurable_const
      (fun x hx ↦ houtside x (by simpa using hx))
  have hμA : μ A ≠ ∞ := measure_ne_top _ _
  have hμAc : μ Aᶜ ≠ ∞ := measure_ne_top _ _
  have key : μ A * (∫⁻ x in Aᶜ, q x ∂μ) < (∫⁻ x in A, q x ∂μ) * μ Aᶜ := by
    rcases hstrict with h | h
    · have h1 : c * μ A < ∫⁻ x in A, q x ∂μ := by
        have := lintegral_strict_mono_of_ae_le_of_ae_lt_on (μ := μ.restrict A)
          (f := fun _ ↦ c) (g := q) hq.aemeasurable (by simp [lintegral_const, hc, hμA,
            ENNReal.mul_eq_top])
          ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall hinside))
          (s := {x | c < q x}) (by rwa [Measure.restrict_apply' hA, Set.inter_comm])
          (Filter.Eventually.of_forall fun x hx ↦ hx)
        simpa [lintegral_const] using this
      calc μ A * (∫⁻ x in Aᶜ, q x ∂μ) ≤ μ A * (c * μ Aᶜ) := by gcongr
        _ = (c * μ A) * μ Aᶜ := by ring
        _ < (∫⁻ x in A, q x ∂μ) * μ Aᶜ := (ENNReal.mul_lt_mul_iff_left hAc0 hμAc).2 h1
    · have h1 : (∫⁻ x in Aᶜ, q x ∂μ) < c * μ Aᶜ := by
        have := lintegral_strict_mono_of_ae_le_of_ae_lt_on (μ := μ.restrict Aᶜ)
          (f := q) (g := fun _ ↦ c) measurable_const.aemeasurable
          (ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _))
          ((ae_restrict_iff' hA.compl).2 (Filter.Eventually.of_forall houtside))
          (s := {x | q x < c}) (by rwa [Measure.restrict_apply' hA.compl, Set.inter_comm])
          (Filter.Eventually.of_forall fun x hx ↦ hx)
        simpa [lintegral_const] using this
      calc μ A * (∫⁻ x in Aᶜ, q x ∂μ) < μ A * (c * μ Aᶜ) :=
            (ENNReal.mul_lt_mul_iff_right hA0 hμA).2 h1
        _ = (c * μ A) * μ Aᶜ := by ring
        _ ≤ (∫⁻ x in A, q x ∂μ) * μ Aᶜ := by gcongr
  rw [← lintegral_add_compl q hA, mul_add]
  calc μ A * (∫⁻ x in A, q x ∂μ) + μ A * (∫⁻ x in Aᶜ, q x ∂μ)
      < μ A * (∫⁻ x in A, q x ∂μ) + (∫⁻ x in A, q x ∂μ) * μ Aᶜ :=
        ENNReal.add_lt_add_left (ENNReal.mul_ne_top hμA ha) key
    _ = (∫⁻ x in A, q x ∂μ) * (μ A + μ Aᶜ) := by rw [mul_add]; ac_rfl
    _ = ∫⁻ x in A, q x ∂μ := by rw [measure_add_measure_compl hA, measure_univ, mul_one]

/-- Coordinate selection `x ↦ (x (f a))ₐ` as a continuous linear map. -/
private def selectCLM {k m : ℕ} (f : Fin k → Fin m) : Coord m →L[ℝ] Coord k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦ EuclideanSpace.proj (f a))

@[simp]
private theorem selectCLM_apply {k m : ℕ} (f : Fin k → Fin m) (x : Coord m) (a : Fin k) :
    selectCLM f x a = x (f a) :=
  rfl

/-- The image of a centered Gaussian under a coordinate selection is the Gaussian with the
corresponding principal submatrix as covariance. -/
private theorem map_selectCLM_multivariateGaussian_zero
    {k m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosSemidef) (f : Fin k → Fin m) :
    Measure.map (selectCLM f) (multivariateGaussian (0 : Coord m) R) =
      multivariateGaussian (0 : Coord k) (R.submatrix f f) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
    · simp
    · exact IsGaussian.integrable_id (μ := multivariateGaussian (0 : Coord m) R)
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hi : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis i) u) ∘
        selectCLM f = fun u : Coord m ↦ u (f i) := by
      ext u
      simp [PiLp.inner_apply]
    have hj : (fun u ↦ inner ℝ ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis j) u) ∘
        selectCLM f = fun u : Coord m ↦ u (f j) := by
      ext u
      simp [PiLp.inner_apply]
    rw [hi, hj, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix f)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

/-- Relabelling the coordinates by a permutation leaves rectangle probabilities unchanged. -/
private theorem multivariateGaussian_symmetricRectangle_perm
    {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : R.PosSemidef) (σ : Equiv.Perm (Fin m))
    (r : Fin m → ℝ) :
    multivariateGaussian (0 : Coord m) (R.submatrix σ σ) (symmetricRectangle (r ∘ σ)) =
      multivariateGaussian (0 : Coord m) R (symmetricRectangle r) := by
  rw [← map_selectCLM_multivariateGaussian_zero hR σ,
    Measure.map_apply (selectCLM σ).measurable (measurableSet_symmetricRectangle _)]
  congr 1
  ext x
  simp only [Set.mem_preimage, symmetricRectangle, Set.mem_setOf_eq, selectCLM_apply,
    Function.comp_apply]
  exact ⟨fun h k ↦ by simpa using h (σ.symm k), fun h i ↦ h (σ i)⟩

/-- A positive-volume set has positive standard Gaussian measure. -/
private theorem gaussianReal_ne_zero_of_volume_ne_zero {S : Set ℝ} (h : volume S ≠ 0) :
    gaussianReal 0 1 S ≠ 0 := fun h0 ↦
  h (gaussianReal_absolutelyContinuous' 0 (one_ne_zero (α := NNReal)) h0)

/-- The conditional-shift mass of a `2 × 2` correlation matrix is a centered one-dimensional
Gaussian measure of a shifted interval. -/
private theorem regressionShiftMass_pair_eq
    {R : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ} (r' : Fin 1 → ℝ) :
    ∃ v : NNReal, ∀ t : ℝ, regressionShiftMass R r' t =
      gaussianReal 0 v
        {z | z + t * R (Fin.castSucc 0) (Fin.last 1) ∈ Set.Icc (-r' 0) (r' 0)} := by
  let μ := multivariateGaussian (0 : Coord (1 + 1)) R
  let L : Coord (1 + 1) →L[ℝ] ℝ :=
    EuclideanSpace.proj (Fin.castSucc 0) -
      R (Fin.castSucc 0) (Fin.last 1) • EuclideanSpace.proj (Fin.last 1)
  have hId : HasGaussianLaw (id : Coord (1 + 1) → Coord (1 + 1)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hL := (hId.map L).map_eq_gaussianReal
  have hmean : μ[L ∘ id] = 0 := by
    have h1 : μ[L ∘ id] = ∫ x, L x ∂μ := rfl
    have h2 : ∫ x : Coord (1 + 1), x ∂μ = 0 := integral_id_multivariateGaussian
    have h3 : ∫ x, L x ∂μ = L (∫ x : Coord (1 + 1), x ∂μ) := by
      simpa using L.integral_comp_comm (μ := μ) (φ := id) hId.integrable
    rw [h1, h3, h2]
    simp
  rw [hmean] at hL
  refine ⟨Var[L; μ].toNNReal, fun t ↦ ?_⟩
  have hmeasS : MeasurableSet
      {z : ℝ | z + t * R (Fin.castSucc 0) (Fin.last 1) ∈ Set.Icc (-r' 0) (r' 0)} :=
    measurableSet_Icc.preimage (by fun_prop)
  have hmeasT : MeasurableSet
      {y : Fin 1 → ℝ | y + t • regressionSlope R ∈ symmetricRectanglePi r'} :=
    (measurableSet_symmetricRectanglePi r').preimage (by fun_prop)
  rw [Function.comp_id] at hL
  rw [← hL, Measure.map_apply L.measurable hmeasS, regressionShiftMass,
    Measure.map_apply (regressionResidualCLM R).measurable hmeasT]
  congr 1
  ext x
  simp [regressionResidualCLM, symmetricRectanglePi, regressionSlope, Fin.forall_fin_one, L]

/-- An interval of positive length has positive Lebesgue measure. -/
private theorem volume_Icc_ne_zero' {a b : ℝ} (h : a < b) : volume (Set.Icc a b) ≠ 0 := by
  simp [Real.volume_Icc, h]

/-- Every centered Gaussian charges every interval around the origin. -/
private theorem gaussianReal_Icc_ne_zero (v : NNReal) {ε : ℝ} (hε : 0 < ε) :
    gaussianReal 0 v (Set.Icc (-ε) ε) ≠ 0 := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, Measure.dirac_apply' _ measurableSet_Icc]
    simp [Set.indicator, hε.le]
  · intro h0
    exact volume_Icc_ne_zero' (by linarith : -ε < ε)
      (gaussianReal_absolutelyContinuous' 0 hv h0)

/-- The tails of a finite measure on `ℝ` vanish. -/
private theorem exists_measure_abs_gt_lt (ν : Measure ℝ) [IsFiniteMeasure ν] {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ M : ℝ, ν {y | M < |y|} < ε := by
  let s : ℕ → Set ℝ := fun n ↦ {y | (n : ℝ) < |y|}
  have hs : ∀ n, MeasurableSet (s n) := fun n ↦
    measurableSet_lt measurable_const (by fun_prop)
  have hanti : Antitone s := fun m n hmn y (hy : (n : ℝ) < |y|) ↦
    show (m : ℝ) < |y| from lt_of_le_of_lt (by exact_mod_cast hmn) hy
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n ↦ (hs n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ n, s n) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, not_lt, s,
      Set.mem_setOf_eq]
    obtain ⟨n, hn⟩ := exists_nat_ge |y|
    exact ⟨n, hn⟩
  rw [hinter, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, hn⟩

/-- The marginal rectangle probability of a one-coordinate unit-variance Gaussian. -/
private theorem multivariateGaussian_fin_one_rect {R : Matrix (Fin 1) (Fin 1) ℝ}
    (hR : R.PosSemidef) (hdiag : R 0 0 = 1) (r' : Fin 1 → ℝ) :
    multivariateGaussian (0 : Coord 1) R (symmetricRectangle r') =
      gaussianReal 0 1 (Set.Icc (-r' 0) (r' 0)) := by
  have h := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord 1)) hR (i := (0 : Fin 1))).map_eq
  simp only [hdiag, PiLp.zero_apply, Real.toNNReal_one] at h
  rw [← h, Measure.map_apply (by fun_prop) measurableSet_Icc]
  congr 1
  ext x
  simp [symmetricRectangle, Fin.forall_fin_one]

/-- Strict bivariate inequality: a `2 × 2` correlation matrix with nonzero off-diagonal entry
(singular or not) gives a strictly larger rectangle probability than independence. -/
private theorem pair_rectangle_gt
    {R : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ} (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (h01 : R 0 1 ≠ 0) (r : Fin (1 + 1) → ℝ) (hr : ∀ i, 0 < r i) :
    gaussianReal 0 1 (Set.Icc (-r 0) (r 0)) * gaussianReal 0 1 (Set.Icc (-r 1) (r 1)) <
      multivariateGaussian (0 : Coord (1 + 1)) R (symmetricRectangle r) := by
  have hpi := pi_gaussianReal_eq_withDensity_piGaussianDensity (1 + 1)
  let r' : Fin 1 → ℝ := fun i ↦ r (Fin.castSucc i)
  let q := regressionShiftMass R r'
  let ρ : ℝ := R (Fin.castSucc 0) (Fin.last 1)
  have hρ : ρ ≠ 0 := h01
  have ha0 : 0 < r' 0 := hr _
  have hs : 0 < r (Fin.last 1) := hr _
  have hq := measurable_isLogConcave_regressionShiftMass R r' hpi
  have heven := regressionShiftMass_even R r' hpi
  have hanti : AntitoneOn q (Set.Ici 0) := antitoneOn_nonneg_of_even_logConcave hq.2 heven
  have habs (x : ℝ) : q |x| = q x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      exact heven x
  have hμ := multivariateGaussian_symmetricRectangle_eq_setLIntegral_regressionShiftMass
    hR hdiag r
  have hmarg := lintegral_regressionShiftMass_eq_marginal_symmetricRectangle hR hdiag r'
  have hR' : (R.submatrix Fin.castSucc Fin.castSucc).PosSemidef :=
    hR.submatrix Fin.castSucc
  rw [multivariateGaussian_fin_one_rect hR' (hdiag _) r'] at hmarg
  obtain ⟨v, hv⟩ := regressionShiftMass_pair_eq (R := R) r'
  have hqG : ∀ t, q t = gaussianReal 0 v {z | z + t * ρ ∈ Set.Icc (-r' 0) (r' 0)} := hv
  -- the threshold
  set s := r (Fin.last 1) with hs_def
  let A : Set ℝ := Set.Icc (-s) s
  have hA : MeasurableSet A := measurableSet_Icc
  have hAc : Aᶜ ⊇ Set.Ioi s := fun x hx h ↦ not_lt.2 h.2 hx
  have hinside : ∀ x ∈ A, q s ≤ q x := fun x hx ↦ by
    rw [← habs x]
    exact hanti (abs_nonneg x) hs.le ((abs_le).2 hx)
  have houtside : ∀ x ∉ A, q x ≤ q s := fun x hx ↦ by
    rw [← habs x]
    have hnot : ¬ |x| ≤ s := fun h ↦ hx ((abs_le).1 h)
    exact hanti hs.le (abs_nonneg x) (lt_of_not_ge hnot).le
  -- positive measure of a witness set
  have hκ : 0 < gaussianReal 0 v (Set.Icc (-(r' 0 / 2)) (r' 0 / 2)) :=
    pos_iff_ne_zero.2 (gaussianReal_Icc_ne_zero v (by linarith))
  obtain ⟨M, hM⟩ := exists_measure_abs_gt_lt (gaussianReal 0 v) hκ
  have hρabs : 0 < |ρ| := abs_pos.2 hρ
  let T : ℝ := (M + r' 0 + 1) / |ρ|
  have hqtail : ∀ t, T < t → q t < gaussianReal 0 v (Set.Icc (-(r' 0 / 2)) (r' 0 / 2)) := by
    intro t ht
    refine lt_of_le_of_lt ?_ hM
    rw [hqG]
    apply measure_mono
    intro z hz
    have hz' : |z + t * ρ| ≤ r' 0 := abs_le.2 hz
    have h1 : |t * ρ| ≤ |z| + r' 0 := by
      calc |t * ρ| = |(z + t * ρ) - z| := by ring_nf
        _ ≤ |z + t * ρ| + |z| := abs_sub _ _
        _ ≤ |z| + r' 0 := by linarith
    have h2 : M + r' 0 + 1 < t * |ρ| := by
      have := (div_lt_iff₀ hρabs).1 ht
      linarith
    have h3 : t * |ρ| ≤ |t * ρ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (le_abs_self t) (abs_nonneg ρ)
    show M < |z|
    linarith
  have hc : q s ≠ ∞ := by
    rw [hqG]
    exact measure_ne_top _ _
  have hfin : ∫⁻ x, q x ∂gaussianReal 0 1 ≠ ∞ := by
    rw [hmarg]
    exact measure_ne_top _ _
  have hA0 : gaussianReal 0 1 A ≠ 0 :=
    gaussianReal_ne_zero_of_volume_ne_zero (volume_Icc_ne_zero' (by linarith))
  have hIoi : ∀ w : ℝ, gaussianReal 0 1 (Set.Ioi w) ≠ 0 := fun w ↦
    gaussianReal_ne_zero_of_volume_ne_zero (by simp)
  have hAc0 : gaussianReal 0 1 Aᶜ ≠ 0 := fun h0 ↦ hIoi s (measure_mono_null hAc h0)
  have hstrict : gaussianReal 0 1 (A ∩ {x | q s < q x}) ≠ 0 ∨
      gaussianReal 0 1 (Aᶜ ∩ {x | q x < q s}) ≠ 0 := by
    by_cases hlt : q s < gaussianReal 0 v (Set.Icc (-(r' 0 / 2)) (r' 0 / 2))
    · left
      let u : ℝ := min s (r' 0 / (2 * |ρ|))
      have hu : 0 < u := lt_min hs (by positivity)
      intro h0
      refine gaussianReal_ne_zero_of_volume_ne_zero
        (volume_Icc_ne_zero' (by linarith : -u < u)) (measure_mono_null ?_ h0)
      intro x hx
      have hxu : |x| ≤ u := abs_le.2 hx
      refine ⟨abs_le.1 (hxu.trans (min_le_left _ _)), ?_⟩
      show q s < q x
      refine lt_of_lt_of_le hlt ?_
      rw [hqG]
      apply measure_mono
      intro z hz
      have hz' : |z| ≤ r' 0 / 2 := abs_le.2 hz
      have hxρ : |x| * |ρ| ≤ r' 0 / 2 := by
        have h1 : |x| ≤ r' 0 / (2 * |ρ|) := hxu.trans (min_le_right _ _)
        have := (le_div_iff₀ (by positivity : 0 < 2 * |ρ|)).1 h1
        linarith
      show z + x * ρ ∈ Set.Icc (-r' 0) (r' 0)
      have : |z + x * ρ| ≤ r' 0 := by
        calc |z + x * ρ| ≤ |z| + |x * ρ| := abs_add_le _ _
          _ ≤ r' 0 := by rw [abs_mul]; linarith
      exact abs_le.1 this
    · right
      push Not at hlt
      intro h0
      refine hIoi (max s T) (measure_mono_null ?_ h0)
      intro x hx
      have hx1 : s < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hx2 : T < x := lt_of_le_of_lt (le_max_right _ _) hx
      refine ⟨fun h ↦ not_lt.2 h.2 hx1, ?_⟩
      exact lt_of_lt_of_le (hqtail x hx2) hlt
  have key := measure_mul_lintegral_lt_setLIntegral_of_threshold (gaussianReal 0 1) hA hq.1
    hc hinside houtside hfin hA0 hAc0 hstrict
  rw [hmarg] at key
  rw [mul_comm]
  rw [hμ]
  exact key

/-- The product of the standard Gaussian slab masses over the coordinates of index at least
two; the first two coordinates are the pair block treated separately. -/
private def tailProd {m : ℕ} (r : Fin m → ℝ) : ℝ≥0∞ :=
  ∏ k : Fin m, if 2 ≤ k.val then gaussianReal 0 1 (Set.Icc (-r k) (r k)) else 1

/-- Šidák peeling for a pair block: the rectangle probability dominates the probability of the
first two slabs times the independent masses of all remaining slabs. Valid for singular
covariance, since the one-coordinate peeling step needs only positive semidefiniteness. -/
private theorem block_peel {m : ℕ} (hm : 2 ≤ m) (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) :
    multivariateGaussian (0 : Coord 2) (R.submatrix (Fin.castLE hm) (Fin.castLE hm))
        (symmetricRectangle (r ∘ Fin.castLE hm)) * tailProd r ≤
      multivariateGaussian (0 : Coord m) R (symmetricRectangle r) := by
  induction m, hm using Nat.le_induction with
  | base =>
      have he : (Fin.castLE (le_refl 2) : Fin 2 → Fin 2) = id := funext fun a ↦ Fin.ext rfl
      have h1 : tailProd r = 1 :=
        Finset.prod_eq_one fun k _ ↦ if_neg (by have := k.isLt; omega)
      rw [he, h1, mul_one]
      simp
  | succ m hm ih =>
      let R' := R.submatrix Fin.castSucc Fin.castSucc
      let r' : Fin m → ℝ := fun i ↦ r (Fin.castSucc i)
      have hR' : R'.PosSemidef := hR.submatrix Fin.castSucc
      have hind := ih R' hR' (fun i ↦ hdiag _) r' (fun i ↦ hr _)
      have hstep := symmetricRectangle_step hR hdiag r (hr (Fin.last m))
        (pi_gaussianReal_eq_withDensity_piGaussianDensity (m + 1))
      have he : (Fin.castLE (hm.trans (Nat.le_succ m)) : Fin 2 → Fin (m + 1)) =
          Fin.castSucc ∘ Fin.castLE hm := funext fun a ↦ Fin.ext rfl
      have hprod : tailProd r = tailProd r' *
          gaussianReal 0 1 (Set.Icc (-r (Fin.last m)) (r (Fin.last m))) := by
        unfold tailProd
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_last, Fin.val_castSucc, hm, if_true, r']
        rfl
      rw [he, hprod]
      calc multivariateGaussian (0 : Coord 2)
              (R.submatrix (Fin.castSucc ∘ Fin.castLE hm) (Fin.castSucc ∘ Fin.castLE hm))
              (symmetricRectangle (r ∘ (Fin.castSucc ∘ Fin.castLE hm))) *
            (tailProd r' * gaussianReal 0 1 (Set.Icc (-r (Fin.last m)) (r (Fin.last m))))
          = gaussianReal 0 1 (Set.Icc (-r (Fin.last m)) (r (Fin.last m))) *
            (multivariateGaussian (0 : Coord 2)
              (R'.submatrix (Fin.castLE hm) (Fin.castLE hm))
              (symmetricRectangle (r' ∘ Fin.castLE hm)) * tailProd r') := by
            rw [mul_comm (tailProd r'), ← mul_assoc, mul_comm _ (gaussianReal 0 1 _), mul_assoc]
            rfl
        _ ≤ gaussianReal 0 1 (Set.Icc (-r (Fin.last m)) (r (Fin.last m))) *
            multivariateGaussian (0 : Coord m) R' (symmetricRectangle r') := by gcongr
        _ ≤ multivariateGaussian (0 : Coord (m + 1)) R (symmetricRectangle r) := hstep

/-- Splitting the full product of slab masses into the pair block of the first two coordinates
and the tail product. -/
private theorem prod_slab_eq_pair_mul_tailProd {m : ℕ} (hm : 2 ≤ m) (r : Fin m → ℝ) :
    (∏ k, gaussianReal 0 1 (Set.Icc (-r k) (r k))) =
      (gaussianReal 0 1 (Set.Icc (-r (Fin.castLE hm 0)) (r (Fin.castLE hm 0))) *
        gaussianReal 0 1 (Set.Icc (-r (Fin.castLE hm 1)) (r (Fin.castLE hm 1)))) *
        tailProd r := by
  set g : Fin m → ℝ≥0∞ := fun k ↦ gaussianReal 0 1 (Set.Icc (-r k) (r k)) with hg
  have hsplit : (∏ k, g k) = (∏ k : Fin m, if k.val < 2 then g k else 1) * tailProd r := by
    rw [tailProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    by_cases hk : k.val < 2
    · simp [hk, show ¬ 2 ≤ k.val by omega]
    · simp [hk, hg, show 2 ≤ k.val by omega]
  have hab : Fin.castLE hm 0 ≠ Fin.castLE hm 1 := fun h ↦ by
    have := congrArg Fin.val h
    simp at this
  have hfirst : (∏ k : Fin m, if k.val < 2 then g k else 1) =
      g (Fin.castLE hm 0) * g (Fin.castLE hm 1) := by
    have hmem : ∀ k : Fin m,
        k.val < 2 ↔ k ∈ ({Fin.castLE hm 0, Fin.castLE hm 1} : Finset (Fin m)) := by
      intro k
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE]
      simp only [Fin.val_zero, Fin.val_one]
      omega
    simp_rw [hmem]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pair hab]
  rw [hsplit, hfirst]

/-- A correlation matrix other than the identity has a nonzero off-diagonal entry. -/
private theorem exists_offDiag_ne_zero {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (hdiag : ∀ i, S i i = 1) (hne : S ≠ 1) : ∃ i j, i ≠ j ∧ S i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  · simp [Matrix.one_apply_ne hij, hcon i j hij]

/-- A permutation sending the first two coordinates to two prescribed distinct coordinates. -/
private theorem exists_perm_pair {m : ℕ} (hm : 2 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin m), σ (Fin.castLE hm 0) = i ∧ σ (Fin.castLE hm 1) = j := by
  set a : Fin m := Fin.castLE hm 0
  set b : Fin m := Fin.castLE hm 1
  have hab : a ≠ b := fun h ↦ by
    have := congrArg Fin.val h
    simp [a, b] at this
  refine ⟨Equiv.swap a i * Equiv.swap b (Equiv.swap a i j), ?_, ?_⟩
  · have h1 : Equiv.swap b (Equiv.swap a i j) a = a := by
      apply Equiv.swap_apply_of_ne_of_ne hab
      intro h
      apply hij
      have := congrArg (Equiv.swap a i) h
      simpa using this
    simp [h1]
  · simp

end Peel

/-- Lemma 1 (strict symmetric rectangle inequality). Singular `S` is allowed. -/
theorem symmetricRectangle_gt_iid
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsCorrelation S) (hne : S ≠ 1)
    (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) :
    (∏ i, gaussianReal 0 1 (Icc (-r i) (r i))) <
      multivariateGaussian (0 : Coord m) S (symmetricRectangle r) := by
  obtain ⟨i, j, hij, hSij⟩ := Peel.exists_offDiag_ne_zero S hS.2 hne
  have hm : 2 ≤ m := by
    have h1 := i.isLt
    have h2 := j.isLt
    have h3 : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    omega
  obtain ⟨σ, hσ0, hσ1⟩ := Peel.exists_perm_pair hm hij
  let T : Matrix (Fin m) (Fin m) ℝ := S.submatrix σ σ
  have hT : T.PosSemidef := hS.1.submatrix σ
  have hTdiag : ∀ k, T k k = 1 := fun k ↦ hS.2 _
  let rσ : Fin m → ℝ := r ∘ σ
  have hrσ : ∀ k, 0 ≤ rσ k := fun k ↦ (hr _).le
  have hpeel := Peel.block_peel hm T hT hTdiag rσ hrσ
  have hperm := Peel.multivariateGaussian_symmetricRectangle_perm hS.1 σ r
  have hprod : (∏ k, gaussianReal 0 1 (Icc (-r k) (r k))) =
      ∏ k, gaussianReal 0 1 (Icc (-rσ k) (rσ k)) :=
    (Equiv.prod_comp σ fun k ↦ gaussianReal 0 1 (Icc (-r k) (r k))).symm
  have hpair := Peel.pair_rectangle_gt
    (R := T.submatrix (Fin.castLE hm) (Fin.castLE hm)) (hT.submatrix _)
    (fun k ↦ hTdiag _) (by simpa [T, hσ0, hσ1] using hSij)
    (rσ ∘ Fin.castLE hm) (fun k ↦ hr _)
  have htail : Peel.tailProd rσ ≠ 0 ∧ Peel.tailProd rσ ≠ ∞ := by
    refine ⟨?_, ?_⟩
    · rw [Peel.tailProd, Finset.prod_ne_zero_iff]
      intro k _
      split_ifs
      · exact Peel.gaussianReal_Icc_ne_zero 1 (hr _) |>.elim
      · simp
    · rw [Peel.tailProd]
      exact ENNReal.prod_ne_top fun k _ ↦ by
        split_ifs <;> simp [measure_ne_top]
  rw [hprod, Peel.prod_slab_eq_pair_mul_tailProd hm rσ, ← hperm]
  refine lt_of_lt_of_le ?_ hpeel
  exact (ENNReal.mul_lt_mul_iff_left htail.1 htail.2).2 hpair

end SimplexUniqueness
