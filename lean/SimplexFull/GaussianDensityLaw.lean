import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension
import SimplexFull.GaussianDensity
import SimplexFull.GaussianDensityMatrix

/-!
# Gaussian density law

`stdGaussian` on `EuclideanSpace ℝ (Fin m)` is Lebesgue measure weighted by
`rho 1`. For positive definite `R`, `multivariateGaussian 0 R` is that measure
pushed forward by `toEuclideanCLM (CFC.sqrt R)`, which is Lebesgue measure
weighted by `rho R`.
-/

noncomputable section

open Classical MeasureTheory ProbabilityTheory Set WithLp ENNReal
open scoped BigOperators Real

namespace SimplexFull.Covariance

variable {m : ℕ}

/-- Pushing a density forward along a measurable equivalence composes the density
with the inverse equivalence. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (f : α → ℝ≥0∞) (μ : Measure α) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y ↦ f (e.symm y)) := by
  refine Measure.ext fun s hs ↦ ?_
  have hs' : MeasurableSet (e ⁻¹' s) := hs.preimage e.measurable_toFun
  rw [e.map_apply, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs,
    e.measurableEmbedding.lintegral_map]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : e a ∈ s
  · rw [indicator_of_mem ha, indicator_of_mem (show a ∈ e ⁻¹' s from ha),
      MeasurableEquiv.symm_apply_apply]
  · rw [indicator_of_notMem ha, indicator_of_notMem (show a ∉ e ⁻¹' s from ha)]

/-- The law of `m` i.i.d. standard real Gaussians is Lebesgue measure on `ℝᵐ` with
density `∏ gaussianPDF`. -/
theorem pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : Fin m ↦ gaussianReal (0 : ℝ) 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun y ↦ ∏ i, gaussianPDF 0 1 (y i)) := by
  let pdf : ℝ → ℝ := gaussianPDFReal 0 1
  have hpdf_nn : ∀ x, 0 ≤ pdf x := fun x ↦ gaussianPDFReal_nonneg 0 1 x
  have hpdf_int : Integrable pdf := integrable_gaussianPDFReal 0 1
  refine Measure.pi_eq fun s hs ↦ ?_
  have hrect : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind_int : ∀ i, Integrable ((s i).indicator pdf) := fun i ↦ hpdf_int.indicator (hs i)
  have hφ_int : Integrable (fun y : Fin m → ℝ ↦ ∏ i, (s i).indicator pdf (y i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hind_int
  have hφ_nn : 0 ≤ᵐ[volume] (fun y : Fin m → ℝ ↦ ∏ i, (s i).indicator pdf (y i)) :=
    ae_of_all _ fun y ↦ Finset.prod_nonneg fun i _ ↦
      indicator_nonneg (fun x _ ↦ hpdf_nn x) (y i)
  calc
    volume.withDensity (fun y ↦ ∏ i, gaussianPDF 0 1 (y i)) (Set.univ.pi s)
        = ∫⁻ y in Set.univ.pi s, ∏ i, gaussianPDF 0 1 (y i) ∂volume :=
      withDensity_apply _ hrect
    _ = ∫⁻ (y : Fin m → ℝ), ENNReal.ofReal (∏ i, (s i).indicator pdf (y i)) ∂volume := by
      rw [← lintegral_indicator hrect]
      refine lintegral_congr fun y ↦ ?_
      by_cases hy : y ∈ Set.univ.pi s
      · rw [indicator_of_mem hy]
        simp_rw [gaussianPDF, pdf]
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hpdf_nn (y i))]
        congr 1
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [indicator_of_mem ((mem_univ_pi.mp hy) i)]
      · rw [indicator_of_notMem hy]
        have hprod : ∏ i, (s i).indicator pdf (y i) = 0 := by
          simp only [mem_univ_pi, not_forall] at hy
          obtain ⟨i, hi⟩ := hy
          exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi pdf)
        rw [hprod, ofReal_zero]
    _ = ENNReal.ofReal (∫ (y : Fin m → ℝ), ∏ i, (s i).indicator pdf (y i) ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hφ_int hφ_nn).symm
    _ = ENNReal.ofReal (∏ i, ∫ x, (s i).indicator pdf x) := by
      rw [integral_fintype_prod_volume_eq_prod (fun i x ↦ (s i).indicator pdf x)]
    _ = ∏ i, ENNReal.ofReal (∫ x, (s i).indicator pdf x) := by
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro i _
      exact integral_nonneg fun x ↦ indicator_nonneg (fun z _ ↦ hpdf_nn z) x
    _ = ∏ i, ∫⁻ x, ENNReal.ofReal ((s i).indicator pdf x) ∂volume := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      exact ofReal_integral_eq_lintegral_ofReal (hind_int i)
        (ae_of_all _ fun x ↦ indicator_nonneg (fun z _ ↦ hpdf_nn z) x)
    _ = ∏ i, ∫⁻ x in s i, gaussianPDF 0 1 x ∂volume := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [← lintegral_indicator (hs i)]
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : x ∈ s i
      · rw [indicator_of_mem hx, indicator_of_mem hx, gaussianPDF]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, ofReal_zero]
    _ = ∏ i, gaussianReal 0 1 (s i) := by
      refine Finset.prod_congr rfl fun i _ ↦ (gaussianReal_apply 0 one_ne_zero (s i)).symm

/-- The standard Gaussian on Euclidean space is Lebesgue measure with density `rho 1`. -/
theorem stdGaussian_eq_withDensity_rho_one :
    stdGaussian (EuclideanSpace ℝ (Fin m)) =
      volume.withDensity (fun x : EuclideanSpace ℝ (Fin m) ↦
        ENNReal.ofReal (rho (1 : Matrix (Fin m) (Fin m) ℝ) x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity,
    (MeasurableEquiv.coe_toLp (p := 2) (X := Fin m → ℝ)).symm,
    map_withDensity_measurableEquiv (MeasurableEquiv.toLp 2 (Fin m → ℝ))]
  have hvol : Measure.map (⇑(MeasurableEquiv.toLp 2 (Fin m → ℝ)))
      (volume : Measure (Fin m → ℝ)) = (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    simpa [MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (Fin m)).map_eq
  rw [hvol]
  refine withDensity_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp_rw [MeasurableEquiv.coe_toLp_symm, gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ gaussianPDFReal_nonneg 0 1 _),
    rho_one_eq_prod_gaussianPDFReal]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- An invertible continuous linear endomorphism pushes a Haar density forward by the
absolute value of the inverse determinant. -/
theorem haar_withDensity_map_detNeZero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (L : E →L[ℝ] E) (hL : L.det ≠ 0) (f : E → ℝ≥0∞) :
    (μ.withDensity f).map L =
      μ.withDensity fun y ↦
        ENNReal.ofReal |(L.det)⁻¹| *
          f ((L.toContinuousLinearEquivOfDetNeZero hL).symm y) := by
  let eCLE := L.toContinuousLinearEquivOfDetNeZero hL
  let e : E ≃ᵐ E := eCLE.toHomeomorph.toMeasurableEquiv
  have hcoe : (e : E → E) = (L : E → E) := by
    ext x
    simp [e, eCLE, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  have hmapL : (μ.withDensity f).map L = (μ.withDensity f).map (e : E → E) := by
    rw [hcoe]
  rw [hmapL, map_withDensity_measurableEquiv]
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := by simpa using hL
  have hmap : μ.map (e : E → E) = ENNReal.ofReal |(L.det)⁻¹| • μ := by
    rw [hcoe]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [hmap, withDensity_smul_measure,
    ← withDensity_smul' (ENNReal.ofReal |(L.det)⁻¹|) (fun y ↦ f (e.symm y))
      ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, e, eCLE, Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.coe_symm_toHomeomorph]

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- The Euclidean representation preserves determinants. -/
lemma det_toEuclideanCLM (S : Matrix (Fin m) (Fin m) ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) S).det = S.det := by
  change LinearMap.det
      (Matrix.toEuclideanCLM (𝕜 := ℝ) S : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _) = S.det
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The inverse of `toEuclideanCLM S` is `toEuclideanCLM` of the matrix inverse. -/
lemma toEuclideanCLM_equiv_symm_apply (S : Matrix (Fin m) (Fin m) ℝ) (hS : IsUnit S.det)
    (hL : (Matrix.toEuclideanCLM (𝕜 := ℝ) S).det ≠ 0) (x : EuclideanSpace ℝ (Fin m)) :
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) S).toContinuousLinearEquivOfDetNeZero hL).symm x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ x := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) S
  have hmul : L * Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ = 1 := by
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) S from rfl, ← map_mul,
      Matrix.mul_nonsing_inv S hS, map_one]
  have happ : L (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ x) = x := by
    have hcomp : L ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ = ContinuousLinearMap.id ℝ _ := by
      rw [← ContinuousLinearMap.mul_def, hmul, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.rightInverse_of_comp hcomp x
  apply (L.toContinuousLinearEquivOfDetNeZero hL).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  exact happ.symm

/-- Centered nondegenerate Gaussian law on `EuclideanSpace` is Lebesgue measure with density `rho`. -/
theorem multivariateGaussian_eq_withDensity_rho (R : Matrix (Fin m) (Fin m) ℝ) (hR : R.PosDef) :
    multivariateGaussian 0 R =
      volume.withDensity (fun x : EuclideanSpace ℝ (Fin m) ↦ ENNReal.ofReal (rho R x)) := by
  let S : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt R
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) S
  have hSdet : S.det ≠ 0 := by
    rw [hR.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact (Real.sqrt_pos.2 hR.det_pos).ne'
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hLdet : L.det ≠ 0 := by
    unfold L
    rw [det_toEuclideanCLM]
    exact hSdet
  have hpush : (fun x : EuclideanSpace ℝ (Fin m) ↦ (0 : EuclideanSpace ℝ (Fin m)) + L x) =
      (L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) := by
    ext x
    rw [zero_add]
  rw [multivariateGaussian, hpush, stdGaussian_eq_withDensity_rho_one,
    haar_withDensity_map_detNeZero (volume : Measure (EuclideanSpace ℝ (Fin m))) L hLdet
      (fun x ↦ ENNReal.ofReal (rho (1 : Matrix (Fin m) (Fin m) ℝ) x))]
  refine withDensity_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hsymm : (L.toContinuousLinearEquivOfDetNeZero hLdet).symm x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ x := by
    unfold L
    exact toEuclideanCLM_equiv_symm_apply S hSunit hLdet x
  change ENNReal.ofReal |(L.det)⁻¹| * ENNReal.ofReal
      (rho (1 : Matrix (Fin m) (Fin m) ℝ)
        ((L.toContinuousLinearEquivOfDetNeZero hLdet).symm x)) =
    ENNReal.ofReal (rho R x)
  try dsimp only
  rw [hsymm, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [show L.det = S.det from by unfold L; exact det_toEuclideanCLM S, rho_inv_sqrt_transform R hR]

set_option pp.fullNames true
#print axioms map_withDensity_measurableEquiv
#print axioms pi_gaussianReal_eq_withDensity
#print axioms stdGaussian_eq_withDensity_rho_one
#print axioms haar_withDensity_map_detNeZero
#print axioms det_toEuclideanCLM
#print axioms toEuclideanCLM_equiv_symm_apply
#print axioms multivariateGaussian_eq_withDensity_rho

end SimplexFull.Covariance
