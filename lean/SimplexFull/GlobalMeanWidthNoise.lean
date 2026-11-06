import SimplexFull.GlobalMeanWidthBase
import SimplexFull.GaussianShift

noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace
namespace SimplexFull

theorem map_add_eq_multivariateGaussian {m : ℕ}
    (G H : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) (hH : H.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) H)).map
        (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1+p.2) =
      multivariateGaussian 0 (G+H) := by
  haveI : IsProbabilityMeasure
      (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) H)).map
          (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1+p.2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hmul := integral_prod_mul
    (fun x : EuclideanSpace ℝ (Fin m) => Complex.exp (inner ℝ x t * Complex.I))
    (fun y : EuclideanSpace ℝ (Fin m) => Complex.exp (inner ℝ y t * Complex.I))
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G)
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) H)
  rw [hmul, ← charFun_apply, ← charFun_apply,
    charFun_centered G hG, charFun_centered H hH, charFun_centered (G+H) (hG.add hH),
    ← Complex.exp_add, dot_add_matrix]
  congr 1
  push_cast
  ring

variable {m : ℕ} [NeZero m]

theorem integrable_maxCoord_const_add (H : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin m) => maxCoord (x+y))
      (multivariateGaussian 0 H) := by
  have hn : Integrable (fun y : EuclideanSpace ℝ (Fin m) => ‖x‖+‖y‖)
      (multivariateGaussian 0 H) := (integrable_const _).add IsGaussian.integrable_id.norm
  apply hn.mono'
  · exact (continuous_maxCoord.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable
  · exact ae_of_all _ (fun y => (norm_maxCoord_le (x+y)).trans (norm_add_le x y))

theorem integrable_gaussian_coord (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosSemidef)
    (i : Fin m) :
    Integrable (fun y : EuclideanSpace ℝ (Fin m) => y i) (multivariateGaussian 0 H) := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin m))) hH (i := i)
  exact hp.integrable_comp_of_integrable IsGaussian.integrable_id

theorem integral_gaussian_coord_eq_zero (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosSemidef)
    (i : Fin m) :
    (∫ y : EuclideanSpace ℝ (Fin m), y i ∂multivariateGaussian 0 H) = 0 := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin m))) hH (i := i)
  calc
    (∫ y : EuclideanSpace ℝ (Fin m), y i ∂multivariateGaussian 0 H) =
        ∫ z : ℝ, z ∂(multivariateGaussian 0 H).map (fun y : EuclideanSpace ℝ (Fin m) => y i) := by
      exact (integral_map (f := fun z : ℝ => z) hp.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [hp.map_eq, integral_id_gaussianReal]; rfl

/-- Jensen's inequality for the finite maximum, proved by choosing an attained
maximum coordinate and using its actual zero Gaussian mean. -/
theorem maxCoord_le_integral_add_gaussian (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.PosSemidef) (x : EuclideanSpace ℝ (Fin m)) :
    maxCoord x ≤ ∫ y, maxCoord (x+y) ∂multivariateGaussian 0 H := by
  obtain ⟨i,hi,hx⟩ := Finset.exists_mem_eq_sup' univNonempty (fun i => x i)
  have hmax : maxCoord x = x i := hx
  have hcoord := (integrable_const (x i)).add (integrable_gaussian_coord H hH i)
  have hle : (∫ y : EuclideanSpace ℝ (Fin m), x i+y i ∂multivariateGaussian 0 H) ≤
      ∫ y, maxCoord (x+y) ∂multivariateGaussian 0 H := by
    apply integral_mono hcoord (integrable_maxCoord_const_add H x)
    intro y
    exact Finset.le_sup' (fun j => (x+y) j) (Finset.mem_univ i)
  rw [integral_add (integrable_const (x i)) (integrable_gaussian_coord H hH i),
    integral_const, integral_gaussian_coord_eq_zero H hH i] at hle
  simpa [hmax] using hle

theorem integrable_maxCoord_add_prod (G H : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (hH : H.PosSemidef) :
    Integrable (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      maxCoord (p.1+p.2))
      ((multivariateGaussian 0 G).prod (multivariateGaussian 0 H)) := by
  have hp : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => p.1+p.2)
      ((multivariateGaussian 0 G).prod (multivariateGaussian 0 H))
      (multivariateGaussian 0 (G+H)) :=
    ⟨by fun_prop, map_add_eq_multivariateGaussian G H hG hH⟩
  exact hp.integrable_comp_of_integrable (integrable_maxCoord_mvg (G+H))

/-- Adding any independent centered Gaussian covariance cannot decrease the
actual expected maximum. No abstract stochastic-order assumption is supplied. -/
theorem gaussianMaxMean_le_add (G H : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) (hH : H.PosSemidef) :
    gaussianMaxMean G ≤ gaussianMaxMean (G+H) := by
  have hp := integrable_maxCoord_add_prod G H hG hH
  have hiter : gaussianMaxMean (G+H) =
      ∫ x, ∫ y, maxCoord (x+y) ∂multivariateGaussian 0 H ∂multivariateGaussian 0 G := by
    unfold gaussianMaxMean
    rw [← map_add_eq_multivariateGaussian G H hG hH,
      integral_map (by fun_prop) measurable_maxCoord.aestronglyMeasurable]
    exact integral_prod _ hp
  rw [hiter]
  apply integral_mono (integrable_maxCoord_mvg G) hp.integral_prod_left
  exact maxCoord_le_integral_add_gaussian H hH

#print axioms map_add_eq_multivariateGaussian
#print axioms maxCoord_le_integral_add_gaussian
#print axioms gaussianMaxMean_le_add
end SimplexFull
