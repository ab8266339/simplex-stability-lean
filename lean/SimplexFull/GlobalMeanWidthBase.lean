import SimplexFull.Decoder
import SimplexFull.GlobalRankBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section
open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace

namespace SimplexFull
variable {m : ℕ} [NeZero m]

/-- Actual expected largest coordinate of a centered multivariate Gaussian. -/
def gaussianMaxMean (G : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ x, maxCoord x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G

theorem norm_maxCoord_le (x : EuclideanSpace ℝ (Fin m)) :
    ‖maxCoord x‖ ≤ ‖x‖ := by
  obtain ⟨i,hi,hx⟩ := Finset.exists_mem_eq_sup' univNonempty (fun i => x i)
  have hmax : maxCoord x = x i := hx
  rw [hmax]
  exact PiLp.norm_apply_le x i

theorem integrable_maxCoord_mvg (G : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
      (multivariateGaussian 0 G) := by
  have hn : Integrable (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖)
      (multivariateGaussian 0 G) := IsGaussian.integrable_id.norm
  exact hn.mono' measurable_maxCoord.aestronglyMeasurable
    (ae_of_all _ norm_maxCoord_le)

namespace Geometry

/-- Actual expected Gaussian support function of a finite configuration. -/
def configGaussianMax {d : ℕ} (X : Config m d) : ℝ :=
  gaussianMaxMean (gram X)

theorem scoreMap_measurePreserving {d : ℕ} (X : Config m d) :
    MeasurePreserving (scoreMap X) (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (multivariateGaussian 0 (gram X)) := by
  refine ⟨(scoreMap X).continuous.measurable, ?_⟩
  exact gaussian_score_law X

theorem integrable_configGaussianMax {d : ℕ} (X : Config m d) :
    Integrable (fun z => maxCoord (scoreMap X z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (scoreMap_measurePreserving X).integrable_comp_of_integrable (integrable_maxCoord_mvg (gram X))

theorem configGaussianMax_eq_integral {d : ℕ} (X : Config m d) :
    configGaussianMax X =
      ∫ z, maxCoord (scoreMap X z) ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  unfold configGaussianMax gaussianMaxMean
  rw [← (scoreMap_measurePreserving X).map_eq]
  exact integral_map (by fun_prop) measurable_maxCoord.aestronglyMeasurable

omit [NeZero m] in
def gaussianRadiusMean (d : ℕ) : ℝ :=
  ∫ z, ‖z‖ ∂stdGaussian (EuclideanSpace ℝ (Fin d))

/-- The Gaussian formula for normalized mean width, with its actual ambient
Gaussian radial factor. -/
def normalizedGaussianWidth {d : ℕ} (X : Config m d) : ℝ :=
  2 * configGaussianMax X / gaussianRadiusMean d

theorem integrable_gaussianRadius (d : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  IsGaussian.integrable_id.norm

theorem gaussianRadiusMean_pos {d : ℕ} (hd : 1 ≤ d) :
    0 < gaussianRadiusMean d := by
  let i : Fin d := ⟨0, by omega⟩
  have hp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => x i)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) (gaussianReal 0 1) := by
    simpa using measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin d))) (Matrix.PosSemidef.one) (i := i)
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have he : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin d)), z i ≠ 0 :=
    hp.quasiMeasurePreserving.ae (by rw [ae_iff]; simp : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0)
  have hn : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin d)), 0 < ‖z‖ := he.mono (by
    intro z hz
    apply norm_pos_iff.mpr
    intro hzero
    apply hz
    simp [hzero])
  have hnonneg : 0 ≤ gaussianRadiusMean d := integral_nonneg (fun _ => norm_nonneg _)
  by_contra hnot
  have hzero : gaussianRadiusMean d = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hzeroae : (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) =ᵐ[
      stdGaussian (EuclideanSpace ℝ (Fin d))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) (integrable_gaussianRadius d)).mp hzero
  obtain ⟨z,hz,hz0⟩ := (hn.and hzeroae).exists
  exact (ne_of_gt hz) hz0

#print axioms integrable_configGaussianMax
#print axioms configGaussianMax_eq_integral
#print axioms gaussianRadiusMean_pos
end Geometry
#print axioms integrable_maxCoord_mvg
end SimplexFull
