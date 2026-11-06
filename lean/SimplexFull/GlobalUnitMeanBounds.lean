import SimplexFull.GlobalNormalizationAlgebra
import SimplexFull.GlobalGaussianCDF
import SimplexFull.GlobalCentroidDecoderNormalization
import SimplexFull.GlobalMeanWidth
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Set WeakSimplex
namespace SimplexFull.GlobalTail
variable {m : ℕ} [NeZero m]

theorem meanGap_normalizedCovariance (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) :
    gaussianMaxMean (1 : Matrix (Fin m) (Fin m) ℝ) -
        gaussianMaxMean (normalizedCovariance G) =
      Real.sqrt (Geometry.alpha m) *
        (gaussianMaxMean (Geometry.simplexGram m)-gaussianMaxMean G) := by
  have hh := gaussianMaxMean_normalizedCovariance hm
    (Geometry.simplexGram m) (simplexGram_isCorrelation hm)
  rw [normalizedCovariance_simplexGram hm] at hh
  rw [hh, gaussianMaxMean_normalizedCovariance hm G hG, mul_sub]

def centroidMeanConstant (m : ℕ) : ℝ :=
  GlobalCentroid.eta m / Real.sqrt (Geometry.alpha m)

theorem centroidMeanConstant_pos (hm : 2 ≤ m) : 0 < centroidMeanConstant m :=
  div_pos (GlobalCentroid.eta_pos hm)
    (Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm))

theorem gaussianMaxMean_centroid_penalty (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G) :
    centroidMeanConstant m * Geometry.entrySum G ≤
      gaussianMaxMean (Geometry.simplexGram m)-gaussianMaxMean G := by
  have hs : 0 < Real.sqrt (Geometry.alpha m) :=
    Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm)
  have hh := gaussianMaxMean_gap_ge_of_thresholdDeficit
    (normalizedCovariance G) (normalizedCovariance_isWeakSimplexCov hm G hG)
    (mul_nonneg (GlobalCentroid.eta_pos hm).le (Geometry.global_entrySum_nonneg hG.1))
    (fun c hc => centroid_entrySum_penalty hm G hG hc)
  rw [meanGap_normalizedCovariance hm G hG] at hh
  unfold centroidMeanConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hh)

/-- Transfer of a concrete uniform covariance-defect window to a unit Gram bound.
The final global theorem instantiates this helper with the proved paper kappa. -/
theorem gaussianMaxMean_gram_penalty_of_thresholdDeficit (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : IsCorrelation G)
    {k : ℝ} (hk : 0 ≤ k)
    (hl : ∀ c ∈ Icc (0:ℝ) 1,
      k * Geometry.frobSq (normalizedCovariance G-1) ≤
        GlobalCentroid.thresholdDeficit (normalizedCovariance G) c) :
    (k*(Geometry.alpha m)^2 / Real.sqrt (Geometry.alpha m)) *
        Geometry.frobSq (G-Geometry.simplexGram m) ≤
      gaussianMaxMean (Geometry.simplexGram m)-gaussianMaxMean G := by
  have hs : 0 < Real.sqrt (Geometry.alpha m) :=
    Real.sqrt_pos.mpr (GlobalCentroid.alpha_pos hm)
  have hF : 0 ≤ Geometry.frobSq (normalizedCovariance G-1) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hh := gaussianMaxMean_gap_ge_of_thresholdDeficit
    (normalizedCovariance G) (normalizedCovariance_isWeakSimplexCov hm G hG)
    (mul_nonneg hk hF) hl
  rw [meanGap_normalizedCovariance hm G hG, frobSq_normalizedCovariance hm] at hh
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hh]

#print axioms meanGap_normalizedCovariance
#print axioms gaussianMaxMean_centroid_penalty
#print axioms gaussianMaxMean_gram_penalty_of_thresholdDeficit
end SimplexFull.GlobalTail
