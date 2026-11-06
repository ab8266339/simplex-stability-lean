import SimplexFull.GlobalMeanWidthBase
import SimplexFull.GlobalFoundationBridge
import SimplexFull.SignalSmooth
import WeakSimplexConjectureLean.Coding.Normalization
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SimplexFull.GlobalTail
variable {m : ℕ} [NeZero m]

def normalizedCovariance (G : Matrix (Fin m) (Fin m) ℝ) :=
  Geometry.alpha m • G + (m : ℝ)⁻¹ • Geometry.onesMatrix m

theorem normalizedCovariance_isWeakSimplexCov
    (hm : 2 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : WeakSimplex.IsCorrelation G) :
    WeakSimplex.IsWeakSimplexCov (normalizedCovariance G) := by
  have h := (WeakSimplex.gramNormalization (show 1 < m by omega) G hG).1
  simpa only [normalizedCovariance, Geometry.alpha, one_div,
    show WeakSimplex.allOnesMatrix m = Geometry.onesMatrix m from rfl] using h

theorem hasDerivAt_prefactored_mgf_zero (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t^2)/2) *
      mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) (multivariateGaussian 0 G) t)
      (gaussianMaxMean G) 0 := by
  have hmem : (0 : ℝ) ∈ interior
      (integrableExpSet (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
        (multivariateGaussian 0 G)) := by
    rw [integrableExpSet_maxCoord_eq_univ G hG, interior_univ]
    trivial
  have hmg : HasDerivAt
      (mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) (multivariateGaussian 0 G))
      (gaussianMaxMean G) 0 := by
    simpa [gaussianMaxMean] using hasDerivAt_mgf hmem
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(t^2)/2)) 0 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).pow 2).neg).div_const 2).exp using 1 <;> norm_num
  convert he.mul hmg using 1 <;> (first | rfl | simp)

theorem gaussianMaxMean_normalizedCovariance
    (hm : 2 ≤ m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : WeakSimplex.IsCorrelation G) :
    gaussianMaxMean (normalizedCovariance G) =
      Real.sqrt (Geometry.alpha m) * gaussianMaxMean G := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < Geometry.alpha m := by unfold Geometry.alpha; positivity
  have hs : Real.sqrt (Geometry.alpha m) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hR := normalizedCovariance_isWeakSimplexCov hm G hG
  have hdG := hasDerivAt_prefactored_mgf_zero G hG.1
  have hdR := hasDerivAt_prefactored_mgf_zero (normalizedCovariance G) hR.1.1
  have houter : HasDerivAt (fun t : ℝ => Real.exp (-(t^2)/2) *
      mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
        (multivariateGaussian 0 (normalizedCovariance G)) t)
      (gaussianMaxMean (normalizedCovariance G)) (0 / Real.sqrt (Geometry.alpha m)) := by
    simpa only [zero_div] using hdR
  have hcomp := houter.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt (Geometry.alpha m)))
  have heq : (fun t : ℝ => Real.exp (-(t^2)/2) *
      mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) (multivariateGaussian 0 G) t) =
      (fun t : ℝ => Real.exp (-((t / Real.sqrt (Geometry.alpha m))^2)/2) *
        mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
          (multivariateGaussian 0 (normalizedCovariance G)) (t / Real.sqrt (Geometry.alpha m))) := by
    funext t
    simpa only [GlobalFoundation.coordinateMax_eq_maxCoord, normalizedCovariance,
      Geometry.alpha, one_div, show WeakSimplex.allOnesMatrix m = Geometry.onesMatrix m from rfl] using
      WeakSimplex.gramMgf_normalization_identity (show 1 < m by omega) G hG t
  rw [heq] at hdG
  have hd := hdG.unique hcomp
  have hh : gaussianMaxMean G =
      gaussianMaxMean (normalizedCovariance G) / Real.sqrt (Geometry.alpha m) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using hd
  simpa only [mul_comm] using ((eq_div_iff hs).mp hh).symm

#print axioms normalizedCovariance_isWeakSimplexCov
#print axioms gaussianMaxMean_normalizedCovariance
end SimplexFull.GlobalTail
