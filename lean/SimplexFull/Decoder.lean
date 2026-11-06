import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.Lattice
import SimplexFull.GeometryBase
import SimplexFull.GaussianMaps

/-!
Gaussian decoding objective `Pc(G, λ)` from `input/ANALYTIC_PROOF.md`, §11.1.

`maxCoord` is the finite coordinate maximum. `decodingSuccess G lam` is
`exp(-lam^2/2) / m * ∫ exp(lam * maxCoord x) ∂ multivariateGaussian 0 G`.
Integrability of the integrand, for every positive semidefinite covariance, is the
coordinate exponential moment of `gaussianReal`: the maximum is attained, so the
exponential is dominated by the sum of the coordinate exponentials.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace SimplexFull

variable {m : ℕ} [NeZero m]

lemma univNonempty : (univ : Finset (Fin m)).Nonempty :=
  univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (NeZero.pos m))

/-- Largest coordinate of a nonempty Euclidean vector. -/
def maxCoord (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  univ.sup' univNonempty fun i ↦ x i

theorem continuous_maxCoord : Continuous (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) := by
  unfold maxCoord
  exact Continuous.finset_sup'_apply univNonempty fun i _ ↦ by fun_prop

theorem measurable_maxCoord : Measurable (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ) :=
  continuous_maxCoord.measurable

/-- The coordinate maximum is attained, so `exp(λ * max)` is one summand of the
coordinate exponentials. This holds for every real `λ`. -/
theorem exp_mul_maxCoord_le_sum (lam : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Real.exp (lam * maxCoord x) ≤ ∑ i : Fin m, Real.exp (lam * x i) := by
  obtain ⟨i, hi, hx⟩ := exists_mem_eq_sup' univNonempty fun i ↦ x i
  have hmax : maxCoord x = x i := hx
  rw [hmax, ← add_sum_erase univ (fun j ↦ Real.exp (lam * x j)) hi]
  have hnn : 0 ≤ ∑ j ∈ univ.erase i, Real.exp (lam * x j) :=
    sum_nonneg fun _ _ ↦ (Real.exp_pos _).le
  linarith

omit [NeZero m] in
/-- Each coordinate of a centered multivariate Gaussian is a real Gaussian, so it has
an exponential moment. -/
theorem integrable_exp_mul_coord (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (lam : ℝ) (i : Fin m) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (lam * x i))
      (multivariateGaussian 0 G) := by
  have hmap := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin m)))
    hG (i := i)
  have hint := hmap.integrable_comp_of_integrable
    (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := (G i i).toNNReal) lam)
  simpa [Function.comp_def] using hint

/-- `x ↦ exp(λ * maxCoord x)` is integrable for every PSD covariance, by comparison
with the finite sum of coordinate exponential moments. -/
theorem integrable_exp_mul_maxCoord (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (lam : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (lam * maxCoord x))
      (multivariateGaussian 0 G) := by
  have hsum : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ ∑ i : Fin m, Real.exp (lam * x i))
      (multivariateGaussian 0 G) :=
    integrable_finsetSum univ fun i _ ↦ integrable_exp_mul_coord G hG lam i
  refine hsum.mono' ?_ ?_
  · exact (((continuous_maxCoord.measurable.const_mul lam).exp).aestronglyMeasurable)
  · refine ae_of_all _ fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_mul_maxCoord_le_sum lam x

/-- Maximum-likelihood success probability `Pc(G, λ)` of §11.1.
`ξ ∼ multivariateGaussian 0 G` and
`Pc(G, λ) = exp(-λ^2/2) / m * ∫ exp(λ * maxCoord x) ∂ξ`. -/
def decodingSuccess (G : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ) : ℝ :=
  Real.exp (-(lam ^ 2) / 2) / (m : ℝ) *
    ∫ x, Real.exp (lam * maxCoord x) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) G)

/-- Configuration Grams are positive semidefinite, so the decoding integrand is integrable. -/
theorem integrable_exp_mul_maxCoord_gram {d : ℕ} (X : Geometry.Config m d) (lam : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (lam * maxCoord x))
      (multivariateGaussian 0 (Geometry.gram X)) :=
  integrable_exp_mul_maxCoord (Geometry.gram X) (Geometry.gram_posSemidef X) lam

/-- Pushing standard Gaussian noise through a linear score map does not change the
exponential moment of the coordinate maximum: the moment depends on the map only
through `linearImageCov`, the Gram matrix of the adjoint coordinate vectors. -/
theorem integral_exp_maxCoord_stdGaussian_map {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) (lam : ℝ) :
    (∫ y, Real.exp (lam * maxCoord (L y)) ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ x, Real.exp (lam * maxCoord x) ∂multivariateGaussian 0 (linearImageCov L) := by
  rw [← stdGaussian_map_linear L]
  have hf : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin m) ↦ Real.exp (lam * maxCoord x))
      ((stdGaussian (EuclideanSpace ℝ (Fin d))).map L) :=
    ((continuous_maxCoord.measurable.const_mul lam).exp).aestronglyMeasurable
  exact (integral_map (by fun_prop) hf).symm

/-- `Pc` of a linear image covariance is the normalized noise integral of
`exp(λ * maxCoord (L y))`. -/
theorem decodingSuccess_linearImageCov {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) (lam : ℝ) :
    decodingSuccess (linearImageCov L) lam =
      Real.exp (-(lam ^ 2) / 2) / (m : ℝ) *
        ∫ y, Real.exp (lam * maxCoord (L y)) ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  unfold decodingSuccess
  rw [integral_exp_maxCoord_stdGaussian_map]

#print axioms continuous_maxCoord
#print axioms measurable_maxCoord
#print axioms exp_mul_maxCoord_le_sum
#print axioms integrable_exp_mul_coord
#print axioms integrable_exp_mul_maxCoord
#print axioms integrable_exp_mul_maxCoord_gram
#print axioms integral_exp_maxCoord_stdGaussian_map
#print axioms decodingSuccess_linearImageCov

end SimplexFull
