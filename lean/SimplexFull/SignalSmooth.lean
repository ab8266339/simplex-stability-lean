import SimplexFull.GaussianShift
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SimplexFull
variable {m : ℕ} [NeZero m]

theorem integrableExpSet_maxCoord_eq_univ
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) :
    integrableExpSet (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
      (multivariateGaussian 0 G) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_maxCoord G hG t

theorem contDiff_decodingSuccess (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosSemidef) {n : WithTop ℕ∞} :
    ContDiff ℝ n (decodingSuccess G) := by
  have ha : AnalyticOnNhd ℝ
      (mgf (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ)
        (multivariateGaussian 0 G)) Set.univ := by
    simpa only [integrableExpSet_maxCoord_eq_univ G hG, interior_univ] using
      (analyticOnNhd_mgf (X := (maxCoord : EuclideanSpace ℝ (Fin m) → ℝ))
        (μ := multivariateGaussian 0 G))
  have hp : ContDiff ℝ n (fun lam : ℝ => Real.exp (-(lam ^ 2) / 2) / (m : ℝ)) := by
    fun_prop
  exact hp.mul ha.contDiff

theorem contDiff_simplexSuccess_top (hm : 3 ≤ m) :
    ContDiff ℝ ⊤ (fun lam : ℝ => decodingSuccess (Geometry.simplexGram m) lam) :=
  contDiff_decodingSuccess _ simplexGram_posSemidef

theorem contDiff_simplexSuccess (hm : 3 ≤ m) :
    ContDiff ℝ 3 (fun lam : ℝ => decodingSuccess (Geometry.simplexGram m) lam) :=
  contDiff_decodingSuccess _ simplexGram_posSemidef

theorem differentiableAt_simplexSuccess (hm : 3 ≤ m) (lam : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => decodingSuccess (Geometry.simplexGram m) s) lam :=
  (contDiff_simplexSuccess hm).differentiable (by norm_num) |>.differentiableAt

#print axioms integrableExpSet_maxCoord_eq_univ
#print axioms contDiff_decodingSuccess
#print axioms contDiff_simplexSuccess_top
#print axioms contDiff_simplexSuccess
#print axioms differentiableAt_simplexSuccess
end SimplexFull
