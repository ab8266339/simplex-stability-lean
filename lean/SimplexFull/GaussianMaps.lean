import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Analysis.InnerProductSpace.GramMatrix

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace SimplexFull

def linearImageCov {d m : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.gram ℝ (fun i => L.adjoint (EuclideanSpace.basisFun (Fin m) ℝ i))

theorem linearImageCov_posSemidef {d m : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (linearImageCov L).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

theorem stdGaussian_map_linear {d m : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map L =
      multivariateGaussian 0 (linearImageCov L) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (fun i j => ?_)
    simp only [ContinuousLinearMap.toBilinForm_apply]
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian (linearImageCov_posSemidef L)]
    simp [linearImageCov, Matrix.gram]
    rfl

def scoreMap {d m : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ∑ i, (innerSL ℝ (X i)).smulRight (EuclideanSpace.basisFun (Fin m) ℝ i)

@[simp] theorem scoreMap_apply {d m : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) (i : Fin m) :
    scoreMap X z i = ⟪X i, z⟫ := by
  classical
  simp [scoreMap, Pi.single_apply, eq_comm]

theorem scoreMap_adjoint_basis {d m : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (i : Fin m) :
    (scoreMap X).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i) = X i := by
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply, scoreMap_apply]

theorem linearImageCov_scoreMap {d m : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d)) :
    linearImageCov (scoreMap X) = Matrix.gram ℝ X := by
  ext i j
  simp only [linearImageCov, Matrix.gram_apply, scoreMap_adjoint_basis]

theorem gaussian_score_law {d m : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (scoreMap X) =
      multivariateGaussian 0 (Matrix.gram ℝ X) := by
  rw [stdGaussian_map_linear, linearImageCov_scoreMap]

#print axioms gaussian_score_law
#print axioms stdGaussian_map_linear
end SimplexFull