import SimplexFull.GaussianDensity
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section
open Matrix
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace SimplexFull.Covariance
variable {m : ℕ}

theorem quad_inv_eq_norm_inv_sqrt (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosSemidef) (x : EuclideanSpace ℝ (Fin m)) :
    quad R⁻¹ x = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt R)⁻¹) x‖ ^ 2 := by
  let S := (CFC.sqrt R)⁻¹
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) S
  have hS : S.IsHermitian := (CFC.sqrt_nonneg R).isSelfAdjoint.isHermitian.inv
  have hL : IsSelfAdjoint L := hS.isSelfAdjoint.map _
  have hSS : S * S = R⁻¹ := by
    rw [show S * S = (CFC.sqrt R * CFC.sqrt R)⁻¹ by rw [Matrix.mul_inv_rev],
      CFC.sqrt_mul_sqrt_self _ hR.nonneg]
  rw [quad_eq_dotProduct, ← Matrix.inner_toEuclideanCLM]
  rw [← hSS, map_mul]
  change inner ℝ x (L (L x)) = ‖L x‖ ^ 2
  have hi := ContinuousLinearMap.adjoint_inner_left L (L x) x
  rw [hL.adjoint_eq] at hi
  exact hi.symm.trans (real_inner_self_eq_norm_sq _)

set_option pp.fullNames true in
#print axioms quad_inv_eq_norm_inv_sqrt

theorem rho_inv_sqrt_transform (R : Matrix (Fin m) (Fin m) ℝ)
    (hR : R.PosDef) (x : EuclideanSpace ℝ (Fin m)) :
    |((CFC.sqrt R).det)⁻¹| *
      rho (1 : Matrix (Fin m) (Fin m) ℝ)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt R)⁻¹) x) = rho R x := by
  rw [rho_one, ← quad_inv_eq_norm_inv_sqrt R hR.posSemidef, rho]
  rw [hR.posSemidef.det_sqrt, RCLike.sqrt_real,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [Real.sqrt_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) m)]
  ring

set_option pp.fullNames true in
#print axioms rho_inv_sqrt_transform

end SimplexFull.Covariance
