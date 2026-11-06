import SimplexFull.DensityDerivatives
import SimplexFull.GaussianPolynomial

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Polynomial Topology
namespace SimplexFull.Covariance
variable {m : ℕ}

theorem hasDerivAt_inv_covLine (A : Matrix (Fin m) (Fin m) ℝ) {t : ℝ}
    (ht : ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det ≠ 0) :
    HasDerivAt (fun s : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + s • A)⁻¹)
      (-(((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ * A *
        ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹)) t := by
  have hu : IsUnit ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact ht
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have hh := HasFDerivAt.comp_hasDerivAt_of_eq t hi (hasDerivAt_covLine A t) hu.unit_spec.symm
  have hiu : (↑(hu.unit⁻¹) : Matrix (Fin m) (Fin m) ℝ) =
      ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_of_isUnit hu]
  simpa [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse, mulLeftRight_apply, hiu] using hh

set_option pp.fullNames true in
#print axioms hasDerivAt_inv_covLine
end SimplexFull.Covariance
