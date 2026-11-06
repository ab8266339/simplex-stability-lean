import SimplexFull.DensityCalculus
import SimplexFull.GaussianDensity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Directional derivatives of the Gaussian density at the identity covariance

Matrix norms and derivatives use the L2 operator norm (`Matrix.Norms.L2Operator`).
-/

noncomputable section

open Matrix ContinuousLinearMap Filter
open scoped BigOperators Matrix.Norms.L2Operator Real Polynomial Topology

namespace SimplexFull.Covariance

variable {m : ℕ}

/-- The affine line `t ↦ I + t A` has constant derivative `A`. -/
lemma hasDerivAt_covLine (A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + s • A) A t := by
  have hsmul : HasDerivAt (fun s : ℝ => s • A) ((1 : ℝ) • A) t :=
    (hasDerivAt_id' t).smul_const A
  have hadd : HasDerivAt (fun s : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + s • A)
      (0 + (1 : ℝ) • A) t :=
    (hasDerivAt_const t (1 : Matrix (Fin m) (Fin m) ℝ)).add hsmul
  simpa using hadd

/-- `det(I + t A)` is the evaluation of the polynomial `det(I + X A)`. -/
lemma det_covLine_eq_eval (A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det =
      (((1 : Matrix (Fin m) (Fin m) ℝ[X]) +
        (Polynomial.X : ℝ[X]) • A.map Polynomial.C).det.eval t) := by
  let M : Matrix (Fin m) (Fin m) ℝ[X] :=
    1 + (Polynomial.X : ℝ[X]) • A.map Polynomial.C
  have hdet : (M.det.eval t) =
      ((Polynomial.evalRingHom t).mapMatrix M).det := by
    simpa using RingHom.map_det (Polynomial.evalRingHom t) M
  rw [hdet]
  congr 1
  ext i j
  simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · simp [hij, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_comm _ _
  · simp [hij, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_comm _ _

/-- Derivative of the determinant along `t ↦ I + t A` at `t = 0` is the trace. -/
theorem hasDerivAt_det_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det)
      (Matrix.trace A) 0 := by
  let p : ℝ[X] :=
    ((1 : Matrix (Fin m) (Fin m) ℝ[X]) +
      (Polynomial.X : ℝ[X]) • A.map Polynomial.C).det
  have hp : HasDerivAt (fun t => p.eval t) (p.derivative.eval 0) 0 := p.hasDerivAt 0
  have hfun : (fun t : ℝ => ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A).det) =
      fun t => p.eval t := by
    ext t
    exact det_covLine_eq_eval A t
  have hder : p.derivative.eval 0 = Matrix.trace A := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul A
  rw [hfun, ← hder]
  exact hp

/-- `M ↦ xᵀ M x` is linear, hence continuous for the L2 operator norm. -/
def quadLinearMap (x : EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ where
  toFun M := quad M x
  map_add' M N := quad_add M N x
  map_smul' c M := by simp [quad_smul, RingHom.id_apply, smul_eq_mul]

private lemma hasDerivAt_ringInverse_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) (-A) 0 := by
  have hline : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) A 0 :=
    hasDerivAt_covLine A 0
  have hinv : HasFDerivAt Ring.inverse
      (-mulLeftRight ℝ (Matrix (Fin m) (Fin m) ℝ)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹))
      (1 : Matrix (Fin m) (Fin m) ℝ) :=
    hasFDerivAt_ringInverse (1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq 0 hinv hline (by simp)
  have hderiv :
      (-mulLeftRight ℝ (Matrix (Fin m) (Fin m) ℝ)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)
        (↑(1 : (Matrix (Fin m) (Fin m) ℝ)ˣ)⁻¹)) A = -A := by
    simp [mulLeftRight_apply, Units.val_one, inv_one, one_mul, mul_one]
  simpa [hderiv] using hcomp

/-- Each entry of `(I + t A)⁻¹` has derivative `-A i j` at `t = 0`. -/
theorem hasDerivAt_inv_entry_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) i j)
      ((-A) i j) 0 := by
  have hmat := hasDerivAt_ringInverse_covLine_zero A
  have hclm := (entryLinearMap i j).toContinuousLinearMap.hasFDerivAt
    (x := (Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) 0)
  have hcomp := hclm.comp_hasDerivAt 0 hmat
  have hfun : (fun t : ℝ => (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) i j) =
      entryLinearMap i j ∘ Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A := by
    ext t
    simp [entryLinearMap, Function.comp, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  simpa [entryLinearMap, LinearMap.coe_toContinuousLinearMap] using hcomp

/-- Directional derivative of the inverse quadratic form at the identity: `d/dt |₀ xᵀ(I+tA)⁻¹x = -xᵀ A x`. -/
theorem hasDerivAt_quad_inv_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => quad (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) x)
      (-quad A x) 0 := by
  have hmat := hasDerivAt_ringInverse_covLine_zero A
  have hclm := (quadLinearMap x).toContinuousLinearMap.hasFDerivAt
    (x := (Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A) 0)
  have hcomp := hclm.comp_hasDerivAt 0 hmat
  have hfun : (fun t : ℝ => quad (((1 : Matrix (Fin m) (Fin m) ℝ) + t • A)⁻¹) x) =
      quadLinearMap x ∘ Ring.inverse ∘ fun t : ℝ => (1 : Matrix (Fin m) (Fin m) ℝ) + t • A := by
    ext t
    simp [quadLinearMap, Function.comp, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  have hquad : quad (-A) x = -quad A x := by
    rw [show -A = (-1 : ℝ) • A by simp, quad_smul, neg_one_mul]
  simpa [quadLinearMap, LinearMap.coe_toContinuousLinearMap, hquad] using hcomp

/-- Arithmetic form of the logarithmic derivative of the Gaussian prefactor at determinant `1`. -/
lemma gaussian_line_deriv_algebra (c tr qA nrm : ℝ) (hc : 0 < c) :
    (-((c * tr) / (2 * Real.sqrt c)) / (Real.sqrt c) ^ 2) * Real.exp (-nrm / 2) +
        (Real.sqrt c)⁻¹ * (Real.exp (-nrm / 2) * (qA / 2)) =
      ((Real.sqrt c)⁻¹ * Real.exp (-nrm / 2)) * (qA - tr) / 2 := by
  have hs0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hs : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  field_simp [hs0]
  have hct : c * tr = tr * (Real.sqrt c) ^ 2 := by rw [hs, mul_comm]
  rw [hct, mul_sub, mul_comm (Real.sqrt c ^ 2) tr, sub_eq_neg_add]

/-- First directional derivative of the density at the identity covariance.
`d/dt |₀ ρ(I + t A, x) = ρ(I, x) (xᵀ A x - tr A) / 2`. -/
theorem hasDerivAt_rho_covLine_zero (A : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => rho ((1 : Matrix (Fin m) (Fin m) ℝ) + t • A) x)
      (rho (1 : Matrix (Fin m) (Fin m) ℝ) x * (quad A x - Matrix.trace A) / 2) 0 := by
  have hc : 0 < (2 * Real.pi) ^ m := pow_pos (mul_pos (by norm_num) Real.pi_pos) _
  have hconst := hasDerivAt_const (0 : ℝ) ((2 * Real.pi) ^ m)
  have hd := hasDerivAt_det_covLine_zero A
  have hg := (hconst.mul hd).congr_deriv (by simp; rfl)
  have hg0 : (2 * Real.pi) ^ m * ((1 : Matrix (Fin m) (Fin m) ℝ) + (0 : ℝ) • A).det ≠ 0 := by
    simp [Matrix.det_one, hc.ne']
  have hs := hg.sqrt hg0
  have hs0 : Real.sqrt ((2 * Real.pi) ^ m *
      ((1 : Matrix (Fin m) (Fin m) ℝ) + (0 : ℝ) • A).det) ≠ 0 := by
    refine (Real.sqrt_pos.2 ?_).ne'
    simp [Matrix.det_one, hc]
  have ha := hs.inv hs0
  have hq := hasDerivAt_quad_inv_covLine_zero A x
  have hexp := (hq.neg.div_const (2 : ℝ)).exp
  have hmul := ha.mul hexp
  refine (hmul.congr_of_eventuallyEq ?_).congr_deriv ?_
  · apply Eventually.of_forall
    intro t
    simp [rho, Pi.mul_apply, Pi.neg_apply]
  · simp only [Pi.mul_apply, Pi.neg_apply, Pi.inv_apply, Matrix.det_one, zero_smul, add_zero,
      matrix_inv_one, quad_one, mul_one, neg_neg]
    rw [rho_one]
    exact gaussian_line_deriv_algebra ((2 * Real.pi) ^ m) (Matrix.trace A) (quad A x)
      (‖x‖ ^ 2) hc

#print axioms hasDerivAt_det_covLine_zero
#print axioms hasDerivAt_inv_entry_covLine_zero
#print axioms hasDerivAt_quad_inv_covLine_zero
#print axioms hasDerivAt_rho_covLine_zero

end SimplexFull.Covariance
