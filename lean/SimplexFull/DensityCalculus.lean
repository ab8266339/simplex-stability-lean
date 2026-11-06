import SimplexFull.GaussianDensity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Calculus of the multivariate Gaussian density in the covariance

Matrix norms and derivatives use the L2 operator norm (`Matrix.Norms.L2Operator`).
-/

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Real

namespace SimplexFull.Covariance

variable {m : ℕ}

/-- Coordinate functional for the L2 operator norm on matrices. -/
def entryLinearMap (i j : Fin m) : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ where
  toFun R := R i j
  map_add' _ _ := by simp [Matrix.add_apply]
  map_smul' _ _ := by simp [Matrix.smul_apply]

lemma contDiff_entry (i j : Fin m) :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => R i j) := by
  simpa [entryLinearMap] using (entryLinearMap i j).toContinuousLinearMap.contDiff

lemma contDiff_det_of_entries
    (f : Fin m → Fin m → Matrix (Fin m) (Fin m) ℝ → ℝ)
    (hf : ∀ i j, ContDiff ℝ ⊤ (f i j)) :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => (Matrix.of (fun i j => f i j R)).det) := by
  classical
  have hdet : (fun R => (Matrix.of (fun i j => f i j R)).det) =
      fun R => ∑ σ : Equiv.Perm (Fin m),
        Equiv.Perm.sign σ • ∏ i, f (σ i) i R := by
    ext R
    simp [Matrix.det_apply, Matrix.of_apply]
  rw [hdet]
  refine ContDiff.sum fun σ _ => ?_
  have hsmul : (fun R => Equiv.Perm.sign σ • ∏ i, f (σ i) i R) =
      fun R => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (σ i) i R := by
    ext R
    rw [Units.smul_def, zsmul_eq_mul]
  rw [hsmul]
  exact contDiff_const.mul (contDiff_prod fun i _ => hf (σ i) i)

lemma contDiff_det :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => R.det) := by
  have hdet : (fun R : Matrix (Fin m) (Fin m) ℝ => R.det) =
      fun R => (Matrix.of (fun i j => R i j)).det := by
    ext R
    congr 1
  rw [hdet]
  exact contDiff_det_of_entries (fun i j R => R i j) fun i j => contDiff_entry i j

lemma contDiff_updateRow_cov_entry (j : Fin m) (v : Fin m → ℝ) (p q : Fin m) :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => (R.updateRow j v) p q) := by
  by_cases hp : p = j
  · have hfun : (fun R : Matrix (Fin m) (Fin m) ℝ => (R.updateRow j v) p q) = fun _ => v q := by
      ext R
      simp [Matrix.updateRow_apply, hp]
    rw [hfun]
    exact contDiff_const
  · have hfun : (fun R : Matrix (Fin m) (Fin m) ℝ => (R.updateRow j v) p q) = fun R => R p q := by
      ext R
      simp [Matrix.updateRow_apply, hp]
    rw [hfun]
    exact contDiff_entry p q

lemma contDiff_adjugate_cov_entry (i j : Fin m) :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => (adjugate R) i j) := by
  simp_rw [Matrix.adjugate_apply]
  have hdet : (fun R : Matrix (Fin m) (Fin m) ℝ =>
        ((R.updateRow j (Pi.single i (1 : ℝ))).det)) =
      fun R => (Matrix.of (fun p q => (R.updateRow j (Pi.single i (1 : ℝ))) p q)).det := by
    ext R
    congr 1
  rw [hdet]
  exact contDiff_det_of_entries _
    fun p q => contDiff_updateRow_cov_entry j (Pi.single i (1 : ℝ)) p q

lemma contDiff_cov_adjQuad (x : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ⊤ (fun R : Matrix (Fin m) (Fin m) ℝ => quad (adjugate R) x) := by
  unfold quad
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_const.mul (contDiff_adjugate_cov_entry i j)).mul contDiff_const

/-- On `{R | 0 < det R}` the density is a smooth function of the covariance matrix. -/
theorem contDiffAt_rho {x : EuclideanSpace ℝ (Fin m)} {R : Matrix (Fin m) (Fin m) ℝ}
    (hR : 0 < R.det) :
    ContDiffAt ℝ ⊤ (fun S : Matrix (Fin m) (Fin m) ℝ => rho S x) R := by
  have hbase : (2 * Real.pi) ^ m ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hdet_ne : R.det ≠ 0 := ne_of_gt hR
  have harg_ne : (2 * Real.pi) ^ m * R.det ≠ 0 := mul_ne_zero hbase hdet_ne
  have hsqrt_ne : Real.sqrt ((2 * Real.pi) ^ m * R.det) ≠ 0 := by
    refine (Real.sqrt_pos.2 ?_).ne'
    exact mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) m) hR
  have hexpr : ContDiffAt ℝ ⊤ (fun S : Matrix (Fin m) (Fin m) ℝ =>
      (Real.sqrt ((2 * Real.pi) ^ m * S.det))⁻¹ *
        Real.exp ((-(S.det⁻¹ * quad S.adjugate x)) / 2)) R := by
    refine ContDiffAt.mul ?_ ?_
    · exact ((contDiff_const.mul contDiff_det).contDiffAt.sqrt harg_ne).inv hsqrt_ne
    · exact ContDiffAt.exp <|
        (((contDiff_det.contDiffAt.inv hdet_ne).mul (contDiff_cov_adjQuad x).contDiffAt).neg.div_const 2)
  have heq : (fun S : Matrix (Fin m) (Fin m) ℝ => rho S x) =
      fun S => (Real.sqrt ((2 * Real.pi) ^ m * S.det))⁻¹ *
        Real.exp ((-(S.det⁻¹ * quad S.adjugate x)) / 2) := by
    ext S
    exact rho_eq_adjugate S x
  rw [heq]
  exact hexpr

#print axioms contDiffAt_rho

end SimplexFull.Covariance

