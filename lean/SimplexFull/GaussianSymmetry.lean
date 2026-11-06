import SimplexFull.GaussianSmooth
import SimplexFull.Decoder

/-!
Coordinate permutation symmetry of `rhoExpectation`.

`coordPerm σ` reorders Euclidean coordinates by `σ`. It preserves Lebesgue measure and
`maxCoord`, and it pushes `quad` and `rho` onto `R.submatrix σ σ`.
-/

noncomputable section

open MeasureTheory Matrix Finset
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace SimplexFull.Covariance

variable {m : ℕ}

/-- Permute coordinates by `σ`: `(coordPerm σ x) i = x (σ i)`. -/
def coordPerm (σ : Equiv.Perm (Fin m)) :
    EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm

@[simp]
lemma coordPerm_apply (σ : Equiv.Perm (Fin m)) (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    coordPerm σ x i = x (σ i) := by
  simp [coordPerm, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

@[simp]
lemma coordPerm_symm (σ : Equiv.Perm (Fin m)) :
    (coordPerm σ).symm = coordPerm σ.symm := by
  simp [coordPerm, LinearIsometryEquiv.piLpCongrLeft_symm]

/-- Reindexing both axes of `M` by `σ` is the quadratic form of the permuted vector. -/
lemma quad_submatrix_coordPerm (M : Matrix (Fin m) (Fin m) ℝ) (σ : Equiv.Perm (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    quad (M.submatrix σ σ) (coordPerm σ x) = quad M x := by
  simp only [quad, Matrix.submatrix_apply, coordPerm_apply]
  rw [Equiv.sum_comp σ (fun i ↦ ∑ j, x i * M i (σ j) * x (σ j))]
  refine sum_congr rfl fun i _ ↦ ?_
  exact Equiv.sum_comp σ fun j ↦ x i * M i j * x j

/-- The Gaussian density is invariant under the simultaneous permutation of covariance and
coordinates. This is algebraic in `det` and `⁻¹`, including the singular case. -/
lemma rho_submatrix_coordPerm (R : Matrix (Fin m) (Fin m) ℝ) (σ : Equiv.Perm (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    rho (R.submatrix σ σ) (coordPerm σ x) = rho R x := by
  unfold rho
  rw [Matrix.det_submatrix_equiv_self, Matrix.inv_submatrix_equiv, quad_submatrix_coordPerm]

variable [NeZero m]

/-- The coordinate maximum is unchanged by reordering coordinates. -/
lemma maxCoord_coordPerm (σ : Equiv.Perm (Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    maxCoord (coordPerm σ x) = maxCoord x := by
  unfold maxCoord
  refine le_antisymm ?_ ?_
  · rw [sup'_le_iff]
    intro i _
    rw [coordPerm_apply, le_sup'_iff]
    exact ⟨σ i, mem_univ _, le_rfl⟩
  · rw [sup'_le_iff]
    intro i _
    have hx : coordPerm σ x (σ.symm i) = x i := by
      rw [coordPerm_apply, Equiv.apply_symm_apply]
    rw [← hx, le_sup'_iff]
    exact ⟨σ.symm i, mem_univ _, le_rfl⟩

/-- `ρ(R.submatrix σ σ)` with the exponential coordinate tilt agrees with `ρ(R)` after
`coordPerm σ`. -/
lemma exp_maxCoord_rho_submatrix_coordPerm (lam : ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    Real.exp (lam * maxCoord (coordPerm σ x)) * rho (R.submatrix σ σ) (coordPerm σ x) =
      Real.exp (lam * maxCoord x) * rho R x := by
  rw [maxCoord_coordPerm, rho_submatrix_coordPerm]

/-- Permuting the rows and columns of the covariance by the same permutation does not change
`rhoExpectation`. `coordPerm σ` preserves volume, so the change of variables needs no
integrability hypothesis. -/
theorem rhoExpectation_submatrix_perm (lam : ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) :
    rhoExpectation lam (R.submatrix σ σ) = rhoExpectation lam R := by
  unfold rhoExpectation
  rw [← MeasurePreserving.integral_comp' (f := (coordPerm σ).toMeasurableEquiv)
      (LinearIsometryEquiv.measurePreserving (coordPerm σ))
      (fun x ↦ Real.exp (lam * maxCoord x) * rho (R.submatrix σ σ) x)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  change Real.exp (lam * maxCoord (coordPerm σ x)) * rho (R.submatrix σ σ) (coordPerm σ x) =
    Real.exp (lam * maxCoord x) * rho R x
  exact exp_maxCoord_rho_submatrix_coordPerm lam R σ x

#print axioms maxCoord_coordPerm
#print axioms quad_submatrix_coordPerm
#print axioms rho_submatrix_coordPerm
#print axioms exp_maxCoord_rho_submatrix_coordPerm
#print axioms rhoExpectation_submatrix_perm

end SimplexFull.Covariance
