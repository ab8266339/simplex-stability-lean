import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.Matrix.Order
noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace SimplexFull.Geometry
instance realMatrixIsometricCFC (m : ℕ) :
    IsometricContinuousFunctionalCalculus ℝ (Matrix (Fin m) (Fin m) ℝ) IsSelfAdjoint where
  isometric A hA := by
    have hh : A.IsHermitian := hA
    rw [hh.cfcHom_eq_cfcAux]
    apply AddMonoidHomClass.isometry_of_norm hh.cfcAux
    intro f
    simp only [Matrix.IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply]
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hh.eigenvectorUnitary.property), CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    let v : Fin m → ℝ := fun i => f ⟨hh.eigenvalues i, hh.eigenvalues_mem_spectrum_real i⟩
    change ‖v‖ = ‖f‖
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr (fun i => f.norm_coe_le_norm _)
    · apply (ContinuousMap.norm_le f (norm_nonneg v)).mpr
      intro x
      have hxmem : x.val ∈ Set.range hh.eigenvalues := by
        rw [← hh.spectrum_real_eq_range_eigenvalues]
        exact x.property
      obtain ⟨i, hi⟩ := hxmem
      have hx : x = ⟨hh.eigenvalues i, hh.eigenvalues_mem_spectrum_real i⟩ :=
        Subtype.ext hi.symm
      rw [hx]
      exact norm_le_pi_norm v i
#print axioms realMatrixIsometricCFC
end SimplexFull.Geometry