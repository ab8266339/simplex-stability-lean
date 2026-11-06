import SimplexFull.GlobalCentroidMatrix
import SimplexFull.GlobalCentroidEnergy
import SimplexFull.GlobalCentroidConstants
noncomputable section
open WeakSimplex
open scoped InnerProductSpace BigOperators
namespace SimplexFull.GlobalCentroid

def centeredMatrix {m : Nat} (R : Matrix (Fin m) (Fin m) Real) :=
  R-(1/(m:Real)) • allOnesMatrix m

def rowDisplacement {m : Nat} (R : Matrix (Fin m) (Fin m) Real) (i : Fin m) : Real :=
  matrixMul R (allOnesVector m) i-1

def centroidExcess {m : Nat} (R : Matrix (Fin m) (Fin m) Real) : Real :=
  qform R (allOnesVector m)-(m:Real)

theorem centered_row {m : Nat} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) Real) (i : Fin m) :
    matrixMul (centeredMatrix R) (allOnesVector m) i=rowDisplacement R i := by
  have hmne : (m:Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold rowDisplacement
  rw [matrixMul_one_apply, matrixMul_one_apply]
  simp [centeredMatrix, Matrix.sub_apply, Matrix.smul_apply, allOnesMatrix,
    Finset.sum_sub_distrib]
  field_simp

theorem qform_centered {m : Nat} (hm : 0 < m)
    (R : Matrix (Fin m) (Fin m) Real) :
    qform (centeredMatrix R) (allOnesVector m)=centroidExcess R := by
  have hmne : (m:Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [centeredMatrix, qform_sub_matrix, qform_smul_matrix, qform_allOnes]
  simp only [allOnesVector_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  unfold centroidExcess
  field_simp
  <;> ring

theorem centered_diagonal {m : Nat} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) Real} (hd : ∀ i, R i i=1) (i : Fin m) :
    centeredMatrix R i i=alpha m := by
  have hmne : (m:Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [centeredMatrix, Matrix.sub_apply, Matrix.smul_apply, allOnesMatrix,
    hd i, alpha, Geometry.alpha]
  field_simp
  <;> ring

theorem centroidExcess_nonneg {m : Nat} (hm : 0 < m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R) :
    0 ≤ centroidExcess R := by
  have hh := qform_nonneg_of_posSemidef hR.2 (allOnesVector m)
  rwa [← centeredMatrix, qform_centered hm] at hh

theorem sum_rowDisplacement {m : Nat} (R : Matrix (Fin m) (Fin m) Real) :
    (∑ i, rowDisplacement R i)=centroidExcess R := by
  simp [rowDisplacement, centroidExcess, qform, inner_one_eq_sum, Finset.sum_sub_distrib]


theorem sum_rowDisplacement_sq_le {m : Nat} (hm : 2 ≤ m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R) :
    (∑ i, (rowDisplacement R i)^2) ≤ ((m:Real)-1)*centroidExcess R := by
  have hm0 : 0<m := by omega
  have hh := sum_row_sq_le (A:=centeredMatrix R) (alpha:=alpha m)
    hR.2 (centered_diagonal hm0 hR.1.2)
  simp only [centered_row hm0, qform_centered hm0] at hh
  rw [mul_comm (m:Real) (alpha m), alpha_mul_m hm0] at hh
  exact hh

theorem abs_rowDisplacement_le {m : Nat} (hm : 2 ≤ m)
    {R : Matrix (Fin m) (Fin m) Real} (hR : IsWeakSimplexCov R) (i : Fin m) :
    |rowDisplacement R i| ≤ (m:Real)-1 := by
  have hm0 : 0<m := by omega
  have hh := row_abs_le (A:=centeredMatrix R) (alpha:=alpha m)
    hR.2 (alpha_pos hm).le (centered_diagonal hm0 hR.1.2) i
  rw [centered_row hm0, mul_comm (m:Real) (alpha m), alpha_mul_m hm0] at hh
  exact hh

#print axioms sum_rowDisplacement_sq_le
#print axioms abs_rowDisplacement_le
end SimplexFull.GlobalCentroid