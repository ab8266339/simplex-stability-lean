import SimplexFull.GlobalProcrustesDecomp
noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

theorem global_frobSq_eq_trace_transpose_mul {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq A = Matrix.trace (A.transpose * A) := by
  simp only [frobSq, trace_eq_sum_diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem global_frobSq_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq A.transpose = frobSq A := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem global_centering_complement_posSemidef {m : ℕ} (hm : m ≠ 0) :
    (1 - centering m).PosSemidef := by
  have hsym : (1 - centering m).transpose = 1 - centering m := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, (centering_isSymm m).eq]
  have hsq : (1 - centering m) * (1 - centering m) = 1 - centering m := by
    calc
      (1 - centering m) * (1 - centering m) =
          1 - centering m - centering m + centering m * centering m := by noncomm_ring
      _ = 1 - centering m := by rw [centering_mul_self hm]; abel
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1 - centering m)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hsym, hsq] using hp

/-- Left multiplication by the centering projection contracts the concrete
Frobenius square, for arbitrary real matrices. -/
theorem global_frobSq_centering_mul_le {m : ℕ} (hm : m ≠ 0)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq (centering m * A) ≤ frobSq A := by
  have hnonneg := ((global_centering_complement_posSemidef hm).conjTranspose_mul_mul_same A).trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hnonneg
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub] at hnonneg
  have hprod : (centering m * A).transpose * (centering m * A) =
      A.transpose * centering m * A := by
    rw [Matrix.transpose_mul, (centering_isSymm m).eq]
    calc
      A.transpose * centering m * (centering m * A) =
          A.transpose * (centering m * centering m) * A := by simp only [Matrix.mul_assoc]
      _ = A.transpose * centering m * A := by rw [centering_mul_self hm]
  rw [global_frobSq_eq_trace_transpose_mul (centering m * A), hprod,
    global_frobSq_eq_trace_transpose_mul A]
  linarith

theorem global_frobSq_mul_centering_le {m : ℕ} (hm : m ≠ 0)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq (A * centering m) ≤ frobSq A := by
  calc
    frobSq (A * centering m) = frobSq ((A * centering m).transpose) :=
      (global_frobSq_transpose _).symm
    _ = frobSq (centering m * A.transpose) := by
      rw [Matrix.transpose_mul, (centering_isSymm m).eq]
    _ ≤ frobSq A.transpose := global_frobSq_centering_mul_le hm A.transpose
    _ = frobSq A := global_frobSq_transpose A

theorem global_frobSq_compression_le {m : ℕ} (hm : m ≠ 0)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq (centering m * A * centering m) ≤ frobSq A :=
  (global_frobSq_mul_centering_le hm (centering m * A)).trans
    (global_frobSq_centering_mul_le hm A)

/-- The exact compressed simplex Gram identity, with no symmetry or PSD
assumption on the comparison matrix. -/
theorem global_compressed_gram_sub_simplex {m : ℕ} (hm : m ≠ 0)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    centering m * G * centering m - simplexGram m =
      centering m * (G - simplexGram m) * centering m := by
  have hdelta : centering m * simplexGram m * centering m = simplexGram m := by
    rw [simplexGram, Matrix.mul_smul, Matrix.smul_mul,
      centering_mul_self hm, centering_mul_self hm]
  rw [Matrix.mul_sub, Matrix.sub_mul, hdelta]

theorem global_frobSq_compressed_gram_sub_simplex_le {m : ℕ} (hm : m ≠ 0)
    (G : Matrix (Fin m) (Fin m) ℝ) :
    frobSq (centering m * G * centering m - simplexGram m) ≤
      frobSq (G - simplexGram m) := by
  rw [global_compressed_gram_sub_simplex hm G]
  exact global_frobSq_compression_le hm (G - simplexGram m)

#print axioms global_frobSq_centering_mul_le
#print axioms global_frobSq_mul_centering_le
#print axioms global_frobSq_compression_le
#print axioms global_frobSq_compressed_gram_sub_simplex_le
end SimplexFull.Geometry
