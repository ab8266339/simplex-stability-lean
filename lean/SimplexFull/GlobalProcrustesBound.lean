import SimplexFull.GlobalSqrtContraction
noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

theorem global_frobSq_smul {m : ℕ} (c : ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    frobSq (c • A) = c^2 * frobSq A := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem global_centeredGram_sub_centering {m d : ℕ}
    (hm : 2 ≤ m) (X : Config m d) :
    centeredGram X - centering m =
      alpha m • (centering m * gram X * centering m - simplexGram m) := by
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m (by omega)
  rw [smul_sub, simplexGram, smul_smul, mul_inv_cancel₀ hα, one_smul]
  rfl

/-- Global Procrustes control by the centered Gram error and actual centroid.
The configuration X is allowed arbitrary vector lengths. -/
theorem global_procrustesSq_le_compressed_gram_centroid {m d : ℕ} (hm : 2 ≤ m)
    (X V : Config m d) (hVgram : gram V = simplexGram m) :
    procrustesSq X V ≤
      alpha m * frobSq (centering m * gram X * centering m - simplexGram m) +
        ‖∑ i, X i‖^2 / (m : ℝ) := by
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m (by omega)
  have hα0 : 0 ≤ alpha m := alpha_nonneg (by omega)
  have hroot := global_frobSq_centeredRoot_le (show 1 ≤ m by omega) X
  rw [global_centeredGram_sub_centering hm X, global_frobSq_smul] at hroot
  have hcoef : (alpha m)⁻¹ * (alpha m)^2 = alpha m := by
    field_simp [hα]
  rw [global_procrustesSq_decomposition hm X V hVgram]
  calc
    ‖∑ i, X i‖^2 / (m : ℝ) +
        (alpha m)⁻¹ * frobSq (centeredRoot X-centering m) ≤
      ‖∑ i, X i‖^2 / (m : ℝ) +
        (alpha m)⁻¹ * ((alpha m)^2 *
          frobSq (centering m * gram X * centering m - simplexGram m)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot (inv_nonneg.mpr hα0))
    _ = alpha m * frobSq (centering m * gram X * centering m - simplexGram m) +
        ‖∑ i, X i‖^2 / (m : ℝ) := by
      rw [← mul_assoc, hcoef]
      ring

/-- The global geometric conversion used in both quantitative simplex
recovery and the arbitrary-length inscribed-simplex mean-width theorem.
All quantities are the actual configuration Gram, centroid, and sInf over O(d).
No supplied scalar comparison, PSD, rank, or unit-length hypothesis is used. -/
theorem global_procrustesSq_le_gram_centroid {m d : ℕ} (hm : 2 ≤ m)
    (X V : Config m d) (hVgram : gram V = simplexGram m) :
    procrustesSq X V ≤
      alpha m * frobSq (gram X - simplexGram m) +
        ‖∑ i, X i‖^2 / (m : ℝ) := by
  apply (global_procrustesSq_le_compressed_gram_centroid hm X V hVgram).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (global_frobSq_compressed_gram_sub_simplex_le (by omega) (gram X))
      (alpha_nonneg (m := m) (by omega))) le_rfl

#print axioms global_procrustesSq_le_compressed_gram_centroid
#print axioms global_procrustesSq_le_gram_centroid
end SimplexFull.Geometry
