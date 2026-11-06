import SimplexFull.GlobalProcrustesBound
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

theorem global_trace_square_eq_sum_eigenvalues_sq {m : ℕ}
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.IsHermitian) :
    Matrix.trace (G*G) = ∑ i, (hG.eigenvalues i)^2 := by
  have hs : G = Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary
      (Matrix.diagonal hG.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hG.spectral_theorem
  have hs2 : G*G = Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary
      (Matrix.diagonal hG.eigenvalues * Matrix.diagonal hG.eigenvalues) := by
    rw [map_mul, ← hs]
  rw [hs2, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [pow_two]

/-- Actual Hermitian-matrix rank controls the trace Cauchy inequality. -/
theorem global_trace_sq_le_rank_mul_trace_square {m : ℕ}
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.IsHermitian) :
    (Matrix.trace G)^2 ≤ (G.rank : ℝ) * Matrix.trace (G*G) := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => hG.eigenvalues i ≠ 0)
  have hcard : s.card = G.rank := by
    rw [hG.rank_eq_card_non_zero_eigs]
    simp [s, Fintype.card_subtype]
  have hsum : ∑ i ∈ s, hG.eigenvalues i = ∑ i, hG.eigenvalues i := by
    apply Finset.sum_subset (Finset.filter_subset _ _) 
    intro i hi hn
    have : hG.eigenvalues i = 0 := by
      simpa [s, Finset.mem_filter, hi] using hn
    exact this
  have hsumsq : ∑ i ∈ s, (hG.eigenvalues i)^2 = ∑ i, (hG.eigenvalues i)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    have : hG.eigenvalues i = 0 := by
      simpa [s, Finset.mem_filter, hi] using hn
    simp [this]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _ : Fin m => (1 : ℝ)) hG.eigenvalues
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [hcard, hsum, hsumsq] at hc
  rw [hG.trace_eq_sum_eigenvalues, global_trace_square_eq_sum_eigenvalues_sq hG]
  simpa using hc

theorem global_entrySum_nonneg {m : ℕ}
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.PosSemidef) :
    0 ≤ entrySum G := by
  simpa [entrySum, Matrix.mulVec, dotProduct] using
    hG.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))

theorem global_trace_mul_onesMatrix {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (G * onesMatrix m) = entrySum G := by
  simp [Matrix.trace, Matrix.mul_apply, onesMatrix, entrySum]

theorem global_trace_of_unit_diagonal {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ)
    (hdiag : ∀ i, G i i = 1) : Matrix.trace G = (m : ℝ) := by
  simp [Matrix.trace, Matrix.diag_apply, hdiag]

/-- Exact simplex Gram deficit, including its centroid/entry-sum term. -/
theorem global_simplex_frobSq_identity {m : ℕ} (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.IsSymm)
    (hdiag : ∀ i, G i i = 1) :
    frobSq (G - simplexGram m) = Matrix.trace (G*G) -
      (m : ℝ)^2 / ((m : ℝ)-1) + 2 / ((m : ℝ)-1) * entrySum G := by
  have hm0 : m ≠ 0 := by omega
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hm1r : (m : ℝ)-1 ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hD : (simplexGram m).IsSymm := by
    unfold Matrix.IsSymm
    rw [simplexGram, Matrix.transpose_smul, (centering_isSymm m).eq]
  have hDiff : (G-simplexGram m).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, hG.eq, hD.eq]
  have hcross : Matrix.trace (G*simplexGram m) =
      (alpha m)⁻¹ * ((m : ℝ) - (m : ℝ)⁻¹ * entrySum G) := by
    rw [simplexGram, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      centering, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, global_trace_mul_onesMatrix,
      global_trace_of_unit_diagonal G hdiag]
  have hDsq : Matrix.trace (simplexGram m*simplexGram m) =
      (alpha m)⁻¹ * (alpha m)⁻¹ * ((m : ℝ)-1) := by
    rw [simplexGram, Matrix.smul_mul, Matrix.mul_smul, centering_mul_self hm0,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      global_trace_centering m hm0]
    ring
  rw [global_frobSq_eq_trace_mul_of_isSymm hDiff]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm (simplexGram m) G, hcross, hDsq, alpha]
  field_simp [hmr, hm1r]
  <;> ring

/-- Cauchy-Schwarz on the actual nonzero eigenvalue support. The trace bound
is proved here, not assumed. -/
theorem global_trace_square_lower_of_rank_le {m d : ℕ} (hd : 1 ≤ d)
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.IsHermitian)
    (hrank : G.rank ≤ d) (hdiag : ∀ i, G i i = 1) :
    (m : ℝ)^2 / (d : ℝ) ≤ Matrix.trace (G*G) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnn : 0 ≤ Matrix.trace (G*G) := by
    rw [global_trace_square_eq_sum_eigenvalues_sq hG]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hCS := global_trace_sq_le_rank_mul_trace_square hG
  rw [global_trace_of_unit_diagonal G hdiag] at hCS
  have hrR : (G.rank : ℝ) ≤ (d : ℝ) := by exact_mod_cast hrank
  have hbound : (m : ℝ)^2 ≤ (d : ℝ) * Matrix.trace (G*G) :=
    hCS.trans (mul_le_mul_of_nonneg_right hrR hnn)
  exact (div_le_iff₀ hdR).mpr (by simpa [mul_comm] using hbound)

/-- The rank-deficiency Gram bound in the original corollary.
The PSD matrix can have arbitrary ambient realization dimension. -/
theorem global_simplex_frobSq_lower_of_rank_le {m d : ℕ}
    (hm : 2 ≤ m) (hd : 1 ≤ d)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1) (hrank : G.rank ≤ d) :
    (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) ≤
      frobSq (G-simplexGram m) := by
  have htr := global_trace_square_lower_of_rank_le hd hG.isHermitian hrank hdiag
  have hm1R : (0 : ℝ) < (m : ℝ)-1 := by
    have : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    linarith
  have he := global_entrySum_nonneg hG
  have hterm : 0 ≤ 2 / ((m : ℝ)-1) * entrySum G :=
    mul_nonneg (div_nonneg (by norm_num) hm1R.le) he
  rw [global_simplex_frobSq_identity hm G (isHermitian_iff_isSymm.mp hG.isHermitian) hdiag]
  have hid : (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) =
      (m : ℝ)^2 / (d : ℝ) - (m : ℝ)^2 / ((m : ℝ)-1) := by ring
  rw [hid]
  linarith

/-- Rank of the concrete configuration Gram is at most the ambient dimension. -/
theorem global_gram_rank_le_ambient {m ambient : ℕ} (X : Config m ambient) :
    (gram X).rank ≤ ambient := by
  let A : Matrix (Fin m) (Fin ambient) ℝ := fun i k => X i k
  have hgram : gram X = A*A.transpose := by
    ext i j
    rw [gram_apply, euclidean_inner_eq_sum, Matrix.mul_apply]
    rfl
  rw [hgram]
  exact (Matrix.rank_mul_le_left A A.transpose).trans A.rank_le_width

theorem global_entrySum_gram {m ambient : ℕ} (X : Config m ambient) :
    entrySum (gram X) = ‖∑ i, X i‖^2 := by
  rw [← global_trace_mul_onesMatrix (gram X), global_trace_gram_mul_onesMatrix X]

theorem global_config_simplex_frobSq_identity {m ambient : ℕ} (hm : 2 ≤ m)
    (X : Config m ambient) (hX : UnitConfig X) :
    frobSq (gram X-simplexGram m) = Matrix.trace (gram X*gram X) -
      (m : ℝ)^2 / ((m : ℝ)-1) + 2 / ((m : ℝ)-1) * ‖∑ i, X i‖^2 := by
  rw [global_simplex_frobSq_identity hm (gram X)
    (isHermitian_iff_isSymm.mp (gram_posSemidef X).isHermitian)
    (gram_diagonal_unit X hX), global_entrySum_gram]

/-- The rank bound for actual configurations in an arbitrary ambient dimension. -/
theorem global_config_simplex_frobSq_lower_of_rank_le {m ambient d : ℕ}
    (hm : 2 ≤ m) (hd : 1 ≤ d) (X : Config m ambient) (hX : UnitConfig X)
    (hrank : (gram X).rank ≤ d) :
    (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) ≤
      frobSq (gram X-simplexGram m) :=
  global_simplex_frobSq_lower_of_rank_le hm hd (gram X) (gram_posSemidef X)
    (gram_diagonal_unit X hX) hrank

/-- Specialization when the given ambient space itself has dimension d. -/
theorem global_config_simplex_frobSq_lower_of_ambient {m d : ℕ}
    (hm : 2 ≤ m) (hd : 1 ≤ d) (X : Config m d) (hX : UnitConfig X) :
    (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) ≤
      frobSq (gram X-simplexGram m) :=
  global_config_simplex_frobSq_lower_of_rank_le hm hd X hX
    (global_gram_rank_le_ambient X)

theorem global_rank_deficiency_coefficient_pos {m d : ℕ}
    (hd : 1 ≤ d) (hdm : d < m-1) :
    0 < (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdmR : (d : ℝ) < (m : ℝ)-1 := by
    have hh : (d : ℝ)+1 < m := by exact_mod_cast (show d+1 < m by omega)
    linarith
  have hm1R : (0 : ℝ) < (m : ℝ)-1 := lt_trans hdR hdmR
  have hmR : (0 : ℝ) < m := by linarith
  have hid : 1 / (d : ℝ) - 1 / ((m : ℝ)-1) =
      ((m : ℝ)-1-(d : ℝ)) / ((d : ℝ)*((m : ℝ)-1)) := by
    field_simp [hdR.ne', hm1R.ne']
    <;> ring
  rw [hid]
  exact mul_pos (sq_pos_of_pos hmR)
    (div_pos (sub_pos.mpr hdmR) (mul_pos hdR hm1R))

/-- Original rank-deficiency range: a strictly positive quantitative obstruction,
with no restriction on a possible ambient realization dimension. -/
theorem global_rank_deficiency_gap {m d : ℕ}
    (hd : 1 ≤ d) (hdm : d < m-1)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1) (hrank : G.rank ≤ d) :
    0 < (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) ∧
      (m : ℝ)^2 * (1 / (d : ℝ) - 1 / ((m : ℝ)-1)) ≤
        frobSq (G-simplexGram m) :=
  ⟨global_rank_deficiency_coefficient_pos hd hdm,
    global_simplex_frobSq_lower_of_rank_le (by omega) hd G hG hdiag hrank⟩

#print axioms global_gram_rank_le_ambient
#print axioms global_config_simplex_frobSq_identity
#print axioms global_config_simplex_frobSq_lower_of_rank_le
#print axioms global_config_simplex_frobSq_lower_of_ambient
#print axioms global_rank_deficiency_coefficient_pos
#print axioms global_rank_deficiency_gap
#print axioms global_simplex_frobSq_identity
#print axioms global_trace_square_lower_of_rank_le
#print axioms global_simplex_frobSq_lower_of_rank_le
#print axioms global_trace_square_eq_sum_eigenvalues_sq
#print axioms global_trace_sq_le_rank_mul_trace_square
end SimplexFull.Geometry
