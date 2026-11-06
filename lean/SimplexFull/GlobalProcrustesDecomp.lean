import SimplexFull.GlobalProcrustes
noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

theorem global_trace_centering (m : ℕ) (hm : m ≠ 0) :
    Matrix.trace (centering m) = (m : ℝ) - 1 := by
  rw [trace_eq_sum_diag]
  simp_rw [centering_apply_diag]
  rw [sum_const_fin, mul_sub, mul_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm)]

theorem global_trace_gram_mul_onesMatrix {m d : ℕ} (X : Config m d) :
    Matrix.trace (gram X * onesMatrix m) = ‖∑ i, X i‖ ^ 2 := by
  rw [trace_eq_sum_diag]
  have hentry : ∀ i, (gram X * onesMatrix m) i i =
      inner ℝ (X i) (∑ j, X j) := by
    intro i
    rw [Matrix.mul_apply]
    simp_rw [onesMatrix, mul_one, gram_apply]
    exact (inner_sum Finset.univ (fun j => X j) (X i)).symm
  simp_rw [hentry]
  rw [← sum_inner Finset.univ (fun i => X i) (∑ j, X j), real_inner_self_eq_norm_sq]

theorem global_trace_compressed_gram {m d : ℕ} (hm : m ≠ 0) (X : Config m d) :
    Matrix.trace (centering m * gram X * centering m) =
      Matrix.trace (gram X) - (m : ℝ)⁻¹ * ‖∑ i, X i‖ ^ 2 := by
  have hstep1 : Matrix.trace (centering m * gram X * centering m) =
      Matrix.trace ((gram X * centering m) * centering m) := by
    rw [Matrix.mul_assoc]
    exact Matrix.trace_mul_comm (centering m) (gram X * centering m)
  have hstep2 : (gram X * centering m) * centering m = gram X * centering m := by
    rw [Matrix.mul_assoc, centering_mul_self hm]
  rw [hstep1, hstep2]
  have hGP : gram X * centering m =
      gram X - (m : ℝ)⁻¹ • (gram X * onesMatrix m) := by
    rw [centering, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hGP, Matrix.trace_sub, Matrix.trace_smul, global_trace_gram_mul_onesMatrix, smul_eq_mul]

theorem global_frobSq_eq_trace_mul_of_isSymm {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm) :
    frobSq A = Matrix.trace (A * A) := by
  rw [frobSq, trace_eq_sum_diag]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hA.apply i j]
  ring

theorem global_frobSq_sub_centering {m : ℕ} (hm : m ≠ 0)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.IsSymm)
    (hPT : centering m * T = T) (hTP : T * centering m = T) :
    frobSq (T - centering m) =
      Matrix.trace (T * T) - 2 * Matrix.trace T + ((m : ℝ) - 1) := by
  have hsym : (T - centering m).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, hT.eq, (centering_isSymm m).eq]
  rw [global_frobSq_eq_trace_mul_of_isSymm hsym]
  have hsq : (T - centering m) * (T - centering m) =
      T*T - T*centering m - centering m*T + centering m*centering m := by
    noncomm_ring
  rw [hsq, hTP, hPT, centering_mul_self hm, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_sub, global_trace_centering m hm]
  ring

/-- Global orthogonal distance, decomposed into its centroid energy and the
actual centered CFC square-root deviation. No assumptions on the lengths of X. -/
theorem global_procrustesSq_decomposition {m d : ℕ} (hm : 2 ≤ m)
    (X V : Config m d) (hVgram : gram V = simplexGram m) :
    procrustesSq X V = ‖∑ i, X i‖ ^ 2 / (m : ℝ) +
      (alpha m)⁻¹ * frobSq (centeredRoot X - centering m) := by
  have hm0 : m ≠ 0 := by omega
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hm1r : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    linarith
  obtain ⟨hPT,hTP⟩ := centered_mul_centering (centeredRoot_centered X (by omega))
  have hsym : (centeredRoot X).IsSymm :=
    (isHermitian_iff_isSymm).1 (centeredRoot_posSemidef X).isHermitian
  rw [global_procrustesSq_centeredRoot hm X V hVgram,
    global_frobSq_sub_centering hm0 (centeredRoot X) hsym hPT hTP,
    centeredRoot_mul_self X (by omega), centeredGram, compression,
    Matrix.trace_smul, smul_eq_mul, global_trace_compressed_gram hm0 X, alpha]
  field_simp [hmr, hm1r]
  <;> ring

/-- An actual orthogonal motion attains the global infimum, including all
singular configurations. -/
theorem global_procrustesSq_attained {m d : ℕ} (hm : 2 ≤ m)
    (X V : Config m d) (hVgram : gram V = simplexGram m) :
    ∃ U : OrthogonalMotion d, procrustesEnergy X V U = procrustesSq X V := by
  have hm0 : m ≠ 0 := by omega
  have hV : UnitConfig V := unitConfig_of_simplexGram V (by omega) hVgram
  let T := centeredRoot X
  obtain ⟨hPT,hTP⟩ := centered_mul_centering (centeredRoot_centered X (by omega))
  obtain ⟨U,hXP⟩ := global_polar_alignment hm X V hVgram T
    (centeredRoot_posSemidef X) hTP (centeredRoot_mul_self X (by omega))
  have hWgram : gram (act U V) = simplexGram m := by rw [gram_act,hVgram]
  have hWsum : ∑ i, act U V i = 0 :=
    config_barycenter_of_simplexGram (act U V) hm0 hWgram
  have hdot : configDot X (act U V) = Matrix.trace T / alpha m := by
    rw [← configDot_centered_of_sum_zero X (act U V) hWsum, ← hXP,
      ← weightedGram_eq_configDot_recombine, weightedGram_self_eq_trace, hWgram,
      trace_mul_simplexGram_of_centering T hTP, mul_comm, ← div_eq_mul_inv]
  refine ⟨U, ?_⟩
  rw [global_procrustesEnergy X V hV U, hdot,
    global_procrustesSq_centeredRoot hm X V hVgram]
  dsimp only [T]
  ring

#print axioms global_procrustesSq_decomposition
#print axioms global_procrustesSq_attained
#print axioms global_trace_compressed_gram
end SimplexFull.Geometry
