import SimplexFull.ProcrustesFormula
import SimplexFull.CenteredSqrt
import SimplexFull.NormalMinimizer

noncomputable section
open Finset Matrix
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SimplexFull.Geometry

theorem global_recombine_act {m d : ℕ} (U : OrthogonalMotion d)
    (X : Config m d) (A : Matrix (Fin m) (Fin m) ℝ) :
    recombine (act U X) A = act U (recombine X A) := by
  ext j
  simp [recombine_apply, act, map_sum]

theorem global_procrustesEnergy {m d : ℕ} (X V : Config m d)
    (hV : UnitConfig V) (U : OrthogonalMotion d) :
    procrustesEnergy X V U =
      Matrix.trace (gram X) + (m : ℝ) - 2 * configDot X (act U V) := by
  have htrace : Matrix.trace (gram X) = ∑ i, ‖X i‖ ^ 2 := by
    simp [Matrix.trace, gram_apply, real_inner_self_eq_norm_sq]
  rw [htrace]
  have hsq : ∀ i, ‖X i - U (V i)‖ ^ 2 =
      ‖X i‖ ^ 2 + 1 - 2 * inner ℝ (X i) (U (V i)) := by
    intro i
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, hV i]
    ring
  unfold procrustesEnergy configDot
  simp_rw [hsq, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  simp [act, sum_const, card_univ]

/-- Polar alignment by equal Gram matrices, including singular centered Gram. -/
theorem global_polar_alignment {m d : ℕ} (hm : 2 ≤ m) (X V : Config m d)
    (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m)) :
    ∃ U : OrthogonalMotion d, recombine (act U V) T = centeredConfig X := by
  have hα : alpha m ≠ 0 := alpha_ne_zero_of_gt_one m (by omega)
  have hTsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  have hPsym : (centering m).IsSymm := procrustes_centering_isSymm m
  have hg : gram (recombine V T) = gram (centeredConfig X) := by
    rw [gram_recombine, hTsym.eq, hVgram, simplexGram,
      Matrix.mul_smul, Matrix.smul_mul, hTP, hTsq, smul_smul,
      inv_mul_cancel₀ hα, one_smul]
    rw [centeredConfig, gram_recombine, hPsym.eq]
  obtain ⟨U, hU⟩ := exists_orthogonal_of_gram_eq (recombine V T) (centeredConfig X) hg
  refine ⟨U, ?_⟩
  rw [global_recombine_act]
  funext i
  exact hU i

/-- Exact global sInf Procrustes formula, without unit-length or rank
assumptions on X, and without invertibility of the positive square root. -/
theorem global_procrustesSq_sqrt {m d : ℕ} (hm : 2 ≤ m) (X V : Config m d)
    (hVgram : gram V = simplexGram m)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.PosSemidef)
    (hTP : T * centering m = T)
    (hTsq : T * T = (alpha m) • (centering m * gram X * centering m)) :
    procrustesSq X V =
      Matrix.trace (gram X) + (m : ℝ) - 2 / alpha m * Matrix.trace T := by
  have hm0 : m ≠ 0 := by omega
  have hV : UnitConfig V := unitConfig_of_simplexGram V (by omega) hVgram
  have hTsym : T.IsSymm := (isHermitian_iff_isSymm).1 hT.isHermitian
  obtain ⟨U, hXP⟩ := global_polar_alignment hm X V hVgram T hT hTP hTsq
  let W := act U V
  have hgramW : gram W = simplexGram m := by
    dsimp only [W]
    rw [gram_act, hVgram]
  have hWW : weightedGram T W W = Matrix.trace T / alpha m := by
    rw [weightedGram_self_eq_trace, hgramW, trace_mul_simplexGram_of_centering T hTP,
      mul_comm, ← div_eq_mul_inv]
  have hcross : ∀ Z : Config m d, gram Z = simplexGram m →
      configDot (centeredConfig X) Z ≤ Matrix.trace T / alpha m := by
    intro Z hZ
    have hnn := weightedGram_self_nonneg T hT (W - Z)
    rw [weightedGram_sub_sub, ← weightedGram_comm_of_isSymm hTsym W Z] at hnn
    have hZZ : weightedGram T Z Z = Matrix.trace T / alpha m := by
      rw [weightedGram_self_eq_trace, hZ, trace_mul_simplexGram_of_centering T hTP,
        mul_comm, ← div_eq_mul_inv]
    have hWZ : weightedGram T W Z = configDot (centeredConfig X) Z := by
      rw [weightedGram_eq_configDot_recombine, hXP]
    rw [hWW, hZZ, hWZ] at hnn
    linarith
  have hscale : 2 * (Matrix.trace T / alpha m) = 2 / alpha m * Matrix.trace T := by
    ring
  have hge : ∀ U' : OrthogonalMotion d,
      Matrix.trace (gram X) + (m : ℝ) - 2 / alpha m * Matrix.trace T ≤
        procrustesEnergy X V U' := by
    intro U'
    have hZgram : gram (act U' V) = simplexGram m := by rw [gram_act, hVgram]
    have hZsum : ∑ i, act U' V i = 0 :=
      config_barycenter_of_simplexGram (act U' V) hm0 hZgram
    have hdotle : configDot X (act U' V) ≤ Matrix.trace T / alpha m := by
      rw [← configDot_centered_of_sum_zero X (act U' V) hZsum]
      exact hcross (act U' V) hZgram
    rw [global_procrustesEnergy X V hV U']
    rw [← hscale]
    linarith
  have hWsum : ∑ i, W i = 0 := config_barycenter_of_simplexGram W hm0 hgramW
  have hdotEq : configDot X W = Matrix.trace T / alpha m := by
    rw [← configDot_centered_of_sum_zero X W hWsum, ← hXP,
      ← weightedGram_eq_configDot_recombine, hWW]
  have hattain : procrustesEnergy X V U =
      Matrix.trace (gram X) + (m : ℝ) - 2 / alpha m * Matrix.trace T := by
    rw [global_procrustesEnergy X V hV U, show act U V = W from rfl, hdotEq, hscale]
  apply le_antisymm
  · exact (procrustesSq_le_energy X V U).trans_eq hattain
  · apply le_csInf (procrustesEnergy_range_nonempty X V)
    rintro r ⟨U', rfl⟩
    exact hge U'

/-- The square root in the global formula is the actual CFC square root. -/
theorem global_procrustesSq_centeredRoot {m d : ℕ} (hm : 2 ≤ m) (X V : Config m d)
    (hVgram : gram V = simplexGram m) :
    procrustesSq X V =
      Matrix.trace (gram X) + (m : ℝ) -
        2 / alpha m * Matrix.trace (centeredRoot X) := by
  apply global_procrustesSq_sqrt hm X V hVgram (centeredRoot X)
    (centeredRoot_posSemidef X)
    (centered_mul_centering (centeredRoot_centered X (by omega))).2
  exact centeredRoot_mul_self X (by omega)

#print axioms global_procrustesSq_centeredRoot
#print axioms global_procrustesSq_sqrt
#print axioms global_recombine_act
#print axioms global_procrustesEnergy
#print axioms global_polar_alignment
end SimplexFull.Geometry
