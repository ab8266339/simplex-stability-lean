import SimplexFull.CovarianceGeometry
import SimplexFull.UniformGramBound

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator MatrixOrder Topology

namespace SimplexFull.Geometry

def uniformRootCompletionGram (m : ℕ) (G : ShapeMatrix m) : ShapeMatrix m :=
  CFC.sqrt (alpha m • compression G) + (1 - centering m)

def uniformCovarianceGram (m : ℕ) (G : ShapeMatrix m) : ShapeMatrix m :=
  alpha m • G + (m : ℝ)⁻¹ • onesMatrix m

lemma uniformRootCompletionGram_of_simplex (m : ℕ) (hm : 1 < m) :
    uniformRootCompletionGram m (simplexGram m) = 1 := by
  have hbase : alpha m • compression (simplexGram m) = centering m := by
    rw [compression, simplexGram, Matrix.mul_smul, Matrix.smul_mul,
      centering_idempotent (by omega), centering_idempotent (by omega), smul_smul,
      mul_inv_cancel₀ (alpha_ne_zero_of_gt_one m hm), one_smul]
  rw [uniformRootCompletionGram, hbase,
    CFC.sqrt_unique (centering_idempotent (by omega)) (centering_posSemidef (by omega)).nonneg,
    add_sub_cancel]

lemma uniformCovarianceGram_of_simplex (m : ℕ) (hm : 1 < m) :
    uniformCovarianceGram m (simplexGram m) = 1 := by
  rw [uniformCovarianceGram, simplexGram, smul_smul,
    mul_inv_cancel₀ (alpha_ne_zero_of_gt_one m hm), one_smul, centering, sub_add_cancel]

lemma uniformRootCompletionGram_eq {m d : ℕ} (X : Config m d) :
    uniformRootCompletionGram m (gram X) = rootCompletion X := rfl

lemma uniformCovarianceGram_eq {m d : ℕ} (X : Config m d) :
    uniformCovarianceGram m (gram X) = channelCovariance X := rfl

lemma uniformRootCompletionGram_continuousOn (m : ℕ) (hm : 1 ≤ m) :
    ContinuousOn (uniformRootCompletionGram m) {G : ShapeMatrix m | G.PosSemidef} := by
  have hi : Continuous (fun G : ShapeMatrix m => alpha m • compression G) := by
    unfold compression
    exact continuous_const.smul ((continuous_const.mul continuous_id).mul continuous_const)
  have hs : ContinuousOn (fun G : ShapeMatrix m => CFC.sqrt (alpha m • compression G))
      {G : ShapeMatrix m | G.PosSemidef} :=
    CFC.continuousOn_sqrt.comp hi.continuousOn
      (fun G hG => ((compression_posSemidef hG).smul (alpha_nonneg hm)).nonneg)
  exact hs.add continuous_const.continuousOn

lemma uniformCovarianceGram_continuous (m : ℕ) :
    Continuous (uniformCovarianceGram m) := by
  exact (continuous_const.smul continuous_id).add continuous_const

theorem exists_uniform_gram_unit_radius (m : ℕ) (hm : 3 ≤ m) :
    ∃ eps > 0, ∀ G : ShapeMatrix m, G.PosSemidef →
      ‖G - simplexGram m‖ < eps →
      IsUnit (uniformRootCompletionGram m G) ∧ IsUnit (uniformCovarianceGram m G) := by
  have hm1 : 1 < m := by omega
  letI : NeZero m := ⟨by omega⟩
  have hPSD : (simplexGram m).PosSemidef := SimplexFull.simplexGram_posSemidef
  have hroot := (uniformRootCompletionGram_continuousOn m (by omega)) (simplexGram m) hPSD
  obtain ⟨eta, heta, hunit⟩ := Metric.isOpen_iff.mp
    (Units.isOpen : IsOpen {R : ShapeMatrix m | IsUnit R}) 1 isUnit_one
  obtain ⟨er, her, hrootball⟩ := Metric.continuousWithinAt_iff.mp hroot eta heta
  have hopen : IsOpen {G : ShapeMatrix m | IsUnit (uniformCovarianceGram m G)} :=
    Units.isOpen.preimage (uniformCovarianceGram_continuous m)
  have hmem : simplexGram m ∈ {G : ShapeMatrix m | IsUnit (uniformCovarianceGram m G)} := by
    change IsUnit (uniformCovarianceGram m (simplexGram m))
    rw [uniformCovarianceGram_of_simplex m hm1]
    exact isUnit_one
  obtain ⟨ec, hec, hcovball⟩ := Metric.isOpen_iff.mp hopen (simplexGram m) hmem
  refine ⟨min er ec, lt_min her hec, ?_⟩
  intro G hG hdist
  have hd : dist G (simplexGram m) < min er ec := by
    simpa only [dist_eq_norm] using hdist
  constructor
  · apply hunit
    have hh := hrootball hG (lt_of_lt_of_le hd (min_le_left _ _))
    simpa only [Metric.mem_ball, uniformRootCompletionGram_of_simplex m hm1] using hh
  · exact hcovball (lt_of_lt_of_le hd (min_le_right _ _))

set_option pp.fullNames true
#print axioms uniformRootCompletionGram_continuousOn
#print axioms exists_uniform_gram_unit_radius


theorem exists_uniform_geometric_neighborhood (m : ℕ) (hm : 3 ≤ m) :
    ∃ delta > 0, ∀ (d : ℕ) (V X : Config m d),
      gram V = simplexGram m → UnitConfig X → procrustesSq X V < delta →
      IsUnit (rootCompletion X) ∧ (channelCovariance X).PosDef := by
  obtain ⟨eps, heps, hGram⟩ := exists_uniform_gram_unit_radius m hm
  obtain ⟨delta, hdelta, hdeltaGram⟩ := exists_uniform_gram_radius m hm heps
  refine ⟨delta, hdelta, ?_⟩
  intro d V X hV hX hclose
  have hVunit : UnitConfig V := unitConfig_of_simplexGram V (by omega) hV
  have hdist : ‖gram X - simplexGram m‖ < eps := by
    rw [← hV]
    exact hdeltaGram d V X hVunit hX hclose
  obtain ⟨hroot, hcov⟩ := hGram (gram X) (gram_posSemidef X) hdist
  have hroot' : IsUnit (rootCompletion X) := by
    simpa only [uniformRootCompletionGram_eq] using hroot
  have hcov' : IsUnit (channelCovariance X) := by
    simpa only [uniformCovarianceGram_eq] using hcov
  exact ⟨hroot', (channelCovariance_posSemidef X (by omega)).posDef_iff_isUnit.mpr hcov'⟩

#print axioms exists_uniform_geometric_neighborhood

end SimplexFull.Geometry
