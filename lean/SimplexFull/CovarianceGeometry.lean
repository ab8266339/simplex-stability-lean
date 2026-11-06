import SimplexFull.ActualProcrustes
import SimplexFull.GaussianShift
noncomputable section
open scoped Matrix.Norms.L2Operator Topology MatrixOrder
namespace SimplexFull.Geometry
def channelCovariance {m d : ℕ} (X : Config m d) : ShapeMatrix m :=
  alpha m • gram X + (m:ℝ)⁻¹ • onesMatrix m
lemma channelCovariance_posSemidef {m d : ℕ} (X : Config m d) (hm : 1 ≤ m) :
    (channelCovariance X).PosSemidef :=
  ((gram_posSemidef X).smul (alpha_nonneg hm)).add
    (SimplexFull.posSemidef_onesMatrix.smul (inv_nonneg.mpr (Nat.cast_nonneg m)))
lemma channelCovariance_of_simplex {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) : channelCovariance V = 1 := by
  rw [channelCovariance, hV, simplexGram, smul_smul,
    mul_inv_cancel₀ (alpha_ne_zero_of_gt_one m hm), one_smul, centering, sub_add_cancel]
lemma continuous_channelCovariance (m d : ℕ) : Continuous (@channelCovariance m d) :=
  (continuous_const.smul (continuous_gram m d)).add continuous_const
lemma channelCovariance_act {m d : ℕ} (U : Orthogonal d) (X : Config m d) :
    channelCovariance (act U X) = channelCovariance X := by
  simp only [channelCovariance, gram_act]
lemma exists_local_channelCovariance_posDef {m d : ℕ} (V : Config m d) (hm : 1 < m)
    (hV : gram V = simplexGram m) :
    ∃ delta > 0, ∀ X : Config m d, procrustesSq X V < delta →
      (channelCovariance X).PosDef := by
  have hopen : IsOpen {X : Config m d | IsUnit (channelCovariance X)} :=
    Units.isOpen.preimage (continuous_channelCovariance m d)
  have hmem : V ∈ {X : Config m d | IsUnit (channelCovariance X)} := by
    change IsUnit (channelCovariance V)
    rw [channelCovariance_of_simplex V hm hV]
    exact isUnit_one
  obtain ⟨eps,heps,hb⟩ := Metric.isOpen_iff.mp hopen V hmem
  refine ⟨eps^2, sq_pos_of_pos heps,?_⟩
  intro X hX
  obtain ⟨a,⟨U,rfl⟩,ha⟩ := exists_lt_of_csInf_lt (procrustesEnergy_range_nonempty X V) hX
  have hclose := aligned_norm_lt_of_energy_lt X V U heps ha
  have hu : IsUnit (channelCovariance (act U.symm X)) := hb (by
    simpa only [Metric.mem_ball, dist_eq_norm] using hclose)
  rw [channelCovariance_act] at hu
  exact (channelCovariance_posSemidef X (by omega)).posDef_iff_isUnit.mpr hu
#print axioms exists_local_channelCovariance_posDef
lemma channelCovariance_eq_iff_gram {m d : ℕ} (hm : 1 < m) (X Y : Config m d) :
    channelCovariance X = channelCovariance Y ↔ gram X = gram Y := by
  constructor
  · intro h
    have he := congrArg (fun A : ShapeMatrix m => (alpha m)⁻¹ •
      (A-(m:ℝ)⁻¹ • onesMatrix m)) h
    simpa only [channelCovariance, add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ (alpha_ne_zero_of_gt_one m hm), one_smul] using he
  · intro h
    simp only [channelCovariance,h]
lemma orthoOrbit_iff_channelCovariance {m d : ℕ} (hm : 1 < m) (X Y : Config m d) :
    orthoOrbit X Y ↔ channelCovariance X = channelCovariance Y := by
  rw [orthoOrbit_iff_gram_eq, channelCovariance_eq_iff_gram hm]
#print axioms orthoOrbit_iff_channelCovariance
end SimplexFull.Geometry